/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/for_each_fn.h"
#include "kernel/replace_fn.h"
#include "library/locals.h"
#include "library/class.h"
#include "library/trace.h"
#include "library/placeholder.h"
#include "library/protected.h"
#include "library/private.h"
#include "library/aliases.h"
#include "library/explicit.h"
#include "library/constants.h"
#include "library/reducible.h"
#include "library/scoped_ext.h"
#include "library/tactic/elaborate.h"
#include "library/typed_expr.h"
#include "library/annotation.h"
#include "frontends/lean/util.h"
#include "frontends/lean/decl_util.h"
#include "frontends/lean/tokens.h"
#include "frontends/lean/decl_attributes.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/elaborator.h"
#include "frontends/lean/builtin_exprs.h"

namespace lean {
ast_id parse_univ_params(parser & p, buffer<name> & lp_names) {
    if (p.curr_is_token(get_lcurly_tk())) {
        auto& data = p.new_ast("levels", p.pos());
        p.next();
        while (!p.curr_is_token(get_rcurly_tk())) {
            auto pos0 = p.pos();
            ast_id id; name l;
            std::tie(id, l) = p.check_atomic_id_next("invalid declaration, identifier expected");
            data.push(id);
            lp_names.push_back(l);
            p.add_local_level(l, mk_param_univ(l));
            if (p.pos() == pos0) break;
        }
        p.next();
        return data.m_id;
    } else {
        return 0;
    }
}

/*
Naming instances.

For `instance [...] : C (D x y) t u`, we generate the name `D.C`.
However, we remove the current namespace if it is a prefix of `C` and/or `D`.
(Exception: if `C` *equals* the current namespace, we keep the last component of `C`.
Otherwise, the resulting name would be the same as `D`,
which could be a name in the current namespace.)
The current namespace will implicitly be prepended to the resulting name.

For `instance [...] : C α t u`, where `α` is a variable
(at parse time--it might turn into a coercion later, during typechecking)
we generate the name `C`, stripping off the current namespace if possible.
The heuristic can fail in the presence of parameters.

Examples:

```
def foo := ℕ
namespace foo
instance : has_add foo := nat.has_add   -- foo.has_add, not foo.foo.has_add
end

namespace category_theory

class is_right_adjoint := ...
def forgetful_functor := ...
instance : is_right_adjoint forgetful_functor := ...
-- category_theory.forgetful_functor.is_right_adjoint, not
-- category_theory.category_theory.forgetful_functor.category_theory.is_right_adjoint

end category_theory

class lie_algebra (α : Type) : Type :=
(bracket : α → α → α)

namespace lie_algebra

def gl : Type := unit
instance : lie_algebra gl := ⟨λ _ _, ()⟩
-- lie_algebra.gl.lie_algebra, not lie_algebra.gl (already used)

end lie_algebra

class moo (α : Type*)
class zoo (β : Type*)

namespace zoo
instance (β : Type*) [zoo β] : moo β := ⟨⟩  -- zoo.moo
end zoo
```

*/
optional<name> heuristic_inst_name(name const & ns, expr const & type) {
    expr it = type;
    while (is_pi(it)) it = binding_body(it);

    // Extract type class name.
    buffer<expr> args;
    expr const & C = get_app_args(it, args);
    if (!is_constant(C)) return {};
    name class_name = const_name(C);

    // Look at head symbol of last argument.
    if (!args.size()) return {};
    expr arg_head = args.back();
    if (class_name == get_has_coe_to_fun_name() || class_name == get_has_coe_to_sort_name()) {
        // TODO(gabriel): generalize, and pick the last non-out_param argument
        arg_head = args[0];
    }
    while (true) {
        if (is_app(arg_head)) {
            arg_head = app_fn(arg_head);
        } else if (is_typed_expr(arg_head)) {
            arg_head = get_typed_expr_expr(arg_head);
        } else if (is_explicit_or_partial_explicit(arg_head)) {
            arg_head = get_explicit_or_partial_explicit_arg(arg_head);
        } else if (is_annotation(arg_head)) {
            arg_head = get_annotation_arg(arg_head);
        } else {
            break;
        }
    }

    // Generate name for argument.
    name arg_name;
    if (is_constant(arg_head)) {
        arg_name = const_name(arg_head);
    } else if (is_sort(arg_head) || is_sort_wo_universe(arg_head)) {
        arg_name = "sort";
    } else if (is_pi(arg_head)) {
        arg_name = "pi";
    } else if (is_field_notation(arg_head)) {
        expr lhs = macro_arg(arg_head, 0);
        arg_name = get_field_notation_field_name(arg_head);

        // The field projection does not have the full name.
        // If we can guess the type of the lhs, prepend it.
        if (is_local(lhs)) {
            expr type = get_app_fn(mlocal_type(lhs));
            if (is_constant(type))
                arg_name = const_name(type) + arg_name;
        }
    } else if (is_local(arg_head)) {
        // only class name
    } else {
        return {};
    }

    // Strip namespace prefix of class.
    if (class_name == ns && class_name.is_string()) {
        class_name = class_name.get_string();
    } else if (ns && is_prefix_of(ns, class_name)) {
        class_name = class_name.replace_prefix(ns, name());
    }

    name inst_name = arg_name + class_name;

    // Strip namespace prefix to prevent duplicate namespace.
    if (ns && is_prefix_of(ns, inst_name)) {
        inst_name = inst_name.replace_prefix(ns, name());
    }

    if (!inst_name) {
        return {};
    } else {
        return optional<name>(inst_name);
    }
}

expr parse_single_header(parser & p, ast_data & parent, declaration_name_scope & scope,
                         buffer <name> & lp_names, buffer <expr> & params,
                         bool is_example, bool is_instance) {
    auto c_pos  = p.pos();
    name c_name;
    if (is_example) {
        c_name = "_example";
        scope.set_name(c_name);
        parent.push(0).push(0);
    } else {
        parent.push(is_instance ? 0 : parse_univ_params(p, lp_names));
        if (!is_instance || p.curr_is_identifier()) {
            ast_id id;
            std::tie(id, c_name) = p.check_decl_id_next("invalid declaration, identifier expected");
            parent.push(id);
            scope.set_name(c_name);
        } else {
            parent.push(0);
        }
    }
    auto& bis = p.new_ast("binders", p.pos());
    p.parse_optional_binders(&bis, params, /* allow_default */ true, /* explicit delimiters */ true);
    parent.push(bis.m_children.empty() ? 0 : bis.m_id);
    for (expr const & param : params)
        p.add_local(param);
    expr type;
    if (p.curr_is_token(get_colon_tk())) {
        p.next();
        type = p.parse_expr();
        parent.push(p.get_id(type));
    } else {
        type = p.save_pos(mk_expr_placeholder(), c_pos);
        parent.push(0);
    }
    if (is_instance && c_name.is_anonymous()) {
        if (used_match_idx())
            throw parser_error("invalid instance, pattern matching cannot be used in the type of anonymous instance declarations", c_pos);
        /* Try to synthesize name */
        if (auto n = heuristic_inst_name(get_namespace(p.env()), type)) {
            c_name = *n;
        } else {
            p.maybe_throw_error({"failed to synthesize instance name, name should be provided explicitly", c_pos});
            c_name = mk_unused_name(p.env(), "_inst");
        }
        scope.set_name(c_name);
    }
    lean_assert(!c_name.is_anonymous());
    return p.save_pos(mk_local(c_name, type), c_pos);
}

expr parse_single_header(dummy_def_parser & p, declaration_name_scope & scope, buffer <name> & lp_names, buffer <expr> & params,
                         bool is_example, bool is_instance) {
    auto c_pos  = p.pos();
    name c_name;
    if (is_example) {
        c_name = "_example";
        scope.set_name(c_name);
    } else {
        lp_names = p.get_univ_params();
        c_name = p.get_name();
        scope.set_name(c_name);
    }

    params = p.get_binders();
    for (expr const & param : params)
        p.add_local(param);
    expr type = p.get_type();
    if (is_instance && c_name.is_anonymous()) {
        if (used_match_idx())
            throw parser_error("invalid instance, pattern matching cannot be used in the type of anonymous instance declarations", c_pos);
        if (auto n = heuristic_inst_name(get_namespace(p.env()), type)) {
            c_name = *n;
        } else {
            p.maybe_throw_error({"failed to synthesize instance name, name should be provided explicitly", c_pos});
            c_name = mk_unused_name(p.env(), "_inst");
        }
        scope.set_name(c_name);
    }
    lean_assert(!c_name.is_anonymous());
    return mk_local(c_name, type);
}

void parse_mutual_header(parser & p, ast_data & parent, buffer <name> & lp_names, buffer <expr> & cs, buffer <expr> & params) {
    auto& names = p.new_ast("mutuals", p.pos());
    parent.push(parse_univ_params(p, lp_names)).push(names.m_id);
    while (true) {
        auto c_pos  = p.pos();
        ast_id c_id; name c_name;
        std::tie(c_id, c_name) = p.check_decl_id_next("invalid mutual declaration, identifier expected");
        names.push(c_id);
        cs.push_back(p.save_pos(mk_local(c_name, mk_expr_placeholder()), c_pos));
        if (!p.curr_is_token(get_comma_tk()))
            break;
        p.next();
    }
    if (cs.size() < 2) {
        throw parser_error("invalid mutual declaration, must provide more than one identifier (separated by commas)", p.pos());
    }
    auto& bis = p.new_ast("binders", p.pos());
    p.parse_optional_binders(&bis, params, /* allow_default */ true, /* explicit delimiters */ true);
    parent.push(bis.m_children.empty() ? 0 : bis.m_id);
    for (expr const & param : params)
        p.add_local(param);
    for (expr const & c : cs)
        p.add_local(c);
}

pair<expr, decl_attributes> parse_inner_header(parser & p, ast_data & parent, name const & c_expected) {
    decl_attributes attrs;
    p.check_token_next(get_with_tk(), "invalid mutual declaration, 'with' expected");
    parent.push(attrs.parse(p));
    auto id_pos = p.pos();
    ast_id n_id; name n;
    std::tie(n_id, n) = p.check_decl_id_next("invalid mutual declaration, identifier expected");
    parent.push(n_id);
    if (c_expected != n)
        throw parser_error(sstream() << "invalid mutual declaration, '" << c_expected << "' expected",
                           id_pos);
    /* Remark: if this is a private definition, the private prefix must have been set
       before invoking this procedure. */
    declaration_name_scope scope(n);
    p.check_token_next(get_colon_tk(), "invalid mutual declaration, ':' expected");
    expr e = p.parse_expr();
    parent.push(p.get_id(e));
    return {e, attrs};
}

/** \brief Version of collect_locals(expr const & e, collected_locals & ls) that ignores local constants occurring in
    tactics. */
void collect_locals_ignoring_tactics(expr const & e, collected_locals & ls) {
    if (!has_local(e)) return;
    for_each(e, [&](expr const & e, unsigned) {
            if (!has_local(e)) return false;
            if (is_by(e))      return false; // do not visit children
            if (is_local(e))   ls.insert(e);
            return true;
        });
}

name_set collect_univ_params_ignoring_tactics(expr const & e, name_set const & ls) {
    if (!has_param_univ(e)) return ls;
    name_set r = ls;
    for_each(e, [&](expr const & e, unsigned) {
            if (!has_param_univ(e)) {
                return false;
            } else if (is_by(e)) {
                return false;
            } else if (is_sort(e)) {
                collect_univ_params_core(sort_level(e), r);
            } else if (is_constant(e)) {
                for (auto const & l : const_levels(e))
                    collect_univ_params_core(l, r);
            }
            return true;
        });
    return r;
}

/** \brief Collect annonymous instances in section/namespace declarations such as:

        variable [decidable_eq A]
*/
static void collect_annonymous_inst_implicit(parser_info const & p, collected_locals & locals, name_set & lp_found) {
    buffer<pair<name, expr>> entries;
    to_buffer(p.get_local_entries(), entries);
    unsigned i = entries.size();
    while (i > 0) {
        --i;
        auto const & entry = entries[i];
        if (is_local(entry.second) && !locals.contains(entry.second) && local_info(entry.second).is_inst_implicit() &&
            // remark: remove the following condition condition, if we want to auto inclusion also for non anonymous ones.
            is_anonymous_inst_name(entry.first)) {
            bool ok = true;
            for_each(mlocal_type(entry.second), [&](expr const & e, unsigned) {
                    if (!ok) return false; // stop
                    if (is_local(e) && !locals.contains(e))
                        ok = false;
                    return true;
                });
            if (ok) {
                locals.insert(entry.second);
                lp_found = collect_univ_params_ignoring_tactics(entry.second, lp_found);
            }
        }
    }
}

/** \brief Sort local names by order of occurrence, and copy the associated parameters to ps */
static void sort_locals(buffer<expr> const & locals, parser_info const & p, buffer<expr> & ps) {
    buffer<expr> extra;
    name_set     explicit_param_names;
    for (expr const & p : ps) {
        explicit_param_names.insert(mlocal_name(p));
    }
    for (expr const & l : locals) {
        // we only copy the locals that are in p's local context
        if (p.is_local_decl_user_name(l) && !explicit_param_names.contains(mlocal_name(l)))
            extra.push_back(l);
    }
    std::sort(extra.begin(), extra.end(), [&](expr const & p1, expr const & p2) {
            bool is_var1 = p.is_local_variable(p1);
            bool is_var2 = p.is_local_variable(p2);
            if (!is_var1 && is_var2)
                return true;
            else if (is_var1 && !is_var2)
                return false;
            else
                return p.get_local_index(p1) < p.get_local_index(p2);
        });
    buffer<expr> new_ps;
    new_ps.append(extra);
    new_ps.append(ps);
    ps.clear();
    ps.append(new_ps);
}

/** TODO(Leo): mark as static */
void update_univ_parameters(parser_info & p, buffer<name> & lp_names, name_set const & found) {
    unsigned old_sz = lp_names.size();
    found.for_each([&](name const & n) {
            if (std::find(lp_names.begin(), lp_names.begin() + old_sz, n) == lp_names.begin() + old_sz)
                lp_names.push_back(n);
        });
    std::sort(lp_names.begin(), lp_names.end(), [&](name const & n1, name const & n2) {
            return p.get_local_level_index(n1) < p.get_local_level_index(n2);
        });
}

expr replace_locals_preserving_pos_info(expr const & e, unsigned sz, expr const * from, expr const * to) {
    bool use_cache = false;
    return replace(e, [&](expr const & e, unsigned) {
            if (is_local(e)) {
                unsigned i = sz;
                while (i > 0) {
                    --i;
                    if (mlocal_name(from[i]) == mlocal_name(e)) {
                        return some_expr(copy_tag(e, copy(to[i])));
                    }
                }
            }
            return none_expr();
        }, use_cache);
}

expr replace_locals_preserving_pos_info(expr const & e, buffer<expr> const & from, buffer<expr> const & to) {
    lean_assert(from.size() == to.size());
    return replace_locals_preserving_pos_info(e, from.size(), from.data(), to.data());
}

expr replace_local_preserving_pos_info(expr const & e, expr const & from, expr const & to) {
    return replace_locals_preserving_pos_info(e, 1, &from, &to);
}

void collect_implicit_locals(parser_info & p, buffer<name> & lp_names, buffer<expr> & params, buffer<expr> const & all_exprs) {
    collected_locals locals;
    buffer<expr> include_vars;
    name_set lp_found;
    name_set given_params;
    /* Process variables included using the 'include' command */
    p.get_include_variables(include_vars);
    for (expr const & param : include_vars) {
        if (is_local(param)) {
            collect_locals_ignoring_tactics(mlocal_type(param), locals);
            lp_found = collect_univ_params_ignoring_tactics(mlocal_type(param), lp_found);
            locals.insert(param);
        }
    }
    /* Process explicit parameters */
    for (expr const & param : params) {
        collect_locals_ignoring_tactics(mlocal_type(param), locals);
        lp_found = collect_univ_params_ignoring_tactics(mlocal_type(param), lp_found);
        locals.insert(param);
        given_params.insert(mlocal_name(param));
    }
    /* Process expressions used to define declaration. */
    for (expr const & e : all_exprs) {
        collect_locals_ignoring_tactics(e, locals);
        lp_found = collect_univ_params_ignoring_tactics(e, lp_found);
    }
    collect_annonymous_inst_implicit(p, locals, lp_found);
    sort_locals(locals.get_collected(), p, params);
    update_univ_parameters(p, lp_names, lp_found);
    /* Add as_is annotation to section variables and parameters */
    buffer<expr> old_params;
    for (unsigned i = 0; i < params.size(); i++) {
        expr & param = params[i];
        old_params.push_back(param);
        expr type          = mlocal_type(param);
        expr new_type      = replace_locals_preserving_pos_info(type, i, old_params.data(), params.data());
        if (!given_params.contains(mlocal_name(param))) {
            new_type = copy_tag(type, mk_as_is(new_type));
        }
        param = copy_tag(param, update_mlocal(param, new_type));
    }
}

void collect_implicit_locals(parser_info & p, buffer<name> & lp_names, buffer<expr> & params, std::initializer_list<expr> const & all_exprs) {
    buffer<expr> tmp; tmp.append(all_exprs.size(), all_exprs.begin());
    collect_implicit_locals(p, lp_names, params, tmp);
}

void collect_implicit_locals(parser_info & p, buffer<name> & lp_names, buffer<expr> & params, expr const & e) {
    buffer<expr> all_exprs; all_exprs.push_back(e);
    collect_implicit_locals(p, lp_names, params, all_exprs);
}

void elaborate_params(elaborator & elab, buffer<expr> const & params, buffer<expr> & new_params) {
    for (unsigned i = 0; i < params.size(); i++) {
        expr const & param = params[i];
        expr type          = replace_locals_preserving_pos_info(mlocal_type(param), i, params.data(), new_params.data());
        elab.freeze_local_instances();
        expr new_type      = elab.elaborate_type(type);
        elab.unfreeze_local_instances();
        expr new_param     = elab.push_local(mlocal_pp_name(param), new_type, local_info(param));
        new_params.push_back(new_param);
    }
}

environment add_local_ref(parser_info & p, environment const & env, name const & c_name,
                          name const & c_real_name, buffer<name> const & lp_names,
                          buffer<expr> const & var_params) {
    buffer<expr> params;
    buffer<name> lps;
    for (name const & u : lp_names) {
        if (!p.is_local_level(u)) {
            /* Stop, it is a definition parameter */
            break;
        } else if (p.is_local_level_variable(u)) {
            /* Stop, it is a parser universe variable (i.e., it has been declared using the `universe variable` command */
            break;
        } else {
            lps.push_back(u);
        }
    }
    for (expr const & e : var_params) {
        if (!p.is_local_decl(e)) {
            /* Stop, it is a definition parameter */
            break;
        } else if (p.is_local_variable(e)) {
            /* Stop, it is a parser variable (i.e., it has been declared using the `variable` command */
            break;
        } else {
            /* It is a parser parameter (i.e., it has been declared with the `parameter` command */
            params.push_back(e);
        }
    }
    if (lps.empty() && params.empty()) return env;
    /*
      Procedures such as `collect_implicit_locals` wrap parameter types with the `as_is` annotation.
      So, we remove these annotations before creating the local reference using `mk_local_ref`.
      Remark: the resulting object is wrapped with the macro `as_atomic`.

      Remark: The local constants created here and `collect_implicit_locals` are not structurally
      equal. That is, `l : ty` is not structurally equal to `l : as_is ty`, but they are definitionally
      equal, and moreover the collection method relies on the fact that they have the same internal
      id.
    */
    buffer<expr> new_params;
    for (unsigned i = 0; i < params.size(); i++) {
        expr & param = params[i];
        expr type          = mlocal_type(param);
        if (is_as_is(type))
            type = get_as_is_arg(type);
        expr new_type      = replace_locals_preserving_pos_info(type, i, params.data(), new_params.data());
        new_params.push_back(copy_tag(param, update_mlocal(param, new_type)));
    }
    expr ref = mk_local_ref(c_real_name, param_names_to_levels(to_list(lps)), new_params);
    return p.add_local_ref(env, c_name, ref);
}

environment add_alias(environment const & env, bool is_protected, name const & c_name, name const & c_real_name) {
    if (c_name != c_real_name) {
        if (is_protected)
            return add_expr_alias_rec(env, get_protected_shortest_name(c_real_name), c_real_name);
        else
            return add_expr_alias_rec(env, c_name, c_real_name);
    } else {
        return env;
    }
}

struct definition_info {
    name     m_prefix; // prefix for local names
    name     m_actual_prefix; // actual prefix used to create kernel declaration names. m_prefix and m_actual_prefix are different for scoped/private declarations.
    bool     m_is_private{true}; // pattern matching outside of definitions should generate private names
    /* m_is_meta_decl == true iff declaration uses `meta` keyword */
    bool     m_is_meta_decl{false};
    /* m_is_meta == true iff the current subexpression can use meta declarations and code.
       Remark: a regular (i.e., non meta) declaration provided by the user may contain a meta subexpression (e.g., tactic).
    */
    bool     m_is_meta{false};      // true iff current block
    bool     m_is_noncomputable{false};
    bool     m_is_lemma{false};
    bool     m_aux_lemmas{false};
    unsigned m_next_match_idx{1};
};

MK_THREAD_LOCAL_GET_DEF(definition_info, get_definition_info);

declaration_info_scope::declaration_info_scope(name const & ns, decl_cmd_kind kind, decl_modifiers const & modifiers) {
    definition_info & info = get_definition_info();
    lean_assert(info.m_prefix.is_anonymous());
    info.m_prefix           = name(); // prefix is used to create local name
    /* Remark: if info.m_actual_prefix is not `anonymous`, then it has already been set using private_name_scope */
    if (info.m_actual_prefix.is_anonymous()) {
        info.m_actual_prefix = ns;
    }
    info.m_is_private       = modifiers.m_is_private;
    info.m_is_meta_decl     = modifiers.m_is_meta;
    info.m_is_meta          = modifiers.m_is_meta;
    info.m_is_noncomputable = modifiers.m_is_noncomputable;
    info.m_is_lemma         = kind == decl_cmd_kind::Theorem;
    info.m_aux_lemmas       = kind != decl_cmd_kind::Theorem && !modifiers.m_is_meta;
    info.m_next_match_idx = 1;
}

declaration_info_scope::declaration_info_scope(environment const & env, decl_cmd_kind kind, decl_modifiers const & modifiers):
    declaration_info_scope(get_namespace(env), kind, modifiers) {}

declaration_info_scope::declaration_info_scope(parser const & p, decl_cmd_kind kind, decl_modifiers const & modifiers):
    declaration_info_scope(get_namespace(p.env()), kind, modifiers) {}

declaration_info_scope::~declaration_info_scope() {
    get_definition_info() = definition_info();
}

bool declaration_info_scope::gen_aux_lemmas() const {
    return get_definition_info().m_aux_lemmas;
}

equations_header mk_equations_header(list<name> const & ns, list<name> const & actual_ns) {
    equations_header h;
    h.m_num_fns          = length(ns);
    h.m_fn_names         = ns;
    h.m_fn_actual_names  = actual_ns;
    h.m_is_private       = get_definition_info().m_is_private;
    h.m_is_meta          = get_definition_info().m_is_meta;
    h.m_is_noncomputable = get_definition_info().m_is_noncomputable;
    h.m_is_lemma         = get_definition_info().m_is_lemma;
    h.m_aux_lemmas       = get_definition_info().m_aux_lemmas;
    return h;
}

equations_header mk_equations_header(name const & n, name const & actual_n) {
    return mk_equations_header(to_list(n), to_list(actual_n));
}

equations_header mk_match_header(name const & n, name const & actual_n) {
    equations_header h = mk_equations_header(to_list(n), to_list(actual_n));
    h.m_gen_code = false;
    return h;
}

/* Auxiliary function for creating names for auxiliary declarations.
   We avoid propagating the suffix `_main` used by the top-level equations
   to the nested declarations. */
static name mk_decl_name(name const & prefix, name const & n) {
    if (!prefix.is_atomic() && prefix.is_string() && strcmp(prefix.get_string(), "_main") == 0) {
        return prefix.get_prefix() + n;
    } else {
        return prefix + n;
    }
}

bool used_match_idx() {
    return get_definition_info().m_next_match_idx > 1;
}

declaration_name_scope::declaration_name_scope() {
    definition_info & info = get_definition_info();
    m_old_prefix          = info.m_prefix;
    m_old_actual_prefix   = info.m_actual_prefix;
    m_old_next_match_idx  = info.m_next_match_idx;
    info.m_next_match_idx = 1;
}

void declaration_name_scope::set_name(name const & n) {
    lean_assert(m_name.is_anonymous());
    definition_info & info    = get_definition_info();
    info.m_prefix             = mk_decl_name(info.m_prefix, n);
    info.m_actual_prefix      = mk_decl_name(info.m_actual_prefix, n);
    m_name                    = info.m_prefix;
    m_actual_name             = info.m_actual_prefix;
}

declaration_name_scope::declaration_name_scope(name const & n) {
    definition_info & info = get_definition_info();
    m_old_prefix          = info.m_prefix;
    m_old_actual_prefix   = info.m_actual_prefix;
    m_old_next_match_idx  = info.m_next_match_idx;
    info.m_prefix         = mk_decl_name(info.m_prefix, n);
    info.m_actual_prefix  = mk_decl_name(info.m_actual_prefix, n);
    info.m_next_match_idx = 1;
    m_name                = info.m_prefix;
    m_actual_name         = info.m_actual_prefix;
}

declaration_name_scope::~declaration_name_scope() {
    definition_info & info = get_definition_info();
    info.m_prefix          = m_old_prefix;
    info.m_actual_prefix  = m_old_actual_prefix;
    info.m_next_match_idx  = m_old_next_match_idx;
}

private_name_scope::private_name_scope(bool is_private, environment & env) {
    definition_info & info = get_definition_info();
    m_old_actual_prefix    = info.m_prefix;
    m_old_is_private       = info.m_is_private;
    if (is_private) {
        name prv_prefix;
        std::tie(env, prv_prefix) = mk_private_prefix(env);
        info.m_is_private     = true;
        info.m_actual_prefix = prv_prefix;
    }
}

private_name_scope::~private_name_scope() {
    definition_info & info = get_definition_info();
    info.m_actual_prefix   = m_old_actual_prefix;
    info.m_is_private      = m_old_is_private;
}

match_definition_scope::match_definition_scope(environment const & env) {
    definition_info & info = get_definition_info();
    while (true) {
        m_name        = mk_decl_name(info.m_prefix, name("_match").append_after(info.m_next_match_idx));
        m_actual_name = mk_decl_name(info.m_actual_prefix, name("_match").append_after(info.m_next_match_idx));
        info.m_next_match_idx++;
        if (empty(get_expr_aliases(env, m_name))) {
            /* Make sure we don't introduce aliases.
               This is important when match-expressions are used in several parameters in a section.
               Example:

                  parameter P : match ... end
                  parameter Q : match ... end
            */
            break;
        }
    }
}

meta_definition_scope::meta_definition_scope() {
    definition_info & info = get_definition_info();
    m_old_is_meta  = info.m_is_meta;
    info.m_is_meta = true;
}

meta_definition_scope::~meta_definition_scope() {
    definition_info & info = get_definition_info();
    info.m_is_meta = m_old_is_meta;
}

restore_decl_meta_scope::restore_decl_meta_scope() {
    definition_info & info = get_definition_info();
    m_old_is_meta  = info.m_is_meta;
    info.m_is_meta = info.m_is_meta_decl;
}

restore_decl_meta_scope::~restore_decl_meta_scope() {
    definition_info & info = get_definition_info();
    info.m_is_meta = m_old_is_meta;
}

root_scope::root_scope() {
    definition_info & info = get_definition_info();
    m_old_prefix         = info.m_prefix;
    m_old_actual_prefix  = info.m_actual_prefix;
    info.m_prefix        = {};
    info.m_actual_prefix = {};
}

root_scope::~root_scope() {
    definition_info & info = get_definition_info();
    info.m_prefix        = m_old_prefix;
    info.m_actual_prefix = m_old_actual_prefix;
}
}

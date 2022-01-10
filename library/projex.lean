universes u v

section graph_parts
variables {α : Type u}

class has_adj (G : α) (V : out_param $ Type v) :=
(adj : V → V → Prop)

class is_adj_symm (G : α) {V : out_param $ Type v} [has_adj G V] : Prop :=
(symm [] : symmetric (has_adj.adj G))

class is_adj_irrefl (G : α) {V : out_param $ Type v} [has_adj G V] : Prop :=
(irrefl [] : irreflexive (has_adj.adj G))

end graph_parts

structure simple_graph (V : Type u) :=
(adj' : V → V → Prop)
(symm' : symmetric adj')
(irrefl' : irreflexive adj')

attribute [elab_field_alternatives has_adj is_adj_symm is_adj_irrefl] simple_graph

#print simple_graph

namespace simple_graph

variables {V : Type u} (G : simple_graph V)

instance : has_adj G V := ⟨G.adj'⟩

instance : is_adj_symm G := ⟨G.symm'⟩

instance : is_adj_irrefl G := ⟨G.irrefl'⟩

lemma adj_comm (u v : V) : G.adj u v ↔ G.adj v u := ⟨λ x, G.symm x, λ x, G.symm x⟩

@[symm] lemma adj_symm (u v : V) (h : G.adj u v) : G.adj v u := G.symm h

lemma ne_of_adj {u v : V} (h : G.adj u v) : u ≠ v := by { intro, subst_vars, exact G.irrefl _ h }

protected lemma adj'.ne {G : simple_graph V} {a b : V} (h : G.adj a b) : a ≠ b := G.ne_of_adj h

protected lemma adj'.ne' {G : simple_graph V} {a b : V} (h : G.adj' a b) : b ≠ a := h.ne.symm

lemma ne_of_adj_of_not_adj {v w x : V} (h : G.adj v x) (hn : ¬ G.adj w x) : v ≠ w :=
λ h', hn (h' ▸ h)

end simple_graph

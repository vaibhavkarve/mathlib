variables (α : Type*)

structure refl_rel :=
(r : α → α → Prop)
(refl : ∀ x, r x x)

instance : has_coe_to_fun (refl_rel α) :=
⟨_, λ r, r.1⟩

@[refl] lemma refl' (r : refl_rel α) (x) : r x x := r.2 x
/- invalid binary relation declaration,
   relation 'coe_fn' must have two explicit parameters -/
/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/

import group_theory.mul_action.basic algebra.opposites data.equiv.algebra group_theory.quotient_group

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

open opposite (op unop)

instance op_inv.is_group_hom [group α] : is_group_hom (λ x : α, op (x⁻¹)) :=
{ map_mul := λ x y, mul_inv_rev x y ▸ rfl }

instance unop_inv.is_group_hom [group α] : is_group_hom (λ x : αᵒᵖ, (unop x)⁻¹) :=
{ map_mul := λ x y, mul_inv_rev x y ▸ rfl }

def group.to_units (α : Type u) [group α] : α ≃* (units α) :=
{ to_fun := λ x, (has_lift.lift (units α) x),
  inv_fun := λ x, (↑x : α),
  left_inv := λ x, rfl,
  right_inv := λ x, by ext; refl,
  hom := { map_mul := λ x y, by ext; refl } }

namespace mul_action
def comp_hom [monoid α] (a : α ↷ β) [monoid γ] (g : γ → α) [is_monoid_hom g] : γ ↷ β :=
of_hom (a.smul ∘ g)

def mul_left [monoid α] : α ↷ α :=
of_core
{ smul := λ x y, x * y,
  one_smul := one_mul,
  mul_smul := mul_assoc }

def mul_right [monoid α] : αᵒᵖ ↷ α :=
of_core
{ smul := λ x y, y * (unop x),
  one_smul := mul_one,
  mul_smul := λ x₁ x₂ y, (mul_assoc y (unop x₂) (unop x₁)).symm }

def inv_unop [group α] (a : α ↷ β) : αᵒᵖ ↷ β := a.comp_hom (λ x, (unop x)⁻¹)

def inv_op [group α] (a : αᵒᵖ ↷ β) : α ↷ β := a.comp_hom (λ x, op x⁻¹)

protected def mul_inv_right [group α] : α ↷ α := mul_right.inv_op

def units_conj [monoid α] : (units α) ↷ α :=
of_core
{ smul := λ (x : units α) (y : α), x * y * ↑x⁻¹,
  one_smul := λ y, by rw [one_inv, units.coe_one, one_mul, mul_one],
  mul_smul := λ x₁ x₂ y, by simp only [mul_inv_rev, units.coe_mul, mul_assoc] }

lemma units_conj_def [monoid α] (x : units α) (y : α) : x •[units_conj] y = x * y * ↑x⁻¹ := rfl

def conj [group α] : α ↷ α := units_conj.comp_hom (group.to_units α).to_equiv

lemma conj_def [group α] (x y : α) : x •[conj] y = x * y * x⁻¹ := rfl

instance perm.is_monoid_hom : @is_monoid_hom (equiv.perm α) (category_theory.End α) _ _ equiv.to_fun :=
{ map_mul := λ e₁ e₂, rfl,
  map_one := rfl }

def quotient [group α] (a : α ↷ β) {s : set α} [normal_subgroup s]
  (h : s ⊆ a.stabilizer_Inter) : (quotient_group.quotient s) ↷ β :=
begin
/- Probably, a better approach is to have `quotient_group.lift` for morphisms to a monoid. -/
refine of_hom (equiv.to_fun ∘ (quotient_group.lift s a.to_perm _)),
  { assume x h',
    ext,
    exact a.mem_stabilizer_Inter_iff.1 (h h') _ },
  { refine is_monoid_hom.comp _ _ }
end

end mul_action

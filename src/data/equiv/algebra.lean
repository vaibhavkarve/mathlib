/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

The role of this file is twofold. In the first part there are theorems of the following
form: if α has a group structure and α ≃ β then β has a group structure, and
similarly for monoids, semigroups, rings, integral domains, fields and so on.

In the second part there are extensions of equiv called add_equiv,
mul_equiv, and ring_equiv, which are datatypes representing isomorphisms
of monoids, groups and rings.

-/
import data.equiv.basic algebra.field

universes u v w x
variables {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}

namespace equiv

section group
variables [group α]

protected def mul_left (a : α) : α ≃ α :=
{ to_fun    := λx, a * x,
  inv_fun   := λx, a⁻¹ * x,
  left_inv  := assume x, show a⁻¹ * (a * x) = x, from inv_mul_cancel_left a x,
  right_inv := assume x, show a * (a⁻¹ * x) = x, from mul_inv_cancel_left a x }

attribute [to_additive equiv.add_left._proof_1] equiv.mul_left._proof_1
attribute [to_additive equiv.add_left._proof_2] equiv.mul_left._proof_2
attribute [to_additive equiv.add_left] equiv.mul_left

protected def mul_right (a : α) : α ≃ α :=
{ to_fun    := λx, x * a,
  inv_fun   := λx, x * a⁻¹,
  left_inv  := assume x, show (x * a) * a⁻¹ = x, from mul_inv_cancel_right x a,
  right_inv := assume x, show (x * a⁻¹) * a = x, from inv_mul_cancel_right x a }

attribute [to_additive equiv.add_right._proof_1] equiv.mul_right._proof_1
attribute [to_additive equiv.add_right._proof_2] equiv.mul_right._proof_2
attribute [to_additive equiv.add_right] equiv.mul_right

protected def inv (α) [group α] : α ≃ α :=
{ to_fun    := λa, a⁻¹,
  inv_fun   := λa, a⁻¹,
  left_inv  := assume a, inv_inv a,
  right_inv := assume a, inv_inv a }

attribute [to_additive equiv.neg._proof_1] equiv.inv._proof_1
attribute [to_additive equiv.neg._proof_2] equiv.inv._proof_2
attribute [to_additive equiv.neg] equiv.inv

def units_equiv_ne_zero (α : Type*) [field α] : units α ≃ {a : α | a ≠ 0} :=
⟨λ a, ⟨a.1, units.ne_zero _⟩, λ a, units.mk0 _ a.2, λ ⟨_, _, _, _⟩, units.ext rfl, λ ⟨_, _⟩, rfl⟩

@[simp] lemma coe_units_equiv_ne_zero [field α] (a : units α) :
  ((units_equiv_ne_zero α a) : α) = a := rfl

end group

section instances

variables (e : α ≃ β)

protected def has_zero [has_zero β] : has_zero α := ⟨e.symm 0⟩
lemma zero_def [has_zero β] : @has_zero.zero _ (equiv.has_zero e) = e.symm 0 := rfl

protected def has_one [has_one β] : has_one α := ⟨e.symm 1⟩
lemma one_def [has_one β] : @has_one.one _ (equiv.has_one e) = e.symm 1 := rfl

protected def has_mul [has_mul β] : has_mul α := ⟨λ x y, e.symm (e x * e y)⟩
lemma mul_def [has_mul β] (x y : α) :
  @has_mul.mul _ (equiv.has_mul e) x y = e.symm (e x * e y) := rfl

protected def has_add [has_add β] : has_add α := ⟨λ x y, e.symm (e x + e y)⟩
lemma add_def [has_add β] (x y : α) :
  @has_add.add _ (equiv.has_add e) x y = e.symm (e x + e y) := rfl

protected def has_inv [has_inv β] : has_inv α := ⟨λ x, e.symm (e x)⁻¹⟩
lemma inv_def [has_inv β] (x : α) : @has_inv.inv _ (equiv.has_inv e) x = e.symm (e x)⁻¹ := rfl

protected def has_neg [has_neg β] : has_neg α := ⟨λ x, e.symm (-e x)⟩
lemma neg_def [has_neg β] (x : α) : @has_neg.neg _ (equiv.has_neg e) x = e.symm (-e x) := rfl

protected def semigroup [semigroup β] : semigroup α :=
{ mul_assoc := by simp [mul_def, mul_assoc],
  ..equiv.has_mul e }

protected def comm_semigroup [comm_semigroup β] : comm_semigroup α :=
{ mul_comm := by simp [mul_def, mul_comm],
  ..equiv.semigroup e }

protected def monoid [monoid β] : monoid α :=
{ one_mul := by simp [mul_def, one_def],
  mul_one := by simp [mul_def, one_def],
  ..equiv.semigroup e,
  ..equiv.has_one e }

protected def comm_monoid [comm_monoid β] : comm_monoid α :=
{ ..equiv.comm_semigroup e,
  ..equiv.monoid e }

protected def group [group β] : group α :=
{ mul_left_inv := by simp [mul_def, inv_def, one_def],
  ..equiv.monoid e,
  ..equiv.has_inv e }

protected def comm_group [comm_group β] : comm_group α :=
{ ..equiv.group e,
  ..equiv.comm_semigroup e }

protected def add_semigroup [add_semigroup β] : add_semigroup α :=
@additive.add_semigroup _ (@equiv.semigroup _ _ e multiplicative.semigroup)

protected def add_comm_semigroup [add_comm_semigroup β] : add_comm_semigroup α :=
@additive.add_comm_semigroup _ (@equiv.comm_semigroup _ _ e multiplicative.comm_semigroup)

protected def add_monoid [add_monoid β] : add_monoid α :=
@additive.add_monoid _ (@equiv.monoid _ _ e multiplicative.monoid)

protected def add_comm_monoid [add_comm_monoid β] : add_comm_monoid α :=
@additive.add_comm_monoid _ (@equiv.comm_monoid _ _ e multiplicative.comm_monoid)

protected def add_group [add_group β] : add_group α :=
@additive.add_group _ (@equiv.group _ _ e multiplicative.group)

protected def add_comm_group [add_comm_group β] : add_comm_group α :=
@additive.add_comm_group _ (@equiv.comm_group _ _ e multiplicative.comm_group)

protected def semiring [semiring β] : semiring α :=
{ right_distrib := by simp [mul_def, add_def, add_mul],
  left_distrib := by simp [mul_def, add_def, mul_add],
  zero_mul := by simp [mul_def, zero_def],
  mul_zero := by simp [mul_def, zero_def],
  ..equiv.has_zero e,
  ..equiv.has_mul e,
  ..equiv.has_add e,
  ..equiv.monoid e,
  ..equiv.add_comm_monoid e }

protected def comm_semiring [comm_semiring β] : comm_semiring α :=
{ ..equiv.semiring e,
  ..equiv.comm_monoid e }

protected def ring [ring β] : ring α :=
{ ..equiv.semiring e,
  ..equiv.add_comm_group e }

protected def comm_ring [comm_ring β] : comm_ring α :=
{ ..equiv.comm_monoid e,
  ..equiv.ring e }

protected def zero_ne_one_class [zero_ne_one_class β] : zero_ne_one_class α :=
{ zero_ne_one := by simp [zero_def, one_def],
  ..equiv.has_zero e,
  ..equiv.has_one e }

protected def nonzero_comm_ring [nonzero_comm_ring β] : nonzero_comm_ring α :=
{ ..equiv.zero_ne_one_class e,
  ..equiv.comm_ring e }

protected def domain [domain β] : domain α :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := by simp [mul_def, zero_def, equiv.eq_symm_apply],
  ..equiv.has_zero e,
  ..equiv.zero_ne_one_class e,
  ..equiv.has_mul e,
  ..equiv.ring e }

protected def integral_domain [integral_domain β] : integral_domain α :=
{ ..equiv.domain e,
  ..equiv.nonzero_comm_ring e }

protected def division_ring [division_ring β] : division_ring α :=
{ inv_mul_cancel := λ _,
    by simp [mul_def, inv_def, zero_def, one_def, (equiv.symm_apply_eq _).symm];
      exact inv_mul_cancel,
  mul_inv_cancel := λ _,
    by simp [mul_def, inv_def, zero_def, one_def, (equiv.symm_apply_eq _).symm];
      exact mul_inv_cancel,
  ..equiv.has_zero e,
  ..equiv.has_one e,
  ..equiv.domain e,
  ..equiv.has_inv e }

protected def field [field β] : field α :=
{ ..equiv.integral_domain e,
  ..equiv.division_ring e }

protected def discrete_field [discrete_field β] : discrete_field α :=
{ has_decidable_eq := equiv.decidable_eq e,
  inv_zero := by simp [mul_def, inv_def, zero_def],
  ..equiv.has_mul e,
  ..equiv.has_inv e,
  ..equiv.has_zero e,
  ..equiv.field e }

end instances
end equiv

set_option old_structure_cmd true

structure mul_equiv (α β : Type*) [has_mul α] [has_mul β] extends α ≃ β, α →* β

infix ` ≃* `:50 := mul_equiv

namespace mul_equiv

variables [has_mul α] [has_mul β] [has_mul γ]

instance has_coe_to_mul_hom : has_coe (α ≃* β) (α →* β) := ⟨to_mul_hom⟩
instance : has_coe_to_fun (α ≃* β) := ⟨_, to_fun⟩

@[refl] def refl (α : Type*) [has_mul α] : α ≃* α :=
{ ..mul_hom.id, ..equiv.refl α }

@[symm] def symm (h : α ≃* β) : β ≃* α :=
{ mul := λ n₁ n₂, function.injective_of_left_inverse h.left_inv $
    by erw [h.mul, h.right_inv, h.right_inv, h.right_inv],
  ..h.to_equiv.symm }

@[trans] def trans (h1 : α ≃* β) (h2 : β ≃* γ) : (α ≃* γ) :=
{ mul := (h2.to_mul_hom.comp h1.to_mul_hom).mul,
  ..h1.to_equiv.trans h2.to_equiv }

@[simp] lemma map_mul (h : α ≃* β) : ∀ a b : α, h (a * b) = h a * h b := h.mul

end mul_equiv

set_option old_structure_cmd true

structure add_equiv (α β : Type*) [has_add α] [has_add β] extends α ≃ β, α →+ β

infix ` ≃+ `:50 := add_equiv

namespace add_equiv

variables [has_add α] [has_add β] [has_add γ]

instance has_coe_to_add_hom : has_coe (α ≃+ β) (α →+ β) := ⟨to_add_hom⟩
instance : has_coe_to_fun (α ≃+ β) := ⟨_, to_fun⟩

@[refl] def refl (α : Type*) [has_add α] : α ≃+ α :=
{ ..add_hom.id, ..equiv.refl α }

@[symm] def symm (h : α ≃+ β) : β ≃+ α :=
{ add := λ n₁ n₂, function.injective_of_left_inverse h.left_inv $
    by erw [h.add, h.right_inv, h.right_inv, h.right_inv],
  ..h.to_equiv.symm }

@[trans] def trans (h1 : α ≃+ β) (h2 : β ≃+ γ) : (α ≃+ γ) :=
{ add := (h2.to_add_hom.comp h1.to_add_hom).add,
  ..h1.to_equiv.trans h2.to_equiv }

@[simp] lemma map_add (h : α ≃+ β) : ∀ a b : α, h (a + b) = h a + h b := h.add

attribute [to_additive add_equiv] mul_equiv
attribute [to_additive add_equiv.to_add_hom] mul_equiv.to_mul_hom
attribute [to_additive add_equiv.to_equiv] mul_equiv.to_equiv
attribute [to_additive add_equiv.has_coe_to_add_hom] mul_equiv.has_coe_to_mul_hom
attribute [to_additive add_equiv.refl] mul_equiv.refl
attribute [to_additive add_equiv.refl.equations._eqn_1] mul_equiv.refl.equations._eqn_1
attribute [to_additive add_equiv.symm] mul_equiv.symm
attribute [to_additive add_equiv.symm.equations._eqn_1] mul_equiv.symm.equations._eqn_1
attribute [to_additive add_equiv.trans] mul_equiv.trans
attribute [to_additive add_equiv.trans.equations._eqn_1] mul_equiv.trans.equations._eqn_1
attribute [to_additive add_equiv.map_add] mul_equiv.map_mul

end add_equiv

-- equiv of monoids
namespace mul_equiv

variables [monoid α] [monoid β] [monoid γ]

@[to_additive add_equiv.zero]
lemma one (h : equiv α β) (hom : ∀ x y, h (x * y) = h x * h y) :
  h 1 = 1 :=
by rw [←mul_one (h 1), ←h.apply_symm_apply 1, ←hom]; simp

instance has_coe_to_monoid_hom : has_coe (α ≃* β) (α →1* β) :=
⟨λ x, { to_fun := x.to_fun, mul := x.mul, one := one x.to_equiv x.mul }⟩

end mul_equiv

namespace add_equiv

variables [add_monoid α] [add_monoid β] [add_monoid γ]

instance has_coe_to_add_monoid_hom : has_coe (α ≃+ β) (α →0+ β) :=
⟨λ x, { to_fun := x.to_fun, add := x.add, zero := zero x.to_equiv x.add }⟩

attribute [to_additive add_equiv.has_coe_to_add_monoid_hom] mul_equiv.has_coe_to_monoid_hom

end add_equiv

namespace units

variables [monoid α] [monoid β] [monoid γ] (f : α →1* β) (g : β →1* γ)

def map_equiv (h : α ≃* β) : units α ≃* units β :=
{ to_fun := map (h : α →1* β),
  inv_fun := map (h.symm : β →1* α),
  left_inv := λ u, ext $ h.left_inv u,
  right_inv := λ u, ext $ h.right_inv u,
  mul := λ a b, units.ext $ h.to_mul_hom.map_mul _ _}

end units

structure ring_equiv (α β : Type*) [semiring α] [semiring β] extends α ≃+ β, α ≃* β

infix ` ≃r `:50 := ring_equiv

namespace ring_equiv

variables [semiring α] [semiring β] [semiring γ]

def to_equiv (e : α ≃r β) := e.to_mul_equiv.to_equiv

protected def refl (α : Type*) [semiring α] : α ≃r α :=
{ ..add_equiv.refl α, ..mul_equiv.refl α, }

protected def symm {α β : Type*} [semiring α] [semiring β] (e : α ≃r β) : β ≃r α :=
{ ..e.to_add_equiv.symm, ..e.to_mul_equiv.symm }

protected def trans {α β γ : Type*} [semiring α] [semiring β] [semiring γ]
  (e₁ : α ≃r β) (e₂ : β ≃r γ) : α ≃r γ :=
{ ..e₁.to_add_equiv.trans e₂.to_add_equiv,
  ..e₁.to_mul_equiv.trans e₂.to_mul_equiv  }

@[simp] lemma to_equiv_symm (e : α ≃r β) : e.symm.to_equiv = e.to_equiv.symm := rfl

@[simp] lemma to_equiv_symm_apply (e : α ≃r β) (x : β) :
  e.symm.to_equiv x = e.to_equiv.symm x := rfl

end ring_equiv

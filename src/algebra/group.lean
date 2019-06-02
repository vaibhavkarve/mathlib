/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura

Various multiplicative and additive structures.
-/
import tactic.basic data.option.defs

section pending_1857

/- Transport multiplicative to additive -/
section transport
open tactic

@[user_attribute]
meta def to_additive_attr : user_attribute (name_map name) name :=
{ name      := `to_additive,
  descr     := "Transport multiplicative to additive",
  cache_cfg := ⟨λ ns, ns.mfoldl (λ dict n, do
    val ← to_additive_attr.get_param n,
    pure $ dict.insert n val) mk_name_map, []⟩,
  parser    := lean.parser.ident,
  after_set := some $ λ src _ _, do
    env ← get_env,
    dict ← to_additive_attr.get_cache,
    tgt ← to_additive_attr.get_param src,
    (get_decl tgt >> skip) <|>
      transport_with_dict dict src tgt }

end transport

/- map operations -/
attribute [to_additive has_add.add] has_mul.mul
attribute [to_additive has_zero.zero] has_one.one
attribute [to_additive has_neg.neg] has_inv.inv
attribute [to_additive has_add] has_mul
attribute [to_additive has_zero] has_one
attribute [to_additive has_neg] has_inv

/- map constructors -/
attribute [to_additive has_add.mk] has_mul.mk
attribute [to_additive has_zero.mk] has_one.mk
attribute [to_additive has_neg.mk] has_inv.mk

/- map structures -/
attribute [to_additive add_semigroup] semigroup
attribute [to_additive add_semigroup.mk] semigroup.mk
attribute [to_additive add_semigroup.to_has_add] semigroup.to_has_mul
attribute [to_additive add_semigroup.add_assoc] semigroup.mul_assoc
attribute [to_additive add_semigroup.add] semigroup.mul

attribute [to_additive add_comm_semigroup] comm_semigroup
attribute [to_additive add_comm_semigroup.mk] comm_semigroup.mk
attribute [to_additive add_comm_semigroup.to_add_semigroup] comm_semigroup.to_semigroup
attribute [to_additive add_comm_semigroup.add_comm] comm_semigroup.mul_comm

attribute [to_additive add_left_cancel_semigroup] left_cancel_semigroup
attribute [to_additive add_left_cancel_semigroup.mk] left_cancel_semigroup.mk
attribute [to_additive add_left_cancel_semigroup.to_add_semigroup] left_cancel_semigroup.to_semigroup
attribute [to_additive add_left_cancel_semigroup.add_left_cancel] left_cancel_semigroup.mul_left_cancel

attribute [to_additive add_right_cancel_semigroup] right_cancel_semigroup
attribute [to_additive add_right_cancel_semigroup.mk] right_cancel_semigroup.mk
attribute [to_additive add_right_cancel_semigroup.to_add_semigroup] right_cancel_semigroup.to_semigroup
attribute [to_additive add_right_cancel_semigroup.add_right_cancel] right_cancel_semigroup.mul_right_cancel

attribute [to_additive add_monoid] monoid
attribute [to_additive add_monoid.mk] monoid.mk
attribute [to_additive add_monoid.to_has_zero] monoid.to_has_one
attribute [to_additive add_monoid.to_add_semigroup] monoid.to_semigroup
attribute [to_additive add_monoid.add] monoid.mul
attribute [to_additive add_monoid.add_assoc] monoid.mul_assoc
attribute [to_additive add_monoid.zero] monoid.one
attribute [to_additive add_monoid.zero_add] monoid.one_mul
attribute [to_additive add_monoid.add_zero] monoid.mul_one

attribute [to_additive add_comm_monoid] comm_monoid
attribute [to_additive add_comm_monoid.mk] comm_monoid.mk
attribute [to_additive add_comm_monoid.to_add_monoid] comm_monoid.to_monoid
attribute [to_additive add_comm_monoid.to_add_comm_semigroup] comm_monoid.to_comm_semigroup

attribute [to_additive add_group] group
attribute [to_additive add_group.mk] group.mk
attribute [to_additive add_group.to_has_neg] group.to_has_inv
attribute [to_additive add_group.to_add_monoid] group.to_monoid
attribute [to_additive add_group.add_left_neg] group.mul_left_inv
attribute [to_additive add_group.add] group.mul
attribute [to_additive add_group.add_assoc] group.mul_assoc
attribute [to_additive add_group.zero] group.one
attribute [to_additive add_group.zero_add] group.one_mul
attribute [to_additive add_group.add_zero] group.mul_one
attribute [to_additive add_group.neg] group.inv

attribute [to_additive add_comm_group] comm_group
attribute [to_additive add_comm_group.mk] comm_group.mk
attribute [to_additive add_comm_group.to_add_group] comm_group.to_group
attribute [to_additive add_comm_group.to_add_comm_monoid] comm_group.to_comm_monoid

/- map theorems -/
attribute [to_additive add_assoc] mul_assoc
attribute [to_additive add_semigroup_to_is_associative] semigroup_to_is_associative
attribute [to_additive add_comm] mul_comm
attribute [to_additive add_comm_semigroup_to_is_commutative] comm_semigroup_to_is_commutative
attribute [to_additive add_left_comm] mul_left_comm
attribute [to_additive add_right_comm] mul_right_comm
attribute [to_additive add_left_cancel] mul_left_cancel
attribute [to_additive add_right_cancel] mul_right_cancel
attribute [to_additive add_left_cancel_iff] mul_left_cancel_iff
attribute [to_additive add_right_cancel_iff] mul_right_cancel_iff
attribute [to_additive zero_add] one_mul
attribute [to_additive add_zero] mul_one
attribute [to_additive add_left_neg] mul_left_inv
attribute [to_additive neg_add_self] inv_mul_self
attribute [to_additive neg_add_cancel_left] inv_mul_cancel_left
attribute [to_additive neg_add_cancel_right] inv_mul_cancel_right
attribute [to_additive neg_eq_of_add_eq_zero] inv_eq_of_mul_eq_one
attribute [to_additive neg_zero] one_inv
attribute [to_additive neg_neg] inv_inv
attribute [to_additive add_right_neg] mul_right_inv
attribute [to_additive add_neg_self] mul_inv_self
attribute [to_additive neg_inj] inv_inj
attribute [to_additive add_group.add_left_cancel] group.mul_left_cancel
attribute [to_additive add_group.add_right_cancel] group.mul_right_cancel
attribute [to_additive add_group.to_left_cancel_add_semigroup] group.to_left_cancel_semigroup
attribute [to_additive add_group.to_right_cancel_add_semigroup] group.to_right_cancel_semigroup
attribute [to_additive add_neg_cancel_left] mul_inv_cancel_left
attribute [to_additive add_neg_cancel_right] mul_inv_cancel_right
attribute [to_additive neg_add_rev] mul_inv_rev
attribute [to_additive eq_neg_of_eq_neg] eq_inv_of_eq_inv
attribute [to_additive eq_neg_of_add_eq_zero] eq_inv_of_mul_eq_one
attribute [to_additive eq_add_neg_of_add_eq] eq_mul_inv_of_mul_eq
attribute [to_additive eq_neg_add_of_add_eq] eq_inv_mul_of_mul_eq
attribute [to_additive neg_add_eq_of_eq_add] inv_mul_eq_of_eq_mul
attribute [to_additive add_neg_eq_of_eq_add] mul_inv_eq_of_eq_mul
attribute [to_additive eq_add_of_add_neg_eq] eq_mul_of_mul_inv_eq
attribute [to_additive eq_add_of_neg_add_eq] eq_mul_of_inv_mul_eq
attribute [to_additive add_eq_of_eq_neg_add] mul_eq_of_eq_inv_mul
attribute [to_additive add_eq_of_eq_add_neg] mul_eq_of_eq_mul_inv
attribute [to_additive neg_add] mul_inv

end pending_1857

instance monoid_to_is_left_id {α : Type*} [monoid α]
: is_left_id α (*) 1 :=
⟨ monoid.one_mul ⟩

instance monoid_to_is_right_id {α : Type*} [monoid α]
: is_right_id α (*) 1 :=
⟨ monoid.mul_one ⟩

instance add_monoid_to_is_left_id {α : Type*} [add_monoid α]
: is_left_id α (+) 0 :=
⟨ add_monoid.zero_add ⟩

instance add_monoid_to_is_right_id {α : Type*} [add_monoid α]
: is_right_id α (+) 0 :=
⟨ add_monoid.add_zero ⟩

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

def additive (α : Type*) := α
def multiplicative (α : Type*) := α

instance [semigroup α] : add_semigroup (additive α) :=
{ add := ((*) : α → α → α),
  add_assoc := @mul_assoc _ _ }

instance [add_semigroup α] : semigroup (multiplicative α) :=
{ mul := ((+) : α → α → α),
  mul_assoc := @add_assoc _ _ }

instance [comm_semigroup α] : add_comm_semigroup (additive α) :=
{ add_comm := @mul_comm _ _,
  ..additive.add_semigroup }

instance [add_comm_semigroup α] : comm_semigroup (multiplicative α) :=
{ mul_comm := @add_comm _ _,
  ..multiplicative.semigroup }

instance [left_cancel_semigroup α] : add_left_cancel_semigroup (additive α) :=
{ add_left_cancel := @mul_left_cancel _ _,
  ..additive.add_semigroup }

instance [add_left_cancel_semigroup α] : left_cancel_semigroup (multiplicative α) :=
{ mul_left_cancel := @add_left_cancel _ _,
  ..multiplicative.semigroup }

instance [right_cancel_semigroup α] : add_right_cancel_semigroup (additive α) :=
{ add_right_cancel := @mul_right_cancel _ _,
  ..additive.add_semigroup }

instance [add_right_cancel_semigroup α] : right_cancel_semigroup (multiplicative α) :=
{ mul_right_cancel := @add_right_cancel _ _,
  ..multiplicative.semigroup }

@[simp, to_additive add_left_inj]
theorem mul_left_inj [left_cancel_semigroup α] (a : α) {b c : α} : a * b = a * c ↔ b = c :=
⟨mul_left_cancel, congr_arg _⟩

@[simp, to_additive add_right_inj]
theorem mul_right_inj [right_cancel_semigroup α] (a : α) {b c : α} : b * a = c * a ↔ b = c :=
⟨mul_right_cancel, congr_arg _⟩

structure units (α : Type u) [monoid α] :=
(val : α)
(inv : α)
(val_inv : val * inv = 1)
(inv_val : inv * val = 1)

namespace units
variables [monoid α] {a b c : units α}

instance : has_coe (units α) α := ⟨val⟩

@[extensionality] theorem ext : ∀ {a b : units α}, (a : α) = b → a = b
| ⟨v, i₁, vi₁, iv₁⟩ ⟨v', i₂, vi₂, iv₂⟩ e :=
  by change v = v' at e; subst v'; congr;
      simpa only [iv₂, vi₁, one_mul, mul_one] using mul_assoc i₂ v i₁

theorem ext_iff {a b : units α} : a = b ↔ (a : α) = b :=
⟨congr_arg _, ext⟩

instance [decidable_eq α] : decidable_eq (units α)
| a b := decidable_of_iff' _ ext_iff

protected def mul (u₁ u₂ : units α) : units α :=
⟨u₁.val * u₂.val, u₂.inv * u₁.inv,
  have u₁.val * (u₂.val * u₂.inv) * u₁.inv = 1,
    by rw [u₂.val_inv]; rw [mul_one, u₁.val_inv],
  by simpa only [mul_assoc],
  have u₂.inv * (u₁.inv * u₁.val) * u₂.val = 1,
    by rw [u₁.inv_val]; rw [mul_one, u₂.inv_val],
  by simpa only [mul_assoc]⟩

protected def inv' (u : units α) : units α :=
⟨u.inv, u.val, u.inv_val, u.val_inv⟩

instance : has_mul (units α) := ⟨units.mul⟩
instance : has_one (units α) := ⟨⟨1, 1, mul_one 1, one_mul 1⟩⟩
instance : has_inv (units α) := ⟨units.inv'⟩

variables (a b)
@[simp] lemma coe_mul : (↑(a * b) : α) = a * b := rfl
@[simp] lemma coe_one : ((1 : units α) : α) = 1 := rfl
lemma val_coe : (↑a : α) = a.val := rfl
lemma coe_inv : ((a⁻¹ : units α) : α) = a.inv := rfl
@[simp] lemma inv_mul : (↑a⁻¹ * a : α) = 1 := inv_val _
@[simp] lemma mul_inv : (a * ↑a⁻¹ : α) = 1 := val_inv _

@[simp] lemma mul_inv_cancel_left (a : units α) (b : α) : (a:α) * (↑a⁻¹ * b) = b :=
by rw [← mul_assoc, mul_inv, one_mul]

@[simp] lemma inv_mul_cancel_left (a : units α) (b : α) : (↑a⁻¹:α) * (a * b) = b :=
by rw [← mul_assoc, inv_mul, one_mul]

@[simp] lemma mul_inv_cancel_right (a : α) (b : units α) : a * b * ↑b⁻¹ = a :=
by rw [mul_assoc, mul_inv, mul_one]

@[simp] lemma inv_mul_cancel_right (a : α) (b : units α) : a * ↑b⁻¹ * b = a :=
by rw [mul_assoc, inv_mul, mul_one]

instance : group (units α) :=
by refine {mul := (*), one := 1, inv := has_inv.inv, ..};
  { intros, apply ext, simp only [coe_mul, coe_one,
      mul_assoc, one_mul, mul_one, inv_mul] }

instance {α} [comm_monoid α] : comm_group (units α) :=
{ mul_comm := λ u₁ u₂, ext $ mul_comm _ _, ..units.group }

instance [has_repr α] : has_repr (units α) := ⟨repr ∘ val⟩

@[simp] theorem mul_left_inj (a : units α) {b c : α} : (a:α) * b = a * c ↔ b = c :=
⟨λ h, by simpa only [inv_mul_cancel_left] using congr_arg ((*) ↑(a⁻¹ : units α)) h, congr_arg _⟩

@[simp] theorem mul_right_inj (a : units α) {b c : α} : b * a = c * a ↔ b = c :=
⟨λ h, by simpa only [mul_inv_cancel_right] using congr_arg (* ↑(a⁻¹ : units α)) h, congr_arg _⟩

end units

theorem nat.units_eq_one (u : units ℕ) : u = 1 :=
units.ext $ nat.eq_one_of_dvd_one ⟨u.inv, u.val_inv.symm⟩

def units.mk_of_mul_eq_one [comm_monoid α] (a b : α) (hab : a * b = 1) : units α :=
⟨a, b, hab, (mul_comm b a).trans hab⟩

instance [monoid α] : add_monoid (additive α) :=
{ zero     := (1 : α),
  zero_add := @one_mul _ _,
  add_zero := @mul_one _ _,
  ..additive.add_semigroup }

instance [add_monoid α] : monoid (multiplicative α) :=
{ one     := (0 : α),
  one_mul := @zero_add _ _,
  mul_one := @add_zero _ _,
  ..multiplicative.semigroup }

def free_monoid (α) := list α

instance {α} : monoid (free_monoid α) :=
{ one := [],
  mul := λ x y, (x ++ y : list α),
  mul_one := by intros; apply list.append_nil,
  one_mul := by intros; refl,
  mul_assoc := by intros; apply list.append_assoc }

@[simp] lemma free_monoid.one_def {α} : (1 : free_monoid α) = [] := rfl

@[simp] lemma free_monoid.mul_def {α} (xs ys : list α) : (xs * ys : free_monoid α) = (xs ++ ys : list α) := rfl

def free_add_monoid (α) := list α

instance {α} : add_monoid (free_add_monoid α) :=
{ zero := [],
  add := λ x y, (x ++ y : list α),
  add_zero := by intros; apply list.append_nil,
  zero_add := by intros; refl,
  add_assoc := by intros; apply list.append_assoc }

@[simp] lemma free_add_monoid.zero_def {α} : (1 : free_monoid α) = [] := rfl

@[simp] lemma free_add_monoid.add_def {α} (xs ys : list α) : (xs * ys : free_monoid α) = (xs ++ ys : list α) := rfl

section monoid
  variables [monoid α] {a b c : α}

  /-- Partial division. It is defined when the
    second argument is invertible, and unlike the division operator
    in `division_ring` it is not totalized at zero. -/
  def divp (a : α) (u) : α := a * (u⁻¹ : units α)

  infix ` /ₚ `:70 := divp

  @[simp] theorem divp_self (u : units α) : (u : α) /ₚ u = 1 := units.mul_inv _

  @[simp] theorem divp_one (a : α) : a /ₚ 1 = a := mul_one _

  theorem divp_assoc (a b : α) (u : units α) : a * b /ₚ u = a * (b /ₚ u) :=
  mul_assoc _ _ _

  @[simp] theorem divp_mul_cancel (a : α) (u : units α) : a /ₚ u * u = a :=
  (mul_assoc _ _ _).trans $ by rw [units.inv_mul, mul_one]

  @[simp] theorem mul_divp_cancel (a : α) (u : units α) : (a * u) /ₚ u = a :=
  (mul_assoc _ _ _).trans $ by rw [units.mul_inv, mul_one]

  @[simp] theorem divp_right_inj (u : units α) {a b : α} : a /ₚ u = b /ₚ u ↔ a = b :=
  units.mul_right_inj _

  theorem divp_eq_one (a : α) (u : units α) : a /ₚ u = 1 ↔ a = u :=
  (units.mul_right_inj u).symm.trans $ by rw [divp_mul_cancel, one_mul]

  @[simp] theorem one_divp (u : units α) : 1 /ₚ u = ↑u⁻¹ :=
  one_mul _

end monoid

instance [comm_monoid α] : add_comm_monoid (additive α) :=
{ add_comm := @mul_comm α _,
  ..additive.add_monoid }

instance [add_comm_monoid α] : comm_monoid (multiplicative α) :=
{ mul_comm := @add_comm α _,
  ..multiplicative.monoid }

section comm_semigroup
  variables [comm_semigroup α] {a b c d : α}

  @[to_additive add_add_add_comm]
  theorem mul_mul_mul_comm : (a * b) * (c * d) = (a * c) * (b * d) :=
  by simp [mul_left_comm, mul_assoc]

end comm_semigroup

instance [group α] : add_group (additive α) :=
{ neg := @has_inv.inv α _,
  add_left_neg := @mul_left_inv _ _,
  ..additive.add_monoid }

instance [add_group α] : group (multiplicative α) :=
{ inv := @has_neg.neg α _,
  mul_left_inv := @add_left_neg _ _,
  ..multiplicative.monoid }

section group
  variables [group α] {a b c : α}

  instance : has_lift α (units α) :=
  ⟨λ a, ⟨a, a⁻¹, mul_inv_self _, inv_mul_self _⟩⟩

  @[simp, to_additive neg_inj']
  theorem inv_inj' : a⁻¹ = b⁻¹ ↔ a = b :=
  ⟨λ h, by rw [← inv_inv a, h, inv_inv], congr_arg _⟩

  @[to_additive eq_of_neg_eq_neg]
  theorem eq_of_inv_eq_inv : a⁻¹ = b⁻¹ → a = b :=
  inv_inj'.1

  @[simp, to_additive add_self_iff_eq_zero]
  theorem mul_self_iff_eq_one : a * a = a ↔ a = 1 :=
  by have := @mul_left_inj _ _ a a 1; rwa mul_one at this

  @[simp, to_additive neg_eq_zero]
  theorem inv_eq_one : a⁻¹ = 1 ↔ a = 1 :=
  by rw [← @inv_inj' _ _ a 1, one_inv]

  @[simp, to_additive neg_ne_zero]
  theorem inv_ne_one : a⁻¹ ≠ 1 ↔ a ≠ 1 :=
  not_congr inv_eq_one

  @[to_additive left_inverse_neg]
  theorem left_inverse_inv (α) [group α] :
    function.left_inverse (λ a : α, a⁻¹) (λ a, a⁻¹) :=
  assume a, inv_inv a

  attribute [simp] mul_inv_cancel_left add_neg_cancel_left
                   mul_inv_cancel_right add_neg_cancel_right

  @[to_additive eq_neg_iff_eq_neg]
  theorem eq_inv_iff_eq_inv : a = b⁻¹ ↔ b = a⁻¹ :=
  ⟨eq_inv_of_eq_inv, eq_inv_of_eq_inv⟩

  @[to_additive neg_eq_iff_neg_eq]
  theorem inv_eq_iff_inv_eq : a⁻¹ = b ↔ b⁻¹ = a :=
  by rw [eq_comm, @eq_comm _ _ a, eq_inv_iff_eq_inv]

  @[to_additive add_eq_zero_iff_eq_neg]
  theorem mul_eq_one_iff_eq_inv : a * b = 1 ↔ a = b⁻¹ :=
  by simpa [mul_left_inv, -mul_right_inj] using @mul_right_inj _ _ b a (b⁻¹)

  @[to_additive add_eq_zero_iff_neg_eq]
  theorem mul_eq_one_iff_inv_eq : a * b = 1 ↔ a⁻¹ = b :=
  by rw [mul_eq_one_iff_eq_inv, eq_inv_iff_eq_inv, eq_comm]

  @[to_additive eq_neg_iff_add_eq_zero]
  theorem eq_inv_iff_mul_eq_one : a = b⁻¹ ↔ a * b = 1 :=
  mul_eq_one_iff_eq_inv.symm

  @[to_additive neg_eq_iff_add_eq_zero]
  theorem inv_eq_iff_mul_eq_one : a⁻¹ = b ↔ a * b = 1 :=
  mul_eq_one_iff_inv_eq.symm

  @[to_additive eq_add_neg_iff_add_eq]
  theorem eq_mul_inv_iff_mul_eq : a = b * c⁻¹ ↔ a * c = b :=
  ⟨λ h, by rw [h, inv_mul_cancel_right], λ h, by rw [← h, mul_inv_cancel_right]⟩

  @[to_additive eq_neg_add_iff_add_eq]
  theorem eq_inv_mul_iff_mul_eq : a = b⁻¹ * c ↔ b * a = c :=
  ⟨λ h, by rw [h, mul_inv_cancel_left], λ h, by rw [← h, inv_mul_cancel_left]⟩

  @[to_additive neg_add_eq_iff_eq_add]
  theorem inv_mul_eq_iff_eq_mul : a⁻¹ * b = c ↔ b = a * c :=
  ⟨λ h, by rw [← h, mul_inv_cancel_left], λ h, by rw [h, inv_mul_cancel_left]⟩

  @[to_additive add_neg_eq_iff_eq_add]
  theorem mul_inv_eq_iff_eq_mul : a * b⁻¹ = c ↔ a = c * b :=
  ⟨λ h, by rw [← h, inv_mul_cancel_right], λ h, by rw [h, mul_inv_cancel_right]⟩

  @[to_additive add_neg_eq_zero]
  theorem mul_inv_eq_one {a b : α} : a * b⁻¹ = 1 ↔ a = b :=
  by rw [mul_eq_one_iff_eq_inv, inv_inv]

  @[to_additive neg_comm_of_comm]
  theorem inv_comm_of_comm {a b : α} (H : a * b = b * a) : a⁻¹ * b = b * a⁻¹ :=
  begin
    have : a⁻¹ * (b * a) * a⁻¹ = a⁻¹ * (a * b) * a⁻¹ :=
      congr_arg (λ x:α, a⁻¹ * x * a⁻¹) H.symm,
    rwa [inv_mul_cancel_left, mul_assoc, mul_inv_cancel_right] at this
  end

end group

instance [comm_group α] : add_comm_group (additive α) :=
{ add_comm := @mul_comm α _,
  ..additive.add_group }

instance [add_comm_group α] : comm_group (multiplicative α) :=
{ mul_comm := @add_comm α _,
  ..multiplicative.group }

section add_monoid
  variables [add_monoid α] {a b c : α}

  @[simp] lemma bit0_zero : bit0 (0 : α) = 0 := add_zero _
  @[simp] lemma bit1_zero [has_one α] : bit1 (0 : α) = 1 :=
  show 0+0+1=(1:α), by rw [zero_add, zero_add]

end add_monoid

section add_group
  variables [add_group α] {a b c : α}

  local attribute [simp] sub_eq_add_neg

  def sub_sub_cancel := @sub_sub_self

  @[simp] lemma sub_left_inj : a - b = a - c ↔ b = c :=
  (add_left_inj _).trans neg_inj'

  @[simp] lemma sub_right_inj : b - a = c - a ↔ b = c :=
  add_right_inj _

  lemma sub_add_sub_cancel (a b c : α) : (a - b) + (b - c) = a - c :=
  by rw [← add_sub_assoc, sub_add_cancel]

  lemma sub_sub_sub_cancel_right (a b c : α) : (a - c) - (b - c) = a - b :=
  by rw [← neg_sub c b, sub_neg_eq_add, sub_add_sub_cancel]

  theorem sub_eq_zero : a - b = 0 ↔ a = b :=
  ⟨eq_of_sub_eq_zero, λ h, by rw [h, sub_self]⟩

  theorem sub_ne_zero : a - b ≠ 0 ↔ a ≠ b :=
  not_congr sub_eq_zero

  theorem eq_sub_iff_add_eq : a = b - c ↔ a + c = b :=
  eq_add_neg_iff_add_eq

  theorem sub_eq_iff_eq_add : a - b = c ↔ a = c + b :=
  add_neg_eq_iff_eq_add

  theorem eq_iff_eq_of_sub_eq_sub {a b c d : α} (H : a - b = c - d) : a = b ↔ c = d :=
  by rw [← sub_eq_zero, H, sub_eq_zero]

  theorem left_inverse_sub_add_left (c : α) : function.left_inverse (λ x, x - c) (λ x, x + c) :=
  assume x, add_sub_cancel x c

  theorem left_inverse_add_left_sub (c : α) : function.left_inverse (λ x, x + c) (λ x, x - c) :=
  assume x, sub_add_cancel x c

  theorem left_inverse_add_right_neg_add (c : α) :
      function.left_inverse (λ x, c + x) (λ x, - c + x) :=
  assume x, add_neg_cancel_left c x

  theorem left_inverse_neg_add_add_right (c : α) :
      function.left_inverse (λ x, - c + x) (λ x, c + x) :=
  assume x, neg_add_cancel_left c x
end add_group

section add_comm_group
  variables [add_comm_group α] {a b c : α}

  lemma sub_eq_neg_add (a b : α) : a - b = -b + a :=
  add_comm _ _

  theorem neg_add' (a b : α) : -(a + b) = -a - b := neg_add a b

  lemma neg_sub_neg (a b : α) : -a - -b = b - a := by simp

  lemma eq_sub_iff_add_eq' : a = b - c ↔ c + a = b :=
  by rw [eq_sub_iff_add_eq, add_comm]

  lemma sub_eq_iff_eq_add' : a - b = c ↔ a = b + c :=
  by rw [sub_eq_iff_eq_add, add_comm]

  lemma add_sub_cancel' (a b : α) : a + b - a = b :=
  by rw [sub_eq_neg_add, neg_add_cancel_left]

  lemma add_sub_cancel'_right (a b : α) : a + (b - a) = b :=
  by rw [← add_sub_assoc, add_sub_cancel']

  lemma sub_right_comm (a b c : α) : a - b - c = a - c - b :=
  add_right_comm _ _ _

  lemma add_add_sub_cancel (a b c : α) : (a + c) + (b - c) = a + b :=
  by rw [add_assoc, add_sub_cancel'_right]

  lemma sub_add_add_cancel (a b c : α) : (a - c) + (b + c) = a + b :=
  by rw [add_left_comm, sub_add_cancel, add_comm]

  lemma sub_add_sub_cancel' (a b c : α) : (a - b) + (c - a) = c - b :=
  by rw add_comm; apply sub_add_sub_cancel

  lemma add_sub_sub_cancel (a b c : α) : (a + b) - (a - c) = b + c :=
  by rw [← sub_add, add_sub_cancel']

  lemma sub_sub_sub_cancel_left (a b c : α) : (c - a) - (c - b) = b - a :=
  by rw [← neg_sub b c, sub_neg_eq_add, add_comm, sub_add_sub_cancel]

  lemma sub_eq_sub_iff_sub_eq_sub {d : α} :
  a - b = c - d ↔ a - c = b - d :=
  ⟨λ h, by rw eq_add_of_sub_eq h; simp, λ h, by rw eq_add_of_sub_eq h; simp⟩

end add_comm_group

section is_conj
variables [group α] [group β]

def is_conj (a b : α) := ∃ c : α, c * a * c⁻¹ = b

@[refl] lemma is_conj_refl (a : α) : is_conj a a :=
⟨1, by rw [one_mul, one_inv, mul_one]⟩

@[symm] lemma is_conj_symm {a b : α} : is_conj a b → is_conj b a
| ⟨c, hc⟩ := ⟨c⁻¹, by rw [← hc, mul_assoc, mul_inv_cancel_right, inv_mul_cancel_left]⟩

@[trans] lemma is_conj_trans {a b c : α} : is_conj a b → is_conj b c → is_conj a c
| ⟨c₁, hc₁⟩ ⟨c₂, hc₂⟩ := ⟨c₂ * c₁, by rw [← hc₂, ← hc₁, mul_inv_rev]; simp only [mul_assoc]⟩

@[simp] lemma is_conj_one_right {a : α} : is_conj 1 a  ↔ a = 1 :=
⟨by simp [is_conj, is_conj_refl] {contextual := tt}, by simp [is_conj_refl] {contextual := tt}⟩

@[simp] lemma is_conj_one_left {a : α} : is_conj a 1 ↔ a = 1 :=
calc is_conj a 1 ↔ is_conj 1 a : ⟨is_conj_symm, is_conj_symm⟩
... ↔ a = 1 : is_conj_one_right

@[simp] lemma is_conj_iff_eq {α : Type*} [comm_group α] {a b : α} : is_conj a b ↔ a = b :=
⟨λ ⟨c, hc⟩, by rw [← hc, mul_right_comm, mul_inv_self, one_mul], λ h, by rw h⟩

end is_conj

class is_mul_hom {α β : Type*} [has_mul α] [has_mul β] (f : α → β) : Prop :=
(map_mul : ∀ {x y}, f (x * y) = f x * f y)

class is_add_hom {α β : Type*} [has_add α] [has_add β] (f : α → β) : Prop :=
(map_add : ∀ {x y}, f (x + y) = f x + f y)

attribute [to_additive is_add_hom] is_mul_hom
attribute [to_additive is_add_hom.cases_on] is_mul_hom.cases_on
attribute [to_additive is_add_hom.dcases_on] is_mul_hom.dcases_on
attribute [to_additive is_add_hom.drec] is_mul_hom.drec
attribute [to_additive is_add_hom.drec_on] is_mul_hom.drec_on
attribute [to_additive is_add_hom.map_add] is_mul_hom.map_mul
attribute [to_additive is_add_hom.mk] is_mul_hom.mk
attribute [to_additive is_add_hom.rec] is_mul_hom.rec
attribute [to_additive is_add_hom.rec_on] is_mul_hom.rec_on

namespace is_mul_hom
variables [has_mul α] [has_mul β] [has_mul γ]

@[to_additive is_add_hom.id]
lemma id : is_mul_hom (id : α → α) := {map_mul := λ _ _, rfl}

@[to_additive is_add_hom.comp]
lemma comp {f : α → β} {g : β → γ} (hf : is_mul_hom f) (hg : is_mul_hom g) : is_mul_hom (g ∘ f) :=
⟨λ x y, by show _ = g _ * g _; rw [←hg.map_mul, ←hf.map_mul]⟩

@[to_additive is_add_hom.comp']
lemma comp' {f : α → β} {g : β → γ} (hf : is_mul_hom f) (hg : is_mul_hom g) :
  is_mul_hom (λ x, g (f x)) :=
⟨λ x y, by rw [←hg.map_mul, ←hf.map_mul]⟩

end is_mul_hom

structure mul_hom (α β : Type*) [has_mul α] [has_mul β] :=
(to_fun : α → β)
(mul : ∀ x y, to_fun (x * y) = to_fun x * to_fun y)

structure add_hom (α β : Type*) [has_add α] [has_add β] :=
(to_fun : α → β)
(add : ∀ x y, to_fun (x + y) = to_fun x + to_fun y)

attribute [to_additive add_hom] mul_hom
attribute [to_additive add_hom.cases_on] mul_hom.cases_on
attribute [to_additive add_hom.has_sizeof_inst] mul_hom.has_sizeof_inst
attribute [to_additive add_hom.mk] mul_hom.mk
attribute [to_additive add_hom.mk.inj] mul_hom.mk.inj
attribute [to_additive add_hom.mk.inj_arrow] mul_hom.mk.inj_arrow
attribute [to_additive add_hom.mk.inj_eq] mul_hom.mk.inj_eq
attribute [to_additive add_hom.mk.sizeof_spec] mul_hom.mk.sizeof_spec
attribute [to_additive add_hom.no_confusion] mul_hom.no_confusion
attribute [to_additive add_hom.no_confusion_type] mul_hom.no_confusion_type
attribute [to_additive add_hom.rec] mul_hom.rec
attribute [to_additive add_hom.rec_on] mul_hom.rec_on
attribute [to_additive add_hom.sizeof] mul_hom.sizeof
attribute [to_additive add_hom.add] mul_hom.mul
attribute [to_additive add_hom.to_fun] mul_hom.to_fun

infixr ` →+ `:25 := add_hom
infixr ` →* `:25 := mul_hom

namespace mul_hom
variables [has_mul α] [has_mul β] [has_mul γ]

@[to_additive add_hom.has_coe_to_fun]
instance : has_coe_to_fun (α →* β) := ⟨_, mul_hom.to_fun⟩

@[to_additive add_hom.is_add_hom]
instance is_mul_hom (f : α →* β) : is_mul_hom f := ⟨mul_hom.mul _⟩

@[to_additive add_hom.ext, extensionality]
lemma ext {f g : α →* β} (h : ∀ x, f x = g x) : f = g :=
by cases f; cases g; congr'; exact funext h
attribute [extensionality] add_hom.ext

@[to_additive add_hom.ext_iff]
lemma ext_iff {f g : α →* β} : f = g ↔ ∀ x, f x = g x :=
⟨λ h _, by rw h, ext⟩

@[simp, to_additive add_hom.map_add]
lemma map_mul (f : α →* β) : ∀ x y : α, f (x * y) = f x * f y := f.mul

def id : α →* α := { to_fun := id, mul := λ _ _, rfl }

@[simp] lemma id_apply (a : α) : (id : α →* α) a = a := rfl

def comp (f : β →* γ) (g : α →* β) : α →* γ :=
{ to_fun := λ x, f (g x),
  mul := by simp [f.map_mul, g.map_mul] }

lemma comp_apply (f : β →* γ) (g : α →* β) (a : α) : (f.comp g) a = f (g a) := rfl

@[simp] lemma comp_id (f : α →* β) : f.comp id = f := by cases f; refl

@[simp] lemma id_comp (f : α →* β) : id.comp f = f := by cases f; refl

end mul_hom

namespace add_hom
variables [has_add α] [has_add β] [has_add γ]

def id : α →+ α := { to_fun := id, add := λ _ _, rfl }

@[simp] lemma id_apply (a : α) : (id : α →+ α) a = a := rfl

def comp (f : β →+ γ) (g : α →+ β) : α →+ γ :=
{ to_fun := λ x, f (g x),
  add := by simp [f.map_add, g.map_add] }

lemma comp_apply (f : β →+ γ) (g : α →+ β) (a : α) : (f.comp g) a = f (g a) := rfl

@[simp] lemma comp_id (f : α →+ β) : f.comp id = f := by cases f; refl

@[simp] lemma id_comp (f : α →+ β) : id.comp f = f := by cases f; refl

attribute [to_additive add_hom.id] mul_hom.id
attribute [to_additive add_hom.id.equations._eqn_1] mul_hom.id.equations._eqn_1
attribute [to_additive add_hom.id_apply] mul_hom.id_apply
attribute [to_additive add_hom.comp] mul_hom.comp
attribute [to_additive add_hom.comp.equations._eqn_1] mul_hom.comp.equations._eqn_1
attribute [to_additive add_hom.comp_apply] mul_hom.comp_apply
attribute [to_additive add_hom.comp_id] mul_hom.comp_id
attribute [to_additive add_hom.id_comp] mul_hom.id_comp

end add_hom

def mul_hom.to_add_hom [semigroup α] [semigroup β] (f : α →* β) :
  additive α →+ additive β := ⟨f.1, f.2⟩

def add_hom.to_mul_hom [add_semigroup α] [add_semigroup β] (f : α →+ β) :
  multiplicative α →* multiplicative β := ⟨f.1, f.2⟩

class is_monoid_hom [monoid α] [monoid β] (f : α → β) extends is_mul_hom f : Prop :=
(map_one : f 1 = 1)

class is_add_monoid_hom [add_monoid α] [add_monoid β] (f : α → β) extends is_add_hom f : Prop :=
(map_zero : f 0 = 0)

attribute [to_additive is_add_monoid_hom] is_monoid_hom
attribute [to_additive is_add_monoid_hom.mk] is_monoid_hom.mk
attribute [to_additive is_add_monoid_hom.cases_on] is_monoid_hom.cases_on
attribute [to_additive is_add_monoid_hom.dcases_on] is_monoid_hom.dcases_on
attribute [to_additive is_add_monoid_hom.rec] is_monoid_hom.rec
attribute [to_additive is_add_monoid_hom.drec] is_monoid_hom.drec
attribute [to_additive is_add_monoid_hom.rec_on] is_monoid_hom.rec_on
attribute [to_additive is_add_monoid_hom.drec_on] is_monoid_hom.drec_on
attribute [to_additive is_add_monoid_hom.map_zero] is_monoid_hom.map_one
attribute [to_additive is_add_monoid_hom.to_is_add_hom] is_monoid_hom.to_is_mul_hom

namespace is_monoid_hom
variables [monoid α] [monoid β] (f : α → β) [is_monoid_hom f]

lemma map_mul {x y} : f (x * y) = f x * f y :=
is_mul_hom.map_mul f

end is_monoid_hom

namespace is_add_monoid_hom
variables [add_monoid α] [add_monoid β] (f : α → β) [is_add_monoid_hom f]

lemma map_add {x y} : f (x + y) = f x + f y :=
is_add_hom.map_add f

attribute [to_additive is_add_monoid_hom.map_add] is_monoid_hom.map_mul

end is_add_monoid_hom

namespace is_monoid_hom
variables [monoid α] [monoid β] (f : α → β) [is_monoid_hom f]

@[to_additive is_add_monoid_hom.id]
instance id : is_monoid_hom (@id α) := by refine {..}; intros; refl

@[to_additive is_add_monoid_hom.comp]
instance comp {γ} [monoid γ] (g : β → γ) [is_monoid_hom g] :
  is_monoid_hom (g ∘ f) :=
{ map_mul := λ x y, show g _ = g _ * g _, by rw [map_mul f, map_mul g],
  map_one := show g _ = 1, by rw [map_one f, map_one g] }

@[to_additive neg.is_add_group_hom]
instance inv.is_monoid_hom [comm_group γ] : is_monoid_hom (has_inv.inv : γ → γ) :=
{ to_is_mul_hom := ⟨λ _ _, by rw [mul_inv_rev, mul_comm]⟩, map_one := one_inv }

end is_monoid_hom

namespace is_add_monoid_hom
variables [add_monoid α] [add_monoid β] (f : α → β) [is_add_monoid_hom f]

instance is_add_monoid_hom_mul_left {γ : Type*} [semiring γ] (x : γ) : is_add_monoid_hom (λ y : γ, x * y) :=
{ map_zero := mul_zero x, map_add := λ y z, mul_add x y z }

instance is_add_monoid_hom_mul_right {γ : Type*} [semiring γ] (x : γ) : is_add_monoid_hom (λ y : γ, y * x) :=
{ map_zero := zero_mul x, map_add := λ y z, add_mul y z x }

end is_add_monoid_hom

set_option old_structure_cmd true

structure monoid_hom (α β : Type*) [monoid α] [monoid β] extends α →* β :=
(one : to_fun 1 = 1)

structure add_monoid_hom (α β : Type*) [add_monoid α] [add_monoid β] extends α →+ β :=
(zero : to_fun 0 = 0)

attribute [to_additive add_monoid_hom] monoid_hom
attribute [to_additive add_monoid_hom.cases_on] monoid_hom.cases_on
attribute [to_additive add_monoid_hom.has_sizeof_inst] monoid_hom.has_sizeof_inst
attribute [to_additive add_monoid_hom.mk] monoid_hom.mk
attribute [to_additive add_monoid_hom.mk.inj] monoid_hom.mk.inj
attribute [to_additive add_monoid_hom.mk.inj_arrow] monoid_hom.mk.inj_arrow
attribute [to_additive add_monoid_hom.mk.inj_eq] monoid_hom.mk.inj_eq
attribute [to_additive add_monoid_hom.mk.sizeof_spec] monoid_hom.mk.sizeof_spec
attribute [to_additive add_monoid_hom.no_confusion] monoid_hom.no_confusion
attribute [to_additive add_monoid_hom.no_confusion_type] monoid_hom.no_confusion_type
attribute [to_additive add_monoid_hom.rec] monoid_hom.rec
attribute [to_additive add_monoid_hom.rec_on] monoid_hom.rec_on
attribute [to_additive add_monoid_hom.sizeof] monoid_hom.sizeof
attribute [to_additive add_monoid_hom.to_add_hom] monoid_hom.to_mul_hom
attribute [to_additive add_monoid_hom.zero] monoid_hom.one
attribute [to_additive add_monoid_hom.add] monoid_hom.mul
attribute [to_additive add_monoid_hom.to_fun] monoid_hom.to_fun

infixr ` →1* `:25 := monoid_hom
infixr ` →0+ `:25 := add_monoid_hom

namespace monoid_hom
variables [monoid α] [monoid β] [monoid γ]

@[to_additive add_monoid_hom.has_coe_to_fun]
instance : has_coe_to_fun (α →1* β) := ⟨_, monoid_hom.to_fun⟩

@[to_additive add_monoid_hom.to_add_hom]
instance : has_coe (α →1* β) (α →* β) := ⟨monoid_hom.to_mul_hom⟩

@[to_additive add_monoid_hom.is_add_monoid_hom]
instance is_monoid_hom (f : α →1* β) : is_monoid_hom f :=
{ to_is_mul_hom := mul_hom.is_mul_hom f.to_mul_hom,
  map_one := monoid_hom.one f }

@[to_additive add_monoid_hom.ext, extensionality]
lemma ext {f g : α →1* β} (h : ∀ x, f x = g x) : f = g :=
by cases f; cases g; congr'; exact funext h
attribute [extensionality] add_monoid_hom.ext

@[to_additive add_monoid_hom.ext_iff]
lemma ext_iff {f g : α →1* β} : f = g ↔ ∀ x, f x = g x :=
⟨λ h _, by rw h, ext⟩

@[simp, to_additive add_monoid_hom.map_add]
lemma map_mul (f : α →1* β) : ∀ x y : α, f (x * y) = f x * f y := f.mul

@[simp, to_additive add_monoid_hom.map_zero]
lemma map_one (f : α →1* β) : f 1 = 1 := f.one

def trivial : α →1* β := { to_fun := λ _, 1, mul := by simp, one := by simp }

@[simp] lemma trivial_apply (a : α) : (trivial : α →1* β) a = 1 := rfl

def id : α →1* α := { to_fun := id, mul := λ _ _, rfl, one := rfl }

@[simp] lemma id_apply (a : α) : (id : α →1* α) a = a := rfl

def comp (f : β →1* γ) (g : α →1* β) : α →1* γ :=
{ to_fun := λ x, f (g x),
  mul := by simp,
  one := by simp }

lemma comp_apply (f : β →1* γ) (g : α →1* β) (a : α) : (f.comp g) a = f (g a) := rfl

@[simp] lemma comp_id (f : α →1* β) : f.comp id = f := by cases f; refl

@[simp] lemma id_comp (f : α →1* β) : id.comp f = f := by cases f; refl

end monoid_hom

namespace add_monoid_hom
variables [add_monoid α] [add_monoid β] [add_monoid γ]

def trivial : α →0+ β := { to_fun := λ _, 0, add := by simp, zero := by simp }

@[simp] lemma trivial_apply (a : α) : (trivial : α →0+ β) a = 0 := rfl

def id : α →0+ α := { to_fun := id, add := λ _ _, rfl, zero := rfl }

@[simp] lemma id_apply (a : α) : (id : α →0+ α) a = a := rfl

def comp (f : β →0+ γ) (g : α →0+ β) : α →0+ γ :=
{ to_fun := λ x, f (g x),
  add := by simp,
  zero := by simp }

lemma comp_apply (f : β →0+ γ) (g : α →0+ β) (a : α) : (f.comp g) a = f (g a) := rfl

@[simp] lemma comp_id (f : α →0+ β) : f.comp id = f := by cases f; refl

@[simp] lemma id_comp (f : α →0+ β) : id.comp f = f := by cases f; refl

attribute [to_additive add_monoid_hom.id] monoid_hom.id
attribute [to_additive add_monoid_hom.id_apply] monoid_hom.id_apply
attribute [to_additive add_monoid_hom.trivial] monoid_hom.trivial
attribute [to_additive add_monoid_hom.trivial_apply] monoid_hom.trivial_apply
attribute [to_additive add_monoid_hom.id.equations._eqn_1] monoid_hom.id.equations._eqn_1
attribute [to_additive add_monoid_hom.comp] monoid_hom.comp
attribute [to_additive add_monoid_hom.comp.equations._eqn_1] monoid_hom.comp.equations._eqn_1
attribute [to_additive add_monoid_hom.comp_apply] monoid_hom.comp_apply
attribute [to_additive add_monoid_hom.comp_id] monoid_hom.comp_id
attribute [to_additive add_monoid_hom.id_comp] monoid_hom.id_comp

end add_monoid_hom

def monoid_hom.to_add_monoid_hom [monoid α] [monoid β] (f : α →1* β) :
  additive α →0+ additive β := ⟨f.1, f.2, f.3⟩

def add_monoid_hom.to_monoid_hom [add_monoid α] [add_monoid β] (f : α →0+ β) :
  multiplicative α →1* multiplicative β := ⟨f.1, f.2, f.3⟩

namespace mul_hom
variables [group α] [group β] (f : α →* β)

@[simp, to_additive add_hom.map_zero]
theorem map_one : f 1 = 1 :=
mul_self_iff_eq_one.1 $ by rw [← map_mul f, one_mul]

@[simp, to_additive add_hom.map_neg]
theorem map_inv (a : α) : f a⁻¹ = (f a)⁻¹ :=
eq_inv_of_mul_eq_one $ by rw [← map_mul f, inv_mul_self, map_one f]

protected lemma is_conj {a b : α} : is_conj a b → is_conj (f a) (f b)
| ⟨c, hc⟩ := ⟨f c, by rw [← f.map_mul, ← f.map_inv, ← f.map_mul, hc]⟩

@[to_additive add_hom.to_monoid_hom]
lemma to_monoid_hom : α →1* β :=
{ to_fun := f, mul := f.map_mul, one := f.map_one }

@[to_additive add_hom.injective_iff]
lemma injective_iff (f : α →* β) :
  function.injective f ↔ (∀ a, f a = 1 → a = 1) :=
⟨λ h _, by rw ← f.map_one; exact @h _ _,
  λ h x y hxy, by rw [← inv_inv (f x), inv_eq_iff_mul_eq_one, ← f.map_inv, ← f.map_mul] at hxy;
    simpa using inv_eq_of_mul_eq_one (h _ hxy)⟩

end mul_hom

namespace monoid_hom

section group
variables [group α] [group β] (f : α →1* β)

@[simp, to_additive add_monoid_hom.map_neg]
theorem map_inv (a : α) : f a⁻¹ = (f a)⁻¹ :=
eq_inv_of_mul_eq_one $ by rw [← map_mul f, inv_mul_self, map_one f]

protected lemma is_conj {a b : α} : is_conj a b → is_conj (f a) (f b)
| ⟨c, hc⟩ := ⟨f c, by rw [← f.map_mul, ← f.map_inv, ← f.map_mul, hc]⟩

@[to_additive add_monoid_hom.injective_iff]
lemma injective_iff (f : α →1* β) :
  function.injective f ↔ (∀ a, f a = 1 → a = 1) :=
⟨λ h _, by rw ← f.map_one; exact @h _ _,
  λ h x y hxy, by rw [← inv_inv (f x), inv_eq_iff_mul_eq_one, ← f.map_inv, ← f.map_mul] at hxy;
    simpa using inv_eq_of_mul_eq_one (h _ hxy)⟩

end group

section monoid
variables [monoid α] [comm_monoid β]

def mul_aux (f g : α →1* β) : α →1* β :=
{ to_fun := λ x, f x * g x,
  mul := by simp [mul_comm, mul_assoc, mul_left_comm],
  one := by simp }

instance : has_mul (α →1* β) := ⟨mul_aux⟩
instance : has_one (α →1* β) := ⟨trivial⟩

@[simp] lemma mul_apply (f g : α →1* β) (a : α) : (f * g) a = f a * g a := rfl

@[simp] lemma one_apply (a : α) : (1 : α →1* β) a = 1 := rfl

instance : comm_monoid (α →1* β) :=
{ mul := (*),
  one := 1,
  mul_assoc := by intros; ext; simp [mul_assoc],
  mul_comm := by intros; ext; simp [mul_comm],
  one_mul := by intros; ext; simp,
  mul_one := by intros; ext; simp }

end monoid

section group
variables [group α] [comm_group β]

def inv_aux (f : α →1* β) : α →1* β :=
{ to_fun := λ x, (f x)⁻¹,
  mul := by simp [mul_comm],
  one := by simp }

instance : has_inv (α →1* β) := ⟨inv_aux⟩

@[simp] lemma inv_apply (f : α →1* β) (a : α) : f⁻¹ a = (f a)⁻¹ := rfl

instance : comm_group (α →1* β) :=
{ inv := has_inv.inv,
  mul_left_inv := by intros; ext; simp,
  ..monoid_hom.comm_monoid }

end group
end monoid_hom

namespace add_monoid_hom
section add_monoid
variables [add_monoid α] [add_comm_monoid β]

def add_aux (f g : α →0+ β) : α →0+ β :=
{ to_fun := λ x, f x + g x,
  add := by simp,
  zero := by simp }

instance : has_add (α →0+ β) := ⟨add_aux⟩
instance : has_zero (α →0+ β) := ⟨trivial⟩

@[simp] lemma add_apply (f g : α →0+ β) (a : α) : (f + g) a = f a + g a := rfl

@[simp] lemma zero_apply (a : α) : (0 : α →0+ β) a = 0 := rfl

instance : add_comm_monoid (α →0+ β) :=
{ add := (+),
  zero := 0,
  add_assoc := by intros; ext; simp [mul_assoc],
  add_comm := by intros; ext; simp [mul_comm],
  zero_add := by intros; ext; simp,
  add_zero := by intros; ext; simp }

end add_monoid

section group
variables [add_group α] [add_comm_group β]

def neg_aux (f : α →0+ β) : α →0+ β :=
{ to_fun := λ x, -(f x),
  add := by simp [mul_comm],
  zero := by simp }

instance : has_neg (α →0+ β) := ⟨neg_aux⟩

@[simp] lemma neg_apply (f : α →0+ β) (a : α) : (-f) a = -(f a) := rfl

instance : add_comm_group (α →0+ β) :=
{ neg := has_neg.neg,
  add_left_neg := by intros; ext; simp,
  ..add_monoid_hom.add_comm_monoid }

end group

attribute [to_additive add_monoid_hom.add_aux] monoid_hom.mul_aux
attribute [to_additive add_monoid_hom.add_aux.equations._eqn_1] monoid_hom.mul_aux.equations._eqn_1
attribute [to_additive add_monoid_hom.has_add] monoid_hom.has_mul
attribute [to_additive add_monoid_hom.has_add.equations._eqn_1] monoid_hom.has_mul.equations._eqn_1
attribute [to_additive add_monoid_hom.has_zero] monoid_hom.has_one
attribute [to_additive add_monoid_hom.has_zero.equations._eqn_1] monoid_hom.has_one.equations._eqn_1
attribute [to_additive add_monoid_hom.add_apply] monoid_hom.mul_apply
attribute [to_additive add_monoid_hom.zero_apply] monoid_hom.one_apply
attribute [to_additive add_monoid_hom.add_comm_monoid] monoid_hom.comm_monoid
attribute [to_additive add_monoid_hom.add_comm_monoid.equations._eqn_1] monoid_hom.comm_monoid.equations._eqn_1
attribute [to_additive add_monoid_hom.neg_aux] monoid_hom.inv_aux
attribute [to_additive add_monoid_hom.neg_aux.equations._eqn_1] monoid_hom.inv_aux.equations._eqn_1
attribute [to_additive add_monoid_hom.has_neg] monoid_hom.has_inv
attribute [to_additive add_monoid_hom.has_neg.equations._eqn_1] monoid_hom.has_inv.equations._eqn_1
attribute [to_additive add_monoid_hom.neg_apply] monoid_hom.inv_apply
attribute [to_additive add_monoid_hom.add_comm_group] monoid_hom.comm_group
attribute [to_additive add_monoid_hom.add_comm_group.equations._eqn_1] monoid_hom.comm_group.equations._eqn_1

end add_monoid_hom

/-- Predicate for group anti-homomorphism, or a homomorphism
  into the opposite group. -/
class is_group_anti_hom {β : Type*} [group α] [group β] (f : α → β) : Prop :=
(map_mul : ∀ a b : α, f (a * b) = f b * f a)

namespace is_group_anti_hom
variables [group α] [group β] (f : α → β) [w : is_group_anti_hom f]
include w

theorem map_one : f 1 = 1 :=
mul_self_iff_eq_one.1 $ by rw [← map_mul f, one_mul]

theorem map_inv (a : α) : f a⁻¹ = (f a)⁻¹ :=
eq_inv_of_mul_eq_one $ by rw [← map_mul f, mul_inv_self, map_one f]

end is_group_anti_hom

theorem inv_is_group_anti_hom [group α] : is_group_anti_hom (λ x : α, x⁻¹) :=
⟨mul_inv_rev⟩

lemma add_hom.map_sub [add_group α] [add_group β] (f : α →+ β) (a b : α) :
  f (a - b) = f a - f b := by simp

lemma add_monoid_hom.map_sub [add_group α] [add_group β] (f : α →0+ β) (a b : α) :
  f (a - b) = f a - f b := by simp

namespace units

variables [monoid α] [monoid β] [monoid γ] (f : α →1* β) (g : β →1* γ)

definition map : units α →1* units β :=
{ to_fun := λ u, ⟨f u.val, f u.inv,
    by rw [← f.map_mul, u.val_inv, f.map_one],
    by rw [← f.map_mul, u.inv_val, f.map_one] ⟩,
  mul := λ _ _, units.ext $ f.mul _ _,
  one := units.ext f.one }

instance : is_monoid_hom (coe : units α → α) :=
{ map_one := rfl, map_mul := by simp }

@[simp] lemma coe_map (u : units α) : (map f u : β) = f u := rfl

@[simp] lemma map_id : map (monoid_hom.id : α →1* α) = monoid_hom.id := by ext; refl

lemma map_comp : map (g.comp f) = (map g).comp (map f) := rfl

end units

@[to_additive with_zero]
def with_one (α) := option α

@[to_additive with_zero.monad]
instance : monad with_one := option.monad

@[to_additive with_zero.has_zero]
instance : has_one (with_one α) := ⟨none⟩

@[to_additive with_zero.has_coe_t]
instance : has_coe_t α (with_one α) := ⟨some⟩

@[simp, to_additive with_zero.zero_ne_coe]
lemma with_one.one_ne_coe {a : α} : (1 : with_one α) ≠ a :=
λ h, option.no_confusion h

@[simp, to_additive with_zero.coe_ne_zero]
lemma with_one.coe_ne_one {a : α} : (a : with_one α) ≠ (1 : with_one α) :=
λ h, option.no_confusion h

@[to_additive with_zero.ne_zero_iff_exists]
lemma with_one.ne_one_iff_exists : ∀ {x : with_one α}, x ≠ 1 ↔ ∃ (a : α), x = a
| 1       := ⟨λ h, false.elim $ h rfl, by { rintros ⟨a,ha⟩ h, simpa using h }⟩
| (a : α) := ⟨λ h, ⟨a, rfl⟩, λ h, with_one.coe_ne_one⟩

@[to_additive with_zero.coe_inj]
lemma with_one.coe_inj {a b : α} : (a : with_one α) = b ↔ a = b :=
option.some_inj

@[elab_as_eliminator, to_additive with_zero.cases_on]
protected lemma with_one.cases_on (P : with_one α → Prop) :
  ∀ (x : with_one α), P 1 → (∀ a : α, P a) → P x :=
option.cases_on

attribute [to_additive with_zero.has_zero.equations._eqn_1] with_one.has_one.equations._eqn_1

@[to_additive with_zero.has_add]
instance [has_mul α] : has_mul (with_one α) :=
{ mul := option.lift_or_get (*) }

@[simp, to_additive with_zero.add_coe]
lemma with_one.mul_coe [has_mul α] (a b : α) : (a : with_one α) * b = (a * b : α) := rfl

attribute [to_additive with_zero.has_add.equations._eqn_1] with_one.has_mul.equations._eqn_1

instance [semigroup α] : monoid (with_one α) :=
{ mul_assoc := (option.lift_or_get_assoc _).1,
  one_mul   := (option.lift_or_get_is_left_id _).1,
  mul_one   := (option.lift_or_get_is_right_id _).1,
  ..with_one.has_one,
  ..with_one.has_mul }

attribute [to_additive with_zero.add_monoid._proof_1] with_one.monoid._proof_1
attribute [to_additive with_zero.add_monoid._proof_2] with_one.monoid._proof_2
attribute [to_additive with_zero.add_monoid._proof_3] with_one.monoid._proof_3
attribute [to_additive with_zero.add_monoid] with_one.monoid
attribute [to_additive with_zero.add_monoid.equations._eqn_1] with_one.monoid.equations._eqn_1

instance [comm_semigroup α] : comm_monoid (with_one α) :=
{ mul_comm := (option.lift_or_get_comm _).1,
  ..with_one.monoid }

instance [add_comm_semigroup α] : add_comm_monoid (with_zero α) :=
{ add_comm := (option.lift_or_get_comm _).1,
  ..with_zero.add_monoid }
attribute [to_additive with_zero.add_comm_monoid] with_one.comm_monoid

namespace with_zero

instance [one : has_one α] : has_one (with_zero α) :=
{ ..one }

instance [has_one α] : zero_ne_one_class (with_zero α) :=
{ zero_ne_one := λ h, option.no_confusion h,
  ..with_zero.has_zero,
  ..with_zero.has_one }

lemma coe_one [has_one α] : ((1 : α) : with_zero α) = 1 := rfl

instance [has_mul α] : mul_zero_class (with_zero α) :=
{ mul       := λ o₁ o₂, o₁.bind (λ a, o₂.map (λ b, a * b)),
  zero_mul  := λ a, rfl,
  mul_zero  := λ a, by cases a; refl,
  ..with_zero.has_zero }

@[simp] lemma mul_coe [has_mul α] (a b : α) :
  (a : with_zero α) * b = (a * b : α) := rfl

instance [semigroup α] : semigroup (with_zero α) :=
{ mul_assoc := λ a b c, match a, b, c with
    | none,   _,      _      := rfl
    | some a, none,   _      := rfl
    | some a, some b, none   := rfl
    | some a, some b, some c := congr_arg some (mul_assoc _ _ _)
    end,
  ..with_zero.mul_zero_class }

instance [comm_semigroup α] : comm_semigroup (with_zero α) :=
{ mul_comm := λ a b, match a, b with
    | none,   _      := (mul_zero _).symm
    | some a, none   := rfl
    | some a, some b := congr_arg some (mul_comm _ _)
    end,
  ..with_zero.semigroup }

instance [monoid α] : monoid (with_zero α) :=
{ one_mul := λ a, match a with
    | none   := rfl
    | some a := congr_arg some $ one_mul _
    end,
  mul_one := λ a, match a with
    | none   := rfl
    | some a := congr_arg some $ mul_one _
    end,
  ..with_zero.zero_ne_one_class,
  ..with_zero.semigroup }

instance [comm_monoid α] : comm_monoid (with_zero α) :=
{ ..with_zero.monoid, ..with_zero.comm_semigroup }

definition inv [has_inv α] (x : with_zero α) : with_zero α :=
do a ← x, return a⁻¹

instance [has_inv α] : has_inv (with_zero α) := ⟨with_zero.inv⟩

@[simp] lemma inv_coe [has_inv α] (a : α) :
  (a : with_zero α)⁻¹ = (a⁻¹ : α) := rfl
@[simp] lemma inv_zero [has_inv α] :
  (0 : with_zero α)⁻¹ = 0 := rfl

section group
variables [group α]

@[simp] lemma inv_one : (1 : with_zero α)⁻¹ = 1 :=
show ((1⁻¹ : α) : with_zero α) = 1, by simp [coe_one]

definition with_zero.div (x y : with_zero α) : with_zero α :=
x * y⁻¹

instance : has_div (with_zero α) := ⟨with_zero.div⟩

@[simp] lemma zero_div (a : with_zero α) : 0 / a = 0 := rfl
@[simp] lemma div_zero (a : with_zero α) : a / 0 = 0 := by change a * _ = _; simp

lemma div_coe (a b : α) : (a : with_zero α) / b = (a * b⁻¹ : α) := rfl

lemma one_div (x : with_zero α) : 1 / x = x⁻¹ := one_mul _

@[simp] lemma div_one : ∀ (x : with_zero α), x / 1 = x
| 0       := rfl
| (a : α) := show _ * _ = _, by simp

@[simp] lemma mul_right_inv : ∀  (x : with_zero α) (h : x ≠ 0), x * x⁻¹ = 1
| 0       h := false.elim $ h rfl
| (a : α) h := by simp [coe_one]

@[simp] lemma mul_left_inv : ∀  (x : with_zero α) (h : x ≠ 0), x⁻¹ * x = 1
| 0       h := false.elim $ h rfl
| (a : α) h := by simp [coe_one]

@[simp] lemma mul_inv_rev : ∀ (x y : with_zero α), (x * y)⁻¹ = y⁻¹ * x⁻¹
| 0       0       := rfl
| 0       (b : α) := rfl
| (a : α) 0       := rfl
| (a : α) (b : α) := by simp

@[simp] lemma mul_div_cancel {a b : with_zero α} (hb : b ≠ 0) : a * b / b = a :=
show _ * _ * _ = _, by simp [mul_assoc, hb]

@[simp] lemma div_mul_cancel {a b : with_zero α} (hb : b ≠ 0) : a / b * b = a :=
show _ * _ * _ = _, by simp [mul_assoc, hb]

lemma div_eq_iff_mul_eq {a b c : with_zero α} (hb : b ≠ 0) : a / b = c ↔ c * b = a :=
by split; intro h; simp [h.symm, hb]

end group

section comm_group
variables [comm_group α] {a b c d : with_zero α}

lemma div_eq_div (hb : b ≠ 0) (hd : d ≠ 0) : a / b = c / d ↔ a * d = b * c :=
begin
  rw ne_zero_iff_exists at hb hd,
  rcases hb with ⟨b, rfl⟩,
  rcases hd with ⟨d, rfl⟩,
  induction a using with_zero.cases_on;
  induction c using with_zero.cases_on,
  { refl },
  { simp [div_coe] },
  { simp [div_coe] },
  erw [with_zero.coe_inj, with_zero.coe_inj],
  show a * b⁻¹ = c * d⁻¹ ↔ a * d = b * c,
  split; intro H,
  { rw mul_inv_eq_iff_eq_mul at H,
    rw [H, mul_right_comm, inv_mul_cancel_right, mul_comm] },
  { rw [mul_inv_eq_iff_eq_mul, mul_right_comm, mul_comm c, ← H, mul_inv_cancel_right] }
end

end comm_group

end with_zero

/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Yury Kudryashov
-/
import algebra.group order.fixed_points data.set.lattice group_theory.submonoid group_theory.subgroup
import category_theory.endomorphism category_theory.types

universes u v w
variables (M : Type u) [monoid M] (α : Type v)

open category_theory (End)

def mul_action := M →* End α

-- TODO : choose notation priorities
infixr ` ↷ `:50 := mul_action

variables {M α}

def mul_action.smul (a : M ↷ α) : M → End α := @coe_fn _ monoid_hom.has_coe_to_fun a

notation x ` •[`:73 a `] ` y:70 := mul_action.smul a x y

namespace mul_action
variables (a : M ↷ α)

@[simp] lemma one_smul (x : α) : 1 •[a] x = x := congr_fun a.map_one x

lemma mul_smul (g₁ g₂ : M) (x : α) : (g₁ * g₂) •[a] x = g₁ •[a] g₂ •[a] x :=
congr_fun (a.map_mul g₁ g₂) x

@[extensionality]
lemma ext : function.injective (@smul M _ α) := monoid_hom.ext

lemma ext_iff : 

variables (M α)

structure core :=
(smul : M → α → α)
(one_smul : ∀ x, smul 1 x = x)
(mul_smul : ∀ g₁ g₂ x, smul (g₁ * g₂) x = smul g₁ (smul g₂ x))

variables {M α}

def of_core (a : core M α) : M ↷ α :=
{ to_fun := a.smul,
  map_one' := funext a.one_smul,
  map_mul' := λ g₁ g₂, funext (a.mul_smul g₁ g₂) }

variables (M α)

def equiv_core : M ↷ α ≃ core M α :=
{ to_fun := λ a, ⟨a.smul, a.one_smul, a.mul_smul⟩,
  inv_fun := of_core,
  left_inv := λ a, _
}

def of_hom (f : α → End β) [h : is_monoid_hom f] : α ↷ β := ⟨f, h⟩

@[simp] lemma one_smul (y : β) : 1 •[a] y = y :=
  (is_monoid_hom.map_one a.smul).symm ▸ rfl

@[simp] lemma mul_smul (x₁ x₂ : α) (y : β) : (x₁ * x₂) •[a] y = x₁ •[a] x₂ •[a] y :=
  by rw [is_monoid_hom.map_mul a.smul]; refl

def orbit (b : β) := set.range (λ x : α, x •[a] b)

@[simp] lemma mem_orbit_iff {b₁ b₂ : β} : b₂ ∈ a.orbit b₁ ↔ ∃ x : α, x •[a] b₁ = b₂ :=
iff.rfl

@[simp] lemma mem_orbit (b : β) (x : α) : x •[a] b ∈ a.orbit b :=
⟨x, rfl⟩

@[refl] lemma mem_orbit_self (b : β) : b ∈ a.orbit b :=
⟨1, a.one_smul b⟩

@[trans] lemma mem_orbit_trans (b₁ b₂ b₃ : β) :
  b₁ ∈ a.orbit b₂ → b₂ ∈ a.orbit b₃ → b₁ ∈ a.orbit b₃ :=
assume ⟨x₁, h₁⟩ ⟨x₂, h₂⟩,
⟨x₁ * x₂, h₁ ▸ h₂ ▸ a.mul_smul x₁ x₂ b₃⟩

def stabilizer (b : β) : set α := {x : α | x •[a] b = b}

@[simp] lemma mem_stabilizer_iff {b : β} {x : α} :
  x ∈ a.stabilizer b ↔ x •[a] b = b := iff.rfl

instance stabilizer_is_submonoid (b : β) : is_submonoid (a.stabilizer b) :=
{ one_mem := a.one_smul b,
  mul_mem := λ x₁ x₂, by simp only [mem_stabilizer_iff, mul_smul]; intros h₁ h₂; exact h₂.symm ▸ h₁ }

def stabilizer_Inter : set α := ⋂ b, a.stabilizer b

instance stabilizer_Inter_is_submonoid : is_submonoid a.stabilizer_Inter :=
set.Inter.is_submonoid a.stabilizer

@[simp] lemma mem_stabilizer_Inter_iff {x : α} :
  x ∈ a.stabilizer_Inter ↔ ∀ b, x •[a] b = b :=
set.mem_Inter

def fixed_points (x : α) := lattice.fixed_points (a.smul x)

@[simp] lemma mem_fixed_points_iff {x : α} {b : β} :
  b ∈ a.fixed_points x ↔ x •[a] b = b := iff.rfl

lemma mem_fixed_points_iff_mem_stabilizer {x : α} {b : β} :
  b ∈ a.fixed_points x ↔ x ∈ a.stabilizer b := iff.rfl

def fixed_points_Inter := ⋂ x : α, a.fixed_points x

@[simp] lemma mem_fixed_points_Inter_iff {b : β} :
  b ∈ a.fixed_points_Inter ↔ ∀ x : α, x •[a] b = b :=
set.mem_Inter

end mul_action

namespace mul_action
  variables [group α] (a : mul_action α β)

  @[simp] lemma smul_inv_left (x : α) (y : β) : x⁻¹ •[a] x •[a] y = y :=
  by rw [← a.mul_smul, mul_left_inv x]; exact a.one_smul y

  @[simp] lemma smul_inv_right (x : α) (y : β) : x •[a] x⁻¹ •[a] y = y :=
  by rw [← a.mul_smul, mul_right_inv x]; exact a.one_smul y

  def to_perm (x : α) : equiv.perm β :=
  { to_fun := a.smul x,
    inv_fun := a.smul x⁻¹,
    left_inv := a.smul_inv_left x,
    right_inv := a.smul_inv_right x }

  instance to_perm_is_group_hom : is_group_hom a.to_perm :=
  { map_mul := λ x₁ x₂, by ext; apply a.mul_smul }

  instance stabilizer_is_subgroup (b : β) : is_subgroup (a.stabilizer b) :=
  { inv_mem := λ x, by simp only [mem_stabilizer_iff]; intro h; rw [← h, smul_inv_left, h] }

  instance stabilizer_Inter_is_subgroup : is_subgroup a.stabilizer_Inter :=
  set.Inter.is_subgroup _
end mul_action

/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Yury Kudryashov
-/
import algebra.group order.fixed_points data.set.lattice group_theory.subgroup
import category_theory.endomorphism category_theory.types logic.unique

universes u v w
variables (M : Type u) [monoid M] {G : Type v} [group G] (α : Type w)

open category_theory (End)

def mul_action := M →* End α

-- TODO : choose notation priorities
infixr ` ↷ `:50 := mul_action

variables {M α}

def mul_action.smul (a : M ↷ α) : M → End α := @coe_fn _ monoid_hom.has_coe_to_fun a

notation x ` •[`:73 a `] ` y:70 := mul_action.smul a x y

namespace mul_action
variables (a : M ↷ α) (a' : G ↷ α)

@[simp] lemma one_smul (x : α) : 1 •[a] x = x := congr_fun a.map_one x

lemma mul_smul (g₁ g₂ : M) (x : α) : (g₁ * g₂) •[a] x = g₁ •[a] g₂ •[a] x :=
congr_fun (a.map_mul g₁ g₂) x

@[simp] lemma smul_inv_left (g : G) (x : α) : g⁻¹ •[a'] g •[a'] x = x :=
by rw [← a'.mul_smul, mul_left_inv g, a'.one_smul]

@[simp] lemma smul_inv_right (g : G) (x : α) : g •[a'] g⁻¹ •[a'] x = x :=
by rw [← a'.mul_smul, mul_right_inv g, a'.one_smul]

@[extensionality]
lemma ext : function.injective (@smul M _ α) := monoid_hom.coe_inj

section
-- TODO : lemmas in this section should be moved to other files
variables (G α)

def units_End_equiv_perm : units (End α) ≃* equiv.perm α :=
{ to_fun := λ f, ⟨f.val, f.inv, λ x, congr_fun f.inv_val x, λ x, congr_fun f.val_inv x⟩,
  inv_fun := λ π, ⟨π.to_fun, π.inv_fun, funext π.right_inv, funext π.left_inv⟩,
  left_inv := λ f, units.ext rfl,
  right_inv := λ π, equiv.eq_of_to_fun_eq rfl,
  map_mul' := λ f g, equiv.eq_of_to_fun_eq rfl }

variables {G α}

-- TODO bad name
def lift_to_perm (f : G →* End α) : G →* equiv.perm α :=
(units_End_equiv_perm α).to_monoid_hom.comp $ (units.map f).comp (to_units G).to_monoid_hom

end

def to_perm : G →* equiv.perm α := lift_to_perm a'

lemma bijective (g : G) : function.bijective (a'.smul g) :=
(a'.to_perm g).bijective

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

lemma of_core_smul (a : core M α) : (of_core a).smul = a.smul := rfl

variables (M α)

def equiv_core : M ↷ α ≃ core M α :=
{ to_fun := λ a, ⟨a.smul, a.one_smul, a.mul_smul⟩,
  inv_fun := of_core,
  left_inv := λ a, ext (of_core_smul _),
  right_inv := λ a, by cases a; refl }

variables {M G α}

def orbit (x : α) : set α := set.range (λ g : M, g •[a] x)

@[simp] lemma mem_orbit_iff {x₁ x₂ : α} :
  x₁ ∈ a.orbit x₂ ↔ ∃ g : M, g •[a] x₂ = x₁ :=
iff.rfl

@[simp] lemma mem_orbit_mk (g : M) (x : α) : (g •[a] x) ∈ a.orbit x :=
⟨g, rfl⟩

def orbit_mk (g : M) (x : α) : a.orbit x := ⟨g •[a] x, ⟨g, rfl⟩⟩

@[refl] lemma mem_orbit_refl (x : α) : x ∈ a.orbit x := ⟨1, a.one_smul x⟩

def orbit_self (x : α) : a.orbit x := ⟨x, a.mem_orbit_refl x⟩

instance orbit_inhabited (x : α) : inhabited (a.orbit x) := ⟨a.orbit_self x⟩

@[simp] lemma orbit_default_val (x : α) : (default $ a.orbit x).val = x := rfl

@[simp] lemma orbit_default_coe (x : α) : ↑(default $ a.orbit x) = x := rfl

@[symm] lemma mem_orbit_symm ⦃x y : α⦄ : y ∈ a'.orbit x → x ∈ a'.orbit y :=
λ ⟨g, h⟩, ⟨g⁻¹, h ▸ a'.smul_inv_left g x⟩

lemma mem_orbit_trans' {x₁ x₂ x₃ : α} {g₁ g₂ : M} (h₁ : g₁ •[a] x₂ = x₁) (h₂ : g₂ •[a] x₃ = x₂) :
  (g₁ * g₂) •[a] x₃ = x₁ :=
h₁ ▸ h₂ ▸ a.mul_smul g₁ g₂ x₃

@[trans] lemma mem_orbit_trans ⦃x₁ x₂ x₃ : α⦄ :
  x₂ ∈ a.orbit x₁ → x₃ ∈ a.orbit x₂ → x₃ ∈ a.orbit x₁ :=
assume ⟨g₁, h₁⟩ ⟨g₂, h₂⟩,
⟨g₂ * g₁, a.mem_orbit_trans' h₂ h₁⟩

lemma orbit_mem_orbit_sub_orbit {x y : α} : y ∈ a.orbit x → a.orbit y ⊆ a.orbit x :=
λ hy z hz, a.mem_orbit_trans hy hz

lemma orbit_mem_orbit_eq_orbit {x y : α} : y ∈ a'.orbit x → a'.orbit y = a'.orbit x :=
λ hy, set.subset.antisymm
  (a'.orbit_mem_orbit_sub_orbit hy)
  (a'.orbit_mem_orbit_sub_orbit (a'.mem_orbit_symm hy))

lemma orbit_eq_iff_mem_orbit {x y : α} : a'.orbit x = a'.orbit y ↔ y ∈ a'.orbit x :=
⟨λ h, h.symm ▸ a'.mem_orbit_refl y, λ h, (a'.orbit_mem_orbit_eq_orbit h).symm⟩

lemma orbit_eq_iff_nonempty_inter {x y : α} :
  a'.orbit x = a'.orbit y ↔ nonempty ↥((a'.orbit x) ∩ (a'.orbit y)) :=
a'.orbit_eq_iff_mem_orbit.trans
{ mp := λ h, ⟨⟨y, ⟨h, a'.mem_orbit_refl y⟩⟩⟩,
  mpr := λ ⟨⟨z, ⟨hx, hy⟩⟩⟩, a'.mem_orbit_trans hx (a'.mem_orbit_symm hy) }

def orbits_setoid : setoid α :=
{ r := a'.orbit,
  iseqv := ⟨a'.mem_orbit_refl, a'.mem_orbit_symm, a'.mem_orbit_trans⟩ }

def orbits := quotient a'.orbits_setoid

def stabilizer (x : α) : set M := {g : M | g •[a] x = x}

@[simp] lemma mem_stabilizer_iff {x : α} {g : M} :
  g ∈ a.stabilizer x ↔ g •[a] x = x := iff.rfl

instance stabilizer_is_submonoid (x : α) : is_submonoid (a.stabilizer x) :=
{ one_mem := a.one_smul x,
  mul_mem := λ g₁ g₂ h₁ h₂, a.mem_orbit_trans' h₁ h₂ }

instance stabilizer_is_subgroup (x : α) : is_subgroup (a'.stabilizer x) :=
{ inv_mem := λ g, by simp only [mem_stabilizer_iff]; intro h; rw [← h, smul_inv_left, h] }

def stabilizer_Inter : set M := ⋂ x, a.stabilizer x

instance stabilizer_Inter_is_submonoid : is_submonoid a.stabilizer_Inter :=
is_submonoid.Inter a.stabilizer

instance stabilizer_Inter_is_subgroup : is_subgroup a'.stabilizer_Inter :=
is_subgroup.Inter a'.stabilizer

@[simp] lemma mem_stabilizer_Inter_iff {g : M} : g ∈ a.stabilizer_Inter ↔ ∀ x, g •[a] x = x :=
set.mem_Inter

def fixed_points (g : M) := lattice.fixed_points (a.smul g)

@[simp] lemma mem_fixed_points_iff {g : M} {x : α} :
  x ∈ a.fixed_points g ↔ g •[a] x = x := iff.rfl

lemma mem_fixed_points_iff_mem_stabilizer {g : M} {x : α} :
  x ∈ a.fixed_points g ↔ g ∈ a.stabilizer x := iff.rfl

def fixed_points_Inter := ⋂ g : M, a.fixed_points g

@[simp] lemma mem_fixed_points_Inter_iff {x : α} :
  x ∈ a.fixed_points_Inter ↔ ∀ g : M, g •[a] x = x :=
set.mem_Inter

lemma orbit_unique_of_mem_fixed_points_Inter {x : α}
  (h : x ∈ a.fixed_points_Inter) : unique (a.orbit x) :=
{ uniq := λ ⟨y, ⟨g, h'⟩⟩, subtype.eq $
     by simp only [h'.symm, a.mem_fixed_points_Inter_iff.1 h, a.orbit_default_val],
 to_inhabited := a.orbit_inhabited x }

lemma mem_fixed_points_Inter_iff_orbit_subsingleton {x : α} :
  x ∈ a.fixed_points_Inter ↔ subsingleton (a.orbit x) :=
⟨λ h, @unique.subsingleton _ $ a.orbit_unique_of_mem_fixed_points_Inter h,
 λ h, a.mem_fixed_points_Inter_iff.2 $
   λ g, subtype.ext.1 $ @subsingleton.elim _ h (a.orbit_mk g x) (a.orbit_self x)⟩

def is_invariant (s : set α) : Prop := ∀ g {x}, x ∈ s → g •[a] x ∈ s

lemma is_invariant.smul_image_subset {s : set α} (h : a.is_invariant s) (g : M) :
  a.smul g '' s ⊆ s :=
λ x ⟨y, ⟨hy, hxy⟩⟩, hxy ▸ h g hy

lemma is_invariant.orbit_subset {s : set α} (h : a.is_invariant s) (x : s) :
  a.orbit x ⊆ s :=
λ y ⟨g, hxy⟩, hxy ▸ h g x.property

end mul_action

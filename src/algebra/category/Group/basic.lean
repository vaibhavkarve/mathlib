/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import algebra.punit_instances
import algebra.category.Mon.basic
import category_theory.endomorphism
import category_theory.epi_mono

/-!
# Category instances for group, add_group, comm_group, and add_comm_group.

We introduce the bundled categories:
* `Group`
* `AddGroup`
* `CommGroup`
* `AddCommGroup`
along with the relevant forgetful functors between them, and to the bundled monoid categories.

## Implementation notes

See the note [locally reducible category instances].
-/

universes u v

open category_theory

/-- The category of groups and group morphisms. -/
@[to_additive AddGroup]
def Group : Type (u+1) := induced_category Mon (bundled.map group.to_monoid)

namespace Group

/-- Construct a bundled Group from the underlying type and typeclass. -/
@[to_additive] def of (X : Type u) [group X] : Group := bundled.of X

local attribute [reducible] Group

@[to_additive]
instance : has_coe_to_sort Group := infer_instance -- short-circuit type class inference

@[to_additive add_group]
instance (G : Group) : group G := G.str

@[to_additive]
instance : has_one Group := ⟨Group.of punit⟩

@[to_additive]
instance : inhabited Group := ⟨1⟩

@[to_additive]
instance : unique (1 : Group.{u}) :=
{ default := 1,
  uniq := λ a, begin cases a, refl, end }

@[simp, to_additive]
lemma one_apply (G H : Group) (g : G) : (1 : G ⟶ H) g = 1 := rfl

@[to_additive]
instance : concrete_category Group := infer_instance -- short-circuit type class inference

@[to_additive,ext]
lemma ext (G H : Group) (f₁ f₂ : G ⟶ H) (w : ∀ x, f₁ x = f₂ x) : f₁ = f₂ :=
by { ext1, apply w }

attribute [ext] AddGroup.ext

@[to_additive has_forget_to_AddMon]
instance has_forget_to_Mon : has_forget₂ Group Mon := infer_instance -- short-circuit type class inference

end Group


/-- The category of commutative groups and group morphisms. -/
@[to_additive AddCommGroup]
def CommGroup : Type (u+1) := induced_category Group (bundled.map comm_group.to_group)

/-- `Ab` is an abbreviation for `AddCommGroup`, for the sake of mathematicians' sanity. -/
abbreviation Ab := AddCommGroup

namespace CommGroup

/-- Construct a bundled CommGroup from the underlying type and typeclass. -/
@[to_additive] def of (G : Type u) [comm_group G] : CommGroup := bundled.of G

local attribute [reducible] CommGroup

@[to_additive]
instance : has_coe_to_sort CommGroup := infer_instance -- short-circuit type class inference

@[to_additive add_comm_group_instance]
instance comm_group_instance (G : CommGroup) : comm_group G := G.str

@[to_additive] instance : has_one CommGroup := ⟨CommGroup.of punit⟩

@[to_additive] instance : inhabited CommGroup := ⟨1⟩

@[to_additive]
instance : unique (1 : CommGroup.{u}) :=
{ default := 1,
  uniq := λ a, begin cases a, refl, end }

@[simp, to_additive]
lemma one_apply (G H : CommGroup) (g : G) : (1 : G ⟶ H) g = 1 := rfl

@[to_additive] instance : concrete_category CommGroup := infer_instance -- short-circuit type class inference

@[to_additive,ext]
lemma ext (G H : CommGroup) (f₁ f₂ : G ⟶ H) (w : ∀ x, f₁ x = f₂ x) : f₁ = f₂ :=
by { ext1, apply w }

attribute [ext] AddCommGroup.ext

@[to_additive has_forget_to_AddGroup]
instance has_forget_to_Group : has_forget₂ CommGroup Group := infer_instance -- short-circuit type class inference

@[to_additive has_forget_to_AddCommMon]
instance has_forget_to_CommMon : has_forget₂ CommGroup CommMon :=
induced_category.has_forget₂ (λ G : CommGroup, CommMon.of G)

end CommGroup

namespace AddCommGroup

/-- Any element of an abelian group gives a unique morphism from `ℤ` sending
`1` to that element. -/
-- TODO allow other universe levels
-- this will require writing a `ulift_instances.lean` file
def as_hom {G : AddCommGroup.{0}} (g : G) : (AddCommGroup.of ℤ) ⟶ G :=
{ to_fun := λ i : ℤ, i • g,
  map_zero' := rfl,
  map_add' := λ a b, gpow_add g a b }

@[simp]
lemma as_hom_apply {G : AddCommGroup.{0}} (g : G) (i : ℤ) : (as_hom g) i = i • g := rfl

lemma as_hom_injective {G : AddCommGroup.{0}} : function.injective (@as_hom G) :=
λ h k w, by convert congr_arg (λ k : (AddCommGroup.of ℤ) ⟶ G, (k : ℤ → G) (1 : ℤ)) w; simp

@[ext]
lemma int_hom_ext
  {G : AddCommGroup.{0}} (f g : (AddCommGroup.of ℤ) ⟶ G) (w : f (1 : ℤ) = g (1 : ℤ)) : f = g :=
begin
  ext,
  change ℤ at x,
  rw ←gsmul_int_one x,
  rw [add_monoid_hom.map_gsmul, add_monoid_hom.map_gsmul, w],
end

-- TODO: this argument should be generalised to the situation where
-- the forgetful functor is representable.
lemma injective_of_mono {G H : AddCommGroup.{0}} (f : G ⟶ H) [mono f] : function.injective f :=
λ g₁ g₂ h,
begin
  have t0 : as_hom g₁ ≫ f = as_hom g₂ ≫ f :=
  begin
    ext,
    dsimp [as_hom],
    simpa using h,
  end,
  have t1 : as_hom g₁ = as_hom g₂ := (cancel_mono _).1 t0,
  apply as_hom_injective t1,
end

end AddCommGroup

variables {X Y : Type u}

/-- Build an isomorphism in the category `Group` from a `mul_equiv` between `group`s. -/
@[to_additive add_equiv.to_AddGroup_iso "Build an isomorphism in the category `AddGroup` from a `add_equiv` between `add_group`s."]
def mul_equiv.to_Group_iso [group X] [group Y] (e : X ≃* Y) : Group.of X ≅ Group.of Y :=
{ hom := e.to_monoid_hom,
  inv := e.symm.to_monoid_hom }

attribute [simps] mul_equiv.to_Group_iso add_equiv.to_AddGroup_iso

/-- Build an isomorphism in the category `CommGroup` from a `mul_equiv` between `comm_group`s. -/
@[to_additive add_equiv.to_AddCommGroup_iso "Build an isomorphism in the category `AddCommGroup` from a `add_equiv` between `add_comm_group`s."]
def mul_equiv.to_CommGroup_iso [comm_group X] [comm_group Y] (e : X ≃* Y) : CommGroup.of X ≅ CommGroup.of Y :=
{ hom := e.to_monoid_hom,
  inv := e.symm.to_monoid_hom }

attribute [simps] mul_equiv.to_CommGroup_iso add_equiv.to_AddCommGroup_iso

namespace category_theory.iso

/-- Build a `mul_equiv` from an isomorphism in the category `Group`. -/
@[to_additive AddGroup_iso_to_add_equiv "Build an `add_equiv` from an isomorphism in the category `AddGroup`."]
def Group_iso_to_mul_equiv {X Y : Group.{u}} (i : X ≅ Y) : X ≃* Y :=
{ to_fun    := i.hom,
  inv_fun   := i.inv,
  left_inv  := by tidy,
  right_inv := by tidy,
  map_mul'  := by tidy }.

attribute [simps] Group_iso_to_mul_equiv AddGroup_iso_to_add_equiv

/-- Build a `mul_equiv` from an isomorphism in the category `CommGroup`. -/
@[to_additive AddCommGroup_iso_to_add_equiv "Build an `add_equiv` from an isomorphism in the category `AddCommGroup`."]
def CommGroup_iso_to_mul_equiv {X Y : CommGroup.{u}} (i : X ≅ Y) : X ≃* Y :=
{ to_fun    := i.hom,
  inv_fun   := i.inv,
  left_inv  := by tidy,
  right_inv := by tidy,
  map_mul'  := by tidy }.

attribute [simps] CommGroup_iso_to_mul_equiv AddCommGroup_iso_to_add_equiv

end category_theory.iso

/-- multiplicative equivalences between `group`s are the same as (isomorphic to) isomorphisms in `Group` -/
@[to_additive add_equiv_iso_AddGroup_iso "additive equivalences between `add_group`s are the same as (isomorphic to) isomorphisms in `AddGroup`"]
def mul_equiv_iso_Group_iso {X Y : Type u} [group X] [group Y] :
  (X ≃* Y) ≅ (Group.of X ≅ Group.of Y) :=
{ hom := λ e, e.to_Group_iso,
  inv := λ i, i.Group_iso_to_mul_equiv, }

/-- multiplicative equivalences between `comm_group`s are the same as (isomorphic to) isomorphisms in `CommGroup` -/
@[to_additive add_equiv_iso_AddCommGroup_iso "additive equivalences between `add_comm_group`s are the same as (isomorphic to) isomorphisms in `AddCommGroup`"]
def mul_equiv_iso_CommGroup_iso {X Y : Type u} [comm_group X] [comm_group Y] :
  (X ≃* Y) ≅ (CommGroup.of X ≅ CommGroup.of Y) :=
{ hom := λ e, e.to_CommGroup_iso,
  inv := λ i, i.CommGroup_iso_to_mul_equiv, }

namespace category_theory.Aut

/-- The (bundled) group of automorphisms of a type is isomorphic to the (bundled) group of permutations. -/
def iso_perm {α : Type u} : Group.of (Aut α) ≅ Group.of (equiv.perm α) :=
{ hom := ⟨λ g, g.to_equiv, (by tidy), (by tidy)⟩,
  inv := ⟨λ g, g.to_iso, (by tidy), (by tidy)⟩ }

/-- The (unbundled) group of automorphisms of a type is `mul_equiv` to the (unbundled) group of permutations. -/
def mul_equiv_perm {α : Type u} : Aut α ≃* equiv.perm α :=
iso_perm.Group_iso_to_mul_equiv

end category_theory.Aut

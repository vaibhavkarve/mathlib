/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import group_theory.mul_action.basic data.equiv.algebra group_theory.quotient_group logic.relator

universes u v w

namespace mul_action

section monoid

variables {M : Type u} [monoid M] {α : Type v} (a : M ↷ α)

def comp_hom {N : Type*} [monoid N] (f : N →* M) : N ↷ α :=
monoid_hom.comp a f

variable {a}

def is_invariant.restrict {s : set α} (h : a.is_invariant s) : M ↷ s :=
of_core
{ smul := λ g x, ⟨g •[a] x, h g x.2⟩,
  mul_smul := λ g₁ g₂ x, subtype.eq $ a.mul_smul g₁ g₂ x,
  one_smul := λ x, subtype.eq $ a.one_smul x }

variable (a)

section

variables (aM : M ↷ α) {N : Type*} [monoid N] (aN : N ↷ α)

def commute : Prop := ∀ gM gN x, gM •[aM] gN •[aN] x = gN •[aN] gM •[aM] x

variables {aM aN}

lemma commute.symm (h : aM.commute aN) : aN.commute aM :=
λ gN gM x, (h gM gN x).symm

lemma commute.orbit_relator (h : aM.commute aN) (gM : M) :
  (aN.orbit ⇒ aN.orbit) (aM.smul gM) (aM.smul gM) :=
assume x y ⟨gN, hxy⟩,
⟨gN,
 show gN •[aN] gM •[aM] x = gM •[aM] y,
 from (h gM gN x) ▸ congr_arg _ hxy⟩

end

def quot {r : α → α → Prop} (h : ∀ g, (r ⇒ r) (a.smul g) (a.smul g)) : M ↷ (quot r) :=
of_core
{ smul := λ g, quot.map (a.smul g) (h g),
  mul_smul := λ g₁ g₂ x, quot.induction_on x $ λ x', by simp only [quot.map, a.mul_smul g₁ g₂ x'],
  one_smul := λ x, quot.induction_on x $ λ x', by simp only [quot.map, a.one_smul x'] }

def quotient [r : setoid α] (h : ∀ g, ((≈) ⇒ (≈)) (a.smul g) (a.smul g)) : M ↷ (quotient r) :=
a.quot h

def on_orbits {G : Type*} [group G] (aG : G ↷ α) (h : a.commute aG) : M ↷ aG.orbits :=
a.quot h.orbit_relator

end monoid

end mul_action

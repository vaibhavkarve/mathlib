/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Probability Theory

TODO: add finite measures to measure theory
-/
import measure_theory.giry_monad
noncomputable theory
local attribute [instance, priority 0] classical.prop_decidable

open set lattice filter function measure_theory measure_theory.measure

namespace probability_theory

section
variables (α : Type*) [measurable_space α]

structure probability_measure extends measure_theory.measure α :=
(measure_univ : to_measure univ = 1)

instance : measurable_space (probability_measure α) :=
measure.measurable_space.comap probability_measure.to_measure

lemma measurable_to_measure :
  measurable (@probability_measure.to_measure α _) :=
measurable_space.le_map_comap

instance : has_coe (probability_measure α) (measure α) :=
⟨probability_measure.to_measure⟩

instance : has_coe_to_fun (probability_measure α) :=
⟨λ_, set α → nnreal, λp s, ennreal.to_nnreal (p.to_measure s)⟩

end

namespace probability_measure
section
parameters {α : Type*} [measurable_space α] (p : probability_measure α)

open ennreal

lemma to_measure_lt_top (s : set α) : p.to_measure s < ⊤ :=
lt_of_le_of_lt (measure_mono $ subset_univ s) $ p.measure_univ.symm ▸ coe_lt_top

lemma to_measure_ne_top (s : set α) : p.to_measure s ≠ ⊤ :=
lt_top_iff_ne_top.1 (to_measure_lt_top s)

lemma coe_eq_to_measure (s : set α) : (p s : ennreal) = p.to_measure s :=
coe_to_nnreal (to_measure_ne_top s)

@[simp] lemma prob_empty : p ∅ = 0 :=
by rw [← coe_eq_coe, coe_eq_to_measure, measure_empty, coe_zero]

@[simp] lemma prob_univ : p univ = 1 :=
by rw [← coe_eq_coe, coe_eq_to_measure]; exact p.measure_univ

@[simp] lemma prob_mono {s t} (h : s ⊆ t) : p s ≤ p t :=
by rw [← coe_le_coe, coe_eq_to_measure, coe_eq_to_measure]; exact measure_mono h

lemma prob_mono_null {s t} (h : t ⊆ s) (h₂ : p s = 0) : p t = 0 :=
by rw [← le_zero_iff_eq, ← h₂]; exact prob_mono p h

lemma prob_Union_null {β} [encodable β] {s : β → set α} (h : ∀ i, p (s i) = 0) : p (⋃i, s i) = 0 :=
begin
  rw [← coe_eq_coe, coe_eq_to_measure, measure_Union_null, coe_zero],
  assume i, specialize h i, rwa [← coe_eq_coe, coe_eq_to_measure] at h
end

theorem prob_union_le (s₁ s₂ : set α) : p (s₁ ∪ s₂) ≤ p s₁ + p s₂ :=
by simp only [coe_le_coe.symm, coe_add, coe_eq_to_measure]; exact measure_union_le _ _

lemma prob_union {s₁ s₂ : set α}
  (hd : disjoint s₁ s₂) (h₁ : is_measurable s₁) (h₂ : is_measurable s₂) :
  p (s₁ ∪ s₂) = p s₁ + p s₂ :=
by simp only [coe_eq_coe.symm, coe_add, coe_eq_to_measure]; exact measure_union hd h₁ h₂

lemma prob_diff {s₁ s₂ : set α} (h : s₂ ⊆ s₁) (h₁ : is_measurable s₁) (h₂ : is_measurable s₂) :
  p (s₁ \ s₂) = p s₁ - p s₂ :=
by simp only [coe_eq_coe.symm, coe_sub, coe_eq_to_measure];
  exact measure_diff h h₁ h₂ (to_measure_lt_top _ _)

protected lemma nonempty : nonempty α :=
classical.by_contradiction $ assume h,
  have 0 = p univ, by rw [univ_eq_empty_iff.2 h]; exact p.prob_empty.symm,
  @zero_ne_one nnreal _ $ by rwa [p.prob_univ] at this

@[simp] lemma integral_const (r : ennreal) : integral p.to_measure (λa, r) = r :=
suffices integral p.to_measure (λa, ⨆ (h : a ∈ (univ : set α)), r) =
  r * p.to_measure univ, by rw [← coe_eq_to_measure] at this; simpa,
@lintegral_supr_const α { μ := p.to_measure } r _ is_measurable.univ

end

section giry_monad

variables {α : Type*} {β : Type*} {γ : Type*}
variables [measurable_space α] [measurable_space β] [measurable_space γ]

def pure (a : α) : probability_measure α :=
⟨measure.dirac a, by rw [dirac_apply a is_measurable.univ]; simp⟩

def map (f : α → β) (p : probability_measure α) : probability_measure β :=
if h : measurable f then
  ⟨measure.map f p, by rw [map_apply h is_measurable.univ, preimage_univ]; exact p.measure_univ⟩
else
  pure (f $ classical.choice p.nonempty)

def join (m : probability_measure (probability_measure α)) : probability_measure α :=
⟨bind m.to_measure probability_measure.to_measure,
  by rw [bind_apply is_measurable.univ (measurable_to_measure α)];
    simp [probability_measure.measure_univ]⟩

def bind (m : probability_measure α) (f : α → probability_measure β) : probability_measure β :=
join (map f m)

attribute [irreducible] pure map join bind

end giry_monad

end probability_measure

end probability_theory

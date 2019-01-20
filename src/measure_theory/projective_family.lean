/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Projective family used to construct the projective limits of (probability) measures.
-/
import measure_theory.measure_space
noncomputable theory
local attribute [instance, priority 0] classical.prop_decidable

open classical set lattice filter function

namespace set

@[simp] theorem preimage_sub {α β} (f : α → β) (s t : set β) :
  f ⁻¹' (s - t) = f ⁻¹' s - f ⁻¹' t := rfl

lemma Union_diff {α ι} {s : set α} {t : ι → set α}: (⋃i:ι, s \ t i) = s \ (⋂i:ι, t i) :=
by ext a; simp [not_forall]

lemma Inter_diff {α ι} [nonempty ι] {s : set α} {t : ι → set α}: (⋂i:ι, s \ t i) = s \ (⋃i:ι, t i) :=
let ⟨i⟩ := ‹nonempty ι› in
begin
  ext a,
  simp ,
  exact iff.intro (assume h, ⟨(h i).1, assume j, (h j).2⟩) (assume h i, ⟨h.1, h.2 i⟩)
end

end set
open set

namespace measure_theory

/- Projective Families and their Limits -/

structure projective_family (ι : Type*) (α : ι → Type*) (β : Type*)
  [preorder ι] [mα : ∀i, measurable_space (α i)] [mβ : measurable_space β] :=
(directed (i j : ι) : ∃k, i ≤ k ∧ j ≤ k)

(map {i j : ι} : i ≤ j → α j → α i)
(map_id (i : ι) : map (refl i) = id)
(map_comp (i j k : ι) (hij : i ≤ j) (hjk : j ≤ k) : map hij ∘ map hjk = map (le_trans hij hjk))
(measurable_map {i j : ι} (hij : i ≤ j) : measurable (map hij))

(proj (i : ι) : β → α i)
(proj_map {i j : ι} (hij : i ≤ j) : map hij ∘ proj j = proj i)
(surjective_proj (i : ι) : surjective (proj i))
(mβ_eq_proj : mβ = (⨆i, (mα i).comap (proj i)))

(μ (i : ι) : measure (α i))
(μ_map {i j : ι} (hij : i ≤ j) : (μ j).map (map hij) = μ i)

namespace projective_family

section limit

parameters {ι : Type*} {α : ι → Type*} {β : Type*}
  [preorder ι] [∀i, measurable_space (α i)] [measurable_space β]
  (pf : projective_family ι α β)

lemma measurable_proj {i : ι} : measurable (pf.proj i) :=
begin
  refine measurable_space.comap_le_iff_le_map.1 (le_trans _ (le_of_eq pf.mβ_eq_proj.symm)),
  exact le_supr_of_le i (le_refl _)
end

lemma μ_map_apply {i j : ι} {s : set (α i)} (h : i ≤ j) (hs : is_measurable s):
  pf.μ j (pf.map h ⁻¹' s) = pf.μ i s :=
by rw [← pf.μ_map h, measure.map_apply (pf.measurable_map _) hs]

def outer_limit.gen (s : set β) : ennreal :=
if nonempty ι then
  ⨅ (i : ι) (t : set (α i)) (ht : is_measurable t) (h : s ⊆ pf.proj i ⁻¹' t), pf.μ i t
else 0

lemma outer_limit.gen_subset
  (s : set β) (i : ι) (t : set (α i)) (ht : is_measurable t) (hs : s ⊆ pf.proj i ⁻¹' t) :
  outer_limit.gen s ≤ pf.μ i t :=
le_trans (le_of_eq $ if_pos ⟨i⟩) $
  infi_le_of_le i $ infi_le_of_le t $ infi_le_of_le ht $ infi_le_of_le hs $ le_refl _

lemma outer_limit.gen_empty : outer_limit.gen ∅ = 0 :=
begin
  by_cases nonempty ι,
  { cases h with i,
    exact (bot_unique $ le_trans
      (outer_limit.gen_subset _ ∅ i ∅ is_measurable.empty (empty_subset _))
      (le_of_eq measure_empty)) },
  { simp [outer_limit.gen, h] }
end

lemma outer_limit.gen_le_gen {s t : set β} (hst : s ⊆ t) : outer_limit.gen s ≤ outer_limit.gen t :=
begin
  by_cases h : nonempty ι,
  { simp [outer_limit.gen, if_pos h],
    exact (assume i u hu hut, infi_le_of_le i $ infi_le_of_le u $ infi_le_of_le hu $
      infi_le_of_le (subset.trans hst hut) $ le_refl _) },
  simp [outer_limit.gen, if_neg h]
end

lemma outer_limit.gen_proj (i : ι) (t : set (α i)) (ht : is_measurable t) :
  outer_limit.gen (pf.proj i ⁻¹' t) = pf.μ i t :=
le_antisymm
  (outer_limit.gen_subset _ _ _ ht $ subset.refl _)
  begin
    haveI hι : nonempty ι := ⟨i⟩,
    simp only [outer_limit.gen, if_pos hι],
    refine (le_infi $ assume j, le_infi $ assume u, le_infi $ assume hu, le_infi $ assume htu, _),
    rcases pf.directed i j with ⟨k, hik, hjk⟩,
    rw [← pf.proj_map hik, preimage_comp, ← pf.proj_map hjk, @preimage_comp _ _ _ (pf.proj k),
      preimage_subset_preimage_iff (pf.surjective_proj _)] at htu,
    rw [← pf.μ_map_apply hik ht, ← pf.μ_map_apply hjk hu],
    exact measure_mono htu
  end

def outer_limit : outer_measure β :=
outer_measure.of_function outer_limit.gen outer_limit.gen_empty

lemma outer_limit_caratheodory_proj (i : ι) (t : set (α i)) (ht : is_measurable t) :
  pf.outer_limit.caratheodory.is_measurable (pf.proj i ⁻¹' t) :=
begin
  refine (outer_measure.caratheodory_is_measurable $ assume s, _),
  have hι : nonempty ι := ⟨i⟩,
  conv { to_rhs, simp only [outer_limit.gen, if_pos hι] },
  refine (le_infi $ assume j, le_infi $ assume u, le_infi $ assume hu, le_infi $ assume hsu, _),
  rcases pf.directed i j with ⟨k, hik, hjk⟩,
  have eq₁ : pf.proj j ⁻¹' u ∩ pf.proj i ⁻¹' t = pf.proj k ⁻¹' (pf.map hjk ⁻¹' u ∩ pf.map hik ⁻¹' t),
    by rw [← pf.proj_map hik, ← pf.proj_map hjk]; refl,
  have eq₂ : pf.proj j ⁻¹' u \ pf.proj i ⁻¹' t = pf.proj k ⁻¹' (pf.map hjk ⁻¹' u \ pf.map hik ⁻¹' t),
    by rw [← pf.proj_map hik, ← pf.proj_map hjk]; refl,
  calc outer_limit.gen pf (s ∩ pf.proj i ⁻¹' t) + outer_limit.gen pf (s \ pf.proj i ⁻¹' t) ≤
    outer_limit.gen pf (pf.proj j ⁻¹' u ∩ pf.proj i ⁻¹' t) +
    outer_limit.gen pf (pf.proj j ⁻¹' u \ pf.proj i ⁻¹' t) :
      add_le_add'
        (outer_limit.gen_le_gen pf $ inter_subset_inter hsu (subset.refl _))
        (outer_limit.gen_le_gen pf $ diff_subset_diff hsu (subset.refl _))
    ... ≤ pf.μ j u :
    begin
      rw [eq₁, eq₂, outer_limit.gen_proj, outer_limit.gen_proj, ← pf.μ_map_apply hjk hu],
      { rw [← measure_union, inter_union_diff],
        exact le_refl _,
        exact assume a ⟨⟨_, ha₁⟩, ⟨_, ha₂⟩⟩, ha₂ ha₁,
        exact is_measurable.inter (pf.measurable_map _ _ hu) (pf.measurable_map _ _ ht),
        exact is_measurable.diff (pf.measurable_map _ _ hu) (pf.measurable_map _ _ ht) },
      { exact is_measurable.diff (pf.measurable_map _ _ hu) (pf.measurable_map _ _ ht) },
      { exact is_measurable.inter (pf.measurable_map _ _ hu) (pf.measurable_map _ _ ht) }
    end
end

def limit : measure β := outer_limit.to_measure $
  le_trans (le_of_eq pf.mβ_eq_proj) $ supr_le $ assume i,
  measurable_space.comap_le_iff_le_map.2 $ assume t (ht : is_measurable t),
    outer_limit_caratheodory_proj i t ht

lemma outer_limit_proj_of_subadditive (i : ι) (t : set (α i)) (ht : is_measurable t)
  (h_sa : ∀(f : ℕ → ι) (s : Πn, set (α (f n))), i ≤ f 0 → monotone f → (∀n, is_measurable (s n)) →
    pf.proj i ⁻¹' t = (⋃ n, pf.proj (f n) ⁻¹' s n) → pf.μ i t ≤ ∑n, pf.μ (f n) (s n)) :
  outer_limit (pf.proj i ⁻¹' t) = pf.μ i t :=
begin
  have hι : nonempty ι := ⟨i⟩,
  refine le_antisymm _ _,
  { rw [← outer_limit.gen_proj pf _ _ ht],
    exact outer_measure.of_function_le _ _ _ },
  refine (le_infi $ λ f, le_infi $ λ hf,
    ennreal.le_of_forall_epsilon_le $ λ ε ε0 h, _),
  rcases ennreal.exists_pos_sum_of_encodable
    (ennreal.zero_lt_coe_iff.2 ε0) ℕ with ⟨ε', ε'0, hε⟩,
  refine le_trans _ (add_le_add_left' (le_of_lt hε)),
  rw ← ennreal.tsum_add,
  choose j' s' his using show ∀ n, ∃ (i : ι) (s : set (α i)),
    is_measurable s ∧ f n ⊆ pf.proj i ⁻¹' s ∧ pf.μ i s < outer_limit.gen pf (f n) + ε' n,
  { assume n,
    have := (ennreal.lt_add_right (lt_of_le_of_lt (ennreal.le_tsum n) h)
        (ennreal.zero_lt_coe_iff.2 (ε'0 n))),
    conv at this { to_lhs, simp only [outer_limit.gen, if_pos hι] },
    simp [infi_lt_iff] at this,
    exact this },
  refine le_trans _ (ennreal.tsum_le_tsum $ λ n, le_of_lt (his n).2.2),

  let i' := classical.some (pf.directed (j' 0) i),
  have j0_i' : j' 0 ≤ i' := (classical.some_spec (pf.directed (j' 0) i)).1,
  have i_i' : i ≤ i' := (classical.some_spec (pf.directed (j' 0) i)).2,

  let j : ℕ → ι := λn, nat.rec_on n i' (λn i, classical.some (pf.directed (j' (n+1)) i)),
  have j_mono : monotone j :=
    monotone_of_monotone_nat (assume n, (classical.some_spec (pf.directed (j' (n+1)) (j n))).2),
  have j_upper : ∀n, j' n ≤ j n,
  { assume n,
    cases n,
    { exact j0_i' },
    { exact (classical.some_spec (pf.directed (j' (n+1)) (j n))).1 } },
  have i_le_j : ∀n, i ≤ j n := assume n, le_trans i_i' (j_mono (nat.zero_le n)),

  let s : Πn, set (α (j n)) := λn, (pf.map (j_upper n) ⁻¹' s' n) ∩ (pf.map (i_le_j n) ⁻¹' t),
  refine le_trans (h_sa j s i_i' j_mono _ _) _,
  { exact assume n, is_measurable.inter
      (pf.measurable_map (j_upper n) _ ((his n).1))
      (pf.measurable_map (i_le_j n) _ ht) },
  { have : ∀n, pf.proj (j n) ⁻¹' s n = pf.proj (j' n) ⁻¹' s' n ∩ pf.proj i ⁻¹' t,
    { simp [s, preimage_inter, pf.proj_map, preimage_comp.symm] },
    simp [this, (inter_Union_right _ _).symm],
    refine (inter_eq_self_of_subset_right _).symm,
    refine subset.trans hf (Union_subset_Union $ assume n, subset.trans (his n).2.1 _),
    rw [← pf.proj_map (j_upper n), preimage_comp] },
  refine ennreal.tsum_le_tsum (assume n, _),
  rw [← pf.μ_map_apply (j_upper n) (his n).1],
  exact measure_mono (inter_subset_left _ _)
end

lemma outer_limit_proj_of_supr (i : ι) (t : set (α i)) (ht : is_measurable t)
  (h_sa : ∀(f : ℕ → ι) (s : Πn, set (α (f n))), i ≤ f 0 → monotone f → (∀n, is_measurable (s n)) →
    monotone (λn, pf.proj (f n) ⁻¹' s n) →
    pf.proj i ⁻¹' t = (⋃ n, pf.proj (f n) ⁻¹' s n) → pf.μ i t ≤ ⨆n, pf.μ (f n) (s n)) :
  outer_limit (pf.proj i ⁻¹' t) = pf.μ i t :=
outer_limit_proj_of_subadditive i t ht
begin
  assume f s hf0 hf hs hts,
  let s' : Πn, set (α (f n)) := λn, ⋃l (h : l ≤ n), pf.map (hf h) ⁻¹' s l,
  have proj_s' : ∀n, pf.proj (f n) ⁻¹' s' n = (⋃l (h : l ≤ n), pf.proj (f l) ⁻¹' s l),
  { simp [s', preimage_Union, preimage_comp.symm, pf.proj_map], },
  refine le_trans (h_sa f s' hf0 hf _ _ _) _,
  { assume n, exact is_measurable.Union (assume n, is_measurable.Union_Prop $ assume h,
      pf.measurable_map (hf h) _ $ hs n) },
  { assume n m hnm,
    simp [s', (pf.proj_map (hf hnm)).symm, preimage_comp.symm],
    assume l hl,
    refine subset.trans _ (subset_Union _ l),
    refine subset.trans _ (subset_Union _ (le_trans hl hnm)),
    simp [pf.proj_map] },
  { simp only [hts, proj_s'],
    refine subset.antisymm
      (Union_subset_Union $ assume l, _)
      (Union_subset $ assume n, Union_subset $ assume l, Union_subset $ assume h, subset_Union _ l),
    refine subset.trans _ (subset_Union _ l),
    exact subset_Union (λh, pf.proj (f l) ⁻¹' s l) (le_refl l) },
  rw [ennreal.tsum_eq_supr_nat],
  refine supr_le (assume n, le_supr_of_le (n + 1) _),
  dsimp only [s'],
  refine le_trans (measure_Union_le _) (le_of_eq _),
  refine eq.trans (tsum_eq_sum _) _,
  { exact finset.range (n + 1) },
  { assume l hl,
    have : n + 1 ≤ l, { simpa using hl },
    have : ¬ l ≤ n := not_le_of_gt this,
    simp [this] },
  { refine finset.sum_congr rfl _,
    assume l hl,
    have : l ≤ n, { simpa [nat.lt_succ_iff] using hl },
    simp [this, (pf.μ_map_apply (hf this) (hs l)).symm] }
end

lemma outer_limit_proj_of_infi (i : ι) (t : set (α i)) (ht : is_measurable t) (htf : pf.μ i t < ⊤)
  (h_sa : ∀(f : ℕ → ι) (s : Πn, set (α (f n))), monotone f → (∀n, is_measurable (s n)) →
    (∀n m, n ≤ m → pf.proj (f m) ⁻¹' s m ≤ pf.proj (f n) ⁻¹' s n) →
    (⋂ n, pf.proj (f n) ⁻¹' s n) = ∅ → (⨅n, pf.μ (f n) (s n)) = 0) :
  outer_limit (pf.proj i ⁻¹' t) = pf.μ i t :=
outer_limit_proj_of_supr i t ht $ assume f s hf0 hf hs hsm hst,
  have hif : ∀n, i ≤ f n := λn, le_trans hf0 $ hf $ nat.zero_le n,
  let s' : Πn, set (α (f n)) := λn, pf.map (hif n) ⁻¹' t \ s n in
  have ht' : ∀n, is_measurable (pf.map (hif n) ⁻¹' t) := assume n, pf.measurable_map (hif n) _ ht,
  have hs' : ∀n, is_measurable (s' n) := assume n, is_measurable.diff (ht' n) (hs n),
  have (⨅i, pf.μ (f i) (s' i)) = 0,
  { refine h_sa f s' hf hs' _ _,
    { assume n m h,
      simp only [s', preimage_diff, preimage_comp.symm, pf.proj_map],
      refine diff_subset_diff (subset.refl _) (hsm h) },
    { simp only [s', preimage_diff, preimage_comp.symm, pf.proj_map, Inter_diff, hst, diff_self] } },
  calc pf.μ i t = (⨆n, pf.μ i t - pf.μ (f n) (s' n)) :
      by rw [← ennreal.sub_infi, this, ennreal.sub_zero]
    ... ≤ ⨆n, pf.μ (f n) (s n) : supr_le_supr $ assume n,
    begin
      have : s' n ⊆ pf.map _ ⁻¹' t := diff_subset_iff.2 (subset_union_right _ _),
      rw [← pf.μ_map_apply (hif n) ht, ← measure_diff this (ht' n) (hs' n)],
      exact measure_mono (assume x ⟨hxt, hxs⟩, classical.by_contradiction $ assume h, hxs ⟨hxt, h⟩),
      calc pf.μ (f n) (s' n) ≤ pf.μ (f n) (pf.map _ ⁻¹' t) : measure_mono this
        ... = pf.μ i t : pf.μ_map_apply _ ht
        ... < ⊤ : htf
    end

lemma limit_proj_of_infi (i : ι) (t : set (α i)) (ht : is_measurable t) (htf : pf.μ i t < ⊤)
  (h_sa : ∀(f : ℕ → ι) (s : Πn, set (α (f n))), monotone f → (∀n, is_measurable (s n)) →
    (∀n m, n ≤ m → pf.proj (f m) ⁻¹' s m ≤ pf.proj (f n) ⁻¹' s n) →
    (⋂ n, pf.proj (f n) ⁻¹' s n) = ∅ → (⨅n, pf.μ (f n) (s n)) = 0) :
  limit (pf.proj i ⁻¹' t) = pf.μ i t :=
eq.trans
  (to_measure_apply _ _ $ measurable_proj _ ht)
  (outer_limit_proj_of_infi i t ht htf h_sa)

end limit

end projective_family

end measure_theory

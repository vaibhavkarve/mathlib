/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Projective family used to construct the projective limits of (probability) measures.
-/
import measure_theory.projective_family measure_theory.giry_monad
noncomputable theory
local attribute [instance, priority 0] classical.prop_decidable

open classical set lattice filter function

namespace measure_theory

section
variables (α : Type*) [measurable_space α]

structure probability_measure extends measure α :=
(measure_univ : to_measure univ = 1)

instance : measurable_space (probability_measure α) :=
measure.measurable_space.comap probability_measure.to_measure

instance : has_coe (probability_measure α) (measure α) := ⟨probability_measure.to_measure⟩

end

namespace probability_measure
open measure

variables {α : Type*} {β : Type*} {γ : Type*}
  [measurable_space α] [measurable_space β] [measurable_space γ]

@[simp] lemma apply_univ_eq_1 (p : probability_measure α) : p univ = 1 :=
p.measure_univ

protected lemma nonempty (p : probability_measure α) : nonempty α :=
classical.by_contradiction $ assume h,
  have 0 = p univ, by rw [univ_eq_empty_iff.2 h]; exact measure_empty.symm,
  @zero_ne_one ennreal _ $ by rwa [p.apply_univ_eq_1] at this

def pure (a : α) : probability_measure α :=
⟨measure.dirac a, by rw [dirac_apply a is_measurable.univ]; simp⟩

def map (f : α → β) (p : probability_measure α) : probability_measure β :=
if h : measurable f then
  ⟨measure.map f p, by rw [map_apply h is_measurable.univ, preimage_univ]; exact p.measure_univ⟩
else
  pure (f $ classical.choice p.nonempty)

def join (m : probability_measure (probability_measure α)) : probability_measure α :=
⟨bind m.to_measure probability_measure.to_measure, sorry⟩

def bind (m : probability_measure α) (f : α → probability_measure β) : probability_measure β :=
join (map f m)

end probability_measure

instance pi.measurable_space (ι : Type*) (α : ι → Type*) [m : ∀i, measurable_space (α i)] :
  measurable_space (Πi, α i) :=
⨆i, (m i).comap (λf, f i)

instance pi.measurable_space_Prop (ι : Prop) (α : ι → Type*) [m : ∀i, measurable_space (α i)] :
  measurable_space (Πi, α i) :=
⨆i, (m i).comap (λf, f i)

lemma measurable_pi {ι : Type*} {α : ι → Type*} {β : Type*}
  [m : ∀i, measurable_space (α i)] [measurable_space β] {f : β → Πi, α i} :
  measurable f ↔ (∀i, measurable (λb, f b i)):=
begin
  rw [measurable, pi.measurable_space, supr_le_iff],
  refine forall_congr (assume i, _),
  rw [measurable_space.comap_le_iff_le_map, measurable_space.map_comp],
  refl
end

lemma measurable_apply {ι : Type*} {α : ι → Type*} {β : Type*}
  [m : ∀i, measurable_space (α i)] [measurable_space β] (f : β → Πi, α i) (i : ι)
  (hf : measurable f) :
  measurable (λb, f b i) :=
measurable_pi.1 hf _

lemma measurable_pi_Prop {ι : Prop} {α : ι → Type*} {β : Type*}
  [m : ∀i, measurable_space (α i)] [measurable_space β] {f : β → Πi, α i} :
  measurable f ↔ (∀i, measurable (λb, f b i)):=
begin
  rw [measurable, pi.measurable_space_Prop, supr_le_iff],
  refine forall_congr (assume i, _),
  rw [measurable_space.comap_le_iff_le_map, measurable_space.map_comp],
  refl
end

lemma measurable_apply_Prop {p : Prop} {α : p → Type*} {β : Type*}
  [m : ∀i, measurable_space (α i)] [measurable_space β] (f : β → Πi, α i) (h : p)
  (hf : measurable f) :
  measurable (λb, f b h) :=
measurable_pi_Prop.1 hf _

def markov_kernel (α : Type*) [measurable_space α] : Type* :=
{ k : α → probability_measure α // measurable k }

namespace markov_kernel
open probability_measure

section pf
parameters (α : Type*) [measurable_space α] [inhabited α] (k : markov_kernel α)

def iter : Π(n : ℕ), α → probability_measure (Πi, i < n → α)
| 0       a := pure $ λi h, (nat.not_lt_zero i h).elim
| (n + 1) a :=
  bind (k.1 a) $ λa, map (λf i h, _) (iter n a)

def pf : projective_family ℕ (λn, Πi<n, α) (ℕ → α) :=
{ directed := assume i j, ⟨max i j, le_max_left _ _, le_max_right _ _⟩,

  proj     := λn s l h, s l,
  proj_map := assume i j hij, funext $ assume s, funext $ assume n, rfl,
  surjective_proj := assume n f,
    ⟨λi, if h : i < n then f i h else default α,
      funext $ assume i, by ext hi; by_cases h : i < n; simp *; exact (h hi).elim ⟩,

  mβ_eq_proj :=
    begin
      simp only [pi.measurable_space, pi.measurable_space_Prop, measurable_space.comap_supr,
        measurable_space.comap_comp, (∘)],
      exact le_antisymm
        (supr_le $ assume i,
          le_supr_of_le (i + 1) $ le_supr_of_le i $ le_supr_of_le (nat.lt_succ_self i) $ le_refl _)
        (supr_le $ assume i, supr_le $ assume j, supr_le $ assume h,
          le_supr_of_le j $ le_refl _),
    end,

  map      := λi j hij f l hli, f l (lt_of_lt_of_le hli hij),
  map_id   := assume i, funext $ assume f, funext $ assume n, funext $ assume h, rfl,
  map_comp := assume i j k hij hjk, funext $ assume f, funext $ assume n, funext $ assume h, rfl,
  measurable_map := assume i j hij, measurable_pi.2 $ assume n, measurable_pi_Prop.2 $ assume h,
    measurable_apply_Prop (λb:Πi, i < j → α, b n) (lt_of_lt_of_le h hij) $
    measurable_apply _ _ measurable_id,

  μ     := _,
  μ_map := _ }


end pf

end markov_kernel

end measure_theory
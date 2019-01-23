/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Constructing Markov Processes out of Markov Kernels
-/
import probability_theory.basic measure_theory.projective_family
noncomputable theory
local attribute [instance, priority 0] classical.prop_decidable

open set lattice filter function

theorem nat.of_le_succ {n m : ℕ} (H : n ≤ m.succ) : n ≤ m ∨ n = m.succ :=
(lt_or_eq_of_le H).imp nat.le_of_lt_succ id

namespace probability_theory
open measure_theory

def seq_markov_kernel (α : ℕ → Type*) [∀n, measurable_space (α n)] : Type* :=
{ k : Πn, α n → probability_measure (α (n + 1)) // ∀n, measurable (k n) }

namespace seq_markov_kernel
open probability_measure

section pf
variables {α : ℕ → Type*} [∀n, measurable_space (α n)]

def snoc (n : ℕ) (f : Πi, i ≤ n → α i) (a : α (n + 1)) (j : ℕ) (hj : j ≤ n + 1) : α j :=
or.by_cases (nat.of_le_succ hj) (f j) (assume h, h.symm.rec_on a)

def red {n m : ℕ} (h : n ≤ m) (f : Πi, i ≤ m → α i) (j : ℕ) (hj : j ≤ n) : α j :=
f j (le_trans hj h)

def iter (k : seq_markov_kernel α) (n : ℕ) (a₀ : α 0) : probability_measure (Πi, i ≤ n → α i) :=
nat.rec_on n
  (pure $ λi hi, (nat.eq_zero_of_le_zero hi).symm.rec_on a₀)
  (λn it, it.bind $ λf, (k.1 n (f n (le_refl n))).map (snoc n f))

def pf (k : seq_markov_kernel α) (a₀ : α 0) : projective_family ℕ (λn, Πi≤n, α i) (Πn, α n) :=
{ directed := assume i j, ⟨max i j, le_max_left _ _, le_max_right _ _⟩,

  proj     := λn s l h, s l,
  proj_map := assume i j hij, funext $ assume s, funext $ assume n, rfl,
  surjective_proj := assume n f,
    ⟨λi, if h : i ≤ n then f i h else _,
      funext $ assume i, by ext hi; by_cases h : i ≤ n; simp *; exact (h hi).elim ⟩,

  mβ_eq_proj :=
    begin
      simp only [pi.measurable_space, pi.measurable_space_Prop, measurable_space.comap_supr,
        measurable_space.comap_comp, (∘)],
      exact le_antisymm
        (supr_le $ assume i,
          le_supr_of_le (i + 1) $ le_supr_of_le i $ le_supr_of_le (nat.le_succ _) $ le_refl _)
        (supr_le $ assume i, supr_le $ assume j, supr_le $ assume h,
          le_supr_of_le j $ le_refl _),
    end,

  map      := assume i j, red,
  map_id   := assume i, funext $ assume f, funext $ assume n, funext $ assume h, rfl,
  map_comp := assume i j k hij hjk, funext $ assume f, funext $ assume n, funext $ assume h, rfl,
  measurable_map := assume i j hij, measurable_pi.2 $ assume n, measurable_pi_Prop.2 $ assume h,
    measurable_apply_Prop (λb:Πi, i ≤ j → α i, b n) (le_trans h hij) $
    measurable_apply _ _ measurable_id,

  μ     := λn, iter k n a₀,
  μ_map := assume i j hij, _ }


end pf

end seq_markov_kernel

end probability_theory

/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import topology.algebra.group
import measure_theory.borel_space
import measure_theory.measure_space
import tactic

/-!
# Haar measure

In this file we define the Haar measure:
A left-translation invariant measure on a locally compact topological group.

## References
Alfsen, E. M. A simplified constructive proof of the existence and uniqueness of Haar measure.
  Math. Scand. 12 (1963), 106--116. MR0158022

-/

variables {G : Type*}
variables [group G] [topological_space G] [topological_group G] [locally_compact_space G]

namespace measure_theory

lemma is_measurable_mul_left (g : G) :
  measurable ((*) g : G → G) :=
measureable_of_continuous _

def left_translate (μ : measure G) (g : G) : measure G :=
{ measure_of := λ s, μ ((*) g '' s),
  empty := by { suffices : (*) g '' ∅ = ∅, { rw [this, measure_empty] }, ext, simp, },
  mono := λ s₁ s₂ h, measure_mono $ by { rintro _ ⟨x, hx, rfl⟩, exact ⟨_, h hx, rfl⟩ },
  Union_nat := λ f,
  begin
    sorry
    -- suggest,
  end,
  m_Union := λ f, _,
  trimmed := _ }


end measure_theory

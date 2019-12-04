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

noncomputable theory

open_locale classical topological_space

variables {G : Type*}
variables [group G] [topological_space G]

namespace measure_theory
namespace measure

/-- A measure `μ` on a topological group is left invariant if
for all measurable sets `s` and all `g`, we have `μ (gs) = μ s`,
where `gs` denotes the translate of `s` by left multiplication with `g`. -/
@[to_additive is_left_add_invariant]
def is_left_invariant (μ : measure G) : Prop :=
∀ s : set G, is_measurable s → ∀ g : G,  μ ((*) g '' s) = μ s

end measure

namespace haar_measure_construction
open lattice
variables [topological_group G] [locally_compact_space G]

/-- `index_prop S T` is a predicate
asserting that `T` is covered by finitely many left-translates of `S`. -/
lemma index_prop (S T : set G) (hS : S ∈ 𝓝 (1:G)) (hT : compact T) :
  ∃ n, ∃ f : fin n → G, T ⊆ supr (λ i : fin n, (*) (f i) '' S) :=
begin
  choose U hU using mem_nhds_sets_iff.1 hS,
  let ι : G → set G := λ g, (*) g '' U,
  have hι : ∀ g : G, g ∈ (set.univ : set G) → is_open (ι g),
  { intros g hg,
    show is_open ((*) g '' U),
    rw show ((*) g '' U) = (*) g⁻¹ ⁻¹' U,
    { ext, exact mem_left_coset_iff g },
    apply continuous_mul_left g⁻¹,
    exact hU.2.1 },
  have := compact_elim_finite_subcover_image hT hι _,
  all_goals {sorry}
end

def index (S T : set G) (hS : S ∈ 𝓝 (1:G)) (hT : compact T) : ℕ :=
nat.find (index_prop S T hS hT)

-- local notation `[`T`:`S`]` := index S T

variables (A : set G) (hA : compact A)
def prehaar_of_compact (K : set G) (hK : compact K) : _ := _

end haar_measure_construction

end measure_theory

#lint

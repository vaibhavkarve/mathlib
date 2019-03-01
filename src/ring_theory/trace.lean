/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import ring_theory.matrix

universes u v
open finset function

namespace matrix

variables {n : Type u} [fintype n] [decidable_eq n] {R : Type v} [comm_ring R]

def tr  (M : matrix n n R) : R := univ.sum (λ i, M i i)

@[simp] lemma tr_diagonal {d : n → R} : tr (diagonal d) = univ.sum d :=
by simp [tr]

@[simp] lemma tr_zero : tr (0 : matrix n n R) = 0 :=
by rw [← diagonal_zero, tr_diagonal]; simp

@[simp] lemma tr_one : tr (1 : matrix n n R) = fintype.card n :=
by rw [← diagonal_one, tr_diagonal]; simp [fintype.card]

@[simp] lemma tr_add (M₁ M₂ : matrix n n R) : tr (M₁ + M₂) = tr M₁ + tr M₂ :=
sum_add_distrib

instance : is_add_group_hom (tr : matrix n n R → R) := ⟨tr_add⟩

end matrix

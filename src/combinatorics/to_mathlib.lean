/-
A collection of useful lemmas that might be useful in mathlib, approximately sorted by where they belong
-/

import data.finset
import algebra.big_operators
import tactic

open finset

section finset
  variables {α : Type*} [decidable_eq α]
  /--
  Given a set A and a set B inside it, we can shrink A to any appropriate size, and keep B
  inside it.
  -/
  lemma exists_intermediate_set {A B : finset α} (i : ℕ)
    (h₁ : card A ≥ i + card B) (h₂ : B ⊆ A) :
    ∃ (C : finset α), B ⊆ C ∧ C ⊆ A ∧ card C = i + card B :=
  begin
    rcases nat.le.dest h₁ with ⟨k, _⟩, clear h₁, revert A,
    induction k with k ih,
      intros A BsubA cards, exact ⟨A, BsubA, subset.refl _, cards.symm⟩,
    intros A BsubA cards,
    have: (A \ B).nonempty,
      rw [← card_pos, card_sdiff BsubA,
          ← cards, nat.add_right_comm, nat.add_sub_cancel, nat.add_succ],
      apply nat.succ_pos,
    rcases this with ⟨a, ha⟩,
    set A' := erase A a,
    have z: i + card B + k = card A',
      rw [card_erase_of_mem, ← cards, nat.add_succ, nat.pred_succ],
      rw mem_sdiff at ha, exact ha.1,
    rcases ih _ z with ⟨B', hB', B'subA', cards⟩,
    refine ⟨B', hB', trans B'subA' (erase_subset _ _), cards⟩,
    rintros t th, apply mem_erase_of_ne_of_mem _ (BsubA th), rintro rfl,
    rw mem_sdiff at ha, tauto
  end

  /-- We can shrink A to any smaller size. -/
  lemma exists_smaller_set (A : finset α) (i : ℕ) (h₁ : card A ≥ i) :
    ∃ (B : finset α), B ⊆ A ∧ card B = i :=
  begin
    rcases exists_intermediate_set i _ (empty_subset A) with ⟨B, _, x₁, x₂⟩,
    simp at x₂, exact ⟨B, x₁, x₂⟩, simpa,
  end
end finset

-- section big_operators
--   lemma sum_flip {α : Type*} [add_comm_monoid α] {n : ℕ} (f : ℕ → α) :
--     sum (range (n+1)) (λ r, f (n - r)) = sum (range (n+1)) f :=
--   begin
--     induction n with n ih,
--       rw [sum_range_one, sum_range_one],
--     rw sum_range_succ', rw sum_range_succ _ (nat.succ n),
--     rw [add_comm], simp [← ih]
--   end
-- end big_operators

section nat
  lemma choose_symm' {n a b : ℕ} (h : n = a + b) : nat.choose n a = nat.choose n b :=
  begin
    have: a = n - b, rw h, rw nat.add_sub_cancel,
    rw [this, nat.choose_symm], apply nat.le.intro, symmetry, rwa add_comm
  end
end nat

section natchoose
  lemma dominate_choose_lt {r n : ℕ} (h : r < n/2) :
    nat.choose n r ≤ nat.choose n (r+1) :=
  begin
    refine le_of_mul_le_mul_right _ (nat.lt_sub_left_of_add_lt (lt_of_lt_of_le h (nat.div_le_self n 2))),
    rw ← nat.choose_succ_right_eq,
    apply nat.mul_le_mul_left,
    rw [← nat.lt_iff_add_one_le, nat.lt_sub_left_iff_add_lt, ← mul_two],
    exact lt_of_lt_of_le (mul_lt_mul_of_pos_right h zero_lt_two) (nat.div_mul_le_self n 2),
  end

  lemma dominate_choose_lt' {n r : ℕ} (hr : r ≤ n/2) : nat.choose n r ≤ nat.choose n (n/2) :=
  begin
    refine @nat.decreasing_induction (λ k, k ≤ n/2 → nat.choose n k ≤ nat.choose n (n/2)) (λ m k a, _) r (n/2) hr (λ _, by refl) hr,
    rcases eq_or_lt_of_le a with rfl | h, refl,
    exact trans (dominate_choose_lt h) (k h)
  end

  lemma dominate_choose {r n : ℕ} : nat.choose n r ≤ nat.choose n (n/2) :=
  begin
    cases le_or_gt r n with b b,
      cases le_or_lt r (n/2) with a h,
        apply dominate_choose_lt' a,
      rw ← nat.choose_symm b,
      apply dominate_choose_lt',
      rw [nat.div_lt_iff_lt_mul' zero_lt_two] at h,
      rw [nat.le_div_iff_mul_le' zero_lt_two, nat.mul_sub_right_distrib, nat.sub_le_iff, mul_two, nat.add_sub_cancel],
      exact le_of_lt h,
    rw nat.choose_eq_zero_of_lt b,
    apply zero_le
  end
end natchoose

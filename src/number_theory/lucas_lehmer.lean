import data.nat.prime
import data.zmod.basic
import data.num.lemmas
import data.nat.modeq

open nat

def M (p : ℕ) : ℕ := 2^p  - 1
def s (p : ℕ) : ℕ → ℕ
| 0 := 4
| (i+1) := ((s i)^2 - 2) % (M p)


def Lucas_Lehmer_residue (p : ℕ) := s p (p-2)

def Lucas_Lehmer_test (p : ℕ) := Lucas_Lehmer_residue p = 0
instance : decidable_pred Lucas_Lehmer_test := λ p, by { dsimp [Lucas_Lehmer_test], apply_instance }

theorem Lucas_Lehmer_sufficiency (p : ℕ) (pp : prime p) (h : p > 2) (w : Lucas_Lehmer_test p) : prime (M p) :=
begin
  -- TODO follow the proof at https://en.wikipedia.org/wiki/Lucas%E2%80%93Lehmer_primality_test#Sufficiency
  sorry
end
theorem Lucas_Lehmer_necessity (p : ℕ) (pp : prime p) (h : p > 2) (h : prime (M p)) : Lucas_Lehmer_test p := sorry

theorem Lucas_Lehmer (p : ℕ) (pp : prime p) (h : p > 2) : Lucas_Lehmer_test p ↔ prime (M p) :=
⟨Lucas_Lehmer_sufficiency p pp h, Lucas_Lehmer_necessity p pp h⟩

example : prime (M 5) := Lucas_Lehmer_sufficiency _ (by norm_num) (by norm_num) dec_trivial
-- Unfortunately this won't work, because the `dec_trivial` times out. We're going to need to
-- provide certificates for the arithmetic.
-- example : prime (M 7) := Lucas_Lehmer_sufficiency _ (by norm_num) (by norm_num) dec_trivial

section
open tactic

-- TODO this is in mathlib, but not found?
meta instance nat_pexpr : has_to_pexpr ℕ := ⟨pexpr.of_expr ∘ λ n, reflect n⟩

lemma s_succ {p a i b c}
  (h1 : 2^p - 1 = a)
  (h2 : s p i = b)
  (h3 : (b * b - 2) % a = c) :
  s p (i+1) = c :=
by { dsimp [s, M], rw [h1, h2, nat.pow_two, h3] }

meta def run_Lucas_Lehmer_test : tactic unit :=
do `(Lucas_Lehmer_test %%p) ← target,
   `[dsimp [Lucas_Lehmer_test, Lucas_Lehmer_residue]],
   p ← eval_expr ℕ p,
   -- Calculate the candidate Mersenne prime
   M ← to_expr ``(2^%%p - 1) >>= eval_expr ℕ,
   t ← to_expr ``(2^%%p - 1 = %%M),
   v ← to_expr ``(by norm_num : 2^%%p - 1 = %%M),
   w ← assertv `w t v,
   -- base case
   t ← to_expr ``(s %%p 0 = 4),
   v ← to_expr ``(rfl),
   h ← assertv `h t v,
   -- step case, repeated p-2 times
   iterate_exactly (p-2) `[replace h := s_succ w h (by { norm_num, refl })],
   -- now close the goal
   h ← get_local `h,
   exact h

end

example : prime (M 7) := Lucas_Lehmer_sufficiency _ (by norm_num) (by norm_num) (by run_Lucas_Lehmer_test).
example : prime (M 13) := Lucas_Lehmer_sufficiency _ (by norm_num) (by norm_num) (by run_Lucas_Lehmer_test).
-- example : prime (M 127) := Lucas_Lehmer_sufficiency _ (by norm_num) (by norm_num) (by run_Lucas_Lehmer_test).

-- #eval 2^127 - 1
-- #eval s 127 50
-- #eval let a := 2^127 - 1 in let b := s 127 50 in (b * b - 2) % a

-- set_option profiler true
-- example : (99592518053374632198667753856515678006 * 99592518053374632198667753856515678006 - 2) % (2^127 - 1) = 71264320053401377760498554706288870501 :=
-- by norm_num

def two_to_the_n_minus_1 (n : ℕ) : num := num.pos (iterate pos_num.bit1 (n-1) pos_num.one)

def fast_mod_1 (n : ℕ) (N : num) : num :=
 N.land (two_to_the_n_minus_1 n) + N.shiftr n

lemma fast_mod_1_lt (n : ℕ) (N : num) (h : N.shiftr n ≠ 0) : fast_mod_1 n N < N := sorry

def fast_mod (n : ℕ) : num → num
| N := let r := fast_mod_1 n N in
       if h : N.shiftr n = 0 then
         if r = two_to_the_n_minus_1 n then 0 else r
       else have r < N := fast_mod_1_lt n N h, fast_mod r

lemma fast_mod_eq_mod (n : ℕ) (N : num) : fast_mod n N = N % n := sorry

#eval fast_mod 5 32

lemma bar (a b : ℕ) : a = (a / b) * b + (a % b) :=
begin
  symmetry,
  rw [add_comm, mul_comm],
  convert nat.mod_add_div _ _,
end


lemma foo (n k : ℕ) : k ≡ ((k / 2^n) + (k % 2^n)) [MOD 2^n - 1] :=
-- See https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/help.20finding.20a.20lemma/near/177698446
begin
  conv {to_rhs, rw [← nat.mod_add_div k (2^n), add_comm]},
  refine nat.modeq.modeq_add _ (by refl),
  conv {to_rhs, skip, rw ← one_mul (k/2^n)},
  refine nat.modeq.modeq_mul _ (by refl),
  symmetry,
  rw [nat.modeq.modeq_iff_dvd, int.coe_nat_sub],
  exact nat.pow_pos dec_trivial _
end


lemma foo' (n k : ℕ) : (k : zmod (2^n -1)) = ((k / 2^n + k % 2^n : ℕ) : zmod (2^n - 1)) :=
begin
  conv {to_lhs, rw [← nat.mod_add_div k (2^n), add_comm]},
  -- I want `push_cast`!
end

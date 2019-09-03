import data.nat.prime
import data.zmod.basic

open nat

def M (p : ℕ) : ℕ := 2^p  - 1
def s (p : ℕ) : ℕ → ℕ
| 0 := 4
| (i+1) := ((s i)^2 - 2) % (2^p - 1)


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
by rw [s, h1, h2, nat.pow_two, h3]

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

import group_theory.order_of_element
import tactic

open nat

-- TODO prove and put in mathlib
lemma prime_pow_dvd_prime_pow {p k l : ℕ} (pp : prime p) : p^k ∣ p^l ↔ k ≤ l :=
sorry

-- TODO put in mathlib (presumably without linarith)
lemma dvd_prime_power (a p k : ℕ) (pp : prime p) (h₁ : ¬(a ∣ p^k)) (h₂ : a ∣ p^(k+1)) : a = p^(k+1) :=
begin
  rcases (dvd_prime_pow pp).1 h₂ with ⟨l,⟨h,rfl⟩⟩,
  congr,
  have : k < l := not_le.1 ((not_congr (prime_pow_dvd_prime_pow pp)).1 h₁),
  linarith,
end

-- TODO add @[simp] to pow_order_of_eq_one in mathlib

variables {G : Type} [group G] [fintype G] [decidable_eq G]

-- TODO put in mathlib
lemma order_of_dvd_iff {n : ℕ} {g : G} : order_of g ∣ n ↔ g^n = 1 :=
⟨λ h, by { rcases h with ⟨k,rfl⟩, simp only [pow_mul, _root_.one_pow, pow_order_of_eq_one] },
   order_of_dvd_of_pow_eq_one⟩

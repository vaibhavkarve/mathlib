/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Scott Morrison
-/
import data.finsupp

/-!
# Monoid algebras

When the domain of a `finsupp` has a multiplicative or additive structure, we can define
a convolution product. To mathematicians this structure is known as the "monoid algebra",
i.e. the finite formal linear combinations over a given semiring of elements of the monoid.
The "group ring" ℤ[G] or the "group algebra" k[G] are typical uses.

In this file we define `monoid_algebra k G := G →₀ k`, and `add_monoid_algebra k G`
in the same way, and then define the convolution product on these.

When the domain is additive, this is used to define polynomials:
```
polynomial α := add_monoid_algebra ℕ α
mv_polynominal σ α := add_monoid_algebra (σ →₀ ℕ) α
```

When the domain is multiplicative, e.g. a group, this will be used to define the group ring.

## Implementation note
Unfortunately because additive and multiplicative structures both appear in both cases,
it doesn't appear to be possible to make much use of `to_additive`, and we just settle for
saying everything twice.

Similarly, I attempted to just define `add_monoid_algebra k G := monoid_algebra k (multiplicative G)`,
but the definitional equality `multiplicative G = G` leaks through everywhere, and
seems impossible to use.
-/

noncomputable theory
open_locale classical

open finset finsupp

universes u₁ u₂
variables (k : Type u₁) (G : Type u₂)

section
variables [semiring k]

/--
The monoid algebra over a semiring `k` generated by the monoid `G`.
It is the type of finite formal `k`-linear combinations of terms of `G`,
endowed with the convolution product.
-/
@[derive [inhabited, add_comm_monoid]]
def monoid_algebra : Type (max u₁ u₂) := G →₀ k

end

namespace monoid_algebra

variables {k G}
local attribute [reducible] monoid_algebra

section
variables [semiring k] [monoid G]

/-- The product of `f g : monoid_algebra k G` is the finitely supported function
  whose value at `a` is the sum of `f x * g y` over all pairs `x, y`
  such that `x * y = a`. (Think of the group ring of a group.) -/
instance : has_mul (monoid_algebra k G) :=
⟨λf g, f.sum $ λa₁ b₁, g.sum $ λa₂ b₂, single (a₁ * a₂) (b₁ * b₂)⟩

lemma mul_def {f g : monoid_algebra k G} :
  f * g = (f.sum $ λa₁ b₁, g.sum $ λa₂ b₂, single (a₁ * a₂) (b₁ * b₂)) :=
rfl

lemma support_mul (a b : monoid_algebra k G) :
  (a * b).support ⊆ a.support.bind (λa₁, b.support.bind $ λa₂, {a₁ * a₂}) :=
subset.trans support_sum $ bind_mono $ assume a₁ _,
  subset.trans support_sum $ bind_mono $ assume a₂ _, support_single_subset

/-- The unit of the multiplication is `single 1 1`, i.e. the function
  that is `1` at `1` and zero elsewhere. -/
instance : has_one (monoid_algebra k G) :=
⟨single 1 1⟩

lemma one_def : (1 : monoid_algebra k G) = single 1 1 :=
rfl

-- TODO: the simplifier unfolds 0 in the instance proof!
private lemma zero_mul (f : monoid_algebra k G) : 0 * f = 0 :=
by simp only [mul_def, sum_zero_index]

private lemma mul_zero (f : monoid_algebra k G) : f * 0 = 0 :=
by simp only [mul_def, sum_zero_index, sum_zero]

private lemma left_distrib (a b c : monoid_algebra k G) : a * (b + c) = a * b + a * c :=
by simp only [mul_def, sum_add_index, mul_add, _root_.mul_zero, single_zero, single_add,
  eq_self_iff_true, forall_true_iff, forall_3_true_iff, sum_add]

private lemma right_distrib (a b c : monoid_algebra k G) : (a + b) * c = a * c + b * c :=
by simp only [mul_def, sum_add_index, add_mul, _root_.mul_zero, _root_.zero_mul, single_zero,
  single_add, eq_self_iff_true, forall_true_iff, forall_3_true_iff, sum_zero, sum_add]

instance : semiring (monoid_algebra k G) :=
{ one       := 1,
  mul       := (*),
  one_mul   := assume f, by simp only [mul_def, one_def, sum_single_index, _root_.zero_mul,
    single_zero, sum_zero, zero_add, one_mul, sum_single],
  mul_one   := assume f, by simp only [mul_def, one_def, sum_single_index, _root_.mul_zero,
    single_zero, sum_zero, add_zero, mul_one, sum_single],
  zero_mul  := zero_mul,
  mul_zero  := mul_zero,
  mul_assoc := assume f g h, by simp only [mul_def, sum_sum_index, sum_zero_index, sum_add_index,
    sum_single_index, single_zero, single_add, eq_self_iff_true, forall_true_iff, forall_3_true_iff,
    add_mul, mul_add, add_assoc, mul_assoc, _root_.zero_mul, _root_.mul_zero, sum_zero, sum_add],
  left_distrib  := left_distrib,
  right_distrib := right_distrib,
  .. finsupp.add_comm_monoid }

end

instance [comm_semiring k] [comm_monoid G] : comm_semiring (monoid_algebra k G) :=
{ mul_comm := assume f g,
  begin
    simp only [mul_def, finsupp.sum, mul_comm],
    rw [finset.sum_comm],
    simp only [mul_comm]
  end,
  .. monoid_algebra.semiring }

instance [ring k] : has_neg (monoid_algebra k G) :=
by apply_instance

instance [ring k] [monoid G] : ring (monoid_algebra k G) :=
{ neg := has_neg.neg,
  add_left_neg := add_left_neg,
  .. monoid_algebra.semiring }

instance [comm_ring k] [comm_monoid G] : comm_ring (monoid_algebra k G) :=
{ mul_comm := mul_comm, .. monoid_algebra.ring}

lemma single_mul_single [semiring k] [monoid G] {a₁ a₂ : G} {b₁ b₂ : k} :
  (single a₁ b₁ : monoid_algebra k G) * single a₂ b₂ = single (a₁ * a₂) (b₁ * b₂) :=
(sum_single_index (by simp only [_root_.zero_mul, single_zero, sum_zero])).trans
  (sum_single_index (by rw [_root_.mul_zero, single_zero]))

universe ui
variable {ι : Type ui}

lemma prod_single [comm_semiring k] [comm_monoid G]
  {s : finset ι} {a : ι → G} {b : ι → k} :
  s.prod (λi, single (a i) (b i)) = single (s.prod a) (s.prod b) :=
finset.induction_on s rfl $ λ a s has ih, by rw [prod_insert has, ih,
  single_mul_single, prod_insert has, prod_insert has]

end monoid_algebra

section
variables [semiring k]

/--
The monoid algebra over a semiring `k` generated by the additive monoid `G`.
It is the type of finite formal `k`-linear combinations of terms of `G`,
endowed with the convolution product.
-/
@[derive [inhabited, add_comm_monoid]]
def add_monoid_algebra := G →₀ k

end

namespace add_monoid_algebra

variables {k G}
local attribute [reducible] add_monoid_algebra

section
variables [semiring k] [add_monoid G]

/-- The product of `f g : add_monoid_algebra k G` is the finitely supported function
  whose value at `a` is the sum of `f x * g y` over all pairs `x, y`
  such that `x + y = a`. (Think of the product of multivariate
  polynomials where `α` is the additive monoid of monomial exponents.) -/
instance : has_mul (add_monoid_algebra k G) :=
⟨λf g, f.sum $ λa₁ b₁, g.sum $ λa₂ b₂, single (a₁ + a₂) (b₁ * b₂)⟩

lemma mul_def {f g : add_monoid_algebra k G} :
  f * g = (f.sum $ λa₁ b₁, g.sum $ λa₂ b₂, single (a₁ + a₂) (b₁ * b₂)) :=
rfl

lemma support_mul (a b : add_monoid_algebra k G) :
  (a * b).support ⊆ a.support.bind (λa₁, b.support.bind $ λa₂, {a₁ + a₂}) :=
subset.trans support_sum $ bind_mono $ assume a₁ _,
  subset.trans support_sum $ bind_mono $ assume a₂ _, support_single_subset

/-- The unit of the multiplication is `single 1 1`, i.e. the function
  that is `1` at `0` and zero elsewhere. -/
instance : has_one (add_monoid_algebra k G) :=
⟨single 0 1⟩

lemma one_def : (1 : add_monoid_algebra k G) = single 0 1 :=
rfl

-- TODO: the simplifier unfolds 0 in the instance proof!
private lemma zero_mul (f : add_monoid_algebra k G) : 0 * f = 0 :=
by simp only [mul_def, sum_zero_index]

private lemma mul_zero (f : add_monoid_algebra k G) : f * 0 = 0 :=
by simp only [mul_def, sum_zero_index, sum_zero]

private lemma left_distrib (a b c : add_monoid_algebra k G) : a * (b + c) = a * b + a * c :=
by simp only [mul_def, sum_add_index, mul_add, _root_.mul_zero, single_zero, single_add,
  eq_self_iff_true, forall_true_iff, forall_3_true_iff, sum_add]

private lemma right_distrib (a b c : add_monoid_algebra k G) : (a + b) * c = a * c + b * c :=
by simp only [mul_def, sum_add_index, add_mul, _root_.mul_zero, _root_.zero_mul, single_zero,
  single_add, eq_self_iff_true, forall_true_iff, forall_3_true_iff, sum_zero, sum_add]

instance : semiring (add_monoid_algebra k G) :=
{ one       := 1,
  mul       := (*),
  one_mul   := assume f, by simp only [mul_def, one_def, sum_single_index, _root_.zero_mul,
    single_zero, sum_zero, zero_add, one_mul, sum_single],
  mul_one   := assume f, by simp only [mul_def, one_def, sum_single_index, _root_.mul_zero,
    single_zero, sum_zero, add_zero, mul_one, sum_single],
  zero_mul  := zero_mul,
  mul_zero  := mul_zero,
  mul_assoc := assume f g h, by simp only [mul_def, sum_sum_index, sum_zero_index, sum_add_index,
    sum_single_index, single_zero, single_add, eq_self_iff_true, forall_true_iff, forall_3_true_iff,
    add_mul, mul_add, add_assoc, mul_assoc, _root_.zero_mul, _root_.mul_zero, sum_zero, sum_add],
  left_distrib  := left_distrib,
  right_distrib := right_distrib,
  .. finsupp.add_comm_monoid }

end

instance [comm_semiring k] [add_comm_monoid G] : comm_semiring (add_monoid_algebra k G) :=
{ mul_comm := assume f g,
  begin
    simp only [mul_def, finsupp.sum, mul_comm],
    rw [finset.sum_comm],
    simp only [add_comm]
  end,
  .. add_monoid_algebra.semiring }

instance [ring k] : has_neg (add_monoid_algebra k G) :=
by apply_instance

instance [ring k] [add_monoid G] : ring (add_monoid_algebra k G) :=
{ neg := has_neg.neg,
  add_left_neg := add_left_neg,
  .. add_monoid_algebra.semiring }

instance [comm_ring k] [add_comm_monoid G] : comm_ring (add_monoid_algebra k G) :=
{ mul_comm := mul_comm, .. add_monoid_algebra.ring}

lemma single_mul_single [semiring k] [add_monoid G] {a₁ a₂ : G} {b₁ b₂ : k}:
  (single a₁ b₁ : add_monoid_algebra k G) * single a₂ b₂ = single (a₁ + a₂) (b₁ * b₂) :=
(sum_single_index (by simp only [_root_.zero_mul, single_zero, sum_zero])).trans
  (sum_single_index (by rw [_root_.mul_zero, single_zero]))

universe ui
variable {ι : Type ui}

lemma prod_single [comm_semiring k] [add_comm_monoid G]
  {s : finset ι} {a : ι → G} {b : ι → k} :
  s.prod (λi, single (a i) (b i)) = single (s.sum a) (s.prod b) :=
finset.induction_on s rfl $ λ a s has ih, by rw [prod_insert has, ih,
  single_mul_single, sum_insert has, prod_insert has]

end add_monoid_algebra

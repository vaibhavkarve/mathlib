/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import linear_algebra.dimension linear_algebra.tensor_product
import set_theory.ordinal
noncomputable theory

local attribute [instance] classical.prop_decidable

section
variables (R : Type*) (M : Type*)
variables [comm_ring R] [add_comm_group M] [module R M]

def module.dual := M →ₗ[R] R

open module

instance : add_comm_group (dual R M) :=
by delta dual; apply_instance

instance : module R (dual R M) :=
by delta dual; apply_instance

def eval : M →ₗ[R] (dual R (dual R M)) := linear_map.id.flip

variables {R} {M}
def pairing : (dual R M) → M → R := λ (f : M →ₗ[R] R) m, f m

end

namespace is_basis
variables {K : Type*} {V : Type*}
variables [discrete_field K] [add_comm_group V] [vector_space K V]
variables {B : set V} (h : is_basis K B)
include h
open vector_space module submodule linear_map cardinal

def dual : set (module.dual K V) :=
{f : V →ₗ[K] K | ∃ v ∈ B, f v = 1 ∧ ∀ w ∈ B, w ≠ v → f w = 0}

def dual_elem (v : V) : module.dual K V :=
h.constr $ λ w, if w = v then 1 else 0

lemma dual_elem_mem (v ∈ B) : h.dual_elem v ∈ h.dual :=
begin
  use [v,H],
  split; intros; erw [constr_basis]; simp *,
end

lemma mem_dual_iff (f : module.dual K V) :
  f ∈ h.dual ↔ ∃ v ∈ B, f = h.dual_elem v :=
begin
  split; intro H; rcases H with ⟨v, hv, H⟩,
  { use [v,hv],
    apply h.ext,
    intros w hw,
    erw [constr_basis _ hw],
    split_ifs with hwv,
    { rw hwv, exact H.1 },
    { apply H.2 w hw hwv, } },
  { rw H, apply h.dual_elem_mem v hv }
end

lemma dual_elem_eq_repr (v ∈ B) (w : V) :
  pairing (h.dual_elem v) w = h.repr w v :=
begin
  delta pairing dual_elem,
  erw constr_apply,
  -- change _ = finsupp.to_fun (((linear_map.to_fun _) ∘
  --            (linear_map.to_fun (linear_equiv.to_linear_map _)))
  --            (linear_map.to_fun _ w)) v,
  -- delta submodule.subtype linear_equiv.to_linear_map cod_restrict
  --   linear_equiv.symm linear_independent.total_equiv lc.total_on
  --   linear_equiv.of_bijective lc.supported comp equiv.of_bijective
  --   lc.total function.comp,
  -- unfold_projs,
end

def to_dual : V →ₗ[K] module.dual K V :=
h.constr $ λ v, h.dual_elem v

lemma to_dual_ker : h.to_dual.ker = ⊥ :=
begin
  ext v,
  split,
  { rw [mem_ker, mem_bot],
    intro hv,
    sorry },
  { rw mem_bot, intro h, simp [h], }
end

-- lemma lc_dual_elem (l : lc K (module.dual K V))
-- (hl : ∀ (f : module.dual K V), f ∉ h.dual → l f = 0)
-- (v : V) (hv : v ∈ B) :
--   l (h.dual_elem v hv) = (pairing K V).to_fun
--     ((lc.total K (module.dual K V)).to_fun l) v :=
-- begin
--   have := lc.total_apply l,
--   change ((lc.total K (module.dual K V)).to_fun l) = _ at this,
--   erw this, clear this,
--   erw finsupp.apply_sum,
--   revert hl,
--   apply finsupp.induction l,
--   { intro hl,
--     rw [finsupp.zero_apply, finsupp.sum_zero_index],
--     symmetry,
--     apply zero_apply v, },
--   { intros f k l' _ _ IH hl',
--     rw [finsupp.add_apply, IH, finsupp.sum_add_index,
--         finsupp.sum_single_index],
--     { congr' 1,
--       by_cases H : f ∈ h.dual,
--         { rw [finsupp.single_apply, smul_apply],
--           split_ifs with hf,
--           { rw [hf, dual_elem, constr_basis _ hv], simp, },
--           sorry },
--         {  }
--        } } }
-- end

lemma dual_is_basis (B : set V) (h : is_basis K B) (hfin : dim K V < omega) :
  is_basis K (h.dual) :=
begin
  split,
  { sorry },
  -- { rw [linear_independent_iff],
  --   intros l hl H,
  --   ext f,
  --   by_cases hf : f ∈ h.dual,
  --   { rw lc.total_apply at H,
  --     rw mem_dual_iff at hf,
  --     rcases hf with ⟨v, hv, hf⟩,
  --     rw hf,
  --     sorry },
  --   { rw [lc.mem_supported'] at hl,
  --     apply hl f hf, } },
  { apply le_antisymm,
    { simp },
    { intros x hx,

      sorry } }
end

end is_basis

lemma eval_ker : (eval K V).ker = ⊥ :=
begin
  ext,
  split,
  { rw [mem_ker, mem_bot],
    intro h,
    sorry },
  { rw mem_bot, intro h, simp [h], }
end

end


/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon

-/

import data.rbmap data.finset data.finmap logic.relation

universes u v

structure uf_state (k : Type u) :=
(parent : finmap k k)
(wf' : well_founded (flip parent.to_rel) )

variables {k : Type u}

namespace uf_state

def to_rel (s : uf_state k) := flip s.parent.to_rel

def wf (s : uf_state k) : well_founded s.to_rel := s.wf'

def equiv (s : uf_state k) : k → k → Prop :=
flip (eqv_gen s.to_rel)

section root

variables [decidable_eq k] (s : uf_state k)

def root : k → k :=
s.wf.fix $ λ x root,
match (s.parent.lookup x).attach with
 | (sum.inr ⟨y,h⟩) := root y $ by rw [to_rel,flip,← dfinmap.lookup_eq_iff_set_mem,h]
 | (sum.inl ⟨h⟩) := x
end

end root

lemma root_eq_of_lookup_eq_none [decidable_eq k] {s : uf_state k} {x : k}
  (h : s.parent.lookup x = none) :
  root s x = x :=
by rw [root,well_founded.fix_eq,option.attach_of_eq_none _ h,root._match_1]

lemma root_eq_of_lookup_eq_some [decidable_eq k] {s : uf_state k} {x y : k}
  (h : s.parent.lookup x = some y) :
  root s x = root s y :=
by rw [root,well_founded.fix_eq,option.attach_of_eq_some _ _ h,root._match_1]

lemma equiv_root [decidable_eq k] (s : uf_state k) (x : k) :
  s.equiv x (s.root x) :=
begin
  apply well_founded.induction s.wf x, clear x,
  introv ih,
  cases h : s.parent.lookup x,
  { rw root_eq_of_lookup_eq_none h, apply eqv_gen.refl },
  { rw root_eq_of_lookup_eq_some h,
    rw dfinmap.lookup_eq_iff_set_mem at h,
    apply eqv_gen.trans _ val,
    { apply ih _ h },
    { apply eqv_gen.rel _ _, exact h } }
end

lemma root_eq [decidable_eq k] (s : uf_state k) (x y : k) :
  s.root x = s.root y ↔ s.equiv x y :=
begin
  split,
  { apply well_founded.induction s.wf x, clear x,
    dsimp [flip], intros x ih,
    cases h : s.parent.lookup x,
    { simp [root_eq_of_lookup_eq_none h],
      intro h', rw h', dsimp [equiv],
      apply eqv_gen.symm, apply equiv_root },
    { simp [root_eq_of_lookup_eq_some h], intro h',
      have : dfinmap.to_rel (s.parent) x val := (dfinmap.lookup_eq_iff_set_mem _ _ _).mp h,
      apply eqv_gen.trans _ val,
      { apply ih _ this h' },
      { apply eqv_gen.rel _ _, exact this }, } },
  { intros h, induction h,
    { rw [to_rel,flip,← dfinmap.lookup_eq_iff_set_mem] at h_a,
      rw [root_eq_of_lookup_eq_some h_a], },
    { refl },
    all_goals { cc } }
end

def lookup [decidable_eq k] (s : uf_state k) (x : k) : plift (s.root x = x) ⊕ Σ' y, s.to_rel y x ∧ s.root x = s.root y :=
match (s.parent.lookup x).attach with
  | (sum.inl ⟨h⟩) := sum.inl ⟨by rw root_eq_of_lookup_eq_none h⟩
  | (sum.inr ⟨y,h⟩) :=
    have h' : to_rel s y x, by rw [to_rel,flip,← dfinmap.lookup_eq_iff_set_mem,h],
    sum.inr ⟨y,h',(root_eq s x y).mpr $ eqv_gen.rel _ _ h'⟩
end

def eqv_state {k} [decidable_eq k] (s' : uf_state k) := { s : uf_state k // ∀ i, s.root i = s'.root i }

lemma well_founded_imp_well_founded {α} (r r' : α → α → Prop)
  (h : ∀ x y, r' x y → r x y) :
  well_founded r → well_founded r' :=
begin
  intro h', cases h', constructor, intro a, specialize h' a, induction h',
  constructor, intros, apply h'_ih, apply h _ _ a_1,
end

open relation

lemma eqv_gen_of_tc {α} (r : α → α → Prop) (x y : α) (h : trans_gen r x y) : eqv_gen r x y :=
by { induction h; [ apply eqv_gen.rel, { apply eqv_gen.trans _ _ _ h_ih; apply eqv_gen.rel } ]; assumption }

lemma tc_flip {α} (r : α → α → Prop) : trans_gen (flip r) = flip (trans_gen r) :=
begin
  ext x y; split; intro h,
  all_goals
  { induction h,
    { apply trans_gen.single, assumption },
    { apply trans_gen.trans, refine trans_gen.single h_a_1, exact h_ih }  },
end

lemma refl_trans_gen_root [decidable_eq k] (s : uf_state k) (x : k) :
  refl_trans_gen s.to_rel (s.root x) x :=
begin
  apply well_founded.induction s.wf x, clear x, introv ih,
  rcases s.lookup x with ⟨ ⟨ h ⟩ ⟩ | ⟨ ⟨ y, h₀, h₁ ⟩ ⟩,
  { rw h, },
  { rw h₁, transitivity y,
    { apply ih _ h₀ },
    { apply refl_trans_gen.single h₀ } }
end

lemma root_root [decidable_eq k] (s : uf_state k) (x : k) : s.root (s.root x) = s.root x :=
begin
  apply well_founded.induction s.wf x, clear x, introv ih,
  rcases s.lookup x with ⟨ ⟨ h ⟩ ⟩ | ⟨ ⟨ y, h₀, h₁ ⟩ ⟩,
  { simp only * },
  { simp only * }
end

lemma var [decidable_eq k] (s : uf_state k) (x y : k) : trans_gen s.to_rel (s.root y) x ↔ s.root x = s.root y ∧ x ≠ s.root y :=
begin
  split,
  { intro h, split,
    { rw ← root_root _ y, rw root_eq, apply eqv_gen_of_tc _ _ _ h, },
    { apply ne.symm,
      apply ne_of_well_founded (trans_gen.wf s.wf) h, }  },
  { rintro ⟨ h₀, h₁ ⟩, rw ← h₀ at *,
    clear h₀, revert h₁, apply well_founded.induction s.wf x, clear x, introv ih h,
    rcases s.lookup x with ⟨ ⟨ h' ⟩ ⟩ | ⟨ ⟨ y, h₀, h₁ ⟩ ⟩,
    { rw h' at h, contradiction },
    { rw h₁,
      by_cases h₂ : y = root s y,
      { rw ← h₂, apply trans_gen.single h₀ },
      { apply trans_gen.tail _ h₀, apply ih _ h₀ h₂, } } }
end

def compress_intl {k} [decidable_eq k] (x y : k) (s : uf_state k) (h : trans_gen s.to_rel y x) : uf_state k :=
{ parent := s.parent.insert x y,
   wf' := by { apply well_founded_imp_well_founded (trans_gen s.to_rel),
              { intros a b h', rw [flip,← dfinmap.lookup_eq_iff_set_mem] at h',
                by_cases h'' : x = b,
                { subst b, rw [dfinmap.lookup_insert] at h',
                  cases h', apply h },
                { rw dfinmap.lookup_insert_of_ne _ h'' at h',
                  apply trans_gen.single, rw [to_rel,flip,← dfinmap.lookup_eq_iff_set_mem,h'] } },
              apply trans_gen.wf, apply s.wf } }

def compress {k} [decidable_eq k] {s' : uf_state k} (x y : k) : Π (s : eqv_state s'), trans_gen s.1.to_rel y x → eqv_state s'
| ⟨ s, h ⟩ h' := subtype.mk (compress_intl x y s h')
begin
  intro, rw ← h,
  set s'' := (compress_intl x y s h') with hs,
  apply well_founded.induction (trans_gen.wf s.wf) i, clear i, intros i ih,
  cases hh : s''.parent.lookup i,
  { rw root_eq_of_lookup_eq_none hh,
    dsimp [s'',compress_intl] at hh,
    by_cases hh' : x = i,
    { subst i, rw dfinmap.lookup_insert at hh,
      cases hh, },
    { rw dfinmap.lookup_insert_of_ne _ hh' at hh,
      rw root_eq_of_lookup_eq_none hh, } },
  { rw root_eq_of_lookup_eq_some hh,
    dsimp [s'',compress_intl] at hh,
    by_cases hh' : x = i,
    { subst i, rw dfinmap.lookup_insert at hh,
      cases hh, rw [ih,root_eq], apply eqv_gen.symm,
      apply eqv_gen_of_tc _ _ _ h', apply h' },
    { rw dfinmap.lookup_insert_of_ne _ hh' at hh,
      rw dfinmap.lookup_eq_iff_set_mem at hh, rw ih,
      { rw root_eq, apply eqv_gen.symm, apply eqv_gen.rel _ _, exact hh, },
      { apply trans_gen.single, apply hh } } }
end

section root

variables [decidable_eq k] (s : uf_state k)

def root_compress' : Π (x : k) (xs : list k), (∀ y ∈ xs, trans_gen s.to_rel (s.root x) y) → uf_state k × k :=
s.wf.fix $ λ x root_compress vs h₀,
(match s.lookup x with
 | (sum.inr ⟨y,h₁,h₂⟩) :=
            have h₄ : trans_gen (to_rel s) (s.root y) x, by { apply trans_gen.trans_right,
                                                                   apply refl_trans_gen_root,
                                                                   apply trans_gen.single h₁ },
            have h₃ : ∀ (x : k), x ∈ vs → trans_gen (to_rel s) (s.root y) x, by { introv h, rw ← h₂, apply h₀ _ h, },
            root_compress y h₁ (x :: vs) $ by { simp; split; assumption }
 | (sum.inl ⟨h₁⟩) := (subtype.val $ vs.attach.foldl (λ (s' : eqv_state s) z,
                              have this : trans_gen (to_rel (s'.val)) x z,
                                by { rw [← h₁,← s'.property,var,s'.property,s'.property,← var],
                                     apply h₀ _ z.2, },
                              compress z x s' this)
                              ⟨s,λ _, rfl⟩,x)
 end)

def root_compress (x : k) : uf_state k × k := root_compress' s x [] $ by simp

-- def merge (x y : k) : uf_state k := s

-- lemma merge_equiv (a b x y : k) :
--   (s.merge x y).equiv a b ↔ s.equiv a b ∨ (s.equiv a x ∧ s.equiv y b) ∨ (s.equiv a y ∧ s.equiv x b) :=
-- sorry

end root


end uf_state

def union_find_t (k : Type u) (m : Type u → Type v) (α : Type u) := state_t (uf_state k) m α

@[reducible] def union_find (k : Type u) (α : Type u) := union_find_t k id α

instance {m} [monad m] {k} : monad (union_find_t k m) :=
state_t.monad

instance {m} [monad m] [is_lawful_monad m] {k} : is_lawful_monad (union_find_t k m) :=
state_t.is_lawful_monad m _

namespace union_find_t

open list

variables {m : Type u → Type v} [monad m]

def root [decidable_eq k] (x : k) : union_find_t k m k :=
do s ← (get : state_t (uf_state k) m _),
   let (s',r) := uf_state.root_compress s x,
   r <$ (put s' : state_t (uf_state k) m _)

def eqv'  [decidable_eq k] (x y : k) : union_find_t k m (ulift bool) :=
do rx ← root x,
   ry ← root y,
   pure ⟨ rx = ry ⟩

def eqv {m} [monad m] {k : Type} [decidable_eq k] (x y : k) : union_find_t k m bool :=
ulift.down <$> eqv' x y

end union_find_t

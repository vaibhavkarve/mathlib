
/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon

The category of complete partial orders
-/
import category_theory.concrete_category
import order.complete_partial_order

open category_theory complete_partial_order

namespace category_theory.instances

@[reducible] def CPO : Type* := bundled complete_partial_order

instance complete_partial_order_unbundled (x : CPO) : complete_partial_order x := x.str

namespace complete_partial_order

instance concrete_category_continuous : concrete_category @continuous' := ⟨@continuous_id', @continuous_comp' ⟩

def of (X : Type*) [complete_partial_order X] : CPO := ⟨X, by apply_instance⟩

def discrete : Type* ⥤ CPO :=
{ obj := λ X, ⟨X, discrete.complete_partial_order _⟩,
  map := λ X Y f, ⟨f, discrete.continuous_of _⟩ }

end complete_partial_order

end category_theory.instances

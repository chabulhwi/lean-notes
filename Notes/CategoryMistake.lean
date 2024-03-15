/-
Copyright (c) 2024 Bulhwi Cha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bulhwi Cha
-/

/-!
# An example of category mistakes: good-smelling drinks

Are the proposition "Water smells good." and its negation both false since water has no smell? If
so, we could easily derive a contradiction from these propositions. I think the sentence "Water
smells good." is a [category mistake][catmis]. We shouldn't allow using statements of the form "`d`
smells good," where `d` is a constant that refers to a drink having no smell.

I used the type `Option Prop` to define the predicate `GoodSmelling` on drinks. If `x` is a drink
that has no smell, `GoodSmelling x` is `none`, which means that you don't have the proposition "`x`
smells good." in the type class I defined below.

## Reference

* 윤유석. 2024. “모순과 반대, 모순과 역설: 사소하지만 자주 있는 혼동.” 2024년 2월 5일에 마지막으로
수정함. https://forum.owlofsogang.com/t/topic/4188.

[catmis]: https://plato.stanford.edu/entries/category-mistakes/
-/

/-- A class of drinks with two predicates `HasSmell` and `GoodSmelling` defined as follows:

* `HasSmell x`: `x` has a smell.
* `GoodSmelling x`: `x` smells good, where `x` is a drink that has a smell.
* `goodSmelling_eq_none_of_not_hasSmell x`: If `x` is a drink that has no smell, `GoodSmelling x` is
  `none`, which means that this class doesn't have the proposition "`x` smells good." -/
class GoodSmellingDrink (Drink : Type u) where
  HasSmell : Drink → Prop
  GoodSmelling : Drink → Option Prop
  goodSmelling_eq_none_of_not_hasSmell {x : Drink} : ¬HasSmell x → GoodSmelling x = none

/-- Bulhwi's drinks: water, limeade, almond milk, and durian smoothie. -/
inductive BulhwiDrink : Type where
  | water
  | limeade
  | almondMilk
  | durianSmoothie
  deriving Repr

/-- Bulhwi's drinks with two predicates `HasSmell` and `GoodSmelling` defined as follows:

* Water has no smell; the rest have it.
* This class instance doesn't have the proposition "Water smells good."
* Limeade and almond milk smell good; durian smoothie doesn't. -/
instance : GoodSmellingDrink BulhwiDrink where
  HasSmell := fun
    | .water => False
    | .limeade => True
    | .almondMilk => True
    | .durianSmoothie => True
  GoodSmelling := fun
    | .water => none
    | .limeade => some True
    | .almondMilk => some True
    | .durianSmoothie => some False
  goodSmelling_eq_none_of_not_hasSmell {x} := by
    cases x <;> simp

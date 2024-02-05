# An example of category mistakes: good-smelling drinks

Are the proposition "Water smells good." and its negation both false
since water has no smell? If so, we could easily derive a contradiction
from these propositions. I think the sentence "Water smells good." is a
[category mistake][stanford]. We shouldn't allow using statements of the
form "`d` smells good," where `d` is a constant that refers to a drink
having no smell.

In the [`CategoryMistake`][catmis] file, I used the type `Option Prop`
to define the predicate `goodSmelling` on drinks. If `x` is a drink that
has no smell, `goodSmelling x` is `none`, which means that you don't
have the proposition "`x` smells good." in the type class I defined
below.

## The type class `GoodSmellingDrink`

The type class `GoodSmellingDrink` of drinks has two predicates
`hasSmell` and `goodSmelling` defined as follows:

* `hasSmell x`: `x` has a smell.
* `goodSmelling x`: `x` smells good, where `x` is a drink that has a
  smell.
* `goodSmelling_eq_none_of_not_hasSmell x`: If `x` is a drink that has
  no smell, `goodSmelling x` is `none`, which means that this class
  doesn't have the proposition "`x` smells good."

```lean
class GoodSmellingDrink (Drink : Type v) where
  hasSmell : Drink → Prop
  goodSmelling : Drink → Option Prop
  goodSmelling_eq_none_of_not_hasSmell {x : Drink} : ¬hasSmell x → goodSmelling x = none
```

## Example

Let's define an inductive type called `BulhwiDrink`. This type has four
constructors: `Water`, `Limeade`, `AlmondMilk`, and `DurianSmoothie`.

```lean
inductive BulhwiDrink : Type where
  | Water
  | Limeade
  | AlmondMilk
  | DurianSmoothie
  deriving Repr
```

We can define an instance of `GoodSmellingDrink BulhwiDrink` as follows:

* Water has no smell; the rest have it.
* This class instance doesn't have the proposition "Water smells good."
* Limeade and almond milk smell good; durian smoothie doesn't.

```lean
instance : GoodSmellingDrink BulhwiDrink where
  hasSmell := fun
    | .Water => False
    | .Limeade => True
    | .AlmondMilk => True
    | .DurianSmoothie => True
  goodSmelling := fun
    | .Water => none
    | .Limeade => some True
    | .AlmondMilk => some True
    | .DurianSmoothie => some False
  goodSmelling_eq_none_of_not_hasSmell {x} := by
    cases x <;> simp
```

## Reference

* 윤유석. 2024. “모순과 반대, 모순과 역설: 사소하지만 자주 있는 혼동.”
  2024년 2월 5일에 마지막으로 수정함.
  https://forum.owlofsogang.com/t/topic/4188.

[stanford]: https://plato.stanford.edu/entries/category-mistakes/
[catmis]: ../../Notes/Anselm.lean

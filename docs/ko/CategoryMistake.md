# 범주 실수의 예: 냄새 좋은 음료

물은 냄새가 나지 않으므로 "물은 냄새가 좋다."라는 명제와 그 부정은 모두 거짓일까요? 만약 그렇다면, 이 명제들에서 모순을 쉽게 이끌어 낼 수 있습니다. 제가 보건대, "물은 냄새가 좋다."라는 문장은 [범주 실수][stanford]입니다. `d`가 냄새가 안 나는 음료를 나타내는 상수일 때, '`d`는 냄새가 좋다.' 꼴의 진술은 이용하지 못하게 해야 합니다.

[`CategoryMistake`][catmis] 파일에서, 저는 유형 `Option Prop`을 이용해, 음료에 대한 술어 `goodSmelling`을 정의했습니다. `x`가 냄새가 안 나는 음료이면, `goodSmelling x`는 `none`입니다. 이는 제가 아래에서 정의한 유형 클래스에 "`x`는 냄새가 좋다."라는 명제가 없다는 뜻입니다.

## 유형 클래스 `GoodSmellingDrink`

음료의 유형 클래스 `GoodSmellingDrink`에는 다음과 같이 정의된 두 술어 `hasSmell`와 `goodSmelling`이 있습니다.

* `hasSmell x`: `x`는 냄새가 난다.
* `goodSmelling x`: `x`는 냄새가 좋다. 이때 `x`는 냄새가 나는 음료이다.
* `goodSmelling_eq_none_of_not_hasSmell x`: `x`가 냄새가 안 나는 음료일 때, `goodSmelling x`는 `none`이다. 이는 유형 클래스 `GoodSmellingDrink`에 "`x`는 냄새가 좋다."라는 명제가 없다는 뜻이다.

```lean
class GoodSmellingDrink (Drink : Type v) where
  hasSmell : Drink → Prop
  goodSmelling : Drink → Option Prop
  goodSmelling_eq_none_of_not_hasSmell {x : Drink} : ¬hasSmell x → goodSmelling x = none
```

## 보기

`BulhwiDrink`라는 귀납형을 정의해 보겠습니다. 이 유형에는 구성자가 네 개 있습니다. `Water`, `Limeade`, `AlmondMilk` 그리고 `DurianSmoothie`가 그 구성자들의 이름입니다.

```lean
inductive BulhwiDrink : Type where
  | Water
  | Limeade
  | AlmondMilk
  | DurianSmoothie
  deriving Repr
```

`GoodSmellingDrink BulhwiDrink`의 사례는 다음과 같이 정의할 수 있습니다.

* 물은 냄새가 없고, 나머지는 냄새가 있다.
* 이 유형 클래스 사례에는 "물은 냄새가 좋다."라는 명제가 없다.
* 라임에이드와 아몬드 우유는 냄새가 좋지만, 두리안 스무디는 그렇지 않다.

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

## 참고 문헌

* 윤유석. 2024. “모순과 반대, 모순과 역설: 사소하지만 자주 있는 혼동.”
2024년 2월 5일에 마지막으로 수정함.
https://forum.owlofsogang.com/t/topic/4188.

[stanford]: https://plato.stanford.edu/entries/category-mistakes/
[catmis]: ../../Notes/CategoryMistake.lean

/-
Copyright (c) 2024 Bulhwi Cha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bulhwi Cha
-/
import Mathlib.Init.Data.Int.CompLemmas
import Mathlib.Order.Bounds.Basic

/-!
# St. Anselm's ontological argument

The [`Anselm`][anselm] file might be the second attempt in the Lean
community to formalize an ontological argument for the existence of God
in Lean. It's a modified version of the formulation of St. Anselm's
ontological argument by Alvin Plantinga. (See [9.1 Formulation
1][plantinga] of the SEP entry ["Ontological Arguments."](#reference))

1. God exists in the understanding but not in reality. (Assumption for
   *reductio*)
2. Existence in reality is greater than existence in the understanding
   alone. (Premise)
3. There exists a being in reality that can be conceived. (*Modified*
   premise)
4. A being that exists in reality and can be conceived is greater than
   God. (From (1) and (2).)
5. There exists a being that can be conceived and is greater than God.
   (From (3) and (4).)
6. No being greater than God can be conceived. (From the definition of
   “God”.)
7. Hence, it is false that God exists in the understanding but not in
   reality. (From (1), (5), (6).)
8. God exists in the understanding. (Premise, to which even the Fool
   agrees.)
9. Hence God exists in reality. (From (7), (8).)

I formalized the three premises of the argument as follows:

* `lt_of_inUnderstanding_not_inReality_inReality {x y : Being} :
inUnderstanding x → ¬inReality x → inReality y → x < y` (Step 2)
* `exists_conceivable_and_inReality : ∃ (x : Being), conceivable x ∧
inReality x` (Step 3)
* `isGod_inUnderstanding {x : Being} : isGod x → inUnderstanding x` (Step 8)

Step 3 of the original formulation by Alvin Plantinga is the following
premise: "A being having all of God’s properties plus existence in
reality can be conceived." This premise is redundant. Since God is the
greatest being that can be conceived, God itself can be conceived.
Therefore, a being having all of God's properties can be conceived.

I think the conclusion of St. Anselm's argument is the following
statement:

```lean
theorem isGod_inReality {x : Being} : isGod x → inReality x
```

This theorem doesn't state that God exists in reality. It merely says
that if a being is God, it exists in reality. In order to prove the
existence of God in reality, you need to show that `∃ (x : Being), isGod
x ∧ inReality x`.

For this reason, I think St. Anselm's argument doesn't show God's
existence. Of course, I might have formalized it wrong.

## Theorem `not_exists_int_isGod`

A user named car_nap of Owl of Sogang, a Korean-speaking philosophy
discussion forum, [pointed out][owl] (in Korean) that I didn't prove
that the statement `∃ (x : Being), isGod x ∧ inReality x` is not a
theorem of a theory whose axioms are the premises of St. Anselm's
argument (and the axioms of Lean's type theory).

So I proved a theorem named `not_exists_int_isGod`, which shows that
there exist a universe level `u`, a type `Being : Type u`, and an
instance of `Anselm Being` where the statement `∃ (x : Being), isGod x`
is false.

## Reference

* Oppy, Graham, "Ontological Arguments", *The Stanford Encyclopedia of
Philosophy* (Fall 2023 Edition), Edward N. Zalta & Uri Nodelman (eds.),
URL =
https://plato.stanford.edu/archives/fall2023/entries/ontological-arguments/.

## Acknowledgements

### The Lean community

I'd like to thank Eric Wieser and Alistair Tucker. Eric Wieser found
inconsistency in my first and second drafts. Alistair Tucker commented
on transcribing premise 3 of the original formulation by Alvin
Plantinga. You can see my discussion with them in [this
link][leanzulip].

Alistair Tucker also [told me][tucker] how to prove that we can't deduce
the statement `∃ (x : Being), isGod x ∧ inReality x` from the premises
of St. Anselm's argument and the axioms of Lean's type theory.

### Owl of Sogang

I want to thank car_nap for raising [the issue mentioned
above](#theorem-anselmnot_exists_int_isgod).

[anselm]: ../../Notes/Anselm.lean
[fst]: https://github.com/forked-from-1kasper/ground_zero/blob/9f83f7c6224eee8905b16aeebc4c234b4b216031/GroundZero/Theorems/Ontological.lean#L520-L521
[plantinga]: https://plato.stanford.edu/entries/ontological-arguments/#StAnsOntArg
[owl]: https://forum.owlofsogang.com/t/lean/3613/9
[leanzulip]: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Formalizing.20St.2E.20Anselm's.20ontological.20argument/near/39867934
[tucker]: https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/how.20do.20I.20say.20.22a.20sentence.20is.20a.20theorem.20of.20a.20theory.22.20in.20lean.3F/near/399042805
-/

section PartialOrder

variable {α : Type u} [PartialOrder α]

theorem IsGreatest.property {x : α} {p q : α → Prop} (hgst : IsGreatest p x)
    (hlt : ∀ {y : α}, ¬q x → q y → x < y) (hex : ∃ (y : α), p y ∧ q y) : q x := by
  have hnnq : ¬¬q x := by
    intro hnq
    rcases hex with ⟨y, hpy, hqy⟩
    have x_lt_y : x < y := hlt hnq hqy
    have y_le_x : y ≤ x := hgst.2 hpy
    exact not_le_of_lt x_lt_y y_le_x
  exact of_not_not hnnq

end PartialOrder

/-- A class for formalizing St. Anselm's ontological argument of the existence of God.

* `conceivable x`: `x` can be conceived.
* `inUnderstanding x`: `x` exists in the understanding.
* `inReality x`: `x` exists in reality.
* `lt_of_inUnderstanding_not_inReality_inReality`: If `x` exists in the understanding alone and
  `y` exists in reality, `y` is greater than `x`.
* `IsGreatest_conceivable_inUnderstanding`: If `x` is a greatest being that can be conceived,
  `x` exists in the understanding.
* `exists_conceivable_and_inReality`: There exists a being in reality that can be conceived. -/
class Anselm (Being : Type u) extends PartialOrder Being where
  conceivable : Being → Prop
  inUnderstanding : Being → Prop
  inReality : Being → Prop
  lt_of_inUnderstanding_not_inReality_inReality {x y : Being} : inUnderstanding x → ¬inReality x →
    inReality y → x < y
  IsGreatest_conceivable_inUnderstanding {x : Being} : IsGreatest conceivable x → inUnderstanding x
  exists_conceivable_and_inReality : ∃ (x : Being), conceivable x ∧ inReality x

namespace Anselm

section

variable {Being : Type u} [Anselm Being]

/-- God is a greatest being that can be conceived. -/
def isGod (x : Being) := IsGreatest conceivable x

/-- God is unique, which means that no two different beings are God. -/
theorem isGod_unique {x y : Being} : isGod x → isGod y → x = y :=
  IsGreatest.unique (s := conceivable)

/-- If a being is God, it exists in the understanding. -/
theorem isGod_inUnderstanding {x : Being} : isGod x → inUnderstanding x :=
  IsGreatest_conceivable_inUnderstanding

/-- God is conceivable. -/
theorem isGod_conceivable {x : Being} : isGod x → conceivable x := And.left

/-- The conclusion of St. Anselm's argument: if a being is God, it exists in reality. -/
theorem isGod_inReality {x : Being} (hgd : isGod x) : inReality x := by
  refine IsGreatest.property hgd ?_ ?_
  · exact lt_of_inUnderstanding_not_inReality_inReality (isGod_inUnderstanding hgd)
  · exact exists_conceivable_and_inReality

end

/-!
## Theorem `not_exists_int_isGod`

There exist a universe level `u`, a type `Being : Type u`, and an
instance of `Anselm Being` where the statement `∃ (x : Being), isGod x`
is false.
-/

/-- A local instance for proving the theorem `not_exists_int_isGod`. -/
instance : Anselm ℤ where
  conceivable := fun _ ↦ True
  inUnderstanding := fun _ ↦ True
  inReality := fun
    | .ofNat _ => True
    | .negSucc _ => False
  lt_of_inUnderstanding_not_inReality_inReality {_ _ : ℤ} := by
    repeat (first | simp | split <;> simp [not_true, not_false])
    rename_i n _ m
    calc
      -(n + 1) < (0 : ℤ) := Int.negSucc_lt_zero n
      0 ≤ ↑m := Int.zero_le_ofNat m
  IsGreatest_conceivable_inUnderstanding := by simp
  exists_conceivable_and_inReality := by exists 0

/-- There exists an instantiation of the `Anselm` class where God doesn't exist. -/
theorem not_exists_int_isGod : ¬∃ (a : ℤ), isGod a := by
  intro hex
  rcases hex with ⟨god, _, hle⟩
  have god_lt_succ_god : god < god + 1 := Int.lt_succ god
  have succ_god_le_god : god + 1 ≤ god := hle trivial
  exact not_le_of_lt god_lt_succ_god succ_god_le_god

end Anselm

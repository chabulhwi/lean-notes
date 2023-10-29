import Mathlib.Init.Data.Int.CompLemmas
import Mathlib.Order.Bounds.Basic

section PartialOrder

variable (α : Type u) [PartialOrder α]

theorem IsGreatest.property {x : α} {p q : α → Prop} (hgst : IsGreatest p x)
    (hlt : ∀ {y : α}, ¬ q x → q y → x < y) (hex : ∃ (y : α), p y ∧ q y) : q x := by
  have hnnq : ¬¬ q x := by
    intro hnq
    rcases hex with ⟨y, hpy, hqy⟩
    have x_lt_y : x < y := hlt hnq hqy
    have y_le_x : y ≤ x := hgst.2 hpy
    exact not_le_of_lt x_lt_y y_le_x
  exact of_not_not hnnq

end PartialOrder

class Anselm (Being : Type u) extends PartialOrder Being where
  conceivable : Being → Prop
  inUnderstanding : Being → Prop
  inReality : Being → Prop
  lt_of_inUnderstanding_not_inReality_inReality {x y : Being} : inUnderstanding x → ¬ inReality x →
    inReality y → x < y
  IsGreatest_conceivable_inUnderstanding {x : Being} : IsGreatest conceivable x → inUnderstanding x
  exists_conceivable_and_inReality : ∃ (x : Being), conceivable x ∧ inReality x

namespace Anselm

section

variable {Being : Type u} [Anselm Being]

def isGod (x : Being) := IsGreatest conceivable x

theorem isGod.unique {x y : Being} : isGod x → isGod y → x = y :=
  IsGreatest.unique (s := conceivable)

theorem isGod_inUnderstanding {x : Being} : isGod x → inUnderstanding x :=
  IsGreatest_conceivable_inUnderstanding

theorem isGod_conceivable {x : Being} : isGod x → conceivable x := And.left

theorem isGod_inReality {x : Being} (hgd : isGod x) : inReality x := by
  refine IsGreatest.property Being hgd ?_ ?_
  · exact lt_of_inUnderstanding_not_inReality_inReality (isGod_inUnderstanding hgd)
  · exact exists_conceivable_and_inReality

#print axioms isGod_inReality
-- 'Anselm.isGod_inReality' depends on axioms: [Classical.choice, Quot.sound, propext]

end

section

local instance : Anselm ℤ where
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

private theorem not_exists_int_isGod : ¬ ∃ (a : ℤ), isGod a := by
  intro hex
  rcases hex with ⟨god, _, hle⟩
  have god_lt_succ_god : god < god + 1 := Int.lt_succ god
  have succ_god_le_god : god + 1 ≤ god := hle trivial
  exact not_le_of_lt god_lt_succ_god succ_god_le_god

end

end Anselm

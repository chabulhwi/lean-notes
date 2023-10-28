import Mathlib.Init.Data.Int.CompLemmas
import Mathlib.Order.Basic

section

variable {α : Type u} [PartialOrder α]

def isMax (x : α) (p : α → Prop) := p x ∧ ∀ (y : α), p y → y ≤ x

theorem isMax_unique {x y : α} (p : α → Prop) : isMax x p ∧ isMax y p → x = y := by
  intro ⟨hx, hy⟩
  have x_le_y : x ≤ y := hy.2 x hx.1
  have y_le_x : y ≤ x := hx.2 y hy.1
  exact le_antisymm x_le_y y_le_x

theorem isMax_mt {x y : α} (p : α → Prop) (hmx : isMax x p) (hlt : x < y) : ¬ p y :=
  mt (hmx.2 y) (not_le_of_lt hlt)

end

theorem isMax_property (α : Type u) [PartialOrder α] {x : α} (p q : α → Prop) (hmx : isMax x p)
    (hlt : ∀ {y : α}, ¬ q x → q y → x < y) (hex : ∃ (y : α), p y ∧ q y) : q x := by
  have hnnqx : ¬¬ q x := by
    intro hnqx
    rcases hex with ⟨y, hpy, hqy⟩
    have x_lt_y : x < y := hlt hnqx hqy
    have y_le_x : y ≤ x := hmx.2 y hpy
    exact not_le_of_lt x_lt_y y_le_x
  exact of_not_not hnnqx

class Anselm (Being : Type u) extends PartialOrder Being where
  conceivable : Being → Prop
  inUnderstanding : Being → Prop
  inReality : Being → Prop
  lt_of_inUnderstanding_not_inReality_inReality {x y : Being} : inUnderstanding x → ¬ inReality x →
    inReality y → x < y
  isMax_conceivable_inUnderstanding {x : Being} : isMax x conceivable → inUnderstanding x
  exists_conceivable_and_inReality : ∃ (x : Being), conceivable x ∧ inReality x

namespace Anselm

section

variable {Being : Type u} [Anselm Being]

def isGod (x : Being) := isMax x conceivable

theorem isGod_unique {x y : Being} : isGod x ∧ isGod y → x = y := isMax_unique conceivable

theorem isGod_mt {x y : Being} (hgx : isGod x) (hlt : x < y) : ¬ conceivable y :=
  isMax_mt conceivable hgx hlt

theorem isGod_inUnderstanding {x : Being} : isGod x → inUnderstanding x :=
  isMax_conceivable_inUnderstanding

theorem isGod_conceivable {x : Being} : isGod x → conceivable x := And.left

theorem isGod_inReality {x : Being} (hgx : isGod x) : inReality x := by
  refine isMax_property Being conceivable inReality hgx ?_ ?_
  · intro y
    exact lt_of_inUnderstanding_not_inReality_inReality (isGod_inUnderstanding hgx)
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
  isMax_conceivable_inUnderstanding := by simp
  exists_conceivable_and_inReality := by exists 0

private theorem not_exists_int_isGod : ¬ ∃ (a : ℤ), isGod a := by
  intro hex
  rcases hex with ⟨god, _hcg, hleg⟩
  have god_lt_succ_god : god < god + 1 := Int.lt_succ god
  have succ_god_le_god : god + 1 ≤ god := hleg (god + 1) trivial
  exact not_le_of_lt god_lt_succ_god succ_god_le_god

end

end Anselm

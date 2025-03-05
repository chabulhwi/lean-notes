/-
Copyright (c) 2025 Bulhwi Cha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bulhwi Cha
-/
import Mathlib.Data.Nat.Prime.Defs

namespace Nat

/-- An alternative definition of `Nat.Prime`. -/
def Prime' (n : Nat) : Prop := n ≥ 2 ∧ (∀ x : Nat, x > 1 ∧ x < n → n % x ≠ 0)

/-- `Nat.Prime` and `Nat.Prime'` are equivalent. -/
theorem prime_eq_prime' : Prime = Prime' := by
  ext n
  constructor
  · intro h
    constructor
    · exact Nat.Prime.two_le h
    · intro m ⟨hmgt1, hmltn⟩ hmod
      have hdvd : m ∣ n := Nat.dvd_of_mod_eq_zero hmod
      have hm1n : m = 1 ∨ m = n := (Nat.dvd_prime h).mp hdvd
      rcases hm1n with hmeq1 | hmeqn
      · exact Nat.ne_of_gt hmgt1 hmeq1
      · exact Nat.ne_of_lt hmltn hmeqn
  · intro h
    have hnpo : n > 0 := Nat.lt_of_lt_of_le Nat.zero_lt_two h.1
    rw [Nat.prime_def]
    constructor
    · exact h.1
    · intro m hdvd
      have hmlen : m ≤ n := Nat.le_of_dvd hnpo hdvd
      have hmod : n % m = 0 := Nat.mod_eq_zero_of_dvd hdvd
      have hmne0 : m ≠ 0 := by
        intro hmeq0
        have hneq0 : n = 0 := calc
          n = n % m := by rw [hmeq0, Nat.mod_zero n]
          _ = 0 := hmod
        exact Nat.ne_of_gt hnpo hneq0
      have hmge1 : m ≥ 1 := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hmne0)
      have hnmb : ¬(m > 1 ∧ m < n) := mt (h.2 m) (not_not_intro hmod)
      rcases Nat.eq_or_lt_of_le hmge1 with h1eqm | h1ltm
      · left; symm; assumption
      · right
        rcases Nat.eq_or_lt_of_le hmlen with hmeqn | hmltn
        · assumption
        · exfalso; exact hnmb ⟨h1ltm, hmltn⟩

end Nat

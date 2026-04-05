/-
Copyright (c) 2026 Bulhwi Cha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bulhwi Cha
-/

/-!
# A variant of a Hilbert system for intuitionistic propositional logic

I formalized a variant of a Hilbert system for intuitionistic propositional logic, which has the
following properties:

1. The axioms and the inference rule of a standard Hilbert system for intuitionistic propositional
   logic all hold in my deduction system.
2. Every proposition translated from a provable well-formed formula is true in Lean's dependent type
   theory.
-/

set_option autoImplicit false

/-!
## Well-formed formulas
-/

namespace Propositional

/-- Well-formed formulas in intuitionistic propositional logic. -/
inductive Wff (PropVar : Type) : Type where
  /-- Propositional variables. -/
  | fromVar (p : PropVar) : Wff PropVar
  /-- Truth, denoted by `⊤`.  -/
  | Tru : Wff PropVar
  /-- Falsity, denoted by `⊥`. -/
  | Fal : Wff PropVar
  /-- Conjunction. `And φ ψ` is denoted by `φ ∧ ψ`. -/
  | And (φ ψ : Wff PropVar) : Wff PropVar
  /-- Disjunction. `Or φ ψ` is denoted by `φ ∨ ψ`. -/
  | Or  (φ ψ : Wff PropVar) : Wff PropVar
  /-- Implication. `Imp φ ψ` is denoted by `φ → ψ`. -/
  | Imp (φ ψ : Wff PropVar) : Wff PropVar

instance {PropVar : Type} : Coe PropVar (Wff PropVar) where
  coe p := Wff.fromVar p

notation "⊤" => Wff.Tru
notation "⊥" => Wff.Fal
notation:max "¬" φ:40 => Wff.Not φ
infixr:35 " ∧ " => Wff.And
infixr:30 " ∨ " => Wff.Or
infixr:25 " → " => Wff.Imp

namespace Wff

variable {PropVar : Type}

/-- Negation. `Not φ` is denoted by `¬φ`. -/
def Not (φ : Wff PropVar) : Wff PropVar := φ → ⊥

notation:max "¬" φ:40 => Not φ

/-- Equivalence. `Iff φ ψ` is denoted by `φ ↔ ψ`. -/
def Iff (φ ψ : Wff PropVar) : Wff PropVar :=
  (φ → ψ) ∧ (ψ → φ)

infixr:20 " ↔ " => Iff

/-- The canonical translation from well-formed formulas to propositions with respect to a
translation of propositional variables into propositions. -/
def toProp (trans : PropVar → Prop) : Wff PropVar → Prop
  | fromVar p => trans p
  | Tru => True
  | Fal => False
  | And φ ψ => (toProp trans φ) ∧ (toProp trans ψ)
  | Or  φ ψ => (toProp trans φ) ∨ (toProp trans ψ)
  | Imp φ ψ => (toProp trans φ) → (toProp trans ψ)

section

variable {trans : PropVar → Prop}

theorem toProp_tru : toProp trans ⊤ ↔ True :=
  Iff.rfl

theorem toProp_fal : toProp trans ⊥ ↔ False :=
  Iff.rfl

theorem toProp_and {φ ψ : Wff PropVar} : (φ ∧ ψ).toProp trans ↔ φ.toProp trans ∧ ψ.toProp trans :=
  Iff.rfl

theorem toProp_or {φ ψ : Wff PropVar} : (φ ∨ ψ).toProp trans ↔ φ.toProp trans ∨ ψ.toProp trans :=
  Iff.rfl

theorem toProp_imp {φ ψ : Wff PropVar} : (φ → ψ).toProp trans ↔ φ.toProp trans → ψ.toProp trans :=
  Iff.rfl

theorem toProp_not {φ : Wff PropVar} : (¬φ).toProp trans ↔ ¬φ.toProp trans :=
  Iff.rfl

theorem toProp_iff {φ ψ : Wff PropVar} : (φ ↔ ψ).toProp trans ↔ (φ.toProp trans ↔ ψ.toProp trans) :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩

end

end Wff

/-!
## Axioms and inference rules
-/

variable {PropVar : Type}

set_option autoImplicit true in
/-- The provability judgment for well-formed formulas. `Provable φ`, or `⊢ φ` means that `φ` is
provable.

An **assertion** is in one of the following forms:

* `⊢ φ`. This form has no hypotheses.
* `(⊢ φ₁) → (⊢ φ₂) → ⋯ → (⊢ φₙ)`, where `n ≥ 2`. In this form, `⊢ φ₁`, `⊢ φ₂`, ⋯, `⊢ φₙ₋₁` are the
  hypotheses, and `⊢ φₙ` is the conclusion.

A **rule** of my Hilbert system is a constructor of the `Provable` inductive family. Every rule is
an assertion, since it has one of the above forms. A rule that has no hypotheses is an **axiom**; if
it has at least one hypothesis, it's an **inference rule**.

Some assertions in my Hilbert system have multiple forms:

* Closed form: An assertion in closed form has no hypotheses at all; all of its preconditions (if
  any) are part of its implication's antecedent.
* Deduction form: An assertion is in deduction form whenever the conclusion and all hypotheses are
  each prefixed with an implication using the same antecedent (`φ`). An assertion in deduction form
  has a label suffix "D" if there are other forms of the same assertion.
* Inference form: An assertion with hypotheses but no common antecedent is in inference form; it
  usually has a label suffix "I" if there are other forms of the same assertion. There's one
  exception: an introduction rule for a logical operator also has a label suffix "I".

This convention is slightly adapted from the one used in the Metamath Proof Explorer. See
https://us.metamath.org/mpeuni/mmnatded.html#current.
-/
inductive Provable : Wff PropVar → Type where
  /-- `ident : ⊢ φ → φ`. The identity axiom. -/
  | ident : Provable (φ → φ)
  /-- `simpl : (⊢ φ) → (⊢ ψ → φ)`. The simplification rule. -/
  | simpl : Provable φ → Provable (ψ → φ)
  /-- `syl : (⊢ φ → ψ) → (⊢ ψ → χ) → (⊢ φ → χ)`. The syllogism rule. -/
  | syl   : Provable (φ → ψ) → Provable (ψ → χ) → Provable (φ → χ)
  /-- `mp : (⊢ φ → ψ) → (⊢ φ) → (⊢ ψ)`. The modus ponens rule. This can be viewed as the inference
  form of the elimination rule for implication. -/
  | mp    : Provable (φ → ψ) → Provable φ → Provable ψ
  /-- `truI : ⊢ ⊤`. The closed form of the introduction rule for truth. -/
  | truI  : Provable ⊤
  /-- `falE : ⊢ ⊥ → φ`. The closed form of the elimination rule for falsity. -/
  | falE  : Provable (⊥ → φ)
  /-- `andID : (⊢ φ → ψ) → (⊢ φ → χ) → (⊢ φ → ψ ∧ χ)`. The deduction form of the introduction rule
  for conjunction. -/
  | andID : Provable (φ → ψ) → Provable (φ → χ) → Provable (φ → ψ ∧ χ)
  /-- `andEL : ⊢ φ ∧ ψ → φ`. The closed form of the left elimination rule for conjunction. -/
  | andEL : Provable (φ ∧ ψ → φ)
  /-- `andER : ⊢ φ ∧ ψ → ψ`. The closed form of the right elimination rule for conjunction. -/
  | andER : Provable (φ ∧ ψ → ψ)
  /-- `orIL : ⊢ φ → φ ∨ ψ`. The closed form of the left introduction rule for disjunction. -/
  | orIL  : Provable (φ → φ ∨ ψ)
  /-- `orIR : ⊢ φ → ψ ∨ φ`. The closed form of the right introduction rule for disjunction. -/
  | orIR  : Provable (φ → ψ ∨ φ)
  /-- `orE : (⊢ φ → ψ ∨ χ) → (⊢ φ ∧ ψ → θ) → (⊢ φ ∧ χ → θ) → (⊢ φ → θ)`. The elimination rule for
  disjunction. -/
  | orE   : Provable (φ → ψ ∨ χ) → Provable (φ ∧ ψ → θ) → Provable (φ ∧ χ → θ) → Provable (φ → θ)
  /-- `impI : (⊢ φ ∧ ψ → χ) → (⊢ φ → (ψ → χ))`. The introduction rule for implication. -/
  | impI  : Provable (φ ∧ ψ → χ) → Provable (φ → (ψ → χ))
  /-- `impED : (⊢ φ → (ψ → χ)) → (⊢ φ → ψ) → (⊢ φ → χ)`. The deduction form of the elimination rule
  for implication. -/
  | impED : Provable (φ → (ψ → χ)) → Provable (φ → ψ) → Provable (φ → χ)

prefix:15 "⊢ " => Provable

/-!
## Basic theorems about intuitionistic propositional logic
-/

namespace Provable

def truID {φ : Wff PropVar} : ⊢ φ → ⊤ :=
  simpl truI

def falEI {φ : Wff PropVar} (d : ⊢ (⊥ : Wff PropVar)) : ⊢ φ :=
  mp falE d

def falED {φ ψ : Wff PropVar} (d : ⊢ φ → ⊥) : ⊢ φ → ψ :=
  syl d falE

def andI {φ ψ : Wff PropVar} (d₁ : ⊢ φ) (d₂ : ⊢ ψ) : ⊢ φ ∧ ψ :=
  mp (andID (simpl d₁) (simpl d₂)) truI

def andELI {φ ψ : Wff PropVar} (d : ⊢ φ ∧ ψ) : ⊢ φ :=
  mp andEL d

def andELD {φ ψ χ : Wff PropVar} (d : ⊢ φ → ψ ∧ χ) : ⊢ φ → ψ :=
  syl d andEL

def andERI {φ ψ : Wff PropVar} (d : ⊢ φ ∧ ψ) : ⊢ ψ :=
  mp andER d

def andERD {φ ψ χ : Wff PropVar} (d : ⊢ φ → ψ ∧ χ) : ⊢ φ → χ :=
  syl d andER

def and_comm {φ ψ : Wff PropVar} : ⊢ φ ∧ ψ → ψ ∧ φ :=
  andID andER andEL

def orILI {φ ψ : Wff PropVar} (d : ⊢ φ) : ⊢ φ ∨ ψ :=
  mp orIL d

def orILD {φ ψ χ : Wff PropVar} (d : ⊢ φ → ψ) : ⊢ φ → ψ ∨ χ :=
  syl d orIL

def orIRI {φ ψ : Wff PropVar} (d : ⊢ ψ) : ⊢ φ ∨ ψ :=
  mp orIR d

def orIRD {φ ψ χ : Wff PropVar} (d : ⊢ φ → χ) : ⊢ φ → ψ ∨ χ :=
  syl d orIR

def orEI {φ ψ χ : Wff PropVar} (left : ⊢ φ → ψ) (right : ⊢ χ → ψ) : ⊢ φ ∨ χ → ψ :=
  orE ident (syl andER left) (syl andER right)

def or_comm {φ ψ : Wff PropVar} : ⊢ φ ∨ ψ → ψ ∨ φ :=
  orEI orIR orIL

def impI_inv {φ ψ χ : Wff PropVar} (d : ⊢ φ → (ψ → χ)) : ⊢ φ ∧ ψ → χ :=
  impED (syl andEL d) andER

def impI_comm {φ ψ χ : Wff PropVar} (d : ⊢ φ ∧ ψ → χ) : ⊢ ψ → φ → χ :=
  impI (syl and_comm d)

def impI_inv_comm {φ ψ χ : Wff PropVar} (d : ⊢ φ → (ψ → χ)) : ⊢ ψ ∧ φ → χ :=
  syl and_comm (impI_inv d)

def notI {φ ψ : Wff PropVar} (d : ⊢ φ ∧ ψ → ⊥) : ⊢ φ → ¬ψ :=
  impI d

def notE {φ : Wff PropVar} (d₁ : ⊢ ¬φ) (d₂ : ⊢ φ) : ⊢ (⊥ : Wff PropVar) :=
  mp d₁ d₂

def notED {φ ψ : Wff PropVar} (d₁ : ⊢ φ → ¬ψ) (d₂ : ⊢ φ → ψ) : ⊢ φ → ⊥ :=
  impED d₁ d₂

def mt {φ ψ : Wff PropVar} (d₁ : ⊢ φ → ψ) (d₂ : ⊢ ¬ψ) : ⊢ ¬φ :=
  syl d₁ d₂

def mtd {φ ψ χ : Wff PropVar} (d₁ : ⊢ φ ∧ ψ → χ) (d₂ : ⊢ φ → ¬χ) : ⊢ φ → ¬ψ :=
  impI (impED (syl andEL d₂) d₁)

def iffI {φ ψ : Wff PropVar} (mp : ⊢ φ → ψ) (mpr : ⊢ ψ → φ) : ⊢ φ ↔ ψ :=
  andI mp mpr

def iffID {φ ψ χ : Wff PropVar} (mp : ⊢ φ → ψ → χ) (mpr : ⊢ φ → χ → ψ) : ⊢ φ → (ψ ↔ χ) :=
  andID (impI (impI_inv mp)) (impI (impI_inv mpr))

def iffEL {φ ψ : Wff PropVar} : ⊢ (φ ↔ ψ) → φ → ψ :=
  andEL

def iffER {φ ψ : Wff PropVar} : ⊢ (φ ↔ ψ) → ψ → φ :=
  andER

def iffELD {φ ψ χ : Wff PropVar} (d : ⊢ φ → (ψ ↔ χ)) : ⊢ φ → ψ → χ :=
  andELD d

def iffERD {φ ψ χ : Wff PropVar} (d : ⊢ φ → (ψ ↔ χ)) : ⊢ φ → χ → ψ :=
  andERD d

def and_assoc {φ ψ χ : Wff PropVar} : ⊢ (φ ∧ ψ) ∧ χ ↔ φ ∧ ψ ∧ χ :=
  iffI
    (andID (syl andEL andEL) (andID (syl andEL andER) andER))
    (andID (andID andEL (syl andER andEL)) (syl andER andER))

def or_assoc {φ ψ χ : Wff PropVar} : ⊢ (φ ∨ ψ) ∨ χ ↔ φ ∨ ψ ∨ χ :=
  iffI
    (orEI
      (orEI orIL (orIRD orIL))
      (orIRD orIR))
    (orEI
      (orILD orIL)
      (orEI (orILD orIR) orIR))

def and_or_left {φ ψ χ : Wff PropVar} : ⊢ φ ∧ (ψ ∨ χ) ↔ φ ∧ ψ ∨ φ ∧ χ :=
  iffI
    (orE andER
      (orILD (andID (syl andEL andEL) andER))
      (orIRD (andID (syl andEL andEL) andER)))
    (orEI
      (andID andEL (orILD andER))
      (andID andEL (orIRD andER)))

def or_and_right {φ ψ χ : Wff PropVar} : ⊢ (φ ∨ ψ) ∧ χ ↔ φ ∧ χ ∨ ψ ∧ χ :=
  iffI
    (orE andEL
      (orILD (andID andER (syl andEL andER)))
      (orIRD (andID andER (syl andEL andER))))
    (orEI
      (andID (orILD andEL) andER)
      (andID (orIRD andEL) andER))

def or_and_left {φ ψ χ : Wff PropVar} : ⊢ φ ∨ ψ ∧ χ ↔ (φ ∨ ψ) ∧ (φ ∨ χ) :=
  iffI
    (orEI
      (andID orIL orIL)
      (andID (syl andEL orIR) (syl andER orIR)))
    (orE andEL
      (orILD (syl andER ident))
      (orE (syl andEL andER)
        (orILD andER)
        (orIRD (andID (syl andEL andER) andER))))

def and_or_right {φ ψ χ : Wff PropVar} : ⊢ φ ∧ ψ ∨ χ ↔ (φ ∨ χ) ∧ (ψ ∨ χ) :=
  iffI
    (orEI
      (andID (orILD andEL) (orILD andER))
      (andID orIR orIR))
    (orE andEL
      (orE (syl andEL andER)
        (orILD (andID (syl andEL andER) andER))
        (orIRD andER))
      (orIRD andER))

/-!
## Axioms of a standard Hilbert system for intuitionistic propositional logic
-/

/-- The first axiom. -/
def ax01 {φ ψ : Wff PropVar} : ⊢ φ → ψ → φ :=
  impI andEL

/-- The second axiom. -/
def ax02 {φ ψ χ : Wff PropVar} : ⊢ (φ → ψ → χ) → ((φ → ψ) → (φ → χ)) :=
  impI <| impI <|
    impED
      (impED (syl andEL andEL) andER)
      (impED (syl andEL andER) andER)

/-- The third axiom. -/
def ax03 {φ : Wff PropVar} : ⊢ (φ → ¬φ) → ¬φ :=
  impI (impED (impED andEL andER) andER)

/-- The fourth axiom. -/
def ax04 {φ ψ : Wff PropVar} : ⊢ ¬φ → (φ → ψ) :=
  impI (syl (impED andEL andER) falE)

/-!
## Translation of provable well-formed formulas into propositions
-/

/-- Every proposition translated from a provable well-formed formula is true in Lean's dependent
type theory. -/
def toProp {PropVar : Type} {φ : Wff PropVar} {trans : PropVar → Prop} (d : ⊢ φ) : φ.toProp trans :=
  match d with
  | @ident PropVar ψ => id
  | @simpl PropVar ψ χ d => fun _ ↦ d.toProp
  | @syl   PropVar ψ _χ θ d₁ d₂ => d₂.toProp ∘ d₁.toProp
  | @mp    PropVar _ψ χ d₁ d₂ => d₁.toProp d₂.toProp
  | truI => trivial
  | @falE  PropVar ψ => False.elim
  | @andID PropVar ψ χ θ d₁ d₂ => fun h ↦ ⟨d₁.toProp h, d₂.toProp h⟩
  | @andEL PropVar ψ χ => And.left
  | @andER PropVar ψ χ => And.right
  | @orIL  PropVar ψ χ => Or.inl
  | @orIR  PropVar ψ χ => Or.inr
  | @orE   PropVar ψ _χ _θ τ d₁ d₂ d₃ => fun h ↦
    (d₁.toProp h).elim
      (fun left  ↦ d₂.toProp ⟨h, left⟩)
      (fun right ↦ d₃.toProp ⟨h, right⟩)
  | @impI  PropVar ψ χ θ d => fun h₁ h₂ ↦ d.toProp ⟨h₁, h₂⟩
  | @impED PropVar ψ _χ θ d₁ d₂ => fun h ↦ d₁.toProp h (d₂.toProp h)

end Provable

end Propositional

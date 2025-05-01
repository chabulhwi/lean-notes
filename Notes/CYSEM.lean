/-
Copyright (c) 2025 Bulhwi Cha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bulhwi Cha
-/

universe u v w t

/-- This type class provides a type `D` of depictions with the following predicates and their
properties:

* `LacksValue d`: `d` lacks any literary, artistic, ideological, scientific, medical, or educational
  value. In short, `d` lacks any value.
* `IsObscene d`: `d` is obscene.
* `IsVisual d`: `d` is a visual depiction.
* `IsPorn d`: `d` is pornography.
* `IsCYP d`: `d` is child or youth pornography (CYP).
* `IsRealCYP d`: `d` is real child or youth pornography.
* `IsVirtualCYP d`: `d` is virtual child or youth pornography.
* `IsCYSEM d`: `d` is a child or youth sexual exploitation material (CYSEM).
* `IsRealCYSEM d`: `d` is a real child or youth sexual exploitation material.
* `IsVirtualCYSEM d`: `d` is a virtual child or youth sexual exploitation material.
* `lacksValue_of_isObscene`: Every obscene material lacks any value.
* `isObscene_of_isPorn`: If `d` is pornography, it is obscene.
* `isCYSEM_iff_isCYP`: Child or youth pornography is logically equivalent to child or youth sexual
  exploitation materials.
* `isRealCYSEM_iff_isRealCYP` : Real child or youth pornography is logically equivalent to
  real child or youth sexual exploitation materials.
* `isVirtualCYSEM_iff_isVirtualCYP` : Virtual child or youth pornography is logically equivalent to
  virtual child or youth sexual exploitation materials. -/
class Depiction (D : Type u) where
  LacksValue : D → Prop
  IsObscene  : D → Prop
  IsVisual   : D → Prop
  IsPorn : D → Prop
  IsCYP  : D → Prop
  IsRealCYP    : D → Prop
  IsVirtualCYP : D → Prop
  IsCYSEM : D → Prop
  IsRealCYSEM    : D → Prop
  IsVirtualCYSEM : D → Prop
  lacksValue_of_isObscene {d : D} (h : IsObscene d) : LacksValue d
  isObscene_of_isPorn {d : D} (h : IsPorn d) : IsObscene d
  isCYSEM_iff_isCYP {d : D} : IsCYSEM d ↔ IsCYP d
  isRealCYSEM_iff_isRealCYP {d : D} : IsRealCYSEM d ↔ IsRealCYP d
  isVirtualCYSEM_iff_isVirtualCYP {d : D} : IsVirtualCYSEM d ↔ IsVirtualCYP d

namespace Depiction

variable {D : Type u} [Depiction D]

/-- If `d` is pornography, it lacks any value. -/
theorem lacksValue_of_isPorn {d : D} (h : IsPorn d) : LacksValue d :=
  lacksValue_of_isObscene (isObscene_of_isPorn h)

end Depiction

export Depiction (LacksValue IsObscene IsVisual IsPorn IsCYP IsRealCYP IsVirtualCYP IsCYSEM)

/-- This type class provides a type `I` of agent identities with the following identities and their
modifiers:

* Identities: (a) Person, (b) image, (c) adult, and (d) child or youth
* Modifiers: (a) *Real* and (b) *virtual* -/
class AgentIdentity (I : Type w) where
  person : I
  image  : I
  adult  : I
  childOrYouth : I
  real    : I → I
  virtual : I → I

export AgentIdentity (person image adult childOrYouth real virtual)

/-- This type class provides the following relations between a type `Ag` of agents and a type `I` of
agent identities and the properties of these relations:

* `Is x i`: `x` is `i`. Use the notation `x is i`.
* `CanBeObviouslyPerceivedAs x i`: `x` can be obviously perceived as `i`. Use the notation `x
  canBeObviouslyPerceivedAs i`.
* `is_person_or_is_image`: Every agent is a person or an image.
* `is_person_of_is_real_adult`: Every real adult is a person.
* `is_person_of_is_real_childOrYouth`: All children or youth are people.
* `is_real_adult_or_is_real_childOrYouth_of_is_person`: Every person is a real adult or a real child
  or youth.
* `not_is_real_adult_and_is_real_childOrYouth_of_is_person`: Every person can't be both a real adult
  and a real child or youth.
* `is_virtual_childOrYouth_def`: `x` is a virtual child or youth if and only if (a) `x` is a real
  adult who can be obviously perceived as a real child or youth or (b) `x` is an image that can be
  obviously perceived as a child or youth. -/
class AgentIdentityRelation (Ag : Type v) (I : Type w) extends AgentIdentity I where
  Is : Ag → I → Prop
  CanBeObviouslyPerceivedAs : Ag → I → Prop
  is_person_or_is_image (x : Ag) : Is x person ∨ Is x image
  is_person_of_is_real_adult {x : Ag} (h : Is x (real adult)) : Is x person
  is_person_of_is_real_childOrYouth {x : Ag} (h : Is x (real childOrYouth)) : Is x person
  is_real_adult_or_is_real_childOrYouth_of_is_person {x : Ag} (h : Is x person) : Is x (real adult)
    ∨ Is x (real childOrYouth)
  not_is_real_adult_and_is_real_childOrYouth_of_is_person {x : Ag} (h : Is x person) :
    ¬(Is x (real adult) ∧ Is x (real childOrYouth))
  is_virtual_childOrYouth_def {x : Ag} : Is x (virtual childOrYouth) ↔ (Is x (real adult) ∧
    CanBeObviouslyPerceivedAs x (real childOrYouth)) ∨ (Is x image ∧ CanBeObviouslyPerceivedAs x
    childOrYouth)

namespace AgentIdentityRelation

infixl:55 " is " => Is
infixl:55 " canBeObviouslyPerceivedAs " => CanBeObviouslyPerceivedAs

end AgentIdentityRelation

/-- This type class provides a type of actions with a field representing a sexual act. -/
class Action (Act : Type t) where
  sexualAct : Act

export Action (sexualAct)

/-- This type class provides a ternary relation, `DepictsDoing`, and its property.

* `DepictsDoing d x someAct`: `d` depicts `x` doing `someAct`. This sentence itself is the notation.
* `depictsDoing_sexualAct_of_isObscene`: Every obscene material depicts some agent doing any sexual
  act. -/
class ObsceneMaterial (D : Type u) (Ag : Type v) (Act : Type t) extends Depiction D, Action Act
    where
  DepictsDoing : D → Ag → Act → Prop
  depictsDoing_sexualAct_of_isObscene {d : D} (h : IsObscene d) : ∃ (x : Ag), DepictsDoing d x
    sexualAct

namespace ObsceneMaterial

notation:55 d "depicts" x "doing" act => DepictsDoing d x act

end ObsceneMaterial

/-- This type class provides Bulhwi Cha's conjecture: every visual depiction of a child or youth
doing any sexual act is obscene. -/
class ObsceneVisualDepiction (D : Type u) (Ag : Type v) (I : Type w) (Act : Type t) extends
    AgentIdentityRelation Ag I, ObsceneMaterial D Ag Act where
  real_childOrYouth_conjecture {d : D} (hv : IsVisual d) (hd : ∃ (x : Ag), x is real childOrYouth ∧
    d depicts x doing sexualAct) : IsObscene d

/-- This type class provides definitions of real and virtual child or youth pornography:

* `isCYP_def`: `d` is child or youth pornography (CYP) if and only if-
  \(a\) `d` is a visual depiction;
  \(b\) `d` is pornography; and
  \(c\) `d` depicts some real or virtual child or youth doing any sexual act.
* `isRealCYP_def`: `d` is real child or youth pornography if and only if-
  \(a\) `d` is a visual depiction;
  \(b\) `d` is pornography; and
  \(c\) `d` depicts some real child or youth doing any sexual act.
* `isVirtualCYP_def`: `d` is virtual child or youth pornography if and only if-
  \(a\) `d` is a visual depiction;
  \(b\) `d` is pornography; and
  \(c\) `d` depicts some virtual child or youth doing any sexual act.
-/
class ChildOrYouthPorn (D : Type u) (Ag : Type v) (I : Type w) (Act : Type t) extends
    ObsceneVisualDepiction D Ag I Act where
  isCYP_def {d : D} : IsCYP d ↔ IsVisual d ∧ IsPorn d ∧ ∃ (x : Ag), (x is real childOrYouth ∨
    x is virtual childOrYouth) ∧ d depicts x doing sexualAct
  isRealCYP_def {d : D} : IsRealCYP d ↔ IsVisual d ∧ IsPorn d ∧ ∃ (x : Ag), x is real childOrYouth
    ∧ d depicts x doing sexualAct
  isVirtualCYP_def {d : D} : IsVirtualCYP d ↔ IsVisual d ∧ IsPorn d ∧ ∃ (x : Ag), x is virtual
    childOrYouth ∧ d depicts x doing sexualAct

/-!
## Lemmas and theorems about visual depictions
-/

namespace Depiction

open ChildOrYouthPorn

variable {D : Type u} {Ag : Type v} {I : Type w} {Act : Type t} [ChildOrYouthPorn D Ag I Act]

/-!
### Lemmas about child or youth pornography (CYP)
-/

/-- If `d` is child or youth pornography, it is pornography. -/
theorem isPorn_of_isCYP {d : D} (h : IsCYP d) : IsPorn d :=
  (isCYP_def.mp h).2.1

/-- If `d` is child or youth pornography, it is obscene. -/
theorem isObscene_of_isCYP {d : D} (h : IsCYP d) : IsObscene d :=
  isObscene_of_isPorn (isPorn_of_isCYP h)

/-- If `d` is child or youth pornography, it lacks any value. -/
theorem lacksValue_of_isCYP {d : D} (h : IsCYP d) : LacksValue d :=
  lacksValue_of_isPorn (isPorn_of_isCYP h)

/-- `d` is child or youth pornography (CYP) if and only if it is real CYP or virtual CYP. -/
theorem isCYP_iff_isRealCYP_or_isVirtualCYP {d : D} : IsCYP d ↔ IsRealCYP d ∨ IsVirtualCYP d :=
  Iff.intro
    (fun h ↦
      let ⟨hvi, hpo, x, his, hde⟩ := isCYP_def.mp h
      his.elim
        (fun hisr ↦ Or.inl (isRealCYP_def.mpr ⟨hvi, hpo, x, hisr, hde⟩))
        (fun hisv ↦ Or.inr (isVirtualCYP_def.mpr ⟨hvi, hpo, x, hisv, hde⟩)))
    (fun h ↦ h.elim
      (fun hr ↦
        let ⟨hvi, hpo, x, hisr, hde⟩ := isRealCYP_def.mp hr
        isCYP_def.mpr ⟨hvi, hpo, x, Or.inl hisr, hde⟩)
      (fun hv ↦
        let ⟨hvi, hpo, x, hisv, hde⟩ := isVirtualCYP_def.mp hv
        isCYP_def.mpr ⟨hvi, hpo, x, Or.inr hisv, hde⟩))

/-!
### Lemmas about real child or youth pornography
-/

/-- If `d` is real child or youth pornography, it is CYP. -/
theorem isCYP_of_isRealCYP {d : D} (h : IsRealCYP d) : IsCYP d :=
  isCYP_iff_isRealCYP_or_isVirtualCYP.mpr (Or.inl h)

/-- If `d` is real child or youth pornography, it is pornography. -/
theorem isPorn_of_isRealCYP {d : D} (h : IsRealCYP d) : IsPorn d :=
  isPorn_of_isCYP (isCYP_of_isRealCYP h)

/-- If `d` is real child or youth pornography, it is obscene. -/
theorem isObscene_of_isRealCYP {d : D} (h : IsRealCYP d) : IsObscene d :=
  isObscene_of_isCYP (isCYP_of_isRealCYP h)

/-- If `d` is real child or youth pornography, it lacks any value. -/
theorem lacksValue_of_isRealCYP {d : D} (h : IsRealCYP d) : LacksValue d :=
  lacksValue_of_isCYP (isCYP_of_isRealCYP h)

/-!
### Lemmas about virtual child or youth pornography
-/

/-- If `d` is virtual child or youth pornography, it is CYP. -/
theorem isCYP_of_isVirtualCYP {d : D} (h : IsVirtualCYP d) : IsCYP d :=
  isCYP_iff_isRealCYP_or_isVirtualCYP.mpr (Or.inr h)

/-- If `d` is virtual child or youth pornography, it is pornography. -/
theorem isPorn_of_isVirtualCYP {d : D} (h : IsVirtualCYP d) : IsPorn d :=
  isPorn_of_isCYP (isCYP_of_isVirtualCYP h)

/-- If `d` is virtual child or youth pornography, it is obscene. -/
theorem isObscene_of_isVirtualCYP {d : D} (h : IsVirtualCYP d) : IsObscene d :=
  isObscene_of_isCYP (isCYP_of_isVirtualCYP h)

/-- If `d` is virtual child or youth pornography, it lacks any value. -/
theorem lacksValue_of_isVirtualCYP {d : D} (h : IsVirtualCYP d) : LacksValue d :=
  lacksValue_of_isCYP (isCYP_of_isVirtualCYP h)

/-!
### Lemmas about child or youth sexual exploitation materials (CYSEM)
-/

/-- Every child or youth sexual exploitation material is pornography. -/
theorem isPorn_of_isCYSEM {d : D} (h : IsCYSEM d) : IsPorn d :=
  isPorn_of_isCYP (isCYSEM_iff_isCYP.mp h)

/-- Every child or youth sexual exploitation material is obscene. -/
theorem isObscene_of_isCYSEM {d : D} (h : IsCYSEM d) : IsObscene d :=
  isObscene_of_isPorn (isPorn_of_isCYSEM h)

/-- Every child or youth sexual exploitation material lacks any value. -/
theorem lacksValue_of_isCYSEM {d : D} (h : IsCYSEM d) : LacksValue d :=
  lacksValue_of_isPorn (isPorn_of_isCYSEM h)

/-- `d` is a child or youth sexual exploitation material (CYSEM) if and only if it is a real CYSEM
or a virtual CYSEM. -/
theorem isCYSEM_iff_isRealCYSEM_or_isVirtualCYSEM {d : D} : IsCYSEM d ↔ IsRealCYSEM d ∨
    IsVirtualCYSEM d := by
  rw [isCYSEM_iff_isCYP, isRealCYSEM_iff_isRealCYP, isVirtualCYSEM_iff_isVirtualCYP]
  apply isCYP_iff_isRealCYP_or_isVirtualCYP

/-!
### Lemmas about real child or youth sexual exploitation materials
-/

/-- Every real child or youth sexual exploitation material is CYSEM. -/
theorem isCYSEM_of_isRealCYSEM {d : D} (h : IsRealCYSEM d) : IsCYSEM d :=
  isCYSEM_iff_isRealCYSEM_or_isVirtualCYSEM.mpr (Or.inl h)

/-- Every real child or youth sexual exploitation material is pornography. -/
theorem isPorn_of_isRealCYSEM {d : D} (h : IsRealCYSEM d) : IsPorn d :=
  isPorn_of_isCYSEM (isCYSEM_of_isRealCYSEM h)

/-- Every real child or youth sexual exploitation material is obscene. -/
theorem isObscene_of_isRealCYSEM {d : D} (h : IsRealCYSEM d) : IsObscene d :=
  isObscene_of_isCYSEM (isCYSEM_of_isRealCYSEM h)

/-- Every real child or youth sexual exploitation material lacks value. -/
theorem lacksValue_of_isRealCYSEM {d : D} (h : IsRealCYSEM d) : LacksValue d :=
  lacksValue_of_isCYSEM (isCYSEM_of_isRealCYSEM h)

/-!
### Lemmas about virtual child or youth sexual exploitation materials
-/

/-- Every virtual child or youth sexual exploitation material is CYSEM. -/
theorem isCYSEM_of_isVirtualCYSEM {d : D} (h : IsVirtualCYSEM d) : IsCYSEM d :=
  isCYSEM_iff_isRealCYSEM_or_isVirtualCYSEM.mpr (Or.inr h)

/-- Every virtual child or youth sexual exploitation material is pornography. -/
theorem isPorn_of_isVirtualCYSEM {d : D} (h : IsVirtualCYSEM d) : IsPorn d :=
  isPorn_of_isCYSEM (isCYSEM_of_isVirtualCYSEM h)

/-- Every virtual child or youth sexual exploitation material is obscene. -/
theorem isObscene_of_isVirtualCYSEM {d : D} (h : IsVirtualCYSEM d) : IsObscene d :=
  isObscene_of_isCYSEM (isCYSEM_of_isVirtualCYSEM h)

/-- Every virtual child or youth sexual exploitation material lacks value. -/
theorem lacksValue_of_isVirtualCYSEM {d : D} (h : IsVirtualCYSEM d) : LacksValue d :=
  lacksValue_of_isCYSEM (isCYSEM_of_isVirtualCYSEM h)

/-!
## Important theorems about visual depictions
-/

/-- Bulhwi Cha's revised definition of child or youth sexual exploitation materials (CYSEM). I
defined it as (a) real CYSEM or (b) virtual CYSEM that lacks any value. -/
theorem isCYSEM_iff_isRealCYSEM_or_isVirtualCYSEM_and_lacksValue {d : D} :
    IsCYSEM d ↔ IsRealCYSEM d ∨ (IsVirtualCYSEM d ∧ LacksValue d) :=
  Iff.intro
    (fun h ↦ (isCYSEM_iff_isRealCYSEM_or_isVirtualCYSEM.mp h).elim
      Or.inl
      (fun hisv ↦ Or.inr ⟨hisv, lacksValue_of_isVirtualCYSEM hisv⟩))
    (fun h ↦ h.elim
      isCYSEM_of_isRealCYSEM
      (fun hvl ↦ isCYSEM_of_isVirtualCYSEM hvl.1))

/-- A corollary of Bulhwi Cha's conjecture about a visual depiction of a child or
youth doing any sexual act: there's no such depiction that isn't obscene. -/
theorem not_exists_isVisual_and_not_isObscene_and_depicts_real_childOrYouth_doing_sexualAct :
    ¬∃ (d : D), IsVisual d ∧ ¬IsObscene d ∧ ∃ (x : Ag), x is real (childOrYouth : I) ∧ d depicts x
    doing (sexualAct : Act) :=
  fun h ↦
    let ⟨d, hv, hno, hd⟩ := h
    have ho : IsObscene d := ObsceneVisualDepiction.real_childOrYouth_conjecture hv hd
    show False from hno ho

end Depiction

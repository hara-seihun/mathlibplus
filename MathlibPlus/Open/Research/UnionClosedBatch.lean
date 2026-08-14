import Mathlib

noncomputable section

namespace MathlibPlus.Open.Research

open scoped BigOperators

/-- The union of all members of a finite family of finite sets. -/
def familyUnion {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) : Finset α :=
  F.biUnion (fun S => S)

/-- The common intersection of a finite family, computed in a finite ambient type. -/
def commonIntersection {α : Type*} [Fintype α] [DecidableEq α]
    (F : Finset (Finset α)) : Finset α :=
  (Finset.univ : Finset α).filter (fun a => ∀ S ∈ F, a ∈ S)

/-- Union-closedness for a finite family. -/
def unionClosed {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F

/-- Intersection of the members containing a specified coordinate. -/
def conditionedIntersection {α : Type*} [Fintype α] [DecidableEq α]
    (F : Finset (Finset α)) (y : α) : Finset α :=
  commonIntersection (F.filter (fun S => y ∈ S))

/-- The joint-output family `A ∨ B`. -/
def joinFamilies {α : Type*} [DecidableEq α]
    (A B : Finset (Finset α)) : Finset (Finset α) :=
  A.biUnion (fun G => B.image (fun H => G ∪ H))

/-- The hypotheses common to the one-exception claims, before the lower bound
on the number of `x`-rows is imposed. -/
def oneExceptionCore {α : Type*} [Fintype α] [DecidableEq α]
    (A B : Finset (Finset α)) (x y : α) : Prop :=
  let U := familyUnion A
  let V := familyUnion B
  x ≠ y ∧
    A.Nonempty ∧ B.Nonempty ∧
    unionClosed A ∧ unionClosed B ∧
    commonIntersection A = ∅ ∧ commonIntersection B = ∅ ∧
    A.filter (fun S => x ∈ S ∧ y ∈ S) = {U} ∧
    B.filter (fun S => x ∈ S ∧ y ∈ S) = {V} ∧
    conditionedIntersection A y ∩ conditionedIntersection B y = {y}

/-- The complete one-exception setup. -/
def oneExceptionSetup {α : Type*} [Fintype α] [DecidableEq α]
    (A B : Finset (Finset α)) (x y : α) : Prop :=
  oneExceptionCore A B x y ∧
    (A.filter (fun S => x ∈ S)).card ≥ 3 ∧
    (B.filter (fun S => x ∈ S)).card ≥ 3

/-- There is exactly one non-top joint output containing both coordinates. -/
def exactlyOneExceptionalOutput {α : Type*} [Fintype α] [DecidableEq α]
    (A B : Finset (Finset α)) (x y : α) (E : Finset α) : Prop :=
  let U := familyUnion A
  let V := familyUnion B
  let Q := U ∪ V
  E ∈ joinFamilies A B ∧
    x ∈ E ∧ y ∈ E ∧ E ≠ Q ∧
    ∀ E', E' ∈ joinFamilies A B → x ∈ E' → y ∈ E' → E' = Q ∨ E' = E

/-- No non-top joint output contains both coordinates. -/
def noExceptionalOutput {α : Type*} [Fintype α] [DecidableEq α]
    (A B : Finset (Finset α)) (x y : α) : Prop :=
  let Q := familyUnion A ∪ familyUnion B
  ∀ E, E ∈ joinFamilies A B → x ∈ E → y ∈ E → E = Q

/-- Claim 21197: the conditioned one-exception setup. -/
def claim21197 {α : Type*} [Fintype α] [DecidableEq α]
    (A B : Finset (Finset α)) (x y : α) : Prop :=
  oneExceptionSetup A B x y

/-- Claim 21198: absence of an exceptional output bounds both source row
fibres by two. -/
def claim21198 : Prop :=
  ∀ (α : Type*) [Fintype α] [DecidableEq α]
    (A B : Finset (Finset α)) (x y : α),
    oneExceptionCore A B x y →
    noExceptionalOutput A B x y →
    (A.filter (fun S => x ∈ S)).card ≤ 2 ∧
    (B.filter (fun S => x ∈ S)).card ≤ 2

/-- Claim 21199: the reconstruction equations in the one-exception case. -/
def claim21199 : Prop :=
  ∀ (α : Type*) [Fintype α] [DecidableEq α]
    (A B : Finset (Finset α)) (x y : α) (E : Finset α),
    oneExceptionCore A B x y →
    exactlyOneExceptionalOutput A B x y E →
    let U := familyUnion A
    let V := familyUnion B
    let Q := U ∪ V
    (∀ G ∈ A, x ∈ G →
      G ∪ conditionedIntersection A y = U ∧
      (G ∪ conditionedIntersection B y = E ∨ G ∪ conditionedIntersection B y = Q)) ∧
    (U = E ∨ U = Q) ∧ (V = E ∨ V = Q)

/-- Claim 21200: the two factor tops equal the pair top. -/
def claim21200 : Prop :=
  ∀ (α : Type*) [Fintype α] [DecidableEq α]
    (A B : Finset (Finset α)) (x y : α) (E : Finset α),
    oneExceptionSetup A B x y →
    exactlyOneExceptionalOutput A B x y E →
    let U := familyUnion A
    let V := familyUnion B
    let Q := U ∪ V
    U ≠ E ∧ V ≠ E ∧ U = Q ∧ V = Q

/-- Claim 21201: the unique exceptional output forces the omitted block into
both conditioned intersections, yielding the stated contradiction. -/
def claim21201 : Prop :=
  ∀ (α : Type*) [Fintype α] [DecidableEq α]
    (A B : Finset (Finset α)) (x y : α) (E : Finset α),
    oneExceptionSetup A B x y →
    exactlyOneExceptionalOutput A B x y E →
    let U := familyUnion A
    let Q := U ∪ familyUnion B
    (∃ G, G ∈ A ∧ x ∈ G ∧
      G ∪ conditionedIntersection A y = Q ∧ G ∪ {y} = E) ∧
    Q \ E ⊆ conditionedIntersection A y ∧
    Q \ E ⊆ conditionedIntersection B y ∧
    False

/-- Claim 21202: the one-exception separation theorem. -/
def claim21202 : Prop :=
  ∀ (α : Type*) [Fintype α] [DecidableEq α]
    (A B : Finset (Finset α)) (x y : α),
    oneExceptionSetup A B x y →
    let Q := familyUnion A ∪ familyUnion B
    (joinFamilies A B).filter
      (fun E => x ∈ E ∧ y ∈ E ∧ E ≠ Q) |>.card ≥ 2

end MathlibPlus.Open.Research

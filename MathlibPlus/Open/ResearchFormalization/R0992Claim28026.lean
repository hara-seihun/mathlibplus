import MathlibPlus.Open.Research.OrbitalCriteria

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0992Claim28026

noncomputable section

abbrev F3 := ZMod 3
abbrev Plane := Fin 2 → F3
abbrev Coeff := Fin 3 → F3
abbrev E := F3 × (Plane × Coeff)

/-- The quadratic displacement used by the displayed order-three action. -/
def quadraticQ (x : Plane) : Coeff :=
  ![x 0 * (x 0 - 1), (2 * x 0 - 1) * x 1, x 1 ^ 2]

/-- The coefficient-table dot product on the fibre coordinates. -/
def coefficientDot (v w : Coeff) : F3 :=
  ∑ i : Fin 3, v i * w i

/-- The displayed transporter formula on `E = F₃ ⊕ F₃² ⊕ F₃³`. -/
def transporterFormula (F : Plane → Coeff) : E → E :=
  fun p =>
    (p.1 + coefficientDot (F p.2.1) p.2.2,
      (p.2.1, p.2.2 + quadraticQ p.2.1))

/-- A permutation is the displayed `q_F` exactly when it has the displayed
coordinate formula at every point. -/
def isDisplayedTransporter (F : Plane → Coeff) (q : Equiv.Perm E) : Prop :=
  ∀ p : E, q p = transporterFormula F p

/-- The generated group `G_F = ⟨T,T^{q_F}⟩`, with the regular translation
set and the conjugate regular set retained literally. -/
def generatedPairGroup (q : Equiv.Perm E) : Subgroup (Equiv.Perm E) :=
  Subgroup.closure
    ((MathlibPlus.Open.Research.OrbitalCriteria.translationSet :
        Set (Equiv.Perm E)) ∪
      MathlibPlus.Open.Research.OrbitalCriteria.conjugateSet q
        (MathlibPlus.Open.Research.OrbitalCriteria.translationSet :
          Set (Equiv.Perm E)))

/-- Conjugation of the displayed regular pair by a transporter lying in the
exact 2-closure. -/
def conjugatesDisplayedRegularPair (q : Equiv.Perm E) : Prop :=
  ∃ c : Equiv.Perm E,
    c ∈ MathlibPlus.Open.Research.OrbitalCriteria.twoClosureOf
      (generatedPairGroup q : Set (Equiv.Perm E)) ∧
      Set.image (fun h => c⁻¹ * h * c)
          (MathlibPlus.Open.Research.OrbitalCriteria.translationSet :
            Set (Equiv.Perm E)) =
        MathlibPlus.Open.Research.OrbitalCriteria.conjugateSet q
          (MathlibPlus.Open.Research.OrbitalCriteria.translationSet :
            Set (Equiv.Perm E))

/-- A table has exactly two nonzero plane-point values, with the support
represented as an unlabelled two-element set. -/
def exactlyTwoPointSupport (F : Plane → Coeff) : Prop :=
  ∃ S : Finset Plane,
    S.card = 2 ∧ ∀ z : Plane, F z ≠ 0 ↔ z ∈ S

/-- The finite family of coefficient tables with exactly two-point support. -/
def twoPointTables : Finset (Plane → Coeff) :=
  letI : DecidablePred exactlyTwoPointSupport := Classical.decPred _
  Finset.univ.filter exactlyTwoPointSupport

/-- Claim 28026: every nonzero two-point slice has its displayed transporter
in the exact generated-pair 2-closure and has the displayed regular pair
conjugate there; the unlabelled table family has the stated census. -/
def twoPointSupportTheorem_claim28026 : Prop :=
  (∀ (x y : Plane) (lam mu : Coeff),
    x ≠ y → lam ≠ 0 → mu ≠ 0 →
      let F : Plane → Coeff :=
        fun z => if z = x then lam else if z = y then mu else 0
      ∀ q : Equiv.Perm E,
        isDisplayedTransporter F q →
          q ∈ MathlibPlus.Open.Research.OrbitalCriteria.twoClosureOf
            (generatedPairGroup q : Set (Equiv.Perm E)) ∧
            conjugatesDisplayedRegularPair q) ∧
    twoPointTables.card = Nat.choose 9 2 * 26 ^ 2 ∧
      Nat.choose 9 2 * 26 ^ 2 = 24336

end

end MathlibPlus.Open.ResearchFormalization.R0992Claim28026

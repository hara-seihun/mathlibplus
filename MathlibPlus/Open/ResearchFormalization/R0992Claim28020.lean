import MathlibPlus.Open.ResearchFormalization.R0992Claim28032

namespace MathlibPlus.Open.ResearchFormalization.R0992Claim28020

noncomputable section

abbrev F3 := MathlibPlus.Open.ResearchFormalization.R0992Claim28032.F3
abbrev Plane := MathlibPlus.Open.ResearchFormalization.R0992Claim28032.Plane
abbrev Fibre := MathlibPlus.Open.ResearchFormalization.R0992Claim28032.Fibre
abbrev E := MathlibPlus.Open.ResearchFormalization.R0992Claim28032.E

open MathlibPlus.Open.ResearchFormalization.R0992Claim28032
open MathlibPlus.Open.Research.OrbitalCriteria

/-- The one-plane-supported homogeneous-linear coefficient table. -/
def onePlaneTable (x₀ : Plane) (lam : Fibre) : Plane → Fibre :=
  fun x => if x = x₀ then lam else 0

def onePlaneSupported (F : Plane → Fibre) : Prop :=
  ∃ x₀ : Plane, ∃ lam : Fibre, lam ≠ 0 ∧ F = onePlaneTable x₀ lam

/-- The set-level conjugation relation used for the displayed `T^{q}`. -/
def conjugatesTranslation (c q : Equiv.Perm E) : Prop :=
  Set.image (fun h : Equiv.Perm E => c⁻¹ * h * c)
      (translationGroup : Set (Equiv.Perm E)) =
    conjugateSet q (translationGroup : Set (Equiv.Perm E))

/-- Claim 28020: every one-plane-supported nonzero table has the displayed
transporter in the exact 2-closure, and the transporter itself conjugates the
regular translation group to its displayed conjugate. -/
def onePlaneSupportedHomogeneousLinearTwists_claim28020 : Prop :=
  (∀ x₀ : Plane, ∀ lam : Fibre, lam ≠ 0 →
    let F := onePlaneTable x₀ lam
    let q := transporter F
    q ∈ twoClosureOf (generatedGroup q : Set (Equiv.Perm E)) ∧
      conjugatesTranslation q q) ∧
    Nat.card {F : Plane → Fibre // onePlaneSupported F} = 234 ∧
    9 * (3 ^ 3 - 1) = (234 : ℕ)

end
end MathlibPlus.Open.ResearchFormalization.R0992Claim28020

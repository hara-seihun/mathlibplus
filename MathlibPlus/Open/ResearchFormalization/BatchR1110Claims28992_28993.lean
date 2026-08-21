-- UNVERIFIED (downstream): submitted but not kernel-verified, so it is not built and MathlibPlus.lean does not import it. See unverified.txt.
import Mathlib
import MathlibPlus.Algebra.Claim28994

namespace MathlibPlus.Open.ResearchFormalization.BatchR1110Claims

noncomputable section

abbrev F7 := ZMod 7

private def normalizedSolution
    (b c t : F7 → F7) : Prop :=
  b 0 = 0 ∧
    t 0 = 0 ∧
    ∀ x u : F7,
      t (x + 3 * u) - t x =
        b (x + 2 * u) - b (x + 3 * u) - 2 * c u

private def quadraticRow
    (b c t : F7 → F7) : Prop :=
  ∃ α β ε : F7,
    β ≠ 0 ∧
    (∀ x : F7, b x = α * x + β * x ^ 2) ∧
    (∀ x : F7, c x = (3 * α + 2 * ε) * x + 6 * β * x ^ 2) ∧
    (∀ x : F7, t x = ε * x + 2 * β * x ^ 2)

/-- Claim 28992: the normalized voltage-equation nullspace is exactly the
unique three-parameter affine/quadratic family over `F₇`. -/
def claim28992_exactQuadraticNullspaceClassification : Prop :=
  ∀ (b c t : F7 → F7),
    normalizedSolution b c t ↔
      ∃! parameters : F7 × F7 × F7,
        let α := parameters.1
        let β := parameters.2.1
        let ε := parameters.2.2
        (∀ x : F7, b x = α * x + β * x ^ 2) ∧
          (∀ x : F7,
            c x = (3 * α + 2 * ε) * x + 6 * β * x ^ 2) ∧
          (∀ x : F7, t x = ε * x + 2 * β * x ^ 2)

/-- Claim 28993: the exact finite normalized-row carrier has 7³ rows, and
exactly the nonzero-beta rows are nonlinear, numbering 6·7²=294. -/
def claim28993_normalizedAndNonlinearRowCounts : Prop := by
  classical
  exact
    (Finset.univ.filter (fun row :
        (F7 → F7) × (F7 → F7) × (F7 → F7) =>
      normalizedSolution row.1 row.2.1 row.2.2)).card = 343 ∧
    (Finset.univ.filter (fun row :
        (F7 → F7) × (F7 → F7) × (F7 → F7) =>
      normalizedSolution row.1 row.2.1 row.2.2 ∧
        quadraticRow row.1 row.2.1 row.2.2)).card = 294

end

end MathlibPlus.Open.ResearchFormalization.BatchR1110Claims

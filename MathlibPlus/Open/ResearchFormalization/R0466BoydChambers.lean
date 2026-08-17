import MathlibPlus.Open.ResearchFormalization.BoydWeights25796
import MathlibPlus.Open.ResearchFormalization.LehmerMinimum25803

open scoped BigOperators
open Classical

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.R0466

open MathlibPlus.Open.ResearchFormalization
open MathlibPlus.Open.ResearchFormalization.BoydWeights25796

/-- The number of distinct roots outside the unit circle. -/
def outsideRootCount (p : Polynomial ℝ) : ℕ :=
  (((p.map (algebraMap ℝ ℂ)).roots.toFinset).filter
    (fun z => 1 < ‖z‖)).card

def containsOneExteriorMember {n : ℕ}
    (ell : Polynomial ℝ) (S : Set (Fin n → ℝ)) : Prop :=
  ∃ v ∈ S, ∃ q A : Polynomial ℝ, ∃ θ : ℝ,
    affineBoydFormula n ell (correctionPolynomial v) q A ∧
      BoydWeights25796.exteriorRoot A θ

/-- Claim 25790: on every Salem-trace Boyd family, the exterior-root count is
constant on each wall-complement component.  A component containing a member
with one exterior root is a Pisot chamber; every member of such a chamber has
one exterior root, and an integral correction has a monic irreducible Pisot
factor after removal of a power of `z`. -/
def claim25790 : Prop :=
  ∀ (n : ℕ) (R ell : Polynomial ℤ),
    (isSalemPolynomial R n ∧ traceLift R ell n) →
      (∀ S : Set (Fin n → ℝ),
        connectedComponent (wallComplement (traceToReal ell)) S →
          ∀ v w : Fin n → ℝ, v ∈ S → w ∈ S →
            ∀ qv Av qw Aw : Polynomial ℝ,
              affineBoydFormula n (traceToReal ell) (correctionPolynomial v) qv Av →
                affineBoydFormula n (traceToReal ell) (correctionPolynomial w) qw Aw →
                outsideRootCount Av = outsideRootCount Aw) ∧
      (∀ S : Set (Fin n → ℝ),
        connectedComponent (wallComplement (traceToReal ell)) S →
          containsOneExteriorMember (traceToReal ell) S →
            pisotChamber n (traceToReal ell) S) ∧
      (∀ S : Set (Fin n → ℝ),
        pisotChamber n (traceToReal ell) S →
          (∀ v : Fin n → ℝ, v ∈ S →
            ∀ q A : Polynomial ℝ,
              affineBoydFormula n (traceToReal ell) (correctionPolynomial v) q A →
                outsideRootCount A = 1) ∧
          (∀ v : Fin n → ℝ, v ∈ S →
            integralPolynomial (correctionPolynomial v) →
              ∀ q A : Polynomial ℝ,
                affineBoydFormula n (traceToReal ell) (correctionPolynomial v) q A →
                  ∃ k : ℕ, ∃ p : Polynomial ℤ,
                    A.map (algebraMap ℝ ℂ) =
                      (Polynomial.X : Polynomial ℂ) ^ k *
                        p.map (algebraMap ℤ ℂ) ∧
                      LehmerMinimum25803.pisotPolynomial p))

end MathlibPlus.Open.ResearchFormalization.R0466

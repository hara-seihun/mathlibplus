import MathlibPlus.Open.ResearchFormalization.BoydWeights25796

open scoped BigOperators
open Polynomial

namespace MathlibPlus.Open.ResearchFormalization.R0466Claim25820

noncomputable section

open MathlibPlus.Open.ResearchFormalization
open MathlibPlus.Open.ResearchFormalization.BoydWeights25796

/-- The explicit reciprocal lift of a degree-at-most-`m` trace polynomial. -/
noncomputable def reciprocalLift (m : ℕ) (d : Polynomial ℤ) : Polynomial ℤ :=
  Finset.sum (Finset.range (m + 1)) (fun k =>
    Finset.sum (Finset.range (k + 1)) (fun j =>
      Polynomial.C (d.coeff k * (Nat.choose k j : ℤ)) *
        Polynomial.X ^ (m + k - 2 * j)))

/-- Record 33's central interlacer data, retaining the Salem trace, the
actual Boyd chamber, the central correction `c=t d`, and the degree gap. -/
def record33Interlacer
    (n : ℕ) (R ell d : Polynomial ℤ)
    (u : Fin (n - 1) → ℝ) : Prop :=
  2 ≤ n ∧
    isSalemPolynomial R n ∧
    traceLift R ell n ∧
    completeInteriorTraceRoots n (traceToReal ell) u ∧
    d.Monic ∧
    d.natDegree ≤ n - 2 ∧
    let c : Polynomial ℝ :=
      Polynomial.X * d.map (algebraMap ℤ ℝ)
    ∃ S : Set (Fin n → ℝ),
      coefficientVector c ∈ S ∧
        pisotChamber n (traceToReal ell) S ∧
          ∃ q A : Polynomial ℝ,
            affineBoydFormula n (traceToReal ell) c q A

private def allRootsOnUnitCircle (D : Polynomial ℤ) : Prop :=
  ∀ z : ℂ, evalIntComplex D z = 0 → ‖z‖ = 1

private def cyclotomicProduct (D : Polynomial ℤ) : Prop :=
  ∃ s : Multiset ℕ,
    D = (s.map (fun n => Polynomial.cyclotomic n ℤ)).prod

/-- A monic integral interlacer lifts by the displayed reciprocal formula to a
monic integral polynomial with unit-circle roots, hence a cyclotomic product. -/
def claim25820 : Prop :=
  ∀ (n : ℕ) (R ell d : Polynomial ℤ)
    (u : Fin (n - 1) → ℝ),
    record33Interlacer n R ell d u →
      let D := reciprocalLift (n - 2) d
      D.Monic ∧
        D.natDegree = 2 * (n - 2) ∧
        (∀ z : ℂ, z ≠ 0 →
          evalIntComplex D z =
            z ^ (n - 2) * evalIntComplex d (z + z⁻¹)) ∧
        allRootsOnUnitCircle D ∧
        cyclotomicProduct D

end

end MathlibPlus.Open.ResearchFormalization.R0466Claim25820

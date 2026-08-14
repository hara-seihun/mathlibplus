import Mathlib

open scoped BigOperators

namespace MathlibPlus
namespace Open
namespace Research

noncomputable section

abbrev PositiveNat := {n : ℕ // 0 < n}

abbrev RootPolynomial := MvPolynomial (Option ℕ) ℤ

private def rootShiftExponent (s : PositiveNat) (m : (Option ℕ) →₀ ℕ) : (Option ℕ) →₀ ℕ :=
  m - Finsupp.single none (m none) +
    Finsupp.single (some (m none + s.1 - 1)) 1

private def rootShiftMonomial (s : PositiveNat) (m : (Option ℕ) →₀ ℕ) : RootPolynomial :=
  MvPolynomial.monomial (rootShiftExponent s m) 1

private def rootShift (s : PositiveNat) : RootPolynomial →ₗ[ℤ] RootPolynomial :=
  { toFun := fun p =>
      Finsupp.linearCombination ℤ (rootShiftMonomial s) (AddMonoidAlgebra.coeff p)
    map_add' := by
      intro p q
      cases p
      cases q
      simp
    map_smul' := by
      intro c p
      cases p with
      | ofCoeff coeff =>
          change Finsupp.linearCombination ℤ (rootShiftMonomial s) (c • coeff) =
            c • Finsupp.linearCombination ℤ (rootShiftMonomial s) coeff
          exact (Finsupp.linearCombination ℤ (rootShiftMonomial s)).map_smul c coeff }

private def sourceDerivativeMonomial (t : ℤ) (m : (Option ℕ) →₀ ℕ) : RootPolynomial :=
  ∑ i ∈ m.support, match i with
    | none => 0
    | some j =>
        MvPolynomial.monomial (m - Finsupp.single (some j) 1)
          ((m (some j) : ℤ) * t ^ j)

private def sourceDerivative (t : ℤ) : RootPolynomial →ₗ[ℤ] RootPolynomial :=
  { toFun := fun p =>
      Finsupp.linearCombination ℤ (sourceDerivativeMonomial t) (AddMonoidAlgebra.coeff p)
    map_add' := by
      intro p q
      cases p
      cases q
      simp
    map_smul' := by
      intro c p
      cases p with
      | ofCoeff coeff =>
          change Finsupp.linearCombination ℤ (sourceDerivativeMonomial t) (c • coeff) =
            c • Finsupp.linearCombination ℤ (sourceDerivativeMonomial t) coeff
          exact (Finsupp.linearCombination ℤ (sourceDerivativeMonomial t)).map_smul c coeff }

private def substituteRoot (t : ℤ) : RootPolynomial →+* RootPolynomial :=
  MvPolynomial.eval₂Hom (MvPolynomial.C : ℤ →+* RootPolynomial)
    (fun i : Option ℕ => match i with
      | none => MvPolynomial.C t
      | some j => MvPolynomial.X (some j))

/-- Root-shift/source-derivative commutator for finite polynomials. -/
def rootShiftSourceDerivativeCommutator : Prop :=
  ∀ (t : ℤ) (s : PositiveNat) (H : RootPolynomial),
    sourceDerivative t (rootShift s H) - rootShift s (sourceDerivative t H) =
      (t ^ (s.1 - 1)) • substituteRoot t H

end

end Research
end Open
end MathlibPlus

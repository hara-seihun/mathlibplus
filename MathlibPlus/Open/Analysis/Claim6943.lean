import Mathlib

namespace MathlibPlus.Open.Analysis.Claim6943

open scoped BigOperators

noncomputable def localJetIdeal (m : ℕ) : Ideal (Polynomial ℂ) :=
  Ideal.span ({Polynomial.X ^ m} : Set (Polynomial ℂ))

abbrev localJet (m : ℕ) : Type := Polynomial ℂ ⧸ localJetIdeal m

noncomputable def localJetCoordinate (m : ℕ) : localJet m :=
  Ideal.Quotient.mk (localJetIdeal m) Polynomial.X

noncomputable def jetNilpotent (m : ℕ) : Module.End ℂ (localJet m) :=
  (Algebra.lmul ℂ (localJet m)) (localJetCoordinate m)

noncomputable def primePower (p : ℕ) (z : ℂ) : ℂ :=
  Complex.exp ((Real.log (p : ℝ) : ℂ) * z)

noncomputable def localJetExponential (p m : ℕ) : localJet m :=
  Finset.sum (Finset.range m) (fun k =>
    (((Real.log (p : ℝ) : ℂ) ^ k) / (k.factorial : ℂ)) •
      (localJetCoordinate m ^ k))

noncomputable def operatorExponential (p m : ℕ) : Module.End ℂ (localJet m) :=
  Finset.sum (Finset.range m) (fun k =>
    (((Real.log (p : ℝ) : ℂ) ^ k) / (k.factorial : ℂ)) •
      (jetNilpotent m ^ k))

noncomputable def primeJetAction (p : ℕ) (z : ℂ) (m : ℕ) : Module.End ℂ (localJet m) :=
  (Algebra.lmul ℂ (localJet m)) (primePower p z • localJetExponential p m)

noncomputable def primeActionOnLocalJet : Prop :=
  ∀ (p : ℕ), p.Prime → ∀ (z : ℂ) (m : ℕ), 0 < m →
    primeJetAction p z m = primePower p z • operatorExponential p m ∧
      jetNilpotent m ^ m = 0 ∧
      Module.finrank ℂ (localJet m) = m ∧
      jetNilpotent m ^ (m - 1) ≠ 0

end MathlibPlus.Open.Analysis.Claim6943

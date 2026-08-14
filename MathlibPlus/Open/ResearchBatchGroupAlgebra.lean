import Mathlib

namespace MathlibPlus.Open.ResearchBatchGroupAlgebra

noncomputable section

abbrev baseGroup (r : ℕ) := ZMod 4 × (Fin r → ZMod 3)
abbrev regularGroup (r : ℕ) := Multiplicative (baseGroup r)
abbrev groupAlgebra (r : ℕ) := MonoidAlgebra (ZMod 2) (regularGroup r)

def allOnes (r : ℕ) : groupAlgebra r :=
  MonoidAlgebra.ofCoeff
    (∑ g : regularGroup r, Finsupp.single g (1 : ZMod 2))

def coefficientSum (r : ℕ) (x : groupAlgebra r) : ZMod 2 :=
  ∑ g : regularGroup r, x.coeff g

def j2 (r : ℕ) : Submodule (ZMod 2) (groupAlgebra r) :=
  Submodule.span (ZMod 2) ({allOnes r} : Set (groupAlgebra r))

def annihilatorOfJ2 (r : ℕ) : Submodule (ZMod 2) (groupAlgebra r) :=
  LinearMap.ker ((Algebra.lmul (ZMod 2) (groupAlgebra r)) (allOnes r))

/-- Multiplication by the all-ones element and the resulting exact
augmentation-zero annihilator. -/
def groupAlgebraAnnihilatorClaim : Prop :=
  ∀ r : ℕ,
    (∀ x : groupAlgebra r,
      allOnes r * x = coefficientSum r x • allOnes r) ∧
      allOnes r * allOnes r = 0 ∧
      (∀ x : groupAlgebra r,
        x ∈ annihilatorOfJ2 r ↔ coefficientSum r x = 0) ∧
      Module.finrank (ZMod 2) (annihilatorOfJ2 r) = 4 * 3 ^ r - 1

end
end MathlibPlus.Open.ResearchBatchGroupAlgebra

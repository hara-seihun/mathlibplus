import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0982.Claim27879

noncomputable section

abbrev Plane (p : ℕ) := Fin 2 → ZMod p
abbrev SymmetricSquare (p : ℕ) := Fin 3 → ZMod p
abbrev QuotientCarrier (p : ℕ) := Plane p × Plane p

/-- The symmetric product r ⊙ lambda in the Record 12 quotient
coordinates. -/
def symmetricProduct {p : ℕ} (r lam : Plane p) : SymmetricSquare p :=
  ![r 0 * lam 0,
    r 0 * lam 1 + r 1 * lam 0,
    r 1 * lam 1]

/-- The Record 12 commutator form on the identified X/U carrier. -/
def commutatorForm {p : ℕ}
    (x y : QuotientCarrier p) : SymmetricSquare p :=
  symmetricProduct x.1 y.2 - symmetricProduct y.1 x.2

def isotropicSubspace {p : ℕ}
    (W : Submodule (ZMod p) (QuotientCarrier p)) : Prop :=
  ∀ u ∈ W, ∀ v ∈ W, commutatorForm u v = 0

def topProjectionKernelVanishes {p : ℕ}
    (W : Submodule (ZMod p) (QuotientCarrier p)) : Prop :=
  ∀ v : QuotientCarrier p, v ∈ W → v.1 = 0 → v = 0

/-- Claim 27879: isotropic subspaces of the Record 12 commutator quotient
have dimension at most two; a nonzero top direction has injective symmetric
multiplication and kills the top-projection kernel. -/
def claim27879_isotropicSubspaces : Prop :=
  ∀ (p : ℕ) (hp : Nat.Prime p), p % 2 = 1 →
    letI : Fact (Nat.Prime p) := ⟨hp⟩
    (∀ W : Submodule (ZMod p) (QuotientCarrier p),
      isotropicSubspace W →
        Module.finrank (ZMod p) W ≤ 2) ∧
      (∀ r : Plane p, r ≠ 0 →
        Function.Injective (fun lam : Plane p => symmetricProduct r lam)) ∧
      (∀ W : Submodule (ZMod p) (QuotientCarrier p),
        isotropicSubspace W →
          (∃ v : QuotientCarrier p, v ∈ W ∧ v.1 ≠ 0) →
            topProjectionKernelVanishes W)

end

end MathlibPlus.Open.ResearchFormalization.R0982.Claim27879

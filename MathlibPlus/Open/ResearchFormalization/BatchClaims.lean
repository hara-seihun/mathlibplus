import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.FinitePrimeLiGram

/-- The Taylor coefficient used by the finite-place Li sequence. -/
noncomputable def taylorCoefficient (f : ℂ → ℂ) (n : ℕ) : ℂ :=
  iteratedDeriv n f 0 / (n.factorial : ℂ)

/-- The finite Euler product in the admitted finite-prime Li construction. -/
noncomputable def finiteEulerProduct (P : Finset ℕ) (s : ℂ) : ℂ :=
  ∏ p ∈ P, (1 - (p : ℂ) ^ (-s))⁻¹

/-- The logarithmic generating function in the admitted finite-prime Li construction. -/
noncomputable def finiteLiGeneratingFunction (P : Finset ℕ) : ℂ → ℂ :=
  fun u => Complex.log (finiteEulerProduct P (1 / (1 - u)))

/-- The regularized finite-place Li sequence, with λ₀ = 0. -/
noncomputable def finitePrimeLi (P : Finset ℕ) (n : ℕ) : ℂ :=
  if n = 0 then 0
  else (n : ℂ) * taylorCoefficient (finiteLiGeneratingFunction P) n

/-- The Li--Gram kernel on natural indices. -/
noncomputable def finitePrimeLiGramKernel (P : Finset ℕ) (j k : ℕ) : ℂ :=
  finitePrimeLi P j + finitePrimeLi P k - finitePrimeLi P (Nat.dist j k)

/--
The admitted finite-prime Li--Gram definition, with the finite nonempty prime
carrier, the Euler-product/logarithmic coefficient construction of λ, and the
regularized natural-index kernel exposed in the statement itself.
-/
def finitePrimeLiGramKernel_claim10367 : Prop :=
  ∀ (P : Finset ℕ),
    P.Nonempty →
    (∀ p ∈ P, Nat.Prime p) →
      (let lambdaSeq : ℕ → ℂ := fun n =>
        if n = 0 then 0
        else
          (n : ℂ) *
            (iteratedDeriv n
              (fun u : ℂ =>
                Complex.log
                  (∏ p ∈ P, (1 - (p : ℂ) ^ (-(1 / (1 - u))))⁻¹))
              0 / (n.factorial : ℂ))
       ∃! K : ℕ → ℕ → ℂ,
         ∀ j k, K j k =
           lambdaSeq j + lambdaSeq k - lambdaSeq (Nat.dist j k))

end MathlibPlus.Open.FinitePrimeLiGram

namespace MathlibPlus.Open.RawA2Monodromy

/-- The two-state raw A₂ Milnor monodromy matrix. -/
def rawA2Monodromy : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(0 : ℂ), -1; 1, -1]

/-- The KSV coordinate length-two Jordan block. -/
def ksvCoordinateJordan : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(-3 : ℂ), 1; 0, -3]

/-- Eigenvalue for a complex two-state matrix, written with its eigenvector. -/
def matrixEigenvalue (A : Matrix (Fin 2) (Fin 2) ℂ) (μ : ℂ) : Prop :=
  ∃ v : Fin 2 → ℂ, v ≠ 0 ∧ A.mulVec v = μ • v

/-- A primitive cube root of unity, in the form used by the claim. -/
def primitiveCubeRoot (μ : ℂ) : Prop :=
  μ ^ 3 = 1 ∧ μ ≠ 1

/--
The raw A₂ monodromy has the stated cyclotomic polynomial and primitive-cube
spectrum, and is distinct from both the scalar and KSV Jordan modules.
-/
def rawA2Monodromy_claim10405 : Prop :=
  let M := rawA2Monodromy
  let J := ksvCoordinateJordan
  M ^ 2 + M + (1 : Matrix (Fin 2) (Fin 2) ℂ) = 0 ∧
    (∀ μ : ℂ, matrixEigenvalue M μ ↔ primitiveCubeRoot μ) ∧
    M ≠ (-3 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
    M ≠ J ∧
    ¬ ∃ S : Matrix (Fin 2) (Fin 2) ℂ,
      IsUnit S ∧ S * M = J * S

end MathlibPlus.Open.RawA2Monodromy

namespace MathlibPlus.Open.LiteralZetaRank

/-- The trivial-parameter local factor on the actual finite-dimensional carrier. -/
noncomputable def trivialParameterLocalFactor (Vμ : Type*) [AddCommGroup Vμ] [Module ℂ Vμ]
    [FiniteDimensional ℂ Vμ] (u : ℂ) : ℂ :=
  (LinearMap.det
    ((LinearMap.id : Vμ →ₗ[ℂ] Vμ) - u • (LinearMap.id : Vμ →ₗ[ℂ] Vμ)))⁻¹

/--
For the Satake representation carrier Vμ, equality with the literal degree-one
factor forces coefficient rank one.
-/
def literalZetaFactorForcesRankOne_claim10426 : Prop :=
  ∀ (Vμ : Type*) [AddCommGroup Vμ] [Module ℂ Vμ]
    [FiniteDimensional ℂ Vμ],
    (∀ u : ℂ, trivialParameterLocalFactor Vμ u = (1 - u)⁻¹) →
      Module.finrank ℂ Vμ = 1

end MathlibPlus.Open.LiteralZetaRank


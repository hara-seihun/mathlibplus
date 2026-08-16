import MathlibPlus.Open.RepresentationTheory.CoefficientRepresentationCharacterTableClaim14726

open scoped BigOperators

namespace MathlibPlus.Open.RepresentationTheory

noncomputable section

/- The ordered D8 class operators on the admitted coefficient carrier
   M_k = Sym^k(C^2) tensor Sym^k(C^2). -/
def coefficientClassOperator (k : ℕ) :
    Fin 8 → CoefficientMixedSpace k →ₗ[ℂ] CoefficientMixedSpace k :=
  let S := coefficientFactorSwap k
  let R := coefficientLeftReversal k
  let D := coefficientDoubleReversal k
  let r := S * R
  ![LinearMap.id, r, D, r ^ 3, S, D * S, R, D * R]

/- The character of M_k, in the class order
   (e,r,w0,r^3,s0,w0*s0,s1,w0*s1). -/
def coefficientCharacter (k : ℕ) : Fin 8 → ℂ :=
  fun c => coefficientTrace k (coefficientClassOperator k c)

/- The one-dimensional character whose generator values are (a,b). -/
def chiAB (a b : ℂ) : Fin 8 → ℂ :=
  ![1, a * b, 1, a * b, a, a, b, b]

/- The explicit two-dimensional irrep rho_2. Its generators have matrices
   diag(1,-1) and [[0,1],[1,0]], so its ordered character is
   (2,0,-2,0,0,0,0,0). -/
def rhoS₀ : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if i = j then if i.1 = 0 then 1 else -1 else 0

def rhoS₁ : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if (i.1 = 0 ∧ j.1 = 1) ∨ (i.1 = 1 ∧ j.1 = 0) then 1 else 0

def rhoTwoClassMatrix : Fin 8 → Matrix (Fin 2) (Fin 2) ℂ :=
  let r := rhoS₀ * rhoS₁
  let w := r ^ 2
  ![1, r, w, r ^ 3, rhoS₀, w * rhoS₀, rhoS₁, w * rhoS₁]

def rhoTwoCharacter : Fin 8 → ℂ :=
  fun c => Matrix.trace (rhoTwoClassMatrix c)

/- Character inner products in the ordered eight-element D8 character table. -/
def characterInnerProduct (χ ψ : Fin 8 → ℂ) : ℂ :=
  (∑ c : Fin 8, χ c * ψ c) / 8

def oneDimensionalMultiplicity (k : ℕ) (a b : ℂ) : ℂ :=
  characterInnerProduct (coefficientCharacter k) (chiAB a b)

def rhoMultiplicity (k : ℕ) : ℂ :=
  characterInnerProduct (coefficientCharacter k) rhoTwoCharacter

/- Here n=k+1 and j is 1 in even degree and 0 in odd degree, as in the
   admitted coefficient character table. -/
def allDegreeIrreducibleMultiplicities_claim14727 : Prop :=
  ∀ (k : ℕ) (a b : ℂ),
    (a = 1 ∨ a = -1) → (b = 1 ∨ b = -1) →
      oneDimensionalMultiplicity k a b =
          (let n : ℂ := (k + 1 : ℕ)
           let j : ℂ := if Even k then 1 else 0
           (n ^ 2 + j ^ 2 + 2 * j * a * b + 2 * n * a + 2 * n * j * b) / 8) ∧
        rhoMultiplicity k =
          (let n : ℂ := (k + 1 : ℕ)
           let j : ℂ := if Even k then 1 else 0
           (n ^ 2 - j ^ 2) / 4)

end

end MathlibPlus.Open.RepresentationTheory

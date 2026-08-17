import Mathlib
import MathlibPlus.Algebra.Claim18397MixedGram

namespace MathlibPlus.Open.Algebra

/-- The connection matrix whose entries are the admitted mixed moments. -/
def connectionMatrix_claim18392
    {α R : Type*} [Mul α] [CommRing R]
    (C : α → R) (π : ℕ → α) : Matrix ℕ ℕ R :=
  fun i j => MathlibPlus.Algebra.mixedGramEntry_claim18397 C π i j

/-- The solid consecutive-row/consecutive-column minor of the connection matrix. -/
def solidConnectionMinor_claim18393
    {α R : Type*} [Mul α] [CommRing R]
    (C : α → R) (π : ℕ → α) (i j k : ℕ) : R :=
  Matrix.det (fun r s : Fin k =>
    connectionMatrix_claim18392 C π (i + r.1) (j + s.1))

/-- Claim 18393: the mixed Gram field is the displayed solid minor. -/
def mixedGramField_claim18393 : Prop :=
  ∀ {α R : Type*} [Mul α] [CommRing R]
    (C : α → R) (π : ℕ → α) (i j k : ℕ),
    MathlibPlus.Algebra.mixedGramField_claim18397 C π i j k =
        Matrix.det (fun r s : Fin k =>
          C (π (i + r.1) * π (j + s.1))) ∧
      MathlibPlus.Algebra.mixedGramField_claim18397 C π i j k =
        solidConnectionMinor_claim18393 C π i j k

/-- Claim 18394: every solid connection minor equals the mixed Gram field. -/
def everySolidConnectionMinorIsMixedGram_claim18394 : Prop :=
  ∀ {α R : Type*} [Mul α] [CommRing R]
    (C : α → R) (π : ℕ → α) (i j k : ℕ),
    solidConnectionMinor_claim18393 C π i j k =
      MathlibPlus.Algebra.mixedGramField_claim18397 C π i j k

end MathlibPlus.Open.Algebra

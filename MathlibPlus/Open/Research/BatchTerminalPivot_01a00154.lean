import Mathlib

namespace MathlibPlus.Open.Research

def claim_43646 : Prop :=
  ∀ {n : ℕ}
    (A : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (b : ℝ → (Fin n → ℝ))
    (c : ℝ → ℝ)
    (K : ℝ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (K' : ℝ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ),
    (∀ t, Matrix.PosDef (A t)) →
    (∀ t, HasDerivAt K (K' t) t) →
    (∀ t,
      (∀ i j, K t (Fin.castSucc i) (Fin.castSucc j) = A t i j) ∧
      (∀ i, K t (Fin.castSucc i) (Fin.last n) = b t i) ∧
      (∀ i, K t (Fin.last n) (Fin.castSucc i) = b t i) ∧
      K t (Fin.last n) (Fin.last n) = c t) →
    let q : ℝ → (Fin (n + 1) → ℝ) :=
      fun t => Fin.snoc (-(Matrix.mulVec (A t)⁻¹ (b t))) 1
    let pN : ℝ → ℝ :=
      fun t => c t - dotProduct (b t) (Matrix.mulVec (A t)⁻¹ (b t))
    ∀ t, HasDerivAt pN
      (dotProduct (q t) (Matrix.mulVec (K' t) (q t))) t

end MathlibPlus.Open.Research

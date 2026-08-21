import Mathlib

open Polynomial

namespace MathlibPlus.Algebra.Claim50397

/-- The coefficient-Frobenius power identity, injectivity, and derivative compatibility
for polynomials over a reduced commutative ring of characteristic two. -/
theorem coefficientFrobeniusIdentities
    {K : Type*} [CommRing K] [IsReduced K] [CharP K 2] (τ : ℕ) (P : K[X]) :
    let q := 2 ^ τ
    let Φ : K[X] →+* K[X] := Polynomial.mapRingHom (iterateFrobenius K 2 τ)
    (∀ r : K, (P.eval r) ^ q = (Φ P).eval (r ^ q)) ∧
      Function.Injective Φ ∧
      Polynomial.derivative (Φ P) = Φ (Polynomial.derivative P) := by
  let q := 2 ^ τ
  let Φ : K[X] →+* K[X] := Polynomial.mapRingHom (iterateFrobenius K 2 τ)
  dsimp only
  have hpow : Polynomial.map (iterateFrobenius K 2 τ) ((Polynomial.expand K q) P) = P ^ q := by
    exact Polynomial.map_iterateFrobenius_expand 2 P τ
  have hcomm : Polynomial.map (iterateFrobenius K 2 τ) ((Polynomial.expand K q) P) =
      Polynomial.expand K q (Polynomial.map (iterateFrobenius K 2 τ) P) := by
    rw [Polynomial.map_expand]
  have hpoly : P ^ q = Polynomial.expand K q (Polynomial.map (iterateFrobenius K 2 τ) P) := by
    rw [← hpow, hcomm]
  refine ⟨?_, ?_, ?_⟩
  · intro r
    change (P.eval r) ^ q =
      (Polynomial.map (iterateFrobenius K 2 τ) P).eval (r ^ q)
    rw [← Polynomial.eval_pow]
    rw [hpoly, Polynomial.expand_eval]
  · simpa [Φ] using Polynomial.map_injective _ (iterateFrobenius_inj K 2 τ)
  · simpa [Φ] using Polynomial.derivative_map P (iterateFrobenius K 2 τ)

end MathlibPlus.Algebra.Claim50397

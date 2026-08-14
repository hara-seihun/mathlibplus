import Mathlib

namespace MathlibPlus.Open.Algebra.SolidCompanionBatch

/-- Claim 18705: the grouped Sylvester packet factors by Desnanot--Jacobi.
The contiguous block is indexed by the exact endpoint carrier `Fin k`. -/
def desnanotJacobiPacketFactorization : Prop :=
  ∀ {R : Type*} [CommRing R] (A : ℕ → ℕ → R) (p q k : ℕ),
    2 ≤ k →
      let D : ℕ → ℕ → ℕ → R := fun p q k ↦
        Matrix.det (fun i j : Fin k ↦ A (p + i.val) (q + j.val))
      D p q (k - 1) * D (p + 1) (q + 1) (k - 1) -
          D (p + 1) q (k - 1) * D p (q + 1) (k - 1) =
        D p q k * D (p + 1) (q + 1) (k - 2)

/-- Claim 18706: the one-row extension identity at the origin. -/
def oneRowExtensionIdentity : Prop :=
  ∀ {R : Type*} [CommRing R] (A : ℕ → ℕ → R) (d : ℕ),
    1 ≤ d →
      let D : ℕ → ℕ → ℕ → R := fun p q k ↦
        Matrix.det (fun i j : Fin k ↦ A (p + i.val) (q + j.val))
      D 0 0 (d + 1) * D 1 1 (d - 1) =
        D 0 0 d * D 1 1 d - D 1 0 d * D 0 1 d

end MathlibPlus.Open.Algebra.SolidCompanionBatch

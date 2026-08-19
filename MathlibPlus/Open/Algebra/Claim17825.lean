import Mathlib

namespace MathlibPlus.Open.Algebra

/-- Claim 17825: a pure `r`-cell multilinear construction has degree `r`
under common scaling, and a fixed linear functional preserves that degree. -/
def claim_17825_wedge_homogeneous
    {R : Type _} {M : Type _} {N : Type _} [CommSemiring R]
    [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N]
    (r : ℕ) (W : MultilinearMap R (fun _ : Fin r => M) N)
    (φ : LinearMap (RingHom.id R) N R) (h : M) (c : R) : Prop :=
  W (fun _ : Fin r => c • h) = c ^ r • W (fun _ : Fin r => h) ∧
    φ (W (fun _ : Fin r => c • h)) =
      c ^ r * φ (W (fun _ : Fin r => h))

end MathlibPlus.Open.Algebra

import Mathlib
import MathlibPlus.Open.ResearchFormalization.R1212

namespace MathlibPlus.Open.ResearchFormalization.R1212Claim32303

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R1212

noncomputable def inverseClosed (S : Set (ProductGroup p)) : Prop :=
  ∀ x, x ∈ S → x⁻¹ ∈ S

def cayleyIsomorphismToImage
    {p : ℕ} (S : Set (ProductGroup p))
    (f : Equiv.Perm (ProductGroup p)) : Prop :=
  ∀ x y : ProductGroup p,
    (x⁻¹ * y ∈ S ↔
      (f x)⁻¹ * (f y) ∈ f '' S)

/-- Claim 32303: under the exact singleton-nonlinear A4 chart profile, an
ordinary Cayley-graph isomorphism with inverse-closed image is transported by
a product automorphism, so this branch is CI-harmless. -/
def oneNontranslationChartOrdinaryCIHarmless_claim32303 : Prop :=
  ∀ (p : ℕ), Nat.Prime p → 5 ≤ p →
    ∀ (q : Equiv.Perm A4) (σ : A4 → Equiv.Perm (ZMod p))
      (f : Equiv.Perm (ProductGroup p)),
      oneNonlinearCommonCoordinateProfile_claim32296 q σ f →
      ∀ S : Set (ProductGroup p),
        inverseClosed S →
        inverseClosed (f '' S) →
        cayleyIsomorphismToImage S f →
        ∃ α : ProductGroup p ≃* ProductGroup p,
          α '' S = f '' S

end

end MathlibPlus.Open.ResearchFormalization.R1212Claim32303

namespace MathlibPlus.Algebra.Claim36511

/-- Claim 36511: the four crossed normalizations satisfy the displayed
Pluecker-type syzygy. -/
def crossedNormalizationSyzygy_claim36511 {R : Type*} [CommRing R] : Prop :=
  ∀ (a b c d p q r s z : R),
    let K_pr : R := z * (p * q - r * s) + p * (b - c) + r * (a - d)
    let K_ps : R := z * (p * q - r * s) + p * (b - d) + s * (a - c)
    let K_qr : R := z * (p * q - r * s) + q * (a - c) + r * (b - d)
    let K_qs : R := z * (p * q - r * s) + q * (a - d) + s * (b - c)
    (b - d) * K_pr + (c - b) * K_ps +
        (d - a) * K_qr + (a - c) * K_qs = 0

end MathlibPlus.Algebra.Claim36511

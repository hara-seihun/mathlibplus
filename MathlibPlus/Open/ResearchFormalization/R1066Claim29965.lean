import Mathlib
import MathlibPlus.Open.ResearchFormalization.ProfileClaims

namespace MathlibPlus.Open.ResearchFormalization.R1066Claim29965

abbrev BaseA := Fin 3 → ZMod 2
abbrev BaseH := Multiplicative (Fin 2 → ZMod 3)
abbrev ProductG := BaseA × BaseH

structure TriangularPresentation where
  q : BaseH → Equiv.Perm BaseA
  sigma : Equiv.Perm BaseH

/-- Record 1 normalization and the one-active-fibre condition. -/
def normalizedOneActive (T : TriangularPresentation) : Prop :=
  T.sigma 1 = 1 ∧
    T.q 1 = Equiv.refl BaseA ∧
      ∀ h₁ h₂ : BaseH,
        h₁ ≠ 1 → T.q h₁ ≠ Equiv.refl BaseA →
          h₂ ≠ 1 → T.q h₂ ≠ Equiv.refl BaseA → h₁ = h₂

def triangularMap (T : TriangularPresentation) : ProductG → ProductG :=
  fun z => (T.q z.2 z.1, T.sigma z.2)

/-- Inverse-closedness for the ordinary undirected Cayley connection sets. -/
def inverseClosed (S : Set ProductG) : Prop :=
  ∀ x, x ∈ S ↔ (-x.1, x.2⁻¹) ∈ S

/-- The normalized relative-derivative invariance used by Record 1. -/
def derivativeInvariant (T : TriangularPresentation)
    (S : Set ProductG) : Prop :=
  MathlibPlus.Open.ResearchFormalization.ProfileClaims.derivativeInvariant T.q S

/-- Transport by a product automorphism from `GL(3,2) × GL(2,3)`. -/
def productAutomorphismCarries (T : TriangularPresentation)
    (S : Set ProductG) : Prop :=
  ∃ (φA : BaseA ≃+ BaseA) (φH : BaseH ≃* BaseH),
    Set.image (fun z : ProductG => (φA z.1, φH z.2)) S =
      triangularMap T '' S

/-- Claim 29965: every normalized presentation with at most one active
nonidentity fibre is harmless for ordinary undirected CI. -/
def claim_29965 : Prop :=
  ∀ T : TriangularPresentation,
    normalizedOneActive T →
      ∀ S : Set ProductG,
        S ⊆ {x : ProductG | x ≠ (0, 1)} →
          inverseClosed S →
            inverseClosed (triangularMap T '' S) →
              derivativeInvariant T S →
                productAutomorphismCarries T S

end MathlibPlus.Open.ResearchFormalization.R1066Claim29965

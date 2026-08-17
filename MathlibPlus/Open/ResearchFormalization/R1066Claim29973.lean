import Mathlib
import MathlibPlus.Open.ResearchFormalization.ProfileClaims

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R1066

abbrev BaseA := Fin 3 → ZMod 2
abbrev BaseH := Multiplicative (Fin 2 → ZMod 3)
abbrev ProductG := BaseA × BaseH

structure TriangularPresentation where
  q : BaseH → Equiv.Perm BaseA
  sigma : Equiv.Perm BaseH

private def normalizedPresentation (T : TriangularPresentation) : Prop :=
  T.sigma 1 = 1 ∧
    T.q 1 = Equiv.refl BaseA

private def triangularMap (T : TriangularPresentation) : ProductG → ProductG :=
  fun z => (T.q z.2 z.1, T.sigma z.2)

private noncomputable def activeFiberCount (T : TriangularPresentation) : ℕ :=
  letI := Classical.decEq BaseH
  (Finset.univ.filter (fun h => h ≠ 1 ∧ T.q h ≠ Equiv.refl BaseA)).card

private def inverseClosed (S : Set ProductG) : Prop :=
  ∀ x, x ∈ S ↔ (-x.1, x.2⁻¹) ∈ S

private def derivativeInvariant (T : TriangularPresentation)
    (S : Set ProductG) : Prop :=
  MathlibPlus.Open.ResearchFormalization.ProfileClaims.derivativeInvariant T.q S

private def triangularHarmless (T : TriangularPresentation) : Prop :=
  ∀ (S : Set ProductG),
    S ⊆ {x : ProductG | x ≠ (0, 1)} →
      inverseClosed S →
        inverseClosed (triangularMap T '' S) →
          derivativeInvariant T S →
            ∃ (φA : BaseA ≃+ BaseA) (φH : BaseH ≃* BaseH),
              Set.image (fun z : ProductG => (φA z.1, φH z.2)) S =
                triangularMap T '' S

/-- Claim 29973: the at-most-one-active-fibre closure and the separate
activation consequence for every normalized non-harmless presentation. -/
def supportAtMostOneTriangularMechanisms_claim29973 : Prop :=
  ∀ T : TriangularPresentation,
    normalizedPresentation T →
      ((activeFiberCount T ≤ 1 → triangularHarmless T) ∧
        (¬ triangularHarmless T → 2 ≤ activeFiberCount T))

end MathlibPlus.Open.ResearchFormalization.R1066

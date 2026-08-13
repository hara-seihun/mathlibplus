import Mathlib

namespace MathlibPlus.Open.GroupTheory

/--
Claim 51546.  A finite affine action of a finite group on a nonempty finite
abelian torsor has a fixed point when the two cardinalities are coprime.  The
second conjunct retains the stated cocycle certificate: for every base point,
the displacement is the coboundary of the averaged displacement and the
corresponding translated point is fixed.
-/
def coprimeAffineTorsorFixedPoint_claim51546 : Prop :=
  ∀ (H D T : Type*) [Fintype H] [Group H] [Fintype D] [AddCommGroup D]
    [Fintype T] [AddTorsor D T] [DistribMulAction H D] [MulAction H T],
    (∀ (h : H) (d : D) (t : T),
      h • (d +ᵥ t) = (h • d) +ᵥ (h • t)) →
    Nat.Coprime (Fintype.card H) (Fintype.card D) →
    Nonempty T →
    (∃ t : T, ∀ h : H, h • t = t) ∧
      ∀ t : T,
        let z : H → D := fun h => (h • t) -ᵥ t
        let S : D := ∑ h : H, z h
        ∃ d : D,
          (Fintype.card H) • d = S ∧
            (∀ h : H, z h = d - h • d) ∧
              ∀ h : H, h • (d +ᵥ t) = d +ᵥ t

end MathlibPlus.Open.GroupTheory

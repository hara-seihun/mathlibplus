import Mathlib.GroupTheory.SpecificGroups.Dihedral

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0725Claim26810

noncomputable section

private def prismRotation (n : ℕ) (i : ZMod n) : DihedralGroup n :=
  DihedralGroup.r i

private def prismReflection (n : ℕ) : DihedralGroup n :=
  DihedralGroup.sr 0

private def prismMap (n : ℕ) : DihedralGroup n → DihedralGroup n
  | DihedralGroup.r i =>
      if Even i.val then DihedralGroup.r i else DihedralGroup.sr (i - 1)
  | DihedralGroup.sr i =>
      if Even i.val then DihedralGroup.sr (i - 1) else DihedralGroup.r i

private def prismSource (n : ℕ) : Set (DihedralGroup n) :=
  {prismRotation n 1, (prismRotation n 1)⁻¹, prismReflection n}

private def prismTarget (n : ℕ) : Set (DihedralGroup n) :=
  {prismReflection n,
    prismRotation n 1 * prismReflection n,
    (prismRotation n 1) ^ 2 * prismReflection n}

private def cayleyAdjacency {G : Type*} [Group G]
    (S : Set G) (x y : G) : Prop :=
  x⁻¹ * y ∈ S

private def cayleyGraphIsomorphism {G : Type*} [Group G]
    (S T : Set G) : Prop :=
  ∃ e : Equiv.Perm G,
    ∀ x y, cayleyAdjacency S x y ↔ cayleyAdjacency T (e x) (e y)

private def inverseClosed {G : Type*} [Group G]
    (S : Set G) : Prop :=
  ∀ x, x ∈ S → x⁻¹ ∈ S

private def prismParityForm {n : ℕ} (Φ : DihedralGroup n ≃ DihedralGroup n) : Prop :=
  (∀ i : ZMod n, Even i.val →
    Φ (prismRotation n i) = prismRotation n i ∧
    Φ (prismRotation n i * prismReflection n) =
      prismRotation n (i + 1) * prismReflection n) ∧
  (∀ i : ZMod n, Odd i.val →
    Φ (prismRotation n i) =
      prismRotation n (1 - i) * prismReflection n ∧
    Φ (prismRotation n i * prismReflection n) =
      prismRotation n (-i))

private def prismParityFunctionForm {n : ℕ} : Prop :=
  (∀ i : ZMod n, Even i.val →
    prismMap n (prismRotation n i) = prismRotation n i ∧
    prismMap n (prismRotation n i * prismReflection n) =
      prismRotation n (i + 1) * prismReflection n) ∧
  (∀ i : ZMod n, Odd i.val →
    prismMap n (prismRotation n i) =
      prismRotation n (1 - i) * prismReflection n ∧
    prismMap n (prismRotation n i * prismReflection n) =
      prismRotation n (-i))

/-- Claim 26810: the explicit parity map on the exact dihedral presentation is
    bijective and transports every basepoint Cayley adjacency. -/
def explicitPrismParityBijection_claim26810 : Prop :=
  ∀ n : ℕ, 2 ∣ n →
    ∃ Φ : DihedralGroup n ≃ DihedralGroup n,
      prismParityForm Φ ∧
      (∀ x, Φ x = prismMap n x) ∧
      (∀ x y, cayleyAdjacency (prismSource n) x y ↔
        cayleyAdjacency (prismTarget n) (Φ x) (Φ y))


end

end MathlibPlus.Open.ResearchFormalization.R0725Claim26810

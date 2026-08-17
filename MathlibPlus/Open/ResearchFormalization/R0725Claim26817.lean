import Mathlib.GroupTheory.SpecificGroups.Dihedral

namespace MathlibPlus.Open.ResearchFormalization.R0725Claim26817

noncomputable section

private def rotationSet (n : ℕ) : Set (DihedralGroup n) :=
  Set.range (DihedralGroup.r : ZMod n → DihedralGroup n)

private def rotation (n : ℕ) : DihedralGroup n :=
  DihedralGroup.r 1

private def reflection (n : ℕ) : DihedralGroup n :=
  DihedralGroup.sr 0

private def augmentedSource (n : ℕ) : Set (DihedralGroup n) :=
  let r := rotation n
  let s := reflection n
  let c := r ^ (n / 2)
  {r, r⁻¹, c, s}

private def augmentedTarget (n : ℕ) : Set (DihedralGroup n) :=
  let r := rotation n
  let s := reflection n
  let c := r ^ (n / 2)
  {c, s, r * s, r ^ 2 * s}

private def groupAutomorphismEquivalent {G : Type*} [Group G]
    (S T : Set G) : Prop :=
  ∃ α : G ≃* G, Set.image (fun x => α x) S = T

/-- Claim 26817: at every positive rotation order with four dividing n, the two
    augmented connection sets have different group-automorphism orbits. -/
def twoAugmentedConnectionSetsNotAutomorphismEquivalent_claim26817 : Prop :=
  ∀ n : ℕ, 4 ≤ n → 4 ∣ n →
    let r := rotation n
    let S := augmentedSource n
    let T := augmentedTarget n
    (Set.ncard (S ∩ rotationSet n) = 3) ∧
      (Set.ncard (T ∩ rotationSet n) = 1) ∧
      (∀ α : DihedralGroup n ≃* DihedralGroup n,
        Set.image (fun x => α x) (rotationSet n) = rotationSet n) ∧
      orderOf r = n ∧
      (∀ x, x ∈ T → orderOf x = 2) ∧
      ¬ groupAutomorphismEquivalent S T

end

end MathlibPlus.Open.ResearchFormalization.R0725Claim26817

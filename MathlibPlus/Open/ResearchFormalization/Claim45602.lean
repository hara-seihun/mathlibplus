import MathlibPlus.Open.ResearchBatch.Wreath

open Classical
attribute [local instance] Classical.propDecidable

namespace MathlibPlus.Open.ResearchFormalization.Claim45602

noncomputable section

open MathlibPlus.Open.ResearchBatch.Wreath

/-- A characteristic Hall factor is carried by the actual subgroup of the
full permutation action, has the displayed order, and is invariant under all
abstract automorphisms of that subgroup. -/
def characteristicHallFactor {G : Type*} [Fintype G] [Group G]
    (P : Subgroup G) (order : ℕ) : Prop :=
  Fintype.card P = order ∧
    ∀ φ : G ≃* G, ∀ x : G, x ∈ P ↔ φ x ∈ P

/-- The image of a subgroup under the actual block action, represented by
permutations of the block index set satisfying the defining product-action
formula. -/
def blockProjectionImage {Delta Lambda : Type*}
    (U : Subgroup (Equiv.Perm (wreathOmega Delta Lambda)))
    (P : Subgroup U) : Set (Equiv.Perm Delta) :=
  {σ | ∃ p : P, ∀ d : Delta, ∀ l : Lambda,
    (p.1.1 (d, l)).1 = σ d}

/-- Regularity of a permutation image, with uniqueness taken in the image
rather than among its lifts in the fibre wreath group. -/
def regularPermutationImage {Delta : Type*}
    (S : Set (Equiv.Perm Delta)) : Prop :=
  ∀ x y : Delta, ∃! s : S, s.1 x = y

/-- The actual restriction of a fibre subgroup to each fixed block. -/
def regularOnEveryFibre {Delta Lambda : Type*}
    (U : Subgroup (Equiv.Perm (wreathOmega Delta Lambda)))
    (Q : Subgroup U) : Prop :=
  ∀ d : Delta, ∀ x y : Lambda, ∃! q : Q,
    q.1.1 (d, x) = (d, y)

/-- The orbit of a block index under a permutation image. -/
def blockOrbit {Delta : Type*}
    (S : Set (Equiv.Perm Delta)) (d : Delta) : Set Delta :=
  {e | ∃ s : S, s.1 d = e}

/-- The number of distinct block orbits of a permutation image. -/
def blockOrbitCount {Delta : Type*} [Fintype Delta]
    (S : Set (Equiv.Perm Delta)) : ℕ :=
  Nat.card {O : Set Delta // ∃ d : Delta, blockOrbit S d = O}

/-- Claim 45602: the characteristic Hall factors of a regular copy in the
full-fibre wreath action force the stated block image, fibre kernel, and
coprime orbit count. -/
def claim45602 : Prop :=
  ∀ (A H Delta Lambda : Type*)
    [Fintype A] [Fintype H] [Fintype Delta] [Fintype Lambda]
    [CommGroup A] [Group H],
    Nat.Coprime (Fintype.card A) (Fintype.card H) →
      Fintype.card Delta = Fintype.card A →
      Fintype.card Lambda = Fintype.card H →
      ∀ U : Subgroup (Equiv.Perm (wreathOmega Delta Lambda)),
        regularWreathCopy (A := A) (H := H)
          (Delta := Delta) (Lambda := Lambda) U →
        ∀ P Q : Subgroup U,
          characteristicHallFactor P (Fintype.card A) →
          characteristicHallFactor Q (Fintype.card H) →
          let imageP := blockProjectionImage U P
          let imageQ := blockProjectionImage U Q
          regularPermutationImage imageP ∧
            imageQ = ({1} : Set (Equiv.Perm Delta)) ∧
            regularOnEveryFibre U Q ∧
            blockOrbitCount imageP ∣ Fintype.card A ∧
            blockOrbitCount imageP ∣ Fintype.card H ∧
            blockOrbitCount imageP = 1

end

end MathlibPlus.Open.ResearchFormalization.Claim45602

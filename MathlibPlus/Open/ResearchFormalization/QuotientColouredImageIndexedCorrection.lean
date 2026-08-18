import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.QuotientColouredImageIndexedCorrection

noncomputable section

/-- A subgroup of permutations is regular on the finite point set. -/
def regularPermutationSubgroup {Delta : Type*} [Fintype Delta]
    (P : Subgroup (Equiv.Perm Delta)) : Prop :=
  ∀ x y : Delta, ∃! g : P, (g : Equiv.Perm Delta) x = y

/-- The permutation group is elementary abelian of the displayed prime-field rank. -/
def regularElementaryAbelianRank {p d : ℕ} {Delta : Type*} [Fintype Delta]
    (P : Subgroup (Equiv.Perm Delta)) : Prop :=
  regularPermutationSubgroup P ∧
    Nonempty (P ≃* Multiplicative (Fin d → ZMod p))

/-- Conjugation of a permutation by another permutation. -/
def conjugatePermutation {Delta : Type*}
    (u g : Equiv.Perm Delta) : Equiv.Perm Delta :=
  u.symm.trans (g.trans u)

/-- Conjugacy of permutation subgroups by an explicit permutation. -/
def conjugatesPermutationSubgroups {Delta : Type*}
    (u : Equiv.Perm Delta)
    (P Q : Subgroup (Equiv.Perm Delta)) : Prop :=
  Set.image (conjugatePermutation u) (P : Set (Equiv.Perm Delta)) =
    (Q : Set (Equiv.Perm Delta))

/-- The image of a directed binary relation under a permutation of its points. -/
def permutationRelationImage {Delta : Type*}
    (u : Equiv.Perm Delta) (R : Set (Delta × Delta)) : Set (Delta × Delta) :=
  Set.image (fun z => (u z.1, u z.2)) R

/-- Invariance of a directed binary relation under a permutation subgroup. -/
def relationInvariantUnder {Delta : Type*}
    (P : Subgroup (Equiv.Perm Delta)) (R : Set (Delta × Delta)) : Prop :=
  ∀ g : P, permutationRelationImage (g : Equiv.Perm Delta) R = R

/-- A pointed regular-labeling bijection realizing a group isomorphism. -/
def pointedRegularLabeling {Delta : Type*}
    (base : Delta)
    (P Q : Subgroup (Equiv.Perm Delta))
    (beta : P ≃* Q) (f : Equiv.Perm Delta) : Prop :=
  f base = base ∧
    ∀ g : P,
      conjugatePermutation f (g : Equiv.Perm Delta) =
        (beta g : Equiv.Perm Delta)

/-- A coordinate chart for the regular P-copy, based at the pointed base. -/
def regularPCoordinate {p d : ℕ} {Delta : Type*} [Fintype Delta]
    (base : Delta) (P : Subgroup (Equiv.Perm Delta))
    (coord : (Fin d → ZMod p) ≃ Delta) : Prop :=
  ∃ e : P ≃* Multiplicative (Fin d → ZMod p),
    ∀ v : Fin d → ZMod p,
      coord v =
        ((e.symm (Multiplicative.ofAdd v) : P) : Equiv.Perm Delta) base

/-- The permutation of the point set represented in regular P-coordinates by a
linear automorphism of the coordinate vector space. -/
def coordinatePermutation {p d : ℕ} {Delta : Type*}
    (coord : (Fin d → ZMod p) ≃ Delta)
    (alpha : (Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p)) : Equiv.Perm Delta :=
  coord.symm.trans (alpha.toEquiv.trans coord)

/-- The directed colour for the quotient-difference coset `c + U`. -/
def quotientDifferenceColour {p d s : ℕ} {Delta : Type*}
    (coord : (Fin d → ZMod p) ≃ Delta)
    (U : Fin s → AddSubgroup (Fin d → ZMod p))
    (a : Fin s) (c : Fin d → ZMod p) : Set (Delta × Delta) :=
  {z | (coord.symm z.2 - coord.symm z.1) - c ∈ U a}

/-- Pointwise preservation of every displayed directed quotient-difference colour. -/
def fixesDisplayedColours {p d s : ℕ} {Delta : Type*}
    (coord : (Fin d → ZMod p) ≃ Delta)
    (U : Fin s → AddSubgroup (Fin d → ZMod p))
    (f : Equiv.Perm Delta) : Prop :=
  ∀ (a : Fin s) (c : Fin d → ZMod p),
    permutationRelationImage f (quotientDifferenceColour coord U a c) =
      quotientDifferenceColour coord U a c

/-- The correction `u = f alpha⁻¹`, written on the common point set. -/
def imageIndexedCorrection {p d : ℕ} {Delta : Type*}
    (coord : (Fin d → ZMod p) ≃ Delta)
    (f : Equiv.Perm Delta)
    (alpha : (Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p)) : Equiv.Perm Delta :=
  (coordinatePermutation coord alpha).symm.trans f

/-- Identity of a point-set permutation on every displayed coordinate quotient. -/
def inducesDisplayedQuotientIdentity {p d s : ℕ} {Delta : Type*}
    (coord : (Fin d → ZMod p) ≃ Delta)
    (U : Fin s → AddSubgroup (Fin d → ZMod p))
    (u : Equiv.Perm Delta) : Prop :=
  ∀ (a : Fin s) (x : Fin d → ZMod p),
    coord.symm (u (coord x)) - x ∈ U a

/-- Claim 61244: quotient-coloured image-indexed correction. -/
def quotientColouredImageIndexedCorrectionClaim61244 : Prop :=
  ∀ (p d : ℕ), Nat.Prime p → 1 ≤ d → d ≤ 3 →
    ∀ (Delta : Type*) [Fintype Delta] (base : Delta)
      (P Q : Subgroup (Equiv.Perm Delta)),
      regularElementaryAbelianRank (p := p) (d := d) P →
      regularElementaryAbelianRank (p := p) (d := d) Q →
      ∀ (coord : (Fin d → ZMod p) ≃ Delta),
        regularPCoordinate base P coord →
        ∀ (t : ℕ) (O : Fin t → Set (Delta × Delta)),
          (∀ j : Fin t,
            relationInvariantUnder P (O j) ∧
              relationInvariantUnder Q (O j)) →
          ∀ (s : ℕ)
            (U : Fin s → AddSubgroup (Fin d → ZMod p)),
            ∀ (beta : P ≃* Q) (f : Equiv.Perm Delta),
              pointedRegularLabeling base P Q beta f →
              fixesDisplayedColours coord U f →
              ∃ alpha : (Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p),
                let u := imageIndexedCorrection coord f alpha
                conjugatesPermutationSubgroups u P Q ∧
                  (∀ j : Fin t, permutationRelationImage u (O j) = O j) ∧
                  fixesDisplayedColours coord U u ∧
                  (∀ (a : Fin s) (x : Fin d → ZMod p),
                    alpha x - x ∈ U a) ∧
                  inducesDisplayedQuotientIdentity coord U u

end

end MathlibPlus.Open.ResearchFormalization.QuotientColouredImageIndexedCorrection

import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.ImageIndexedRegularLabeling

noncomputable section

/-- A subgroup of permutations is regular on the finite point set. -/
def regularPermutationSubgroup {Delta : Type*} [Fintype Delta]
    (P : Subgroup (Equiv.Perm Delta)) : Prop :=
  ∀ x y : Delta, ∃! g : P, (g : Equiv.Perm Delta) x = y

/-- The elementary-abelian group of the indicated prime-field rank. -/
def regularElementaryAbelianRank {Delta : Type*} [Fintype Delta]
    (p d : ℕ) (P : Subgroup (Equiv.Perm Delta)) : Prop :=
  regularPermutationSubgroup P ∧
    Nonempty (P ≃* Multiplicative (Fin d → ZMod p))

/-- Conjugation of a permutation subgroup by an explicit permutation. -/
def conjugatePermutation {Delta : Type*}
    (u g : Equiv.Perm Delta) : Equiv.Perm Delta :=
  u.symm.trans (g.trans u)

def conjugatesPermutationSubgroups {Delta : Type*}
    (u : Equiv.Perm Delta)
    (P Q : Subgroup (Equiv.Perm Delta)) : Prop :=
  Set.image (conjugatePermutation u) (P : Set (Equiv.Perm Delta)) =
    (Q : Set (Equiv.Perm Delta))

/-- The image of a directed binary relation under a permutation of its points. -/
def relationImage {Delta : Type*}
    (u : Equiv.Perm Delta) (R : Set (Delta × Delta)) : Set (Delta × Delta) :=
  Set.image (fun x => (u x.1, u x.2)) R

def relationInvariantUnder {Delta : Type*}
    (P : Subgroup (Equiv.Perm Delta)) (R : Set (Delta × Delta)) : Prop :=
  ∀ g : P, relationImage (g : Equiv.Perm Delta) R = R

/-- A pointed regular-labeling bijection realizing a fixed group isomorphism. -/
def pointedRegularLabeling {Delta : Type*}
    (base : Delta)
    (P Q : Subgroup (Equiv.Perm Delta))
    (e : P ≃* Q) (f : Equiv.Perm Delta) : Prop :=
  f base = base ∧
    ∀ g : P,
      conjugatePermutation f (g : Equiv.Perm Delta) =
        (e g : Equiv.Perm Delta)

def regularTupleTransport {t : ℕ} {Delta : Type*} [Fintype Delta]
    (base : Delta) (P Q : Subgroup (Equiv.Perm Delta))
    (O : Fin t → Set (Delta × Delta)) : Prop :=
  ∃ u : Equiv.Perm Delta,
    u base = base ∧
      conjugatesPermutationSubgroups u P Q ∧
        ∀ j : Fin t, relationImage u (O j) = O j

/-- Scalar multiplication in the elementary coordinates. -/
def scalarVector {p d : ℕ}
    (a : (ZMod p)ˣ) (v : Fin d → ZMod p) : Fin d → ZMod p :=
  fun i => (a : ZMod p) * v i

/-- A coordinate chart obtained from a regular elementary-abelian copy. -/
def regularElementaryCoordinate {Delta : Type*} [Fintype Delta]
    (p d : ℕ) (base : Delta)
    (P : Subgroup (Equiv.Perm Delta))
    (coord : (Fin d → ZMod p) ≃ Delta) : Prop :=
  ∃ e : P ≃* Multiplicative (Fin d → ZMod p),
    ∀ v : Fin d → ZMod p,
      coord v = ((e.symm (Multiplicative.ofAdd v) : P) : Equiv.Perm Delta) base

/-- The scalar-stabilizer strengthening of the regular tuple transport. -/
def commonScalarTransport {p d t : ℕ} {Delta : Type*} [Fintype Delta]
    (base : Delta) (P Q : Subgroup (Equiv.Perm Delta))
    (O : Fin t → Set (Delta × Delta))
    (f : Equiv.Perm Delta) : Prop :=
  ∀ (K : Subgroup (Equiv.Perm Delta))
    (sigma : K →* (ZMod p)ˣ)
    (coordP coordQ : (Fin d → ZMod p) ≃ Delta),
    regularElementaryCoordinate p d base P coordP →
    regularElementaryCoordinate p d base Q coordQ →
    (∀ k : K, ∀ v : Fin d → ZMod p,
      (k : Equiv.Perm Delta) (coordP v) =
        coordP (scalarVector (sigma k) v)) →
    (∀ k : K, ∀ v : Fin d → ZMod p,
      (k : Equiv.Perm Delta) (coordQ v) =
        coordQ (scalarVector (sigma k) v)) →
    (∀ k : K, ∀ j : Fin t,
      relationImage (k : Equiv.Perm Delta) (O j) = O j) →
    (∀ k : K, ∀ x : Delta,
      f ((k : Equiv.Perm Delta) x) =
        (k : Equiv.Perm Delta) (f x)) →
    ∃ u : Equiv.Perm Delta,
      u base = base ∧
        conjugatesPermutationSubgroups u P Q ∧
          (∀ j : Fin t, relationImage u (O j) = O j) ∧
            (∀ k : K, ∀ x : Delta,
              u ((k : Equiv.Perm Delta) x) =
                (k : Equiv.Perm Delta) (u x))

/-- Claim 61218: image-indexed regular-labeling correction. -/
def imageIndexedRegularLabelingCorrectionClaim61218 : Prop :=
  ∀ (p d : ℕ), Nat.Prime p → 1 ≤ d → d ≤ 3 →
    ∀ (Delta : Type*) [Fintype Delta] (base : Delta)
      (P Q : Subgroup (Equiv.Perm Delta)),
      regularElementaryAbelianRank p d P →
      regularElementaryAbelianRank p d Q →
      ∀ (t : ℕ) (O : Fin t → Set (Delta × Delta)),
        (∀ j : Fin t,
          relationInvariantUnder P (O j) ∧
            relationInvariantUnder Q (O j)) →
        ∀ (e : P ≃* Q) (f : Equiv.Perm Delta),
          pointedRegularLabeling base P Q e f →
            regularTupleTransport base P Q O ∧
              commonScalarTransport (p := p) (d := d) (t := t) base P Q O f

end

end MathlibPlus.Open.ResearchFormalization.ImageIndexedRegularLabeling

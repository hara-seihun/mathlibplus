import Mathlib

open scoped BigOperators
open Classical
noncomputable section

namespace MathlibPlus.Open.Research.ProjectiveProfiles

abbrev BVec (p : ℕ) := Fin (p + 1) → ZMod p
abbrev VVec (p : ℕ) := Fin (p + 2) → ZMod p

 def bBasis (p : ℕ) (i : Fin (p + 1)) : BVec p :=
  fun j => if j = i then 1 else 0

 def vBasis (p : ℕ) (j : Fin (p + 2)) : VVec p :=
  fun k => if k = j then 1 else 0

 def bSum (p : ℕ) : BVec p := ∑ i : Fin (p + 1), bBasis p i

 def vSum (p : ℕ) : VVec p := ∑ j : Fin (p + 2), vBasis p j

 def bLine (p : ℕ) (v : BVec p) : Submodule (ZMod p) (BVec p) :=
  Submodule.span (ZMod p) ({v} : Set (BVec p))

 def vLine (p : ℕ) (v : VVec p) : Submodule (ZMod p) (VVec p) :=
  Submodule.span (ZMod p) ({v} : Set (VVec p))

abbrev ProfileIndex (p : ℕ) := (Fin (p + 1) ⊕ Fin (p + 1)) ⊕ Unit

 def somlaiPair (p : ℕ) : ProfileIndex p →
    Submodule (ZMod p) (BVec p) × Submodule (ZMod p) (VVec p)
  | Sum.inl (Sum.inl i) =>
      (bLine p (bBasis p i), vLine p (vBasis p 0 + vBasis p i.succ))
  | Sum.inl (Sum.inr i) =>
      (bLine p (bSum p - bBasis p i), vLine p (vBasis p i.succ + vSum p))
  | Sum.inr _ => (bLine p (bSum p), vLine p (vSum p))

/-- The labelled projective coefficient profile described in claim 6478. -/
def somlai_projective_coefficient_profile : Prop :=
  ∀ p : ℕ, Nat.Prime p → p % 2 = 1 →
    Fintype.card (ProfileIndex p) = 2 * p + 3 ∧
      (∀ i : Fin (p + 1),
        somlaiPair p (Sum.inl (Sum.inl i)) =
          (bLine p (bBasis p i), vLine p (vBasis p 0 + vBasis p i.succ))) ∧
      (∀ i : Fin (p + 1),
        somlaiPair p (Sum.inl (Sum.inr i)) =
          (bLine p (bSum p - bBasis p i), vLine p (vBasis p i.succ + vSum p))) ∧
      somlaiPair p (Sum.inr Unit.unit) =
        (bLine p (bSum p), vLine p (vSum p))

end MathlibPlus.Open.Research.ProjectiveProfiles

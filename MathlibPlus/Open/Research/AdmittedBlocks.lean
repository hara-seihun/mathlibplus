import Mathlib

namespace MathlibPlus.Open.ResearchBlocks

/-- The fibre-coordinate permutation associated to a block profile. -/
def profileMap {D B : Type*} [AddGroup D] (p : B → D) : D × B → D × B :=
  fun z => (z.1 + p z.2, z.2)

/-- Claim 6533: every profile gives a blockwise permutation. -/
def baseFixingProfilePermutation
    (D B : Type*) [AddCommGroup D] [Fintype D] [Fintype B]
    (_hD : D ≃+ (ZMod 3 × ZMod 3)) : Prop :=
  ∀ p : B → D,
    Function.Bijective (profileMap p) ∧
      ∀ b : B,
        Set.range (fun d : D => profileMap p (d, b)) =
          Set.range (fun d : D => (d, b))

/-- Claim 6540: a zero-sum cochain integrates independently on three-cycles. -/
def zeroSumIntegratesOnSemiregularThreeCycles
    (D B : Type*) [AddCommGroup D] [Fintype D] [Fintype B]
    (_hD : D ≃+ (ZMod 3 × ZMod 3)) (u : Equiv.Perm B) (c : B → D) : Prop :=
  (∀ b : B,
      u (u (u b)) = b ∧ u b ≠ b ∧ u (u b) ≠ b) →
    (∀ b : B, c b + c (u b) + c (u (u b)) = 0) →
      ∃ p : B → D, ∀ b : B, p (u b) - p b = c b

end MathlibPlus.Open.ResearchBlocks

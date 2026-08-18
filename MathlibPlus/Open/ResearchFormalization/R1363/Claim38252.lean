import MathlibPlus.Open.Research.GeneratedGroupExact

namespace MathlibPlus.Open.ResearchFormalization.R1363.Claim38252

open MathlibPlus.Open.Research.GeneratedGroupExact

noncomputable section

/-- The parity value of a finite permutation, written without hiding the sign
convention behind a temporary nonzero-cardinality instance. -/
def permutationParity38252 {V : Type*} [Fintype V] [DecidableEq V]
    (e : Equiv.Perm V) : ZMod 2 :=
  if Equiv.Perm.sign e = 1 then 0 else 1

/-- A blockwise sign vector attached to a block-fixing permutation. -/
def normalizerSignVector38252 (q : ℕ) [NeZero q]
    (h : Perm q) (ν : Mask) : Prop :=
  ∀ j : Block, ∃ e : Equiv.Perm (Fiber q),
    (∀ x : Fiber q, h (⟨j, x⟩) = ⟨j, e x⟩) ∧
      ν j = permutationParity38252 e

/-- The common-multiplier affine normalizer conclusion and its constant-sign
consequence. -/
def constantSignNormalizer_claim38252 : Prop :=
  ∀ q : ℕ, ∀ hq : Nat.Prime q, 2 < q →
    letI : NeZero q := ⟨hq.ne_zero⟩
    ∀ h : Perm q, blockFixingNormalizer q h →
      (∃ a : (ZMod q)ˣ, ∃ s : Block → Fiber q,
        (∀ j : Block, ∀ t : Fiber q,
          h (⟨j, t⟩) =
            ⟨j, (a : ZMod q) * t + s j⟩) ∧
        (∀ u : Fiber q, Equiv.Perm.sign (Equiv.addRight u) = 1) ∧
        (∃ ε : ZMod 2, ∀ j : Block, ∃ e : Equiv.Perm (Fiber q),
          (∀ t : Fiber q,
            e t = (a : ZMod q) * t + s j) ∧
          permutationParity38252 e = ε) ∧
        (∀ ν : Mask, normalizerSignVector38252 q h ν →
          ∃ ε : ZMod 2, ∀ j : Block, ν j = ε))

end

end MathlibPlus.Open.ResearchFormalization.R1363.Claim38252

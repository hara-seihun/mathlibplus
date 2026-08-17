import MathlibPlus.Open.ResearchFormalization.R1255.Claims30659_30662

namespace MathlibPlus.Open.ResearchFormalization.R1255.Claim30660

/-- Claim 30660: exactly the constant orientation codes preserve the
characteristic partition, with the exact code counts and mixed-layer witness. -/
def constantCodePartitionCriterion : Prop :=
  ∀ {N : Type*} [AddCommGroup N] [Fintype N]
    (q : ℕ) (hq : Nat.Prime q) (ω : ZMod q) (θ : N ≃+ N)
    (R : Subgroup (Equiv.Perm (Point N q))),
    letI : NeZero q := ⟨hq.ne_zero⟩
    partitionContext q ω θ R →
      (∀ ε : QuotientCoordinate q → Bool,
        characteristicPartition
            (conjugatedCopy (orientationMap ε) R) =
            characteristicPartition R ↔ constantCode ε) ∧
        Fintype.card (QuotientCoordinate q → Bool) = 2 ^ q ∧
          Set.ncard {ε : QuotientCoordinate q → Bool | constantCode ε} = 2 ∧
            Set.ncard {ε : QuotientCoordinate q → Bool | ¬ constantCode ε} =
              2 ^ q - 2 ∧
          (∀ ε : QuotientCoordinate q → Bool, ¬ constantCode ε →
            mixedTransportedLayer (N := N) (q := q) ε ∧
              transportedPartition (N := N) (q := q) ε ≠
                globalLayerPartition (N := N) (q := q))

end MathlibPlus.Open.ResearchFormalization.R1255.Claim30660

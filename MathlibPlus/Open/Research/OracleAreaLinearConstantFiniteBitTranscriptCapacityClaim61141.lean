import Mathlib

namespace MathlibPlus.Open.Research.OracleAreaLinearConstantFiniteBitTranscriptCapacity

noncomputable section

def correctTranscriptPairCount
    {Seed State : Type*}
    [Fintype Seed] [Fintype State] [DecidableEq State]
    (q : ℕ)
    (encode : Seed → State → (Fin q → Bool))
    (decode : Seed → (Fin q → Bool) → State) : ℕ :=
  (Finset.univ.filter (fun p : Seed × State =>
    decode p.1 (encode p.1 p.2) = p.2)).card

/-- The finite-seed, finite-bit transcript-capacity theorem. -/
def claim61141 : Prop :=
  ∀ {Seed State : Type*}
    [Fintype Seed] [Fintype State] [DecidableEq State]
    (q : ℕ)
    (encode : Seed → State → (Fin q → Bool))
    (decode : Seed → (Fin q → Bool) → State),
    (correctTranscriptPairCount q encode decode ≤
      Fintype.card Seed * 2 ^ q) ∧
    ((Nonempty Seed ∧ Nonempty State) →
      ((correctTranscriptPairCount q encode decode : ℝ) /
          (Fintype.card (Seed × State) : ℝ) ≤
        (2 ^ q : ℝ) / (Fintype.card State : ℝ))) ∧
    (Fintype.card State > 2 ^ q →
      ∀ seed : Seed,
        ¬ ∃ fixedDecode : (Fin q → Bool) → State,
          ∀ state : State, fixedDecode (encode seed state) = state)

end
end MathlibPlus.Open.Research.OracleAreaLinearConstantFiniteBitTranscriptCapacity

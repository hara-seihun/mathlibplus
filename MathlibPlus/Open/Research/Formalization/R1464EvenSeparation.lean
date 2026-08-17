import MathlibPlus.Open.Research.Batch1464

namespace MathlibPlus.Open.Research.Batch1464

/-- Claim 37387: an even cyclic separation cannot produce a nonzero
alternating shift difference on an odd-order coefficient field. -/
def claim37387_evenSeparationExclusion : Prop :=
  ∀ {q : ℕ}, Odd q →
    ∀ r : Fin 8, Even r.val →
      ¬ ∃ τ : OuterVector q,
        nonzeroAlternating (fun j => shiftPower r.val τ j - τ j)

end MathlibPlus.Open.Research.Batch1464

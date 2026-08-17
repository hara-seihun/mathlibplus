import MathlibPlus.Open.TreeSpectral

namespace MathlibPlus.Open.TreeSpectral

noncomputable section

/-- The iterated graft tower from degree one, transported to the top-degree
index `k + 1`. -/
def degreeOneTowerVector (k : ℕ) (v : TreeSpace 1) : TreeSpace (k + 1) :=
  (transportTreeSpace (Nat.add_comm 1 k)) (graftPow 1 k v)

/-- Claim 5962: on the stable part of the bottom-degree-one tower, the
unshifted spectral label is increased by exactly one. -/
def shiftedDegreeOneTowerSpectrum_claim5962 : Prop :=
  ∀ (k : ℕ), 2 ≤ k + 1 →
    ∀ v : TreeSpace 1, v ∈ LinearMap.ker (leafDeletion 1) →
      glOperator (k + 1) (Nat.zero_lt_succ k) (degreeOneTowerVector k v) =
        (spectralLabel (k + 1) k + 1) • degreeOneTowerVector k v

end

end MathlibPlus.Open.TreeSpectral

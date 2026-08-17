import MathlibPlus.Open.ResearchFormalization.Lease01a0019fCoding

namespace MathlibPlus.Open.ResearchFormalization.R2015InterpolationAndRelaxation

noncomputable section

open MathlibPlus.Open.ResearchFormalization.Batch01

/-- The scalar value of the formal constant degree law, with the floor
implemented by natural-number division.  No graph or edge-indicator carrier is
introduced for this relaxation law. -/
def constantDegreeLaw (n : ℕ) : ℕ := 3 * n / 5

/-- Claim 35801: the floor-`3n/5` constant law obeys all retained degree
moment inequalities, while its normalized value tends to `3/5 > 1/2`. -/
def degreeMomentRelaxationCounterexample_claim35801 : Prop :=
  (∀ n k : ℕ, k ≤ n →
    ((Nat.choose (constantDegreeLaw n) k : ℝ) /
      (Nat.choose n k : ℝ)) ≤ alpha k) ∧
    Filter.Tendsto
      (fun n : ℕ => (constantDegreeLaw n : ℝ) / (n : ℝ))
      Filter.atTop (nhds ((3 : ℝ) / 5)) ∧
    (1 : ℝ) / 2 < 3 / 5

end

end MathlibPlus.Open.ResearchFormalization.R2015InterpolationAndRelaxation

import Mathlib

open BigOperators

namespace MathlibPlus.Open.Analysis.ResearchFormalizationBatch

/-- The Poisson–Charlier polynomial family used by the finite channels. -/
noncomputable def poissonCharlierPolynomial (n r : ℕ) : Polynomial ℝ :=
  match r with
  | 0 => (n.factorial : ℝ)⁻¹ • (Polynomial.X ^ n)
  | r + 1 =>
      (poissonCharlierPolynomial n r).derivative -
        poissonCharlierPolynomial n r

/-- The finite order-`r` channel polynomial. -/
noncomputable def finiteChannelPolynomial (S : Finset ℕ) (S_f : ℕ → ℝ) (r : ℕ) :
    Polynomial ℝ :=
  ∑ n ∈ S, (S_f n) • poissonCharlierPolynomial n r

/-- The real finite channel evaluated at `x`. -/
noncomputable def finiteChannel (S : Finset ℕ) (S_f : ℕ → ℝ) (r : ℕ) (x : ℝ) : ℝ :=
  Real.exp (-x) * Polynomial.eval x (finiteChannelPolynomial S S_f r)

/-- The finite square energy through channel `N - 1`. -/
noncomputable def finiteSquareEnergy (S : Finset ℕ) (S_f : ℕ → ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  ∑ r ∈ Finset.range N,
    x ^ r * (finiteChannel S S_f r x) ^ 2 / (r.factorial : ℝ)

/-- The energy in channels `1, ..., N`, written with the reindexed range. -/
noncomputable def positiveChannelEnergy (S : Finset ℕ) (S_f : ℕ → ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  finiteSquareEnergy S S_f (N + 1) x - (finiteChannel S S_f 0 x) ^ 2

/--
Removing exceptional channel zero from the finite energy through channel `N`
leaves the reindexed higher-channel sum.
-/
def claim4466_higherChannelEnergy : Prop :=
  ∀ (S : Finset ℕ) (S_f : ℕ → ℝ) (N : ℕ) (x : ℝ),
    positiveChannelEnergy S S_f N x =
      ∑ r ∈ Finset.range N,
        x ^ (r + 1) * (finiteChannel S S_f (r + 1) x) ^ 2 /
          ((r + 1).factorial : ℝ)

end MathlibPlus.Open.Analysis.ResearchFormalizationBatch

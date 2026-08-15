import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.OPE

/-- Exact vacancy--occupancy--coherence factorization for a finite discrete OPE. -/
def vacancyOccupancyCoherenceFactorization
    (N : ℕ) (ω x : Fin N → ℝ)
    (_hω : ∀ j, 0 < ω j)
    (_hx : Function.Injective x)
    (n : ℕ) (i : Fin N) (_hn : n + 1 ≤ N) : Prop :=
  let 𝒲 : Finset (Fin N) → ℝ :=
    fun S =>
      (∏ j ∈ S, ω j) *
        (∏ j ∈ S, (∏ k ∈ S.filter (fun k => j < k), (x j - x k) ^ 2))
  let Z : ℕ → ℝ :=
    fun r => ∑ S : Finset (Fin N), if S.card = r then 𝒲 S else 0
  let ℙ : ℕ → Finset (Fin N) → ℝ :=
    fun r S => 𝒲 S / Z r
  let σ : Finset (Fin N) → ℝ :=
    fun S => Real.sign (∏ j ∈ S, (x i - x j))
  let δ : ℝ :=
    (∑ S : Finset (Fin N),
      if S.card = n ∧ i ∉ S then
        σ S * Real.sqrt (ℙ n S * ℙ (n + 1) (insert i S))
      else 0) ^ 2
  let κ : ℕ → ℝ :=
    fun r => ∑ S : Finset (Fin N),
      if S.card = r ∧ i ∈ S then ℙ r S else 0
  let Qminus : Finset (Fin N) → ℝ :=
    fun S => ℙ n S / (1 - κ n)
  let Qplus : Finset (Fin N) → ℝ :=
    fun S => ℙ (n + 1) (insert i S) / κ (n + 1)
  let 𝔠 : ℝ :=
    (∑ S : Finset (Fin N),
      if S.card = n ∧ i ∉ S then
        σ S * Real.sqrt (Qminus S * Qplus S)
      else 0) ^ 2
  δ = (1 - κ n) * κ (n + 1) * 𝔠

end MathlibPlus.Open.OPE

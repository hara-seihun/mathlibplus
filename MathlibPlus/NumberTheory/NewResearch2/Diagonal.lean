import Mathlib

open scoped BigOperators
open Set
open Filter

namespace MathlibPlus.Open.NumberTheory.NewResearch2.Diagonal

noncomputable section

/-- Claim 13372: exact proper-quotient diagonal energy. -/
def claim13372 : Prop :=
  ∀ (B : ℕ → ℝ) (N : ℕ), 0 < N →
    let W : ℕ → ℝ := fun d => ((N / d - N / (d + 1) : ℕ) : ℝ)
    let H : ℝ := ∑ m ∈ Finset.Icc 1 N, B (N / m) ^ 2
    H - B N ^ 2 = ∑ d ∈ Finset.Icc 1 (N - 1), W d * B d ^ 2

/-- Claim 13373: exact Hilbert dual norm for the centered recovery functional. -/
def claim13373 : Prop :=
  let j : ℕ → ℝ := fun n =>
    if n = 0 then 0 else (Nat.totient n : ℝ) / (n : ℝ)
  let J : ℕ → ℝ := fun x => ∑ n ∈ Finset.Icc 1 x, j n
  let P : ℕ → ℕ → ℝ := fun N d => J (N / d) - J (N / (d + 1))
  let c : ℝ := 6 / Real.pi ^ 2
  ∀ N : ℕ, 1 < N →
    let W : ℕ → ℝ := fun d => ((N / d - N / (d + 1) : ℕ) : ℝ)
    let D : ℕ → ℝ := fun d => c * N / ((d : ℝ) * (d + 1)) - P N d
    let C : ℝ := ∑ d ∈ Finset.Icc 1 (N - 1),
      if 0 < W d then D d ^ 2 / W d else 0
    let admissible : (ℕ → ℝ) → Prop := fun v =>
      ∀ d : ℕ, d < N → W d = 0 → v d = 0
    (∀ v : ℕ → ℝ, admissible v →
      (∑ d ∈ Finset.Icc 1 (N - 1), D d * v d) ^ 2 ≤
        C * ∑ d ∈ Finset.Icc 1 (N - 1), W d * v d ^ 2) ∧
      (∃ v : ℕ → ℝ,
        (∀ d : ℕ, d < N →
          v d = if 0 < W d then D d / W d else 0) ∧
        admissible v ∧
        (∑ d ∈ Finset.Icc 1 (N - 1), D d * v d) ^ 2 =
          C * ∑ d ∈ Finset.Icc 1 (N - 1), W d * v d ^ 2)

/-- Claim 13379: square-root upper bound for the squared dual norm. -/
def claim13379 : Prop :=
  let j : ℕ → ℝ := fun n =>
    if n = 0 then 0 else (Nat.totient n : ℝ) / (n : ℝ)
  let J : ℕ → ℝ := fun x => ∑ n ∈ Finset.Icc 1 x, j n
  let P : ℕ → ℕ → ℝ := fun N d => J (N / d) - J (N / (d + 1))
  let c : ℝ := 6 / Real.pi ^ 2
  ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    (∑ d ∈ Finset.Icc 1 (N - 1),
      if 0 < ((N / d - N / (d + 1) : ℕ) : ℝ) then
        (c * N / ((d : ℝ) * (d + 1)) - P N d) ^ 2 /
          ((N / d - N / (d + 1) : ℕ) : ℝ)
      else 0) ≤
      C * Real.sqrt N * Real.log (2 * N) ^ 2

/-- Claim 13381: inherited pointwise growth controls diagonal energy. -/
def claim13381 : Prop :=
  let c : ℝ := 6 / Real.pi ^ 2
  ∀ θ : ℝ, 1 / 2 < θ →
    ∃ Cθ : ℝ, 0 < Cθ ∧ ∀ A : ℝ, 0 ≤ A →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ B : ℕ → ℝ,
          (∀ d : ℕ, 0 < d → |B d| ≤ A * Real.rpow (d : ℝ) θ) →
          (∑ d ∈ Finset.Icc 1 (N - 1),
            ((N / d - N / (d + 1) : ℕ) : ℝ) * B d ^ 2) ≤
            Cθ * A ^ 2 * Real.rpow (N : ℝ) (2 * θ)

/-- Claim 13382: optimal diagonal recovery carries a quarter-power loss. -/
def claim13382 : Prop :=
  let j : ℕ → ℝ := fun n =>
    if n = 0 then 0 else (Nat.totient n : ℝ) / (n : ℝ)
  let J : ℕ → ℝ := fun x => ∑ n ∈ Finset.Icc 1 x, j n
  let P : ℕ → ℕ → ℝ := fun N d => J (N / d) - J (N / (d + 1))
  let c : ℝ := 6 / Real.pi ^ 2
  let C : ℕ → ℝ := fun N =>
    ∑ d ∈ Finset.Icc 1 (N - 1),
      let W : ℝ := ((N / d - N / (d + 1) : ℕ) : ℝ)
      let D : ℝ := c * N / ((d : ℝ) * (d + 1)) - P N d
      if 0 < W then D ^ 2 / W else 0
  ∀ ε : ℝ, 0 < ε →
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      c₁ * Real.rpow (N : ℝ) (1 / 4 - ε) ≤ Real.sqrt (C N) ∧
        Real.sqrt (C N) ≤ c₂ * Real.rpow (N : ℝ) (1 / 4 + ε)

end

end MathlibPlus.Open.NumberTheory.NewResearch2.Diagonal

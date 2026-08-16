import Mathlib

/-!
# First canonical connected-triple sign reversal

This registry node records admitted claim 176 from source record `C-0012`.
The three labels are represented separately by `a`, `b`, and `c`; their canonical
weights and support ratios are built into `moment`. The decimal pair-cumulant values
in the source have no error tolerances, so the formal statement retains their exact
strict signs rather than inventing interval bounds.
-/

namespace MathlibPlus.Open.ConnectedTriple

/-- At rank four, the separately labelled canonical shells `2`, `3`, and `4` have
negative connected pair cumulants but a positive connected triple cumulant with the
stated exact value. -/
noncomputable def firstCanonicalSignReversal : Prop :=
  let moment : ℝ → ℝ → ℝ → ℕ → ℝ := fun a b c j =>
    1 + a / Real.sqrt 2 * ((4 : ℝ)⁻¹) ^ j
      + b / Real.sqrt 3 * ((9 : ℝ)⁻¹) ^ j
      + c / 2 * ((16 : ℝ)⁻¹) ^ j
  let h : ℝ → ℝ → ℝ → ℕ → ℝ := fun a b c j =>
    moment a b c j / (Nat.factorial (2 * j) : ℝ)
  let delta : ℝ → ℝ → ℝ → ℝ := fun a b c =>
    Matrix.det (fun i j : Fin 4 =>
      ∑ q ∈ Finset.range (min i.1 j.1 + 1),
        ((i.1 + j.1 + 1 - 2 * q : ℕ) : ℝ) * h a b c q *
          h a b c (i.1 + j.1 + 1 - q))
  let delta0 : ℝ := delta 0 0 0
  let d₂ : ℝ := deriv (fun a => delta a 0 0) 0
  let d₃ : ℝ := deriv (fun b => delta 0 b 0) 0
  let d₄ : ℝ := deriv (fun c => delta 0 0 c) 0
  let d₂₃ : ℝ := deriv (fun a => deriv (fun b => delta a b 0) 0) 0
  let d₂₄ : ℝ := deriv (fun a => deriv (fun c => delta a 0 c) 0) 0
  let d₃₄ : ℝ := deriv (fun b => deriv (fun c => delta 0 b c) 0) 0
  let d₂₃₄ : ℝ :=
    deriv (fun a => deriv (fun b => deriv (fun c => delta a b c) 0) 0) 0
  let k₂ : ℝ := d₂ / delta0
  let k₃ : ℝ := d₃ / delta0
  let k₄ : ℝ := d₄ / delta0
  let k₂₃ : ℝ := d₂₃ / delta0
  let k₂₄ : ℝ := d₂₄ / delta0
  let k₃₄ : ℝ := d₃₄ / delta0
  let k₂₃₄ : ℝ := d₂₃₄ / delta0
  let κ₂₃ : ℝ := k₂₃ - k₂ * k₃
  let κ₂₄ : ℝ := k₂₄ - k₂ * k₄
  let κ₃₄ : ℝ := k₃₄ - k₃ * k₄
  let κ₂₃₄ : ℝ :=
    k₂₃₄ - k₂₃ * k₄ - k₂₄ * k₃ - k₃₄ * k₂ + 2 * k₂ * k₃ * k₄
  delta0 = 1 / 100356600994650000 ∧
    κ₂₃₄ =
      8231973841573957243952423 * Real.sqrt 6 /
        44115102527743250191613952 ∧
    0 < κ₂₃₄ ∧ κ₂₃ < 0 ∧ κ₂₄ < 0 ∧ κ₃₄ < 0

end MathlibPlus.Open.ConnectedTriple

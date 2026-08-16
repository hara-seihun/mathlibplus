import Mathlib

open scoped BigOperators
open MeasureTheory

namespace MathlibPlus.Open.TranscriptPrefixBernstein

noncomputable def firstDiff
    {d : ℕ} {A : Fin d → Type} (hd : 0 < d)
    (u v : (i : Fin d) → A i) : Fin d := by
  classical
  let s := Finset.univ.filter (fun i => u i ≠ v i)
  exact if h : s.Nonempty then s.min' h else ⟨0, hd⟩

noncomputable def prefixRho
    {d : ℕ} {C : Type} {A : Fin d → Type}
    (hd : 0 < d) (code : C → (i : Fin d) → A i)
    (x y : C) : ℝ := by
  classical
  exact if h : x = y then 0
    else (2 : ℝ) ^ (-((firstDiff hd (code x) (code y)).val : ℤ))

noncomputable def prefixBernsteinTerm
    (b : ℕ) (κ δ : ℝ) (m : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ m *
    (Real.sqrt (2 * (((m + 1 : ℕ) : ℝ) *
      Real.log ((2 * b : ℕ) : ℝ) + Real.log (1 / δ))) +
      κ * ((((m + 1 : ℕ) : ℝ) * Real.log ((2 * b : ℕ) : ℝ)) +
        Real.log (1 / δ)))

noncomputable def prefixBernsteinSum
    (d b : ℕ) (κ δ : ℝ) : ℝ :=
  ∑ m ∈ Finset.range d, prefixBernsteinTerm b κ δ m

def IsUltrametric
    {C : Type} (rho : C → C → ℝ) : Prop :=
  (∀ x y, 0 ≤ rho x y) ∧
  (∀ x y, rho x y = rho y x) ∧
  (∀ x y, rho x y = 0 ↔ x = y) ∧
  (∀ x y z, rho x z ≤ max (rho x y) (rho y z))

def finiteTranscriptPrefixBernstein
    (d b : ℕ) (hd : 1 ≤ d) (hb : 1 ≤ b)
    (C : Type) [Fintype C] [Nonempty C]
    (A : Fin d → Type) [∀ i, Fintype (A i)]
    (hcard : ∀ i, Fintype.card (A i) ≤ b)
    (code : C → (i : Fin d) → A i)
    (hcode : Function.Injective code)
    (Ω : Type) [MeasurableSpace Ω]
    (P : Measure Ω) (hP : IsProbabilityMeasure P)
    (X : C → Ω → ℝ)
    (hmeas : ∀ x, Measurable (X x))
    (κ : ℝ) (hκ : 0 ≤ κ) : Prop :=
  let rho : C → C → ℝ := prefixRho (Nat.zero_lt_of_lt hd) code
  (∀ x y, x ≠ y → ∀ t : ℝ, 0 < t →
      P {ω | X x ω - X y ω >
        rho x y * (Real.sqrt (2 * t) + κ * t)} ≤
        ENNReal.ofReal (Real.exp (-t))) →
    IsUltrametric rho ∧
      (∀ c₀ : C, ∀ δ : ℝ, 0 < δ → δ < 1 →
        P {ω |
          Finset.sup' Finset.univ Finset.univ_nonempty
            (fun x => X x ω - X c₀ ω) ≤ prefixBernsteinSum d b κ δ} ≥
          ENNReal.ofReal (1 - δ) ∧
        prefixBernsteinSum d b κ δ ≤
          4 * Real.sqrt (2 * Real.log ((2 * b : ℕ) : ℝ)) +
            2 * Real.sqrt (2 * Real.log (1 / δ)) +
            κ * (4 * Real.log ((2 * b : ℕ) : ℝ) +
              2 * Real.log (1 / δ)))

end MathlibPlus.Open.TranscriptPrefixBernstein

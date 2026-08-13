import Mathlib

open scoped BigOperators
open scoped Topology
open Filter

noncomputable section
open Classical

namespace MathlibPlus.Open.Combinatorics.BinaryPrefixTilt

def claim10539 : Prop :=
  ∃ Cplus Cminus : Finset (List Bool),
    Cplus ≠ Cminus ∧
    (∀ u ∈ Cplus, ∀ v ∈ Cplus, u ≠ v →
      ¬ (∃ t : List Bool, v = u ++ t) ∧
      ¬ (∃ t : List Bool, u = v ++ t)) ∧
    (∀ u ∈ Cminus, ∀ v ∈ Cminus, u ≠ v →
      ¬ (∃ t : List Bool, v = u ++ t) ∧
      ¬ (∃ t : List Bool, u = v ++ t)) ∧
    (∑ w ∈ Cplus, (1 / 2 : ℝ) ^ w.length = 1) ∧
    (∑ w ∈ Cminus, (1 / 2 : ℝ) ^ w.length = 1) ∧
    let sstar := Real.log ((1 + Real.sqrt 5) / 2)
    let qstar := Real.exp (-sstar)
    0 < sstar ∧ 1 / 2 < qstar ∧ qstar < 1 ∧ qstar ≠ 1 / 2 ∧
      (∑ w ∈ Cplus, qstar ^ w.length) =
        (∑ w ∈ Cminus, qstar ^ w.length)

def claim10540 : Prop :=
  ∃ Cplus Cminus : Finset (List Bool), ∃ q : ℝ,
    Cplus ≠ Cminus ∧
    (∀ u ∈ Cplus, ∀ v ∈ Cplus, u ≠ v →
      ¬ (∃ t : List Bool, v = u ++ t) ∧
      ¬ (∃ t : List Bool, u = v ++ t)) ∧
    (∀ u ∈ Cminus, ∀ v ∈ Cminus, u ≠ v →
      ¬ (∃ t : List Bool, v = u ++ t) ∧
      ¬ (∃ t : List Bool, u = v ++ t)) ∧
    (∑ w ∈ Cplus, (1 / 2 : ℝ) ^ w.length = 1) ∧
    (∑ w ∈ Cminus, (1 / 2 : ℝ) ^ w.length = 1) ∧
    1 / 2 < q ∧ q < 1 ∧
    (∑ w ∈ Cplus, q ^ w.length) =
      (∑ w ∈ Cminus, q ^ w.length)

end MathlibPlus.Open.Combinatorics.BinaryPrefixTilt

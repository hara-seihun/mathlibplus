import MathlibPlus.Open.Combinatorics.Claim42303_42304_42306_42307

namespace MathlibPlus.Open.ResearchFormalization.R2671Claim42311

noncomputable section

open Classical
open MathlibPlus.Open.Combinatorics

/-- The empty-tight-trace portion of a down-region. -/
def emptyTracePart {n : ℕ}
    (G : Finset (Finset (Fin n))) (T R : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  (r2671DownRegion G R).filter (fun A => r2671Trace A T = ∅)

/-- Claim 42311: in the nonempty-`p₂`-trace branch, the second comparable
region cannot have cardinality at least 26.  The arithmetic and incidence
conclusions used in the contradiction are retained explicitly. -/
def claim42311 : Prop :=
  ∀ (n : ℕ) (F G : Finset (Finset (Fin n)))
    (T R₁ R₂ : Finset (Fin n)) (p₀ p₁ p₂ : Fin n),
    normalizedExactK67TerminalSlice_claim4230 F G T R₁ R₂ p₀ p₁ p₂ →
      (r2671ComparableRegion G R₁).card = 31 →
      (∃ A ∈ r2671DownRegion G R₂,
        r2671Trace A T = {p₂}) →
      let D₁ := r2671DownRegion G R₁
      let D₂ := r2671DownRegion G R₂
      let E₂ := r2671ComparableRegion G R₂
      let d := D₂.card
      let k := (r2671UpRegion G R₂).card
      ((26 ≤ E₂.card →
          k + (d + 1) / 2 ≤ 16 ∧
          d / 2 ≥ 10 ∧
          20 ≤ d ∧
          r2671Frequency D₂ p₂ ≤ 3 ∧
          (∃ y : Fin n,
            2 * r2671Frequency D₂ y ≥ d ∧
            7 ≤ r2671Frequency (emptyTracePart G T R₂) y ∧
            emptyTracePart G T R₂ ⊆ D₁ ∧
            7 ≤ r2671Frequency D₁ y ∧
            r2671Frequency D₁ y ≤ 6))) ∧
        E₂.card ≤ 25

end

end MathlibPlus.Open.ResearchFormalization.R2671Claim42311

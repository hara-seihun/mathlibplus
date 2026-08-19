import MathlibPlus.Open.Combinatorics.Claim42303_42304_42306_42307

namespace MathlibPlus.Open.ResearchFormalization.R2671Claim42315

noncomputable section

open Classical
open MathlibPlus.Open.Combinatorics

/-- Claim 42315: equality in the empty-trace branch rigidly fixes the two
region sizes, the branch arithmetic, the four displayed frequencies, and the
frequency in each of the six singleton/pair trace cells. -/
def claim42315 : Prop :=
  ∀ (n : ℕ) (F G : Finset (Finset (Fin n)))
    (T R₁ R₂ : Finset (Fin n)) (p₀ p₁ p₂ : Fin n),
    normalizedExactK67TerminalSlice_claim4230 F G T R₁ R₂ p₀ p₁ p₂ →
      (r2671ComparableRegion G R₁).card = 31 →
      (∀ A ∈ r2671DownRegion G R₂,
        r2671Trace A T = ∅) →
      (r2671ComparableRegion G R₂).card = 25 →
      let D₁ := r2671DownRegion G R₁
      let D₂ := r2671DownRegion G R₂
      let K₂ := r2671UpRegion G R₂
      let Q₁ := r2671IncomparableRegion G R₁
      let Q₂ := r2671IncomparableRegion G R₂
      D₂.card = 12 ∧
        K₂.card = 13 ∧
        K₂.card + (D₂.card + 1) / 2 = 19 ∧
        (∀ y : Fin n,
          2 * r2671Frequency D₂ y ≥ D₂.card →
            r2671Frequency D₂ y = 6 ∧
              r2671Frequency D₁ y = 6 ∧
                r2671Frequency Q₁ y = 6 ∧
                  r2671Frequency Q₂ y = 6 ∧
                    (∀ S : Finset (Fin n),
                      S ⊆ T →
                        (S.card = 1 ∨ S.card = 2) →
                          r2671Frequency (r2671TraceCell G T S) y = 2))

end

end MathlibPlus.Open.ResearchFormalization.R2671Claim42315

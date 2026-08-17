import MathlibPlus.Open.ResearchFormalization.O0092Claim13520

open scoped BigOperators Matrix

namespace MathlibPlus.Open.ResearchFormalization.O0092

noncomputable section

/-- The three displayed separated factors for the physical target row. -/
def explicitThreeTermRealization13525
    (x : ℝ) (σ κ : ℂ) : Prop :=
  let d : ℝ := 2 + x
  let f : Fin 3 → (ℝ → ℂ) :=
    ![ fun U : ℝ => (d : ℂ) * (Real.cosh U : ℂ),
       fun _ : ℝ => (-2 : ℂ),
       fun U : ℝ => σ * κ * (Real.sinh U : ℂ) ]
  let g : Fin 3 → (ℝ → ℂ) :=
    ![ fun _ : ℝ => (1 : ℂ),
       fun Φ : ℝ => (Real.cos Φ : ℂ),
       fun Φ : ℝ => (Real.sin Φ : ℂ) ]
  (∀ i : Fin 3, splitFactor (f i)) ∧
    (∀ i : Fin 3, compactFactor (g i)) ∧
      (∀ U Φ : ℝ,
        targetRow x σ κ U Φ =
          ∑ i : Fin 3, f i U * g i Φ)

/-- Claim 13525: on the physical source interval, the target is exactly the
three-channel separated row
`d cosh U · 1 - 2 · 1 · cos Φ + σ κ sinh U · sin Φ`. -/
def claim13525 : Prop :=
  ∀ (x : ℝ),
    0 ≤ x →
    x ≤ 1 →
    ∀ (σ : ℂ),
      (σ = 1 ∨ σ = -1) →
      ∀ κ : ℂ,
        explicitThreeTermRealization13525 x σ κ ∧
          hasSeparatedRepresentation (targetRow x σ κ) 3

end

end MathlibPlus.Open.ResearchFormalization.O0092

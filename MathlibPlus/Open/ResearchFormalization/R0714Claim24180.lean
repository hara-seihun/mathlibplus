import MathlibPlus.Open.ResearchFormalization.R0714.Claim24184

namespace MathlibPlus.Open.ResearchFormalization.R0714Claim24180

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R0714

/-- The complete one-card profile on a one-vertex extension fibre. -/
def oneCardProfile (n : ℕ) (G : GraphType (n + 1)) :
    GraphType n → ℕ :=
  fun K => oneCard n K G

/-- The complete unordered two-card profile on the same fibre. -/
def twoCardProfile (n : ℕ) (G : GraphType (n + 1)) :
    GraphType (n - 1) → ℕ :=
  fun K => twoCard n K G

/-- Claim 24180: on every exact one-vertex extension fibre, the complete
    profile functions are the one-card and unordered two-card deletion
    multiplicities, and each mixed quadratic coordinate is their product. -/
def claim24180 : Prop :=
  ∀ (n : ℕ) (F : GraphType n) (G : ExtensionFiber n F),
    let a_G : GraphType n → ℕ := oneCardProfile n G.1
    let b_G : GraphType (n - 1) → ℕ := twoCardProfile n G.1
    ∀ (K : GraphType (n - 1)) (P : GraphType n),
      mixedMatrix n F (K, P) G =
        (b_G K : ℚ) * (a_G P : ℚ)

end

end MathlibPlus.Open.ResearchFormalization.R0714Claim24180

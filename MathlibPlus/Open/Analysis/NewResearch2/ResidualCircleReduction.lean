import Mathlib
import MathlibPlus.Open.Analysis.TranslationOrbitDenseClaim2213
import MathlibPlus.Open.ResearchFormalization.SymbolsBatch019ffedc

open Filter Topology
open MathlibPlus.Open.ResearchFormalization

namespace MathlibPlus.Open.Analysis.NewResearch2

noncomputable section

/-- A locally uniform real-translation hull member with the four arithmetic
phase coordinates made explicit.  The phase coordinates are taken at the
real point `z`, so the residual coordinates below are the phases at the zero. -/
def partialZetaHullPhaseLimit
    (r x y₃ y₅ y₇ : ℝ) (g : ℂ → ℂ) (z : ℂ) : Prop :=
  ∃ a : ℕ → ℝ,
    (∀ R ε : ℝ, 0 < R → 0 < ε →
      ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
        ∀ w : ℂ, ‖w‖ ≤ R →
          ‖partialZetaSymbol r (w + (a k : ℂ) + z) - g (w + z)‖ < ε) ∧
    (let phase : ℕ → ℝ := fun n =>
      if n = 1 then 3 * x
      else if n = 2 then x
      else if n = 3 then 3 * x - y₃
      else if n = 4 then -x
      else if n = 5 then 3 * x - y₅
      else if n = 6 then x - y₃
      else if n = 7 then 3 * x - y₇
      else 0
     ∀ n : ℕ, 1 ≤ n → n ≤ 7 →
       Tendsto
         (fun k : ℕ =>
           Complex.exp
             (Complex.I *
               (((partialZetaOmega n * (z.re + a k) : ℝ) : ℂ))))
         atTop
         (𝓝 (Complex.exp (Complex.I * (phase n : ℂ)))))

/-- Claim 2214: a real double zero in any arithmetic partial-zeta hull lies
on the seventh-frequency residual circle. -/
def residualCircleDoubleZero_claim2214 : Prop :=
  ∀ (r x y₃ y₅ y₇ : ℝ) (g : ℂ → ℂ) (z : ℂ),
    (2 : ℝ) / 3 ≤ r →
    z.im = 0 →
    partialZetaHullPhaseLimit r x y₃ y₅ y₇ g z →
    g z = 0 →
    deriv g z = 0 →
    residualQ r x y₃ y₅ = 1

end
end MathlibPlus.Open.Analysis.NewResearch2

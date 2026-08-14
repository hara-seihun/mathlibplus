import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Geometry

noncomputable section

def HeronArea (a b d : ℝ) : ℝ :=
  Real.sqrt (((a + b + d) / 2) * ((-a + b + d) / 2) *
    ((a - b + d) / 2) * ((a + b - d) / 2))

def AreaDerivativeA (a b d : ℝ) : ℝ :=
  a * (b ^ 2 + d ^ 2 - a ^ 2) / (8 * HeronArea a b d)

def AreaDerivativeB (a b d : ℝ) : ℝ :=
  b * (a ^ 2 + d ^ 2 - b ^ 2) / (8 * HeronArea a b d)

def AreaDerivativeD (a b d : ℝ) : ℝ :=
  d * (a ^ 2 + b ^ 2 - d ^ 2) / (8 * HeronArea a b d)

def claim36455 : Prop :=
  ∀ a b d : ℝ,
    1 ≤ a → a ≤ 11 / 10 → 1 ≤ b → b ≤ 11 / 10 →
    1 ≤ d → d ≤ 11 / 10 →
    HeronArea a b d > 0 ∧
    HasDerivAt (fun x => HeronArea x b d) a (AreaDerivativeA a b d) ∧
    HasDerivAt (fun y => HeronArea a y d) b (AreaDerivativeB a b d) ∧
    HasDerivAt (fun z => HeronArea a b z) d (AreaDerivativeD a b d) ∧
    a * (b ^ 2 + d ^ 2 - a ^ 2) ≥ 79 / 100 ∧
    b * (a ^ 2 + d ^ 2 - b ^ 2) ≥ 79 / 100 ∧
    d * (a ^ 2 + b ^ 2 - d ^ 2) ≥ 79 / 100 ∧
    HeronArea a b d ≤ 121 / 200 ∧
    AreaDerivativeA a b d ≥ 79 / 484 ∧
    AreaDerivativeB a b d ≥ 79 / 484 ∧
    AreaDerivativeD a b d ≥ 79 / 484 ∧
    HeronArea a b d - Real.sqrt 3 / 4 ≥
      (79 / 484) * ((a - 1) + (b - 1) + (d - 1))

end
end MathlibPlus.Open.ResearchFormalization.Geometry

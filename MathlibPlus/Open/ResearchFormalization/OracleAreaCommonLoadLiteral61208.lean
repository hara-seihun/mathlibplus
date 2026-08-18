import MathlibPlus.Open.ResearchFormalization.R3630

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.OracleAreaCommonLoadLiteral61208

noncomputable section

open MathlibPlus.Open.ResearchFormalization
open MathlibPlus.Open.ResearchFormalization.R3630

abbrev Cube (n : ℕ) := RademacherCube n
abbrev Law (n : ℕ) := BooleanLaw n

/-- The real-valued positive depth-one literal at a coordinate. -/
def literalValue {n : ℕ} (s : Fin n) : Cube n → ℝ :=
  (signedLiteral s true).1

/-- The uniform finite law on the positive literals of a cube. -/
noncomputable def uniformLiteralLaw (n : ℕ) : Law (n + 1) :=
  Finset.univ.toList.map
    (fun s => (signedLiteral s true, 1 / ((n + 1 : ℕ) : ℝ)))

/-- The barycentre of the uniform literal law. -/
noncomputable def literalBarycenter (n : ℕ) : Cube (n + 1) → ℝ :=
  lawBarycenter (uniformLiteralLaw n)

/-- Uniform variance on a finite Rademacher cube. -/
noncomputable def uniformVariance {n : ℕ} (f : Cube n → ℝ) : ℝ :=
  let μ := uniformMean f
  uniformMean (fun x => (f x - μ) ^ 2)

/-- Insert a fixed sign at a coordinate, leaving the residual cube. -/
def insertSign {n : ℕ} (i : Fin (n + 1)) (b : Bool)
    (x : Cube n) : Cube (n + 1) :=
  Fin.insertNth i b x

/-- Restriction of a target after revealing one coordinate. -/
def coordinateRestriction {n : ℕ} (f : Cube (n + 1) → ℝ)
    (i : Fin (n + 1)) (b : Bool) : Cube n → ℝ :=
  fun x => f (insertSign i b x)

/-- The minimum root-inclusive area saving from revealing a coordinate. -/
noncomputable def areaDecrement {n : ℕ} (f : Cube (n + 1) → ℝ)
    (i : Fin (n + 1)) : ℝ :=
  realIntrinsicArea f -
    (realIntrinsicArea (coordinateRestriction f i false) +
      realIntrinsicArea (coordinateRestriction f i true)) / 2

/-- The maximum of a real load over all coordinates of a nonempty cube. -/
noncomputable def coordinateMaximum {n : ℕ} (a : Fin (n + 1) → ℝ) : ℝ :=
  (Finset.univ : Finset (Fin (n + 1))).sup' Finset.univ_nonempty a

/-- The squared common square-root load of a finite Boolean law. -/
def lawLoad {n : ℕ} (law : Law (n + 1)) (i : Fin (n + 1)) : ℝ :=
  (law.map (fun entry => entry.2 * Real.sqrt (areaDecrement entry.1.1 i))).sum ^ 2

/-- Claim 61208: uniform depth-one literals have variance `1/n`, unit
coordinate decrements, squared common load `1/n^2`, and unbounded ratio;
the final conjunct records the resulting failure for all finite laws. -/
def claim61208 : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    isProbabilityLaw (uniformLiteralLaw n) ∧
    let g := literalBarycenter n
    (∀ i : Fin (n + 1),
      uniformVariance g = 1 / ((n + 1 : ℕ) : ℝ) ∧
        (∀ s : Fin (n + 1),
          areaDecrement (literalValue s) i = if i = s then 1 else 0) ∧
        lawLoad (uniformLiteralLaw n) i =
          1 / (((n + 1 : ℕ) : ℝ) ^ 2)) ∧
      uniformVariance g /
          coordinateMaximum (fun i => lawLoad (uniformLiteralLaw n) i) =
        (n + 1 : ℝ) ∧
      (¬ ∃ C : ℝ,
        ∀ m : ℕ, ∀ law : Law (m + 1),
          isProbabilityLaw law →
            uniformVariance (lawBarycenter law) ≤
              C * coordinateMaximum (fun i => lawLoad law i)) ∧
      (∀ C : ℝ, ∃ m : ℕ, 1 ≤ m ∧
        uniformVariance (literalBarycenter m) >
          C * coordinateMaximum
            (fun i => lawLoad (uniformLiteralLaw m) i))

end

end MathlibPlus.Open.ResearchFormalization.OracleAreaCommonLoadLiteral61208

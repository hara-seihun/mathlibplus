import Mathlib

open scoped BigOperators
noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.OracleMajority61016

/-- The three-coordinate sign cube. -/
abbrev Cube := Fin 3 → Bool

/-- The real value of a Rademacher sign. -/
def signValue (b : Bool) : ℝ :=
  if b then 1 else -1

/-- Coordinate complementation on the three-cube. -/
def flipCoordinate (i : Fin 3) (x : Cube) : Cube :=
  Function.update x i (!x i)

/-- Three-bit majority, with `true` representing the positive sign. -/
def majority (x : Cube) : Bool :=
  (if x 0 then 1 else 0) +
      (if x 1 then 1 else 0) +
      (if x 2 then 1 else 0) ≥ 2

/-- The normalized edge derivative in coordinate `i`. -/
def edgeDerivative (f : Cube → ℝ) (i : Fin 3) (x : Cube) : ℝ :=
  (f x - f (flipCoordinate i x)) / 2

/-- The maximum pointwise `L¹` edge gradient. -/
def maxL1EdgeGradient (f : Cube → ℝ) : ℝ :=
  sSup (Set.range (fun x : Cube =>
    ∑ i : Fin 3, |edgeDerivative f i x|))

/-- A deterministic adaptive coordinate policy, indexed by its answer list. -/
abbrev Policy := List Bool → Fin 3

/-- The answers seen after `m` reveals under a policy. -/
def transcript (q : Policy) (x : Cube) : ℕ → List Bool
  | 0 => []
  | m + 1 =>
      let answers := transcript q x m
      answers ++ [x (q answers)]

/-- A policy never reveals the same coordinate twice before the three-cube is
exhausted. -/
def freshPolicy (q : Policy) : Prop :=
  ∀ (x : Cube) (a b : ℕ), a < b → b < 3 →
    q (transcript q x a) ≠ q (transcript q x b)

/-- The posterior cell of an outcome at a given transcript. -/
def transcriptCell (q : Policy) (x : Cube) (m : ℕ) : Finset Cube :=
  Finset.univ.filter (fun y => transcript q y m = transcript q x m)

/-- The uniform posterior variance on a transcript cell. -/
def posteriorVariance (f : Cube → ℝ) (q : Policy) (x : Cube) (m : ℕ) : ℝ :=
  let cell := transcriptCell q x m
  let card : ℝ := cell.card
  let mean := (∑ y ∈ cell, f y) / card
  (∑ y ∈ cell, (f y - mean) ^ 2) / card

/-- Root-inclusive cumulative posterior-variance area through the final
unrevealed-coordinate stage. -/
def policyArea (f : Cube → ℝ) (q : Policy) : ℝ :=
  ∑ m ∈ Finset.range 3,
    (∑ x : Cube, posteriorVariance f q x m) / (2 : ℝ) ^ 3

/-- A policy determines a real-valued target by at most three fresh reveals. -/
def determines (f : Cube → ℝ) (q : Policy) : Prop :=
  ∃ out : List Bool → ℝ,
    ∀ x : Cube, ∃ m : ℕ, m ≤ 3 ∧
      f x = out (transcript q x m)

/-- The minimum legal root-inclusive area, represented by the infimum over the
explicit finite-cube policy carrier. -/
def minimumArea (f : Cube → ℝ) : ℝ :=
  sInf {a : ℝ | ∃ q : Policy,
    freshPolicy q ∧ determines f q ∧ a = policyArea f q}

/-- Boolean-valued real functions on the sign cube. -/
def booleanFunction (f : Cube → ℝ) : Prop :=
  ∀ x : Cube, f x = 1 ∨ f x = -1

/-- Claim 61016: three-bit majority has maximum pointwise gradient two but
root-inclusive minimum posterior-variance area nine-fourths, so the universal
area-versus-gradient candidate and its gradient route are false. -/
def claim61016 : Prop :=
  let M : Cube → ℝ := fun x => signValue (majority x)
  maxL1EdgeGradient M = 2 ∧
    minimumArea M = 1 + 3 / 4 + 1 / 2 ∧
      1 + 3 / 4 + 1 / 2 > 2 ∧
        booleanFunction M ∧
          ¬ (∀ f : Cube → ℝ,
            maxL1EdgeGradient f ≥ minimumArea f) ∧
            ¬ (∀ f : Cube → ℝ,
              booleanFunction f → minimumArea f ≤ maxL1EdgeGradient f)

end MathlibPlus.Open.ResearchFormalization.OracleMajority61016

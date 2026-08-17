import Mathlib

open scoped BigOperators
open Classical

namespace MathlibPlus.Open.ResearchFormalization.AdaptiveOracleAreaSharp

noncomputable section

/-- The three-coordinate Boolean cube and its reveal histories. -/
abbrev ThreeCube := Fin 3 → Bool
abbrev RealTarget := ThreeCube → ℝ
abbrev ThreeHistory := Fin 3 → Option Bool
abbrev ThreePolicy := ThreeHistory → Option (Fin 3)

/-- The real sign represented by a Boolean value. -/
def signedBoolean (b : Bool) : ℝ :=
  if b then 1 else -1

/-- A Boolean function viewed as a `{-1,1}`-valued real target. -/
def booleanTarget (f : ThreeCube → Bool) : RealTarget :=
  fun x => signedBoolean (f x)

/-- The equally weighted Boolean two-atom midpoint target. -/
def booleanMidpoint (f g : ThreeCube → Bool) : RealTarget :=
  fun x => (booleanTarget f x + booleanTarget g x) / 2

/-- The root history before any coordinate is revealed. -/
def initialHistory : ThreeHistory :=
  fun _ => none

/-- Outcomes compatible with a reveal history. -/
def compatible (h : ThreeHistory) (x : ThreeCube) : Prop :=
  ∀ i : Fin 3, ∀ b : Bool, h i = some b → x i = b

noncomputable def compatibleOutcomes (h : ThreeHistory) : Finset ThreeCube :=
  letI : ∀ x : ThreeCube, Decidable (compatible h x) :=
    fun x => Classical.propDecidable (compatible h x)
  Finset.univ.filter (fun x => compatible h x)

/-- Uniform posterior averaging on a finite compatible fibre. -/
noncomputable def posteriorMean (u : RealTarget) (h : ThreeHistory) : ℝ :=
  if hs : (compatibleOutcomes h).Nonempty then
    ((compatibleOutcomes h).card : ℝ)⁻¹ *
      (∑ x ∈ compatibleOutcomes h, u x)
  else 0

noncomputable def posteriorVariance
    (u : RealTarget) (h : ThreeHistory) : ℝ :=
  if hs : (compatibleOutcomes h).Nonempty then
    ((compatibleOutcomes h).card : ℝ)⁻¹ *
      (∑ x ∈ compatibleOutcomes h,
        (u x - posteriorMean u h) ^ 2)
  else 0

/-- A fresh coordinate set at a history. -/
noncomputable def freshCoordinates (h : ThreeHistory) : Finset (Fin 3) :=
  Finset.univ.filter (fun i => h i = none)

/-- The actual transcript after a legal observation of coordinate `i`. -/
def observe (h : ThreeHistory) (x : ThreeCube) (i : Fin 3) : ThreeHistory :=
  Function.update h i (some (x i))

/-- Legal adaptive coordinate-reveal policies never query an observed
coordinate. -/
def legalAdaptivePolicy (π : ThreePolicy) : Prop :=
  ∀ h : ThreeHistory, ∀ i : Fin 3,
    π h = some i → h i = none

/-- The history generated along an oracle outcome after `n` reveal stages. -/
def historyAt (π : ThreePolicy) (x : ThreeCube) : ℕ → ThreeHistory
  | 0 => initialHistory
  | n + 1 =>
      let h := historyAt π x n
      match π h with
      | none => h
      | some i => observe h x i

/-- A policy has determined the fixed target on every oracle outcome by the
root plus three reveal stages. -/
def revealsTarget (u : RealTarget) (π : ThreePolicy) : Prop :=
  ∀ x : ThreeCube, ∃ n : Fin 4,
    posteriorVariance u (historyAt π x (n : ℕ)) = 0

/-- Root-inclusive cumulative posterior-variance area of a three-cube policy.
The fourth term is the zero-variance terminal padding after at most three
fresh-coordinate reveals. -/
noncomputable def policyArea3
    (u : RealTarget) (π : ThreePolicy) : ℝ :=
  ∑ n : Fin 4,
    (Fintype.card ThreeCube : ℝ)⁻¹ *
      (∑ x : ThreeCube,
        posteriorVariance u (historyAt π x (n : ℕ)))

/-- A totalized finite minimum, used only on the finite policy set. -/
noncomputable def finiteMinimum {α : Type*} [DecidableEq α]
    (s : Finset α) (v : α → ℝ) : ℝ :=
  if hs : s.Nonempty then s.inf' hs v else 0

/-- The legal target-determining policies used by the exact finite minimum. -/
noncomputable def completeLegalPolicies (u : RealTarget) : Finset ThreePolicy :=
  letI : ∀ π : ThreePolicy, Decidable (legalAdaptivePolicy π ∧ revealsTarget u π) :=
    fun π => Classical.propDecidable (legalAdaptivePolicy π ∧ revealsTarget u π)
  Finset.univ.filter (fun π => legalAdaptivePolicy π ∧ revealsTarget u π)

/-- `A₃`, the exact minimum root-inclusive posterior-variance area over
legal adaptive coordinate reveals on the uniform three-cube. -/
noncomputable def A3 (u : RealTarget) : ℝ :=
  finiteMinimum (completeLegalPolicies u) (policyArea3 u)

/-- Claim 61037: the exact Bellman minimum is midpoint-convex on every pair of
Boolean targets on the three-cube, equivalently for every equally weighted
two-atom Boolean law. -/
def claim61037_threeCubeBooleanMidpointConvexity : Prop :=
  ∀ f g : ThreeCube → Bool,
    A3 (booleanMidpoint f g) ≤
      (A3 (booleanTarget f) + A3 (booleanTarget g)) / 2

end

end MathlibPlus.Open.ResearchFormalization.AdaptiveOracleAreaSharp

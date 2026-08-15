import Mathlib

namespace MathlibPlus.Open

open scoped BigOperators

noncomputable section

/-- The eight outcomes of three independent uniform signs, with coordinates
`0`, `1`, and `2` named `X`, `Y`, and `Z`. -/
abbrev Claim60103Outcome := Fin 3 → Bool

/-- Convert a Boolean sign to its real value. -/
def Claim60103SignValue (b : Bool) : ℝ :=
  if b then 1 else -1

/-- The fixed point-mass decision tree from claim 60103. -/
def Claim60103Tree (ω : Claim60103Outcome) : ℝ :=
  if Claim60103SignValue (ω 0) = 1 then
    Claim60103SignValue (ω 1)
  else
    -Claim60103SignValue (ω 2)

/-- The mixture mean of the point-mass tree. -/
def Claim60103MixtureMean : Claim60103Outcome → ℝ := Claim60103Tree

/-- The finite conditional-variance semantics for a revealed coordinate set. -/
def Claim60103Fiber (S : Finset (Fin 3)) (ω : Claim60103Outcome) :
    Finset Claim60103Outcome :=
  Finset.univ.filter (fun ω' => ∀ i ∈ S, ω' i = ω i)

def Claim60103Average (A : Finset Claim60103Outcome)
    (f : Claim60103Outcome → ℝ) : ℝ :=
  if _h : A.Nonempty then
    (Finset.sum A f) / (A.card : ℝ)
  else
    0

def Claim60103ConditionalVariance (S : Finset (Fin 3))
    (ω : Claim60103Outcome) : ℝ :=
  let A := Claim60103Fiber S ω
  let m := Claim60103Average A Claim60103MixtureMean
  Claim60103Average A (fun ω' => (Claim60103MixtureMean ω' - m) ^ 2)

def Claim60103ExpectedConditionalVariance (S : Finset (Fin 3)) : ℝ :=
  Claim60103Average Finset.univ (Claim60103ConditionalVariance S)

/-- Root-inclusive cumulative posterior variance for a fixed ordering. -/
def Claim60103NonadaptiveCumulative (p : Fin 3 → Fin 3) : ℝ :=
  Finset.sum Finset.univ (fun m : Fin 4 =>
    Claim60103ExpectedConditionalVariance
      (Finset.univ.filter (fun j : Fin 3 =>
        ∃ k : Fin 3, k.val < m.val ∧ p k = j)))

/-- The adaptive policy reveals `X`, then `Y` on the positive branch and `Z`
on the negative branch, and stops after that second reveal. -/
def Claim60103AdaptiveSecondCoordinate (x : Bool) : Fin 3 :=
  if Claim60103SignValue x = 1 then 1 else 2

def Claim60103AdaptiveRevealed (ω : Claim60103Outcome) (m : Fin 3) :
    Finset (Fin 3) :=
  match m.1 with
  | 0 => ∅
  | 1 => {0}
  | _ => {0, Claim60103AdaptiveSecondCoordinate (ω 0)}

def Claim60103AdaptiveCumulative : ℝ :=
  Finset.sum Finset.univ (fun m : Fin 3 =>
    Claim60103Average Finset.univ (fun ω =>
      Claim60103ConditionalVariance (Claim60103AdaptiveRevealed ω m) ω))

/-- Claim 60103: the adaptive depth-two policy has root-inclusive value `2`,
whereas every fixed ordering has the stated value by its first coordinate. -/
def claim60103 : Prop :=
  Claim60103AdaptiveCumulative = 2 ∧
    (∀ ω : Claim60103Outcome,
      Claim60103ConditionalVariance
        (Claim60103AdaptiveRevealed ω 2) ω = 0) ∧
    (∀ p : Fin 3 → Fin 3, Function.Bijective p →
      (p 0 = 0 → Claim60103NonadaptiveCumulative p = (5 : ℝ) / 2) ∧
      (p 0 ≠ 0 → Claim60103NonadaptiveCumulative p = (9 : ℝ) / 4)) ∧
    Nat.card {p : Fin 3 → Fin 3 // Function.Bijective p ∧ p 0 = 0} = 2 ∧
    Nat.card {p : Fin 3 → Fin 3 // Function.Bijective p ∧ p 0 ≠ 0} = 4

end

end MathlibPlus.Open

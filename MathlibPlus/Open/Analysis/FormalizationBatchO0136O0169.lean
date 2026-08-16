import Mathlib

open BigOperators

namespace MathlibPlus.Open.Analysis.FormalizationBatch

/-- Free-orbit cocycle transport for linear coefficient maps. -/
def claim_11684
    (K W O M : Type*)
    [Field K] [Group W] [MulAction W O]
    [AddCommGroup M] [Module K M]
    (V : O → Type*) [∀ o : O, AddCommGroup (V o)] [∀ o : O, Module K (V o)]
    (N : ∀ (w : W) (x : O), V x ≃ₗ[K] V (w • x))
    (ρ : W →* (M ≃ₗ[K] M)) : Prop :=
  ((∀ x y : O, ∃ g : W, g • x = y) ∧
    (∀ g : W, (∃ x : O, g • x = x) → g = 1) ∧
    (∀ x, HEq (N 1 x) (LinearEquiv.refl K (V x))) ∧
    (∀ (g h : W) (x : O),
      HEq (N (g * h) x) ((N h x).trans (N g (h • x))))) →
    ∀ (x₀ : O) (B₀ : V x₀ →ₗ[K] M),
      ∃! B : ∀ x : O, V x →ₗ[K] M,
        B x₀ = B₀ ∧
          ∀ (g : W) (x : O),
            (B (g • x)).comp (N g x).toLinearMap = (ρ g).toLinearMap.comp (B x)


noncomputable section

/-- The real value of a uniform sign. -/
def signValue (s : Bool) : ℝ := if s then 1 else -1

abbrev assignment (I : Type*) [DecidableEq I] (J : Finset I) :=
  {i // i ∈ J} → Bool

/-- A character on a finite set of coordinates. -/
def parityCharacter {I : Type*} [DecidableEq I] {J : Finset I}
    (A : Finset {i // i ∈ J}) (σ : assignment I J) : ℝ :=
  ∏ i ∈ A, signValue (σ i)

/-- A finite mixture of sign characters. -/
def mixtureFunction {I : Type*} [DecidableEq I] {J : Finset I}
    (n : ℕ) (weights signs : Fin n → ℝ)
    (supports : Fin n → Finset {i // i ∈ J})
    (σ : assignment I J) : ℝ :=
  ∑ r : Fin n, weights r * signs r * parityCharacter (supports r) σ

/-- Uniform averaging over a finite assignment type; the denominator is its
cardinality, not the cardinality of the assignment-function type squared. -/
def uniformAverage {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  (Fintype.card α : ℝ)⁻¹ * ∑ x, f x

def fourierCoefficient {I : Type*} [DecidableEq I] {J : Finset I}
    (n : ℕ) (weights signs : Fin n → ℝ)
    (supports : Fin n → Finset {i // i ∈ J})
    (A : Finset {i // i ∈ J}) : ℝ :=
  letI : Fintype {i // i ∈ J} := Fintype.ofFinset J (by simp)
  uniformAverage (fun σ : assignment I J =>
    mixtureFunction n weights signs supports σ * parityCharacter A σ)

def characterSets {I : Type*} [DecidableEq I] (J : Finset I) :
    Finset (Finset {i // i ∈ J}) :=
  letI : Fintype {i // i ∈ J} := Fintype.ofFinset J (by simp)
  (Finset.univ : Finset {i // i ∈ J}).powerset

def activeCoordinates {I : Type*} [DecidableEq I] {J : Finset I}
    (α : Finset {i // i ∈ J} → ℝ) : Finset {i // i ∈ J} :=
  (characterSets J).biUnion (fun A =>
    if A.Nonempty ∧ α A ≠ 0 then A else ∅)

def coefficientMass {I : Type*} [DecidableEq I] {J : Finset I}
    (α : Finset {i // i ∈ J} → ℝ) : ℝ :=
  ∑ A ∈ characterSets J, if A.Nonempty then |α A| else 0

def conditioningFiber {I : Type*} [DecidableEq I] {J : Finset I}
    (S : Finset {i // i ∈ J}) (σ : assignment I J) :=
  {τ : assignment I J // ∀ i, i ∈ S → τ i = σ i}

def conditionalMean {I : Type*} [DecidableEq I] {J : Finset I}
    (h : assignment I J → ℝ) (S : Finset {i // i ∈ J})
    (σ : assignment I J) : ℝ :=
  letI : Fintype {i // i ∈ J} := Fintype.ofFinset J (by simp)
  letI : Fintype (conditioningFiber S σ) :=
    Fintype.subtype
      ((Finset.univ : Finset (assignment I J)).filter
        (fun τ => ∀ i, i ∈ S → τ i = σ i)) (by simp)
  uniformAverage (fun τ : conditioningFiber S σ => h τ.1)

def conditionalVariance {I : Type*} [DecidableEq I] {J : Finset I}
    (h : assignment I J → ℝ) (S : Finset {i // i ∈ J})
    (σ : assignment I J) : ℝ :=
  letI : Fintype {i // i ∈ J} := Fintype.ofFinset J (by simp)
  letI : Fintype (conditioningFiber S σ) :=
    Fintype.subtype
      ((Finset.univ : Finset (assignment I J)).filter
        (fun τ => ∀ i, i ∈ S → τ i = σ i)) (by simp)
  uniformAverage (fun τ : conditioningFiber S σ =>
    (h τ.1 - conditionalMean h S σ) ^ 2)

def prefixSet {I : Type*} [DecidableEq I] {J : Finset I}
    (active : Finset {i // i ∈ J}) {m : ℕ}
    (o : Fin m ≃ {i // i ∈ active})
    (t : Fin m) : Finset {i // i ∈ J} :=
  (Finset.univ.filter (fun k : Fin m => k.1 < t.1)).image
    (fun k => (o k).1)

def orderingArea {I : Type*} [DecidableEq I] {J : Finset I}
    (h : assignment I J → ℝ) (active : Finset {i // i ∈ J}) {m : ℕ}
    (o : Fin m ≃ {i // i ∈ active}) : ℝ :=
  letI : Fintype {i // i ∈ J} := Fintype.ofFinset J (by simp)
  ∑ t : Fin m,
    uniformAverage (fun σ : assignment I J =>
      conditionalVariance h (prefixSet active o t) σ)

def previousChoices {I : Type*} [DecidableEq I] {J : Finset I}
    {active : Finset {i // i ∈ J}} {m : ℕ}
    (π : Fin m → assignment I J → {i // i ∈ active})
    (σ : assignment I J) (t : Fin m) : Finset {i // i ∈ active} :=
  (Finset.univ.filter (fun k : Fin m => k.1 < t.1)).image (fun k => π k σ)

def adaptiveRevealPolicy {I : Type*} [DecidableEq I] {J : Finset I}
    {active : Finset {i // i ∈ J}} {m : ℕ}
    (π : Fin m → assignment I J → {i // i ∈ active}) : Prop :=
  ∀ (σ : assignment I J) (t : Fin m),
    π t σ ∉ previousChoices π σ t

/-- The two-coordinate parity gives the sharp value, for either ordering. -/
def singleParitySharpness : Prop :=
  let J₂ : Finset (Fin 2) := Finset.univ
  let A₂ : Finset {i // i ∈ J₂} := Finset.univ
  ∀ (o : Fin 2 ≃ {a // a ∈ A₂}),
    orderingArea
      (I := Fin 2) (J := J₂)
      (fun σ => ∏ i : {i // i ∈ J₂}, signValue (σ i)) A₂ o = 2

/-- The fixed-order area bound for arbitrary finite mixtures of degree at most
 two sign characters, including its sharpness and the induced adaptive policy. -/
def claim_60226
    (I : Type*) [Countable I] [DecidableEq I]
    (J : Finset I) (n : ℕ)
    (weights signs : Fin n → ℝ)
    (supports : Fin n → Finset {i // i ∈ J}) : Prop :=
  ((∀ r, (supports r).card ≤ 2) ∧
    (∀ r, 0 ≤ weights r) ∧
    (∑ r : Fin n, weights r = 1) ∧
    (∀ r, signs r = 1 ∨ signs r = -1)) →
  let h : assignment I J → ℝ := mixtureFunction n weights signs supports
  let α : Finset {i // i ∈ J} → ℝ :=
    fourierCoefficient n weights signs supports
  let q : ℝ := coefficientMass α
  let active : Finset {i // i ∈ J} := activeCoordinates α
  (∃ (o : Fin active.card ≃ {i // i ∈ active}),
      orderingArea h active o ≤ 2 * q ^ 2 ∧
      2 * q ^ 2 ≤ 2 ∧
      adaptiveRevealPolicy (fun t _σ => o t)) ∧
    singleParitySharpness

end

end MathlibPlus.Open.Analysis.FormalizationBatch

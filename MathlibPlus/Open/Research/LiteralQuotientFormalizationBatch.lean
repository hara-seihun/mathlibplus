import Mathlib

namespace MathlibPlus.Open.Research.LiteralQuotient

open scoped BigOperators
noncomputable section

abbrev F2 := ZMod 2
abbrev Vertex (n : ℕ) := Fin n → F2

/-- The direction-i oriented edge domain Ωᵢ. -/
def omegaSubmodule (n : ℕ) (i : Fin n) : Submodule F2 (Vertex n) :=
  { carrier := {x | x i = 0}
    zero_mem' := by simp
    add_mem' := by
      intro x y hx hy
      change x i = 0 at hx
      change y i = 0 at hy
      change x i + y i = 0
      simp [hx, hy]
    smul_mem' := by
      intro a x hx
      change x i = 0 at hx
      change (a • x) i = 0
      simp [hx] }

abbrev Omega (n : ℕ) (i : Fin n) := omegaSubmodule n i

abbrev EdgeFunctions (n : ℕ) := ∀ i : Fin n, Omega n i → Bool

def boolValue (b : Bool) : ℝ :=
  if b then 1 else 0

def uniformExpectation {α : Type} [Fintype α] (f : α → ℝ) : ℝ :=
  (Fintype.card α : ℝ)⁻¹ * ∑ x, f x

def density {n : ℕ} {i : Fin n} (f : Omega n i → Bool) : ℝ := by
  letI := Fintype.ofFinite (Omega n i)
  exact uniformExpectation (fun x => boolValue (f x))

def literalC4Free {n : ℕ} (f : EdgeFunctions n) : Prop :=
  ∀ (i j : Fin n) (hij : i ≠ j), ∀ (x : Vertex n)
    (hi : x i = 0) (hj : x j = 0),
    ¬ (f i ⟨x, hi⟩ = true ∧
      f j ⟨x, hj⟩ = true ∧
      f i ⟨Function.update x j (x j + 1), by
        change Function.update x j (x j + 1) i = 0
        simpa [Function.update_apply, hij] using hi⟩ = true ∧
      f j ⟨Function.update x i (x i + 1), by
        change Function.update x i (x i + 1) j = 0
        simpa [Function.update_apply, Ne.symm hij] using hj⟩ = true)

def positiveDensityExcess {n : ℕ} (f : EdgeFunctions n) (i : Fin n) : ℝ :=
  max 0 (density (f i) - 1 / 2)

def quotientPullbackFunctions (n : ℕ) (i : Fin n) (r : ℕ)
    (f : Omega n i → Bool) : Set (Omega n i → Bool) :=
  {g | ∃ s : ℕ, s ≤ r ∧
      ∃ φ : Omega n i →ₗ[F2] (Fin s → F2),
        Function.Surjective φ ∧
        ∃ h : (Fin s → F2) → Bool, g = h ∘ φ}

def literalNormalizedHammingError {n : ℕ} {i : Fin n}
    (f g : Omega n i → Bool) : ℝ := by
  letI := Fintype.ofFinite (Omega n i)
  exact uniformExpectation (fun x => if f x = g x then 0 else 1)

def quotientDistance {n : ℕ} (f : EdgeFunctions n) (i : Fin n) (r : ℕ) : ℝ :=
  sInf {d : ℝ |
    ∃ g ∈ quotientPullbackFunctions n i r (f i),
      d = literalNormalizedHammingError (f i) g}

/-- Claim 35928: literal edge functions, C₄-freeness, excess, and quotient distance. -/
def literalDirectionalEdgeSetup : Prop := by
  classical
  exact ∀ (n : ℕ) (f : EdgeFunctions n),
    (∀ i : Fin n, positiveDensityExcess f i =
      max 0 (density (f i) - 1 / 2)) ∧
    (∀ i : Fin n, ∀ r : ℕ,
      quotientDistance f i r =
        sInf {d : ℝ |
          ∃ g ∈ quotientPullbackFunctions n i r (f i),
            d = literalNormalizedHammingError (f i) g}) ∧
    (literalC4Free f ↔
      ∀ (i j : Fin n) (hij : i ≠ j), ∀ (x : Vertex n)
        (hi : x i = 0) (hj : x j = 0),
        ¬ (f i ⟨x, hi⟩ = true ∧
          f j ⟨x, hj⟩ = true ∧
          f i ⟨Function.update x j (x j + 1), by
            change Function.update x j (x j + 1) i = 0
            simpa [Function.update_apply, hij] using hi⟩ = true ∧
          f j ⟨Function.update x i (x i + 1), by
            change Function.update x i (x i + 1) j = 0
            simpa [Function.update_apply, Ne.symm hij] using hj⟩ = true))

end
end MathlibPlus.Open.Research.LiteralQuotient

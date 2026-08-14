import Mathlib

namespace MathlibPlus.Open

/-- Claim 59628: the stabilizer-and-fiber criterion for equivariant relation-preserving
bijections of transitive G-sets. -/
def claim59628
    (G X Y Z W I : Type*)
    [Group G]
    [MulAction G X] [MulAction G Y] [MulAction G Z] [MulAction G W]
    (hX : ∀ x₁ x₂ : X, ∃ g : G, g • x₁ = x₂)
    (hY : ∀ y₁ y₂ : Y, ∃ g : G, g • y₁ = y₂)
    (F : Z → W)
    (hF : ∀ g : G, ∀ z : Z, F (g • z) = g • F z)
    (R : I → Set (X × Z))
    (S : I → Set (Y × W))
    (hR : ∀ i : I, ∀ g : G, ∀ x : X, ∀ z : Z,
      ((x, z) ∈ R i ↔ (g • x, g • z) ∈ R i))
    (hS : ∀ i : I, ∀ g : G, ∀ y : Y, ∀ w : W,
      ((y, w) ∈ S i ↔ (g • y, g • w) ∈ S i))
    (x₀ : X) : Prop :=
  (∃ e : X ≃ Y,
      (∀ g : G, ∀ x : X, e (g • x) = g • e x) ∧
      ∀ i : I, ∀ x : X, ∀ z : Z,
        ((x, z) ∈ R i ↔ (e x, F z) ∈ S i)) ↔
    (∃ y₀ : Y,
      (∀ g : G, (g • x₀ = x₀ ↔ g • y₀ = y₀)) ∧
      ∀ i : I, ∀ z : Z,
        ((x₀, z) ∈ R i ↔ (y₀, F z) ∈ S i))

/-- Claim 59632: the prescribed sequence can be retained while a fixed explicit
function has a nonreal zero. -/
def claim59632 : Prop :=
  ∀ g : ℕ → ℕ,
    ∃ k : ℕ → ℕ, ∃ F : ℂ → ℂ,
      (∀ N : ℕ, k N = g N) ∧
      (∀ z : ℂ, F z = z - Complex.I) ∧
      (∃ z : ℂ, F z = 0 ∧ Complex.im z ≠ 0)

/-- The weight appearing in Claim 59643. -/
noncomputable def dilationWeight (n : ℕ) (t : ℝ) : ℝ :=
  Real.exp (-5 * t / 4 - Real.pi * (n : ℝ) ^ 2 * Real.exp (-t)) +
    Real.exp (5 * t / 4 - Real.pi * (n : ℝ) ^ 2 * Real.exp t)

/-- Claim 59643: every strictly increasing positive row and parameter pattern has
an eventually positive common-dilation minor. -/
def claim59643 : Prop :=
  ∀ m : ℕ, 1 ≤ m →
    ∀ r : Fin m → ℕ,
      (∀ i : Fin m, 0 < r i) →
      (∀ i j : Fin m, i < j → r i < r j) →
    ∀ t : Fin m → ℝ,
      (∀ i : Fin m, 0 < t i) →
      (∀ i j : Fin m, i < j → t i < t j) →
    ∃ Q : ℕ, 0 < Q ∧
      ∀ q : ℕ, Q ≤ q →
        0 < Matrix.det (fun i j : Fin m => dilationWeight (q * r i) (t j))

/-- The exact integer bounds in Claim 59652. -/
def callPairLower (c : ℕ) : ℤ :=
  max (Int.floor ((c : ℚ) / 12) + 1)
    (Int.ceil (((c : ℚ) - 6) / 10))

def callPairUpper (c : ℕ) : ℤ :=
  Int.floor ((c : ℚ) / 3)

def callPairAdmissible (c : ℕ) : Set ℤ :=
  {k | 0 < k ∧ (12 : ℤ) ∣ k + (c : ℤ) ∧
    5 * k ≥ (c : ℤ) - 36 ∧ k ≤ 3 * (c : ℤ)}

/-- Claim 59652: the admissible positive integers, their unique parameters, and
 their exact cardinality are as stated. -/
def claim59652 : Prop :=
  ∀ c : ℕ, 0 < c →
    callPairAdmissible c =
      {k | ∃ a : ℤ,
        callPairLower c ≤ a ∧ a ≤ callPairUpper c ∧
        k = 12 * a - (c : ℤ)} ∧
    (callPairAdmissible c).Finite ∧
    (∀ k : ℤ, k ∈ callPairAdmissible c →
      ∃! a : ℤ,
        callPairLower c ≤ a ∧ a ≤ callPairUpper c ∧
        k = 12 * a - (c : ℤ)) ∧
    ((callPairAdmissible c).Nonempty ↔ 3 ≤ c) ∧
    ((callPairAdmissible c).Finite →
      ((Set.ncard (callPairAdmissible c) : ℤ) =
        callPairUpper c - callPairLower c + 1))

/-- Claim 59691: the explicit nonnegative endpoint polynomials preserve a given
nonreal zero while separating successive horizons. -/
def claim59691 : Prop :=
  ∀ (P : ℝ → ℝ) (F : ℂ → ℂ) (z : ℂ),
    P 0 ≠ 0 → F z = 0 → Complex.im z ≠ 0 →
    let H : ℕ → ℝ → ℝ := fun N q => q ^ 2 + (N : ℝ)
    (∀ N : ℕ, ∀ y : ℝ,
        0 ≤ H N (P (-y) / P 0)) ∧
      (∀ N : ℕ,
        Continuous (H N) ∧
        (∃ p : Polynomial ℝ, ∀ q : ℝ, p.eval q = H N q) ∧
        H N 0 ≠ H N 1 ∧
        H N 0 < H (N + 1) 0) ∧
      F z = 0 ∧ Complex.im z ≠ 0

/-- A finite sign row, represented by its two exact values. -/
def signValue (b : Bool) : ℝ :=
  if b then 1 else -1

/-- Claim 59695: every bounded function on a finite set is the column average of a
finite probability law on sign rows. -/
def claim59695 : Prop :=
  ∀ (C : Type*) [Fintype C] [Fintype (C → Bool)],
    ∀ f : C → ℝ,
      (∀ O : C, -1 ≤ f O ∧ f O ≤ 1) →
      ∃ Λ : (C → Bool) → ℝ,
        (∀ T : C → Bool, 0 ≤ Λ T) ∧
        (∑ T : C → Bool, Λ T = 1) ∧
        (∀ O : C,
          ∑ T : C → Bool, Λ T * signValue (T O) = f O)

/-- Claim 59698: the finite telescoping energy identity gives the strict norm
bound at every horizon. -/
def claim59698 : Prop :=
  ∀ (𝒢 : Type*) [NormedAddCommGroup 𝒢] [InnerProductSpace ℝ 𝒢],
    ∀ M : ℕ, ∀ z : ℕ → 𝒢, ∀ ρ : ℝ, 0 < ρ →
      (let d : ℕ → 𝒢 := fun j => z j - z 0
       let δ : ℕ → 𝒢 := fun j => z (j + 1) - z j
       let energy : ℕ → ℝ := fun m =>
         (∑ j ∈ Finset.range m,
           (‖δ j‖ ^ 2 + 2 * inner ℝ (d j) (δ j)))
       (∀ m : ℕ, m ≤ M → energy m < ρ ^ 2) →
       ∀ m : ℕ, m ≤ M →
         ‖z m - z 0‖ < ρ ∧ energy m = ‖z m - z 0‖ ^ 2)

end MathlibPlus.Open

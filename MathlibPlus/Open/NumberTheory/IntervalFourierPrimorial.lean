import Mathlib

open scoped BigOperators Topology
open Filter Set

namespace MathlibPlus.Open.NumberTheory.IntervalFourierPrimorial

noncomputable section

/-- The floor remainder in the interval with right endpoint `u` and length `h`.
The arguments are integers so that the left endpoint is `u - h`, even when it
is negative; positive denominators use integer Euclidean division. -/
def intervalRemainder (u h q : ℤ) : ℚ :=
  ((u / q : ℤ) : ℚ) - (((u - h) / q : ℤ) : ℚ) - (h : ℚ) / (q : ℚ)

def intervalMultiples (u h q : ℤ) : Set ℤ :=
  {j | u - h < j ∧ j ≤ u ∧ q ∣ j}

/-- The additive character used in the finite Fourier expansions. -/
def additiveCharacter (x : ℚ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ))

/-- Claim 36974: the displayed floor expression is the count of multiples in
`(u-h,u]`, with its expected length subtracted. -/
def claim36974 : Prop :=
  ∀ u h q : ℤ, 1 ≤ u → 1 ≤ h → 1 ≤ q →
    intervalRemainder u h q =
      (Set.ncard (intervalMultiples u h q) : ℚ) - (h : ℚ) / (q : ℚ)

/-- The finite coefficient sum in the balanced dyadic block. -/
def balancedRemainderSum (d : ℕ) (u : ℕ) (m₁ n₁ : ℝ)
    (a b : ℕ → ℂ) : ℂ :=
  Finset.sum ((Finset.range (Nat.floor m₁ + 1)).filter
      (fun m : ℕ => Real.sqrt (d : ℝ) < (m : ℝ) ∧ (m : ℝ) ≤ m₁))
    (fun m => Finset.sum ((Finset.range (Nat.floor n₁ + 1)).filter
      (fun n : ℕ => Real.sqrt (d : ℝ) < (n : ℝ) ∧ (n : ℝ) ≤ n₁))
      (fun n => a m * b n *
        (intervalRemainder (u : ℤ) (d : ℤ) ((m * n : ℕ) : ℤ) : ℂ)))

/-- The exponent selected in the sharp-interval estimate. -/
def etaKappa (κ : ℝ) : ℝ :=
  (1 / 2 : ℝ) * min (1 / 12 : ℝ)
    (min ((κ - 1) / 6) ((2 - κ) / 20))

/-- Claim 36978: uniform power saving on the balanced polynomial endpoint
window, with arbitrary bounded complex coefficient sequences. -/
def claim36978 : Prop :=
  ∀ κ : ℝ, 1 < κ → κ < 2 →
    ∃ C : ℝ, 0 < C ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      ∀ u : ℕ, Real.rpow (d : ℝ) κ ≤ (u : ℝ) →
        (u : ℝ) ≤ 2 * Real.rpow (d : ℝ) κ →
        ∀ m₁ n₁ : ℝ, Real.sqrt (d : ℝ) < m₁ → m₁ ≤ 2 * Real.sqrt (d : ℝ) →
          Real.sqrt (d : ℝ) < n₁ → n₁ ≤ 2 * Real.sqrt (d : ℝ) →
          ∀ a b : ℕ → ℂ,
            (∀ m, ‖a m‖ ≤ 1) → (∀ n, ‖b n‖ ≤ 1) →
              ‖balancedRemainderSum d u m₁ n₁ a b‖ ≤
                C * Real.rpow (d : ℝ) (1 - etaKappa κ)

/-- Claim 36979: the selected exponent has strict slack in all three
parameter inequalities and `H U^(-ε)` has the displayed power of `D` on the
endpoint window. -/
def claim36979 : Prop :=
  ∀ κ : ℝ, 1 < κ → κ < 2 →
    let η := etaKappa κ
    let ε := η / κ
    η < 1 / 12 ∧ η < (κ - 1) / 6 ∧ η < (2 - κ) / 20 ∧
      ∀ d u : ℝ, 1 ≤ d → Real.rpow d κ ≤ u → u ≤ 2 * Real.rpow d κ →
        Real.rpow d 1 * Real.rpow u (-ε) ≤ Real.rpow d (1 - η)

/-- Claim 36981: reciprocity is recorded with explicit modular inverse
witnesses, and the displayed residual four-point phase has nonzero
cross-ratio exponent. -/
def claim36981 : Prop :=
  (∀ u h m n : ℕ, 2 ≤ m → 2 ≤ n → Nat.Coprime m n →
    ∃ mbar nbar : ℕ,
      mbar < n ∧ nbar < m ∧
      m * mbar % n = 1 ∧ n * nbar % m = 1 ∧
      additiveCharacter ((u * h : ℚ) / (m * n : ℚ)) =
        additiveCharacter ((u * h * mbar : ℚ) / (n : ℚ)) *
          additiveCharacter ((u * h * nbar : ℚ) / (m : ℚ))) ∧
  ((3 : ℚ) / 5 + (5 : ℚ) / 7 - (2 : ℚ) / 5 - (4 : ℚ) / 7 = 12 / 35) ∧
  (12 / 35 : ℚ) ∉ Set.range (fun k : ℤ => (k : ℚ)) ∧
  additiveCharacter (3 / 5) * additiveCharacter (5 / 7) ≠
    additiveCharacter (2 / 5) * additiveCharacter (4 / 7)

/-- Claim 36982: the relative term in the balanced one-sided estimate has the
stated `UA ≥ D` scale, and decay of that term forces
`U = o(D^(11/10))` when `A ≥ 1`. -/
def claim36982 : Prop :=
  (∀ D U A : ℝ, 0 < D → 0 < U → 1 ≤ A → D ≤ U * A →
    Real.rpow (1 + U * A / D) (1 / 4) *
        Real.rpow D (-1 / 40) * Real.rpow A (-1 / 20) ≥
      Real.rpow U (1 / 4) * Real.rpow D (-11 / 40) * Real.rpow A (1 / 5)) ∧
  (∀ d u a : ℕ → ℝ,
    (∀ n, 0 < d n) → (∀ n, 1 ≤ a n) →
    (∀ᶠ n : ℕ in atTop, d n ≤ u n * a n) →
    Filter.Tendsto
      (fun n => Real.rpow (1 + u n * a n / d n) (1 / 4) *
        Real.rpow (d n) (-1 / 40) * Real.rpow (a n) (-1 / 20))
      atTop (𝓝 0) →
    Filter.Tendsto (fun n => u n / Real.rpow (d n) (11 / 10))
      atTop (𝓝 0))

/-- The primorial support used by the periodicity obstruction. -/
def primorial (z : ℕ) : ℕ :=
  Finset.prod ((Finset.range (z + 1)).filter Nat.Prime) (fun p => p)

def dyadicIndices (M : ℕ) : Finset ℕ :=
  (Finset.range (2 * M + 1)).filter (fun m => M < m ∧ m ≤ 2 * M)

def supportedBilinearBlock (u h M N z : ℕ) (a b : ℕ → ℂ) : ℂ :=
  Finset.sum (dyadicIndices M) (fun m =>
    Finset.sum (dyadicIndices N) (fun n =>
      if m * n ∣ primorial z then
        a m * b n *
          (intervalRemainder (u : ℤ) (h : ℤ) ((m * n : ℕ) : ℤ) : ℂ)
      else 0))

/-- Claim 36983: a block whose every modulus divides the primorial is
periodic in the endpoint modulo that primorial. -/
def claim36983 : Prop :=
  ∀ u h M N z : ℕ, ∀ a b : ℕ → ℂ,
    (∀ m ∈ dyadicIndices M, ∀ n ∈ dyadicIndices N,
      m * n ∣ primorial z) →
      supportedBilinearBlock u h M N z a b =
        supportedBilinearBlock (u + primorial z) h M N z a b

/-- Claim 36985: the half-primorial residue has no small integer
representative, while the primorial has Chebyshev scale `z`. -/
def claim36985 : Prop :=
  (∀ z : ℕ, 2 ≤ z →
    2 ∣ primorial z ∧ 0 < primorial z / 2 ∧ primorial z / 2 < primorial z ∧
    ∀ k : ℤ,
      (primorial z : ℤ) ∣ k - ((primorial z / 2 : ℕ) : ℤ) →
        primorial z / 2 ≤ Int.natAbs k) ∧
  (Filter.Tendsto
      (fun z : ℕ => Real.log ((primorial z : ℕ) : ℝ) / (z : ℝ))
      atTop (𝓝 1)) ∧
  (∀ C : ℝ, 0 < C →
    ∀ᶠ z : ℕ in atTop,
      Real.rpow (z : ℝ) C < ((primorial z / 2 : ℕ) : ℝ))

end
end MathlibPlus.Open.NumberTheory.IntervalFourierPrimorial

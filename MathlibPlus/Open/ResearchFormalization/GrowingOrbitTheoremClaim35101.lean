import MathlibPlus.Open.ResearchFormalization.SharpenedRREFColourCountClaim35100

namespace MathlibPlus.Open.ResearchFormalization.GrowingOrbitTheoremClaim35101

open scoped BigOperators

noncomputable section

open MathlibPlus.Open.ResearchFormalization.SharpenedRREFColourCountClaim35100

abbrev F2 := ZMod 2
abbrev Vector (n : ℕ) := Fin n → F2

abbrev DirectionalFamily :=
  ∀ n : ℕ, ∀ i : Fin n, Vector n → Bool

def coordinateUnit (n : ℕ) (j : Fin n) : Vector n :=
  fun k => if k = j then 1 else 0

def translatedRestriction {n : ℕ} {i : Fin n}
    (f : Vector n → Bool) (v : Vector n) : Vector n → Bool :=
  fun x => if x i = 0 then f (x + v) else false

noncomputable def literalDirectionalOrbitCard {n : ℕ} {i : Fin n}
    (f : Vector n → Bool) : ℕ :=
  Nat.card {g : Vector n → Bool //
    ∃ v : Vector n, v i = 0 ∧
      g = translatedRestriction (i := i) f v}

noncomputable def directionalDensity {n : ℕ} (i : Fin n)
    (f : Vector n → Bool) : ℝ :=
  (Nat.card {x : Vector n // x i = 0 ∧ f x = true} : ℝ) /
    (Nat.card {x : Vector n // x i = 0} : ℝ)

noncomputable def familyDensitySum
    (f : DirectionalFamily) (n : ℕ) : ℝ :=
  ∑ i : Fin n, directionalDensity i (f n i)

noncomputable def directionalEdgeCount {n : ℕ} (i : Fin n)
    (f : Vector n → Bool) : ℕ :=
  Nat.card {x : Vector n // x i = 0 ∧ f x = true}

noncomputable def familyEdgeCount
    (f : DirectionalFamily) (n : ℕ) : ℕ :=
  ∑ i : Fin n, directionalEdgeCount i (f n i)

def familyC4Free (f : DirectionalFamily) : Prop :=
  ∀ (n : ℕ) (i j : Fin n), i ≠ j → ∀ x : Vector n,
    x i = 0 → x j = 0 →
      ¬ (f n i x = true ∧
        f n i (x + coordinateUnit n j) = true ∧
        f n j x = true ∧
        f n j (x + coordinateUnit n i) = true)

def familyOrbitCapped (f : DirectionalFamily) (M : ℕ → ℕ) : Prop :=
  ∀ (n : ℕ) (i : Fin n),
    literalDirectionalOrbitCard (i := i) (f n i) ≤ M n

def log2Value (x : ℝ) : ℝ :=
  Real.log x / Real.log 2

def eventualOrbitBound (M : ℕ → ℕ) (ε : ℝ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    (M n : ℝ) ≤
      Real.rpow 2
        ((1 - ε) * Real.sqrt
          (log2Value (log2Value (n : ℝ))))

noncomputable def sharpenedColourCount (M : ℕ → ℕ) (n : ℕ) : ℕ :=
  max 2 (coarsePairColourCount (Nat.log 2 (M n)))

def colourLogLittleO (M : ℕ → ℕ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    (sharpenedColourCount M n : ℝ) *
        Real.log (sharpenedColourCount M n : ℝ) ≤
      η * Real.log (n : ℝ)

def densityUpperAsymptotic (f : DirectionalFamily) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    familyDensitySum f n ≤ (n : ℝ) / 2 + η * (n : ℝ)

def edgeUpperAsymptotic (f : DirectionalFamily) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    (familyEdgeCount f n : ℝ) ≤
      (1 / 2 + η) * (n : ℝ) * (2 : ℝ) ^ (n - 1)

/-- Claim 35101: the coefficient-below-one orbit theorem, including its
colour-count asymptotic and both upper conclusions. -/
def claim35101 : Prop :=
  ∀ (ε : ℝ) (M : ℕ → ℕ) (f : DirectionalFamily),
    0 < ε →
    eventualOrbitBound M ε →
    familyC4Free f →
    familyOrbitCapped f M →
    colourLogLittleO M ∧
      densityUpperAsymptotic f ∧
        edgeUpperAsymptotic f

end

end MathlibPlus.Open.ResearchFormalization.GrowingOrbitTheoremClaim35101

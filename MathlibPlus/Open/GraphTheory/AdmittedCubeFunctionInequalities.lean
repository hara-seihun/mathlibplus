import Mathlib

namespace MathlibPlus.Open.GraphTheory.AdmittedCubeFunctionInequalities

open scoped BigOperators Topology
noncomputable section
open Filter

abbrev BoolCube (n : ℕ) := Fin n → Bool
abbrev Omega (n : ℕ) (i : Fin n) := {x : BoolCube n // x i = false}
abbrev SquareBase (n : ℕ) (i j : Fin n) :=
  {x : BoolCube n // x i = false ∧ x j = false}

/-- Flipping one coordinate is addition by a standard basis vector in the
Boolean cube. -/
def flipCoordinate {n : ℕ} (j : Fin n) (x : BoolCube n) : BoolCube n :=
  Function.update x j (Bool.not (x j))

def boolMass (b : Bool) : ℝ := if b then 1 else 0

def boolSign (b : Bool) : ℝ := if b then 1 else -1

def edgeAt {n : ℕ} (f : ∀ i : Fin n, Omega n i → Bool)
    (i : Fin n) (x : BoolCube n) : Bool :=
  if h : x i = false then f i ⟨x, h⟩ else false

def density {n : ℕ} (f : ∀ i : Fin n, Omega n i → Bool) (i : Fin n) : ℝ :=
  (∑ x : Omega n i, boolMass (f i x)) /
    (Fintype.card (Omega n i) : ℝ)

def mismatchDensity {n : ℕ} (f g : ∀ i : Fin n, Omega n i → Bool)
    (i : Fin n) : ℝ :=
  (∑ x : Omega n i, boolMass (f i x != g i x)) /
    (Fintype.card (Omega n i) : ℝ)

def influence {n : ℕ} (f : ∀ i : Fin n, Omega n i → Bool)
    (i j : Fin n) : ℝ :=
  (∑ x : Omega n i,
      boolMass (edgeAt f i x.1 != edgeAt f i (flipCoordinate j x.1))) /
    (Fintype.card (Omega n i) : ℝ)

def completedSquareDensity {n : ℕ}
    (g : ∀ i : Fin n, Omega n i → Bool) (i j : Fin n) : ℝ :=
  (∑ x : SquareBase n i j,
      boolMass
        (edgeAt g i x.1 &&
          edgeAt g i (flipCoordinate j x.1) &&
          edgeAt g j x.1 &&
          edgeAt g j (flipCoordinate i x.1))) /
    (Fintype.card (SquareBase n i j) : ℝ)

def c4Free {n : ℕ} (f : ∀ i : Fin n, Omega n i → Bool) : Prop :=
  ∀ i j, i ≠ j → ∀ x : SquareBase n i j,
    ¬ (edgeAt f i x.1 = true ∧
      edgeAt f i (flipCoordinate j x.1) = true ∧
      edgeAt f j x.1 = true ∧
      edgeAt f j (flipCoordinate i x.1) = true)

def densitySum {n : ℕ} (f : ∀ i : Fin n, Omega n i → Bool)
    (L : Finset (Fin n)) : ℝ :=
  L.sum (fun i => density f i)

def influenceSum {n : ℕ} (f : ∀ i : Fin n, Omega n i → Bool)
    (L : Finset (Fin n)) : ℝ :=
  L.sum (fun i => (L.erase i).sum (fun j => influence f i j))

def gamma {n : ℕ} (f : ∀ i : Fin n, Omega n i → Bool)
    (L : Finset (Fin n)) : ℝ :=
  if L.card = 0 then 0
  else if L.card = 1 then 1 / 2
  else
    min ((L.card : ℝ) / 2)
      (influenceSum f L / (2 * ((L.card : ℝ) - 1)))

/-- Claim 35930: every square made by the approximants is charged to a
literal Hamming mismatch; no freeness or compatibility property is imposed on
the approximants. -/
def completedSquaresPayHammingError_claim35930 : Prop :=
  ∀ (n : ℕ) (f g : ∀ i : Fin n, Omega n i → Bool),
    c4Free f →
    ∀ i j, i ≠ j →
      completedSquareDensity g i j ≤
        2 * mismatchDensity f g i + 2 * mismatchDensity f g j

/-- Claim 35940: the pointwise square-avoidance inequality and its localized
finite-set consequence. -/
def localizedLiteralInfluence_claim35940 : Prop :=
  ∀ (n : ℕ) (f : ∀ i : Fin n, Omega n i → Bool),
    c4Free f →
    (∀ i j, i ≠ j →
      density f i + density f j ≤
        1 + (influence f i j + influence f j i) / 2) ∧
    (∀ L : Finset (Fin n), densitySum f L ≤
      (L.card : ℝ) / 2 + gamma f L)

/-- The Walsh character on the affine coordinate hyperplane Ω_i. -/
noncomputable def walshCharacter {n : ℕ} (i : Fin n) (S : Finset (Fin n))
    (x : Omega n i) : ℝ :=
  (-1 : ℝ) ^ S.sum (fun j => if x.1 j then 1 else 0)

noncomputable def walshCoefficient {n : ℕ}
    (f : ∀ i : Fin n, Omega n i → Bool) (i : Fin n)
    (S : Finset (Fin n)) : ℝ :=
  (∑ x : Omega n i, boolSign (f i x) * walshCharacter i S x) /
    (Fintype.card (Omega n i) : ℝ)

noncomputable def walshSupport {n : ℕ}
    (f : ∀ i : Fin n, Omega n i → Bool) (i : Fin n) : Finset (Finset (Fin n)) := by
  classical
  exact (Finset.univ.powerset.filter
    (fun S => i ∉ S ∧ walshCoefficient f i S ≠ 0))

noncomputable def walshDegree {n : ℕ}
    (f : ∀ i : Fin n, Omega n i → Bool) (i : Fin n) : ℕ :=
  (walshSupport f i).sup Finset.card

def totalInfluence {n : ℕ} (f : ∀ i : Fin n, Omega n i → Bool)
    (i : Fin n) : ℝ :=
  (Finset.univ.erase i).sum (fun j => influence f i j)

def averageWalshDegree {n : ℕ}
    (f : ∀ i : Fin n, Omega n i → Bool) (L : Finset (Fin n)) : ℝ :=
  L.sum (fun i => (walshDegree f i : ℝ)) / (L.card : ℝ)

/-- Claim 35941: total literal influence is controlled by Walsh degree, and
therefore the localized charge is controlled by the average degree. -/
def walshDegreeInfluenceControl_claim35941 : Prop :=
  (∀ (n : ℕ) (f : ∀ i : Fin n, Omega n i → Bool) (i : Fin n),
    totalInfluence f i ≤ (walshDegree f i : ℝ)) ∧
  (∀ (n : ℕ) (f : ∀ i : Fin n, Omega n i → Bool) (L : Finset (Fin n)),
    2 ≤ L.card →
      gamma f L ≤
        ((L.card : ℝ) / (2 * ((L.card : ℝ) - 1))) *
          averageWalshDegree f L ∧
      ((L.card : ℝ) / (2 * ((L.card : ℝ) - 1))) *
          averageWalshDegree f L ≤ averageWalshDegree f L) ∧
  (∀ (F : ∀ n : ℕ, ∀ i : Fin n, Omega n i → Bool)
      (Ls : ∀ n : ℕ, Finset (Fin n)),
    Tendsto
      (fun n => averageWalshDegree (F n) (Ls n) / (n : ℝ))
      atTop (𝓝 0) →
    Tendsto
      (fun n => gamma (F n) (Ls n) / (n : ℝ))
      atTop (𝓝 0))

abbrev F2 := ZMod 2
abbrev F2Cube (n : ℕ) := Fin n → F2
abbrev F2Omega (n : ℕ) (i : Fin n) := {x : F2Cube n // x i = 0}

/-- Literal factorization through a binary linear quotient of rank at most r. -/
noncomputable def factorsThroughBinaryQuotient {n : ℕ} (i : Fin n) (r : ℕ)
    (g : F2Omega n i → Bool) : Prop :=
  ∃ m : ℕ, m ≤ r ∧
    ∃ q : (F2Cube n →ₗ[F2] (Fin m → F2)),
      ∃ h : (Fin m → F2) → Bool,
        ∀ x : F2Omega n i, g x = h (q x.1)

noncomputable def f2HammingDistance {n : ℕ} {i : Fin n}
    (f g : F2Omega n i → Bool) : ℝ :=
  (∑ x : F2Omega n i, boolMass (f x != g x)) /
    (Fintype.card (F2Omega n i) : ℝ)

noncomputable def quotientDistance {n : ℕ} (i : Fin n) (r : ℕ)
    (f : F2Omega n i → Bool) : ℝ :=
  sInf {δ : ℝ | ∃ g : F2Omega n i → Bool,
    factorsThroughBinaryQuotient i r g ∧ δ = f2HammingDistance f g}

def f2EdgeAt {n : ℕ} (f : ∀ i : Fin n, F2Omega n i → Bool)
    (i : Fin n) (x : F2Cube n) : Bool :=
  if h : x i = 0 then f i ⟨x, h⟩ else false

def f2Density {n : ℕ} (f : ∀ i : Fin n, F2Omega n i → Bool) (i : Fin n) : ℝ :=
  (∑ x : F2Omega n i, boolMass (f i x)) /
    (Fintype.card (F2Omega n i) : ℝ)

def f2Excess {n : ℕ} (f : ∀ i : Fin n, F2Omega n i → Bool) (i : Fin n) : ℝ :=
  max 0 (f2Density f i - 1 / 2)

def f2FlipCoordinate {n : ℕ} (j : Fin n) (x : F2Cube n) : F2Cube n :=
  Function.update x j (x j + 1)

abbrev F2SquareBase (n : ℕ) (i j : Fin n) :=
  {x : F2Cube n // x i = 0 ∧ x j = 0}

def f2C4Free {n : ℕ} (f : ∀ i : Fin n, F2Omega n i → Bool) : Prop :=
  ∀ i j, i ≠ j → ∀ x : F2SquareBase n i j,
    ¬ (f2EdgeAt f i x.1 = true ∧
      f2EdgeAt f i (f2FlipCoordinate j x.1) = true ∧
      f2EdgeAt f j x.1 = true ∧
      f2EdgeAt f j (f2FlipCoordinate i x.1) = true)

/-- Claim 35929: the finite excess-weighted quotient inequality with literal
Hamming distance and no compatibility requirement on the chosen quotients. -/
def excessWeightedFiniteInequality_claim35929 : Prop :=
  ∀ (C : ℝ), 4 ≤ C →
  ∀ (n r t : ℕ), 2 ≤ t →
  ∀ (f : ∀ i : Fin n, F2Omega n i → Bool), f2C4Free f →
    let B : ℝ := 2 ^ r + (r + 1 : ℝ) / 2
    let m : ℕ := 2 ^ (r + 1) - 1
    let H : ℝ := (r + 1 : ℝ) * (t - 1 : ℝ) *
      (C * (t : ℝ) * Real.log (2 * (m : ℝ))) ^ m
    (∑ i : Fin n, f2Density f i) ≤
      (n : ℝ) / 2 + (n : ℝ) * B / t + H / 2 +
        ∑ i : Fin n,
          min (f2Excess f i) ((t : ℝ) * quotientDistance i r (f i))

end
end MathlibPlus.Open.GraphTheory.AdmittedCubeFunctionInequalities

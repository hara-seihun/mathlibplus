import Mathlib

noncomputable section

namespace MathlibPlus.Open.ResearchFormalizationBatch_019ffedc_a806_7e1a_8dbd_a24540be0245

/- Five-dimensional Newton staircase claims. -/

def newtonStaircase (r : ℝ) : ℝ := Int.fract r / r ^ 3

def radialHalfDensity (y : ℝ) : ℝ :=
  let r := Real.exp (-y)
  Real.rpow r (5 / 2 : ℝ) * newtonStaircase r

def fiveDimensionalNewtonStaircase : Prop :=
  ∀ y : ℝ,
    radialHalfDensity y =
      Real.rpow (Real.exp (-y)) (-(1 / 2 : ℝ)) * Int.fract (Real.exp (-y))

def radialLaplacianFive (g : ℝ → ℝ) (r : ℝ) : ℝ :=
  deriv (deriv g) r + (4 / r) * deriv g r

def fiveDimensionalAnnulusAndBulkLaplacian : Prop :=
  (∀ (n : ℕ) (r : ℝ),
    (n : ℝ) < r ∧ r < (n : ℝ) + 1 →
      newtonStaircase r = 1 / r ^ 2 - (n : ℝ) / r ^ 3 ∧
        radialLaplacianFive newtonStaircase r = -2 / r ^ 4) ∧
  (∀ r : ℝ, 0 < r →
    radialLaplacianFive (fun x : ℝ => 1 / x ^ 3) r = 0 ∧
      radialLaplacianFive (fun x : ℝ => 1 / x ^ 2) r = -2 / r ^ 4)

/- Reciprocal shell coordinates and the product-fiber rapidity identity. -/

def reciprocalShellX (m : ℕ) (c d : ℝ) : ℝ :=
  Real.pi * (m : ℝ) ^ 2 * Real.exp (2 * c + 2 * d)

def reciprocalShellY (n : ℕ) (c d : ℝ) : ℝ :=
  Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * c - 2 * d)

def reciprocalShellCenterRelativeCoordinates : Prop :=
  ∀ (m n : ℕ) (c d t : ℝ),
    0 < m → 0 < n → 0 < t → t < 1 →
      reciprocalShellX m c d =
          Real.pi * (m : ℝ) ^ 2 * Real.exp (2 * c + 2 * d) ∧
        reciprocalShellY n c d =
          Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * c - 2 * d)

def hilleHardyRapidityProductFiber : Prop :=
  ∀ (m n : ℕ) (c d t : ℝ),
    0 < m → 0 < n → 0 < t → t < 1 →
      2 * Real.sqrt (reciprocalShellX m c d * reciprocalShellY n c d * t) / (1 - t) =
        2 * Real.pi * (m : ℝ) * (n : ℝ) * Real.exp (2 * c) * Real.sqrt t / (1 - t)

/- Rank-four monomer/dimer channel data. -/

abbrev Vec8 := Fin 8 → ℝ
abbrev Mat4 := Matrix (Fin 4) (Fin 4) ℝ

def channelVector (r : ℝ) : Vec8 :=
  fun j => r ^ j.val / (Nat.factorial (2 * j.val) : ℝ)

def bezoutMap (u v : Vec8) : Mat4 :=
  fun i j =>
    Finset.sum
      (Finset.filter
        (fun a : Fin 4 => a.val ≤ Nat.min i.val j.val) Finset.univ)
      (fun a =>
        ((i.val + j.val + 1 - 2 * a.val : ℕ) : ℝ) *
          u ⟨a.val, by omega⟩ *
            v ⟨i.val + j.val + 1 - a.val, by omega⟩)

def channelC0 : Mat4 := bezoutMap (channelVector 1) (channelVector 1)

def channelA (r : ℝ) : Mat4 :=
  channelC0⁻¹ *
    (bezoutMap (channelVector 1) (channelVector r) +
      bezoutMap (channelVector r) (channelVector 1))

def channelE (r s : ℝ) : Mat4 :=
  channelC0⁻¹ *
    (bezoutMap (channelVector r) (channelVector s) +
      bezoutMap (channelVector s) (channelVector r))

def normalizedRankFourMonomerAndDimerMatrices : Prop :=
  (∀ (r : ℝ) (j : Fin 8),
    channelVector r j = r ^ j.val / (Nat.factorial (2 * j.val) : ℝ)) ∧
  (∀ (u v : Vec8) (i j : Fin 4),
    bezoutMap u v i j =
      Finset.sum
        (Finset.filter
          (fun a : Fin 4 => a.val ≤ Nat.min i.val j.val) Finset.univ)
        (fun a =>
          ((i.val + j.val + 1 - 2 * a.val : ℕ) : ℝ) *
            u ⟨a.val, by omega⟩ *
              v ⟨i.val + j.val + 1 - a.val, by omega⟩)) ∧
  channelC0 = bezoutMap (channelVector 1) (channelVector 1) ∧
  (∀ (r : ℝ),
    channelA r =
      channelC0⁻¹ *
        (bezoutMap (channelVector 1) (channelVector r) +
          bezoutMap (channelVector r) (channelVector 1))) ∧
  (∀ (r s : ℝ),
    channelE r s =
      channelC0⁻¹ *
        (bezoutMap (channelVector r) (channelVector s) +
          bezoutMap (channelVector s) (channelVector r)))

/-- The vectors and projection asserted by the unit-channel data. -/
def channelUnitRight : Fin 4 → ℝ :=
  fun i => if i = 0 then 1 else 0

def channelUnitLeft : Fin 4 → ℝ :=
  fun i =>
    match i.val with
    | 0 => 5040
    | 1 => 840
    | 2 => 42
    | _ => 1

def channelUnitProjection : Mat4 :=
  fun i j => channelUnitRight i * channelUnitLeft j / 5040

def unitChannelProjectionData : Prop :=
  Matrix.mulVec (channelA 0) channelUnitRight = channelUnitRight ∧
  (fun i => ∑ j : Fin 4, channelUnitLeft j * channelA 0 j i) = channelUnitLeft ∧
  (∑ i : Fin 4, channelUnitLeft i * channelUnitRight i) = 5040 ∧
  channelUnitProjection * channelUnitProjection = channelUnitProjection ∧
  Matrix.rank channelUnitProjection = 1 ∧
  channelUnitProjection =
    fun i j => channelUnitRight i * channelUnitLeft j / 5040

def exactProjectedMonomerDimerLaws : Prop :=
  (∀ r : ℝ,
    channelUnitProjection * channelA r * channelUnitProjection =
      (1 + r) • channelUnitProjection) ∧
  (∀ (r s : ℝ),
    channelUnitProjection * channelE r s * channelUnitProjection =
      (r + s) • channelUnitProjection)

end MathlibPlus.Open.ResearchFormalizationBatch_019ffedc_a806_7e1a_8dbd_a24540be0245

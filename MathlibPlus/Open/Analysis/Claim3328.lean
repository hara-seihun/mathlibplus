import Mathlib

open scoped BigOperators
open Filter MeasureTheory Topology

namespace MathlibPlus.Open.Analysis.Claim3328

private def validNode (N : ℝ → ℕ) (L : ℝ) (n : ℕ) : Prop :=
  1 ≤ n ∧ n ≤ N L

/-- The scale-dependent smooth monotone train in the admitted C-0227 packet. -/
def smoothMonotoneDenseTrain
    (N : ℝ → ℕ) (y t : ℝ → ℕ → ℝ) (d eta q R : ℝ → ℝ)
    (g : ℝ → ℝ → ℝ) (p r Y dLimit : ℝ) : Prop :=
  dLimit > Real.pi ∧
    Tendsto d atTop (𝓝 dLimit) ∧
    Tendsto (fun L : ℝ => q L * Real.log (1 + R L / eta L))
      atTop (𝓝 0) ∧
    ∀ᶠ L : ℝ in atTop,
      1 ≤ L ∧ 0 < eta L ∧ 0 ≤ q L ∧ 0 ≤ R L ∧
      (N L : ℝ) ≤ Real.rpow L p ∧
      R L ≤ Real.rpow L r ∧
      (∀ n : ℕ, validNode N L n → eta L ≤ y L n ∧ y L n ≤ Y) ∧
      (∀ n : ℕ, validNode N L n → y L n = g L (t L n)) ∧
      (∀ u : ℝ, 0 < g L u) ∧
      (∀ u v : ℝ, u ≤ v → g L v ≤ g L u) ∧
      (∀ u v : ℝ, |g L u - g L v| ≤ q L * |u - v|) ∧
      (∀ i j : ℕ, validNode N L i → validNode N L j →
        |t L i - t L j| ≤ R L) ∧
      (∀ n : ℕ, 1 ≤ n → n < N L →
        t L n < t L (n + 1) ∧
        t L (n + 1) - t L n ≥ d L / L ∧
        y L (n + 1) ≤ y L n)

private noncomputable def trainNode
    (y t : ℝ → ℕ → ℝ) (L : ℝ) (n : ℕ) : ℂ :=
  (y L n : ℂ) - Complex.I * (t L n : ℂ)

private noncomputable def shiftedBlaschke
    (y t : ℝ → ℕ → ℝ) (L : ℝ) (n : ℕ) (w : ℂ) : ℂ :=
  Finset.prod (Finset.Icc 1 (n - 1)) (fun k =>
    (w - trainNode y t L k) /
      (w + star (trainNode y t L k)))

private noncomputable def takenakaMalmquistFunction
    (y t : ℝ → ℕ → ℝ) (L : ℝ) (n : ℕ) (w : ℂ) : ℂ :=
  (Real.sqrt (2 * y L n) : ℂ) /
    (w + star (trainNode y t L n)) *
      shiftedBlaschke y t L n w

private noncomputable def laplaceKernel
    (y t : ℝ → ℕ → ℝ) (L : ℝ) (n : ℕ) (w : ℂ) : ℂ :=
  1 / (w + star (trainNode y t L n))

private def hardyKernelSpan
    (N : ℝ → ℕ) (y t : ℝ → ℕ → ℝ) (L : ℝ) :
    Submodule ℂ (ℂ → ℂ) :=
  Submodule.span ℂ {F : ℂ → ℂ |
    ∃ n : ℕ, validNode N L n ∧ F = laplaceKernel y t L n}

private def takenakaSpan
    (N : ℝ → ℕ) (y t : ℝ → ℕ → ℝ) (L : ℝ) :
    Submodule ℂ (ℂ → ℂ) :=
  Submodule.span ℂ {F : ℂ → ℂ |
    ∃ n : ℕ, validNode N L n ∧
      F = takenakaMalmquistFunction y t L n}

private def inverseLaplaceRelation
    (F : ℂ → ℂ) (f : ℝ → ℂ) : Prop :=
  ∀ w : ℂ, 0 < w.re →
    IntegrableOn
        (fun x : ℝ => Complex.exp (-w * (x : ℂ)) * f x)
        (Set.Ioi 0) ∧
      ∫ x in Set.Ioi (0 : ℝ),
          Complex.exp (-w * (x : ℂ)) * f x = F w

/-- The actual TM functions, their inverse-Laplace transforms, and their
orthonormal Hardy-span carrier. -/
def takenakaMalmquistBasis
    (N : ℝ → ℕ) (y t : ℝ → ℕ → ℝ)
    (phi : ℝ → ℕ → ℝ → ℂ) : Prop :=
  (∀ L : ℝ,
    hardyKernelSpan N y t L = takenakaSpan N y t L) ∧
  (∀ L : ℝ, ∀ n : ℕ, validNode N L n →
    takenakaMalmquistFunction y t L n ∈ hardyKernelSpan N y t L ∧
      inverseLaplaceRelation
        (takenakaMalmquistFunction y t L n)
        (phi L n)) ∧
  (∀ L : ℝ, ∀ i j : ℕ, validNode N L i → validNode N L j →
      IntegrableOn (fun x : ℝ => ‖phi L i x‖ ^ 2) (Set.Ioi 0) ∧
      ∫ x in Set.Ioi (0 : ℝ),
          star (phi L i x) * phi L j x =
        if i = j then 1 else 0)

private def individualCompactTailBound
    (N : ℝ → ℕ) (y : ℝ → ℕ → ℝ) (d : ℝ → ℝ)
    (phi : ℝ → ℕ → ℝ → ℂ) (theta : ℝ) : Prop :=
  ∃ error : ℝ → ℝ, Tendsto error atTop (𝓝 0) ∧
    ∃ Ctheta : ℝ, 0 ≤ Ctheta ∧
      ∀ᶠ L : ℝ in atTop,
        ∀ n : ℕ, validNode N L n →
          IntegrableOn (fun x : ℝ => ‖phi L n x‖ ^ 2)
            (Set.Ioi (2 * L)) ∧
          (∫ x in Set.Ioi (2 * L), ‖phi L n x‖ ^ 2) ≤
            Ctheta * Real.exp
              (-(4 - 4 * Real.pi / d L - error L) *
                theta * y L n * L)

private noncomputable def logarithmicHeightFloor (A L : ℝ) : ℝ :=
  A * Real.log L / L

private noncomputable def compactTailNormSq
    (phi : ℝ → ℕ → ℝ → ℂ) (L : ℝ) (n : ℕ) : ℝ :=
  ∫ x in Set.Ioi (2 * L), ‖phi L n x‖ ^ 2

/--
The logarithmic floor makes the finite sum of the exact TM compact tails
vanish.  The tail estimate is stated on the actual inverse-Laplace family,
not as a free callback.
-/
def logarithmicHeightFloorAndVanishingTotalTail : Prop :=
  ∀ (theta : ℝ) (p A dLimit : ℝ)
    (N : ℝ → ℕ) (y t : ℝ → ℕ → ℝ)
    (d q R : ℝ → ℝ) (g : ℝ → ℝ → ℝ)
    (r Y : ℝ) (phi : ℝ → ℕ → ℝ → ℂ),
    0 < theta → theta < 1 →
    dLimit > Real.pi →
    0 < theta * (4 - 4 * Real.pi / dLimit) →
    A > p / (theta * (4 - 4 * Real.pi / dLimit)) →
    smoothMonotoneDenseTrain N y t d
      (fun L => logarithmicHeightFloor A L) q R g p r Y dLimit →
    takenakaMalmquistBasis N y t phi →
    individualCompactTailBound N y d phi theta →
      Tendsto
        (fun L : ℝ =>
          Finset.sum (Finset.Icc 1 (N L))
            (fun n => compactTailNormSq phi L n))
        atTop (𝓝 0)

end MathlibPlus.Open.Analysis.Claim3328

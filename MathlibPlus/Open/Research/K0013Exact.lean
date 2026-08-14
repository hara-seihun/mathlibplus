import Mathlib

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.Research.K0013

/-- The rising factorial `(α)_n` used by the admitted K-0013 claims. -/
def risingFactorial (α : ℝ) (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, (α + (k : ℝ))

/-- Gamma moments and normalized moments from Claim 7497. -/
def gammaMoment (α : ℝ) (n : ℕ) : ℝ := risingFactorial α n

def gammaH (α : ℝ) (n : ℕ) : ℝ :=
  risingFactorial α n / (Nat.factorial (2 * n) : ℝ)

/-- The completed Bézout matrix entry in Claim 7497. -/
def completedBezoutEntry (α : ℝ) (i j : ℕ) : ℝ :=
  ∑ a ∈ Finset.range (min i j + 1),
    ((i + j + 1 - 2 * a : ℕ) : ℝ) *
      gammaH α a * gammaH α (i + j + 1 - a)

def completedBezoutMatrix (α : ℝ) : Matrix ℕ ℕ ℝ :=
  fun i j => completedBezoutEntry α i j

def completedBezoutSection (α : ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => completedBezoutEntry α i.1 j.1

/-- Claim 7497: moments, the infinite entry formula, and its leading sections. -/
def claim7497 (α : ℝ) (N : ℕ) : Prop :=
  (∀ n : ℕ,
    gammaMoment α n = risingFactorial α n ∧
      gammaH α n = risingFactorial α n / (Nat.factorial (2 * n) : ℝ)) ∧
    ∀ i j : Fin N,
      completedBezoutSection α N i j = completedBezoutMatrix α i.1 j.1 ∧
        completedBezoutMatrix α i.1 j.1 =
          ∑ a ∈ Finset.range (min i.1 j.1 + 1),
            ((i.1 + j.1 + 1 - 2 * a : ℕ) : ℝ) *
              gammaH α a * gammaH α (i.1 + j.1 + 1 - a)

/-- Coefficients of the two shifted Kummer series in Claim 7498. -/
def aCoeff (α : ℝ) (j n : ℕ) : ℝ :=
  risingFactorial (α + (j : ℝ)) n /
    ((4 : ℝ) ^ n * (Nat.factorial n : ℝ) *
      risingFactorial ((2 : ℝ) * (j : ℝ) + (1 / 2 : ℝ)) n)

def pCoeff (α : ℝ) (j n : ℕ) : ℝ :=
  risingFactorial (α + (j : ℝ) + 1) n /
    ((4 : ℝ) ^ n * (Nat.factorial n : ℝ) *
      risingFactorial ((2 : ℝ) * (j : ℝ) + (3 / 2 : ℝ)) n)

def aSeries (α : ℝ) (j : ℕ) : PowerSeries ℝ :=
  PowerSeries.mk (aCoeff α j)

def pSeries (α : ℝ) (j : ℕ) : PowerSeries ℝ :=
  PowerSeries.mk (pCoeff α j)

/-- A nested power-series ring represents the two formal variables `(z,w)`. -/
abbrev KernelSeries := PowerSeries (PowerSeries ℝ)

def embedInner (s : PowerSeries ℝ) : KernelSeries :=
  PowerSeries.C s

def outerize (s : PowerSeries ℝ) : KernelSeries :=
  PowerSeries.map (PowerSeries.C : ℝ →+* PowerSeries ℝ) s

def kernelZ : KernelSeries := PowerSeries.C PowerSeries.X

def kernelW : KernelSeries := PowerSeries.X

def kernelNumerator (α : ℝ) (j : ℕ) : KernelSeries :=
  embedInner (aSeries α j) * kernelW * outerize (pSeries α j) -
    kernelZ * embedInner (pSeries α j) * outerize (aSeries α j)

/-- The coefficient formula stated in Claim 7500. -/
def qUpperCoeff (α : ℝ) (j u v : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (u + 1),
    (aCoeff α j k * pCoeff α j (u + v - k) -
      if 0 < k then pCoeff α j (k - 1) * aCoeff α j (u + v + 1 - k) else 0)

def qCoeff (α : ℝ) (j u v : ℕ) : ℝ :=
  if u ≤ v then qUpperCoeff α j u v else qUpperCoeff α j v u

def qSeries (α : ℝ) (j : ℕ) : KernelSeries :=
  PowerSeries.mk (fun v => PowerSeries.mk (fun u => qCoeff α j u v))

/-- Claim 7498: the formal kernel quotient, its symmetry, and the derivative data. -/
def claim7498 (α : ℝ) (j : ℕ) : Prop :=
  (kernelW - kernelZ) * qSeries α j = kernelNumerator α j ∧
    (∀ u v : ℕ,
      (PowerSeries.coeff u) ((PowerSeries.coeff v) (qSeries α j)) =
        (PowerSeries.coeff v) ((PowerSeries.coeff u) (qSeries α j))) ∧
    (∀ u v : ℕ,
      (PowerSeries.coeff u) ((PowerSeries.coeff v) (kernelNumerator α j)) =
        -((PowerSeries.coeff v) ((PowerSeries.coeff u) (kernelNumerator α j)))) ∧
    (∀ T : KernelSeries,
      (kernelW - kernelZ) * T = kernelNumerator α j → T = qSeries α j) ∧
    aSeries α 0 = PowerSeries.mk (gammaH α) ∧
    (PowerSeries.derivative ℝ) (aSeries α j) =
      ((α + (j : ℝ)) / (2 * ((4 : ℝ) * (j : ℝ) + 1))) • pSeries α j

/-- Claim 7499: the exact rank-one Darboux peel. -/
def darbouzCoefficient (α : ℝ) (j : ℕ) : ℝ :=
  ((α + (j : ℝ) + 1) * (2 * α - 2 * (j : ℝ) - 1)) /
    (2 * ((4 : ℝ) * (j : ℝ) + 1) * ((4 : ℝ) * (j : ℝ) + 3) ^ 2 *
      ((4 : ℝ) * (j : ℝ) + 5))

def claim7499 (α : ℝ) (j : ℕ) : Prop :=
  qSeries α j =
    embedInner (pSeries α j) * outerize (pSeries α j) +
      darbouzCoefficient α j • (kernelZ * kernelW * qSeries α (j + 1))

/-- Claim 7500: coefficientwise anti-diagonal formula and symmetry. -/
def claim7500 (α : ℝ) (j : ℕ) : Prop :=
  (∀ u v : ℕ, u ≤ v →
    (PowerSeries.coeff u) ((PowerSeries.coeff v) (qSeries α j)) =
      ∑ k ∈ Finset.range (u + 1),
        (aCoeff α j k * pCoeff α j (u + v - k) -
          if 0 < k then pCoeff α j (k - 1) * aCoeff α j (u + v + 1 - k) else 0)) ∧
    ∀ u v : ℕ,
      (PowerSeries.coeff u) ((PowerSeries.coeff v) (qSeries α j)) =
        (PowerSeries.coeff v) ((PowerSeries.coeff u) (qSeries α j))

/-- The lower-triangular coefficient matrix in Claim 7503. -/
def LEntry (α : ℝ) (i j : ℕ) : ℝ :=
  if j ≤ i then
    risingFactorial (α + (j : ℝ) + 1) (i - j) /
      ((4 : ℝ) ^ (i - j) * (Nat.factorial (i - j) : ℝ) *
        risingFactorial ((2 : ℝ) * (j : ℝ) + (3 / 2 : ℝ)) (i - j))
  else 0

def LMatrix (α : ℝ) : Matrix ℕ ℕ ℝ :=
  fun i j => LEntry α i j

def UnitLowerTriangular (L : Matrix ℕ ℕ ℝ) : Prop :=
  (∀ i j : ℕ, i < j → L i j = 0) ∧ ∀ i : ℕ, L i i = 1

/-- Claim 7503: explicit entries, coefficient realization, and unit lower-triangularity. -/
def claim7503 (α : ℝ) : Prop :=
  (∀ i j : ℕ, j ≤ i →
    LEntry α i j =
      risingFactorial (α + (j : ℝ) + 1) (i - j) /
        ((4 : ℝ) ^ (i - j) * (Nat.factorial (i - j) : ℝ) *
          risingFactorial ((2 : ℝ) * (j : ℝ) + (3 / 2 : ℝ)) (i - j))) ∧
    (∀ i j : ℕ, i < j → LEntry α i j = 0) ∧
    (∀ i j : ℕ,
      LEntry α i j = (PowerSeries.coeff i) (PowerSeries.X ^ j * pSeries α j)) ∧
    (∀ i : ℕ, LEntry α i i = 1) ∧ UnitLowerTriangular (LMatrix α)

/-- Positivity of every completed Bézout determinant through rank `N`. -/
def allLeadingDeterminantsPositive (α : ℝ) (N : ℕ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → n ≤ N →
    0 < Matrix.det (completedBezoutSection α n)

/-- Claim 7506: the consecutive positivity chamber and its variance coordinates. -/
def claim7506 : Prop :=
  ∀ N : ℕ, 1 ≤ N → ∀ α : ℝ, 0 < α →
    (allLeadingDeterminantsPositive α N ↔ α > (N : ℝ) - (3 / 2 : ℝ)) ∧
      (allLeadingDeterminantsPositive α N ↔
        1 < 1 + 1 / α ∧
          1 + 1 / α < 1 + 2 / ((2 : ℝ) * (N : ℝ) - 3))

end MathlibPlus.Open.Research.K0013

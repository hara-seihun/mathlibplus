import Mathlib

open scoped BigOperators
open Filter Topology

namespace MathlibPlus.Open.ResearchFormalization.ZeroMotion

noncomputable section

/-- A bi-infinite strictly increasing configuration escaping at both ends. -/
def zeroConfiguration (x : ℤ → ℝ) : Prop :=
  StrictMono x ∧ Tendsto x atTop atTop ∧ Tendsto x atBot atBot

/-- The symmetric principal-value interpretation of the primed interaction. -/
def symmetricPrimedInteraction (x : ℤ → ℝ) (i : ℤ) (s : ℝ) : Prop :=
  Tendsto
    (fun N : ℕ =>
      ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        if j ≠ i then 1 / (x i - x j) else 0)
    atTop (nhds s)

/-- The exact De Bruijn--Newman zero-motion vector field. -/
def deBruijnNewmanZeroMotion (x : ℝ → ℤ → ℝ) (t : ℝ) : Prop :=
  zeroConfiguration (x t) ∧
    ∀ i : ℤ, ∃ s : ℝ,
      symmetricPrimedInteraction (x t) i s ∧
      HasDerivAt (fun r => x r i) (2 * s) t

/-- The adjacent pressure, with the two adjacent indices excluded from the
absolutely convergent pressure series. -/
def pressureSummand (x : ℤ → ℝ) (i m : ℤ) : ℝ :=
  if m ≠ i ∧ m ≠ i + 1 then
    1 / ((x (i + 1) - x m) * (x i - x m))
  else 0

def pressureAt (x d : ℤ → ℝ) (i : ℤ) : ℝ :=
  2 - (d i) ^ 2 * ∑' m : ℤ, pressureSummand x i m

/-- The gap flow attached to a zero configuration and the normalized
symmetric gap profile. -/
def rootGapFlow (x : ℝ → ℤ → ℝ) (t : ℝ) (i : ℤ) : ℝ :=
  x t (i + 1) - x t i

def gapProfileStatic (d : ℤ → ℝ) (k : ℤ) (r : ℕ) : ℝ :=
  1 / d k *
    ∑ j ∈ Finset.range r,
      (d (k - (j : ℤ) - 1) + d (k + (j : ℤ) + 1) - 2 * d k)

def gapProfile (d : ℝ → ℤ → ℝ) (t : ℝ) (k : ℤ) (r : ℕ) : ℝ :=
  gapProfileStatic (d t) k r

def rootGapProfile (x : ℝ → ℤ → ℝ) (t : ℝ) (k : ℤ) (r : ℕ) : ℝ :=
  gapProfile (rootGapFlow x) t k r

/-- The exact pressure-curvature bracket from the profile evolution. -/
def correlatedPressureStatic (d P : ℤ → ℝ) (k : ℤ) (r : ℕ) : ℝ :=
  (∑ j ∈ Finset.range r,
      (d k * P (k - (j : ℤ) - 1) / d (k - (j : ℤ) - 1) +
        d k * P (k + (j : ℤ) + 1) / d (k + (j : ℤ) + 1) - 2 * P k)) -
    gapProfileStatic d k r * P k

def correlatedPressureFromRoots
    (x : ℝ → ℤ → ℝ) (t : ℝ) (k : ℤ) (r : ℕ) : ℝ :=
  correlatedPressureStatic (rootGapFlow x t)
    (fun i => pressureAt (x t) (rootGapFlow x t) i) k r

/-- The exact gap evolution supplied by the zero-motion vector field. -/
def exactGapEvolution (x : ℝ → ℤ → ℝ) (t : ℝ) : Prop :=
  ∀ i : ℤ,
    0 < rootGapFlow x t i ∧
      HasDerivAt (fun s => rootGapFlow x s i)
        (2 * pressureAt (x t) (rootGapFlow x t) i /
          rootGapFlow x t i) t

/-- The dense-tail gap train and its recursively defined roots. -/
def denseTailGap (q ε : ℝ) (i : ℤ) : ℝ :=
  (ε + q ^ i.natAbs) / (1 + ε)

def denseTailRoot (q ε : ℝ) (i : ℤ) : ℝ :=
  if 0 ≤ i then
    ∑ n ∈ Finset.range i.natAbs, denseTailGap q ε (n : ℤ)
  else
    -(∑ n ∈ Finset.range i.natAbs,
      denseTailGap q ε (-((n : ℤ) + 1)))

def denseTailPressure (q ε : ℝ) (i : ℤ) : ℝ :=
  pressureAt (denseTailRoot q ε) (denseTailGap q ε) i

def profileDerivativeStatic (d P : ℤ → ℝ) (k : ℤ) (r : ℕ) : ℝ :=
  2 / (d k) ^ 2 * correlatedPressureStatic d P k r

def denseTailProfileDerivative (q ε : ℝ) : ℝ :=
  profileDerivativeStatic (denseTailGap q ε) (denseTailPressure q ε) 0 1

/-- The sign function in the dense-tail asymptotic. -/
def profileSignFunction (q : ℝ) : ℝ :=
  Real.log (1 + q - q ^ 2) + (2 * q - 1) * Real.log q

/-- A dynamic dense-tail family is tied to the explicit train, the exact
zero-motion field, the exact pressure gap evolution, and the actual profile
derivative; it is not an unconstrained pressure callback. -/
def denseTailFlow (q : ℝ) (X : ℝ → ℝ → ℤ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    let x : ℝ → ℤ → ℝ := fun t i => X ε t i
    (∀ i : ℤ, x 0 i = denseTailRoot q ε i) ∧
      deBruijnNewmanZeroMotion x 0 ∧
      exactGapEvolution x 0 ∧
      (∀ i : ℤ, Summable (fun m : ℤ => ‖pressureSummand (x 0) i m‖)) ∧
      HasDerivAt (fun t : ℝ => rootGapProfile x t 0 1)
        (denseTailProfileDerivative q ε) 0

/-- Claim 22292: the displayed logarithmic inequality is itself asserted;
its derivative consequence, positivity of the exact sign function, and the
resulting `E₀,₁' → -∞` conclusion are all retained on the exact dense-tail
zero-motion carrier. -/
def strictProfileSignPositivity : Prop :=
  ∀ q : ℝ, 0 < q → q < 1 →
    Real.log q < 2 * (q - 1) / (q + 1) ∧
      deriv profileSignFunction q < 0 ∧
      profileSignFunction 1 = 0 ∧
      0 < profileSignFunction q ∧
      Tendsto (fun ε : ℝ => denseTailProfileDerivative q ε)
        (nhdsWithin 0 (Set.Ioi 0)) atBot ∧
      (∀ X : ℝ → ℝ → ℤ → ℝ,
        denseTailFlow q X →
          Tendsto
            (fun ε : ℝ => deriv
              (fun t : ℝ =>
                rootGapProfile (fun s i => X ε s i) t 0 1) 0)
            (nhdsWithin 0 (Set.Ioi 0)) atBot)

/-- Claim 22293: arbitrary finite one-sided profile control can coexist with
arbitrarily negative actual central profile curvature under the exact
zero-motion field. -/
def oneSidedProfilesDoNotControlBackwardPressureCurvature : Prop :=
  ∀ (R : ℕ), 1 ≤ R → ∀ η M : ℝ, 0 < η → 0 < M →
    ∃ (q ε : ℝ) (x : ℝ → ℤ → ℝ),
      0 < q ∧ q < 1 ∧ 0 < ε ∧
      (∀ i : ℤ, x 0 i = denseTailRoot q ε i) ∧
      zeroConfiguration (x 0) ∧
      denseTailGap q ε 0 = 1 ∧
      (∀ i : ℤ, 0 < denseTailGap q ε i) ∧
      (∀ i : ℤ, rootGapFlow x 0 i = denseTailGap q ε i) ∧
      deBruijnNewmanZeroMotion x 0 ∧
      exactGapEvolution x 0 ∧
      (∀ i : ℤ, Summable (fun m : ℤ => ‖pressureSummand (x 0) i m‖)) ∧
      (∀ k : ℤ, ∀ j : ℕ, 1 ≤ j → j ≤ R →
        denseTailGap q ε (k - (j : ℤ)) +
            denseTailGap q ε (k + (j : ℤ)) -
            2 * denseTailGap q ε k ≤
          η * denseTailGap q ε k * (j : ℝ) ^ 2) ∧
      ∃ v : ℝ,
        HasDerivAt (fun t : ℝ => rootGapProfile x t 0 1) v 0 ∧
          v < -M

/-- Claim 22294: after imposing the exact zero-motion field and its exact
pressure-driven gap evolution, the correlated functional is precisely the
profile derivative numerator. -/
def correlatedPressureFunctionalIdentity : Prop :=
  ∀ (x : ℝ → ℤ → ℝ) (t : ℝ) (k : ℤ) (r : ℕ),
    1 ≤ r →
    deBruijnNewmanZeroMotion x t →
    exactGapEvolution x t →
    HasDerivAt (fun s : ℝ => rootGapProfile x s k r)
      (2 * correlatedPressureFromRoots x t k r /
        (rootGapFlow x t k) ^ 2) t

end

end MathlibPlus.Open.ResearchFormalization.ZeroMotion

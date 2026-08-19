import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.BatchR2411R2412

noncomputable section

/-- Claim 40879: exact positive equal-product gcd reduction, including the
reduced factors, coprimality, divisibility consequences, and one common
quotient. -/
def claim40879_equalProductReducedRatio : Prop :=
  ∀ m m' n n' : ℕ,
    0 < m → 0 < m' → 0 < n → 0 < n' →
      m * n = m' * n' →
        let g := Nat.gcd m m'
        let r := m / g
        let s := m' / g
        Nat.Coprime r s ∧
          m = g * r ∧ m' = g * s ∧
            s ∣ n ∧ r ∣ n' ∧
              ∃ h : ℕ, n = s * h ∧ n' = r * h

/-- Claim 40884: the full complex improved-triangle change of variables and
its norm bound, with the source's real parameter range. -/
def claim40884_improvedTriangleChangeOfVariables : Prop :=
  ∀ (A B : ℂ) (a : ℝ), 0 ≤ a → a < 1 →
    let F : ℂ := B - (a : ℂ) * A
    let K : ℂ := A - (a : ℂ) * B
    B - A = (F - K) / (1 + (a : ℂ)) ∧
      (((1 - a) / (1 + a) : ℝ) : ℂ) * (B + A) =
        (F + K) / (1 + (a : ℂ)) ∧
      max ‖B - A‖ (((1 - a) / (1 + a)) * ‖B + A‖) ≤
        (‖F‖ + ‖K‖) / (1 + a)

private def phi40889 (u : ℝ) : ℝ :=
  ∑' n : ℕ,
    (2 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp (9 * u) -
      3 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (5 * u)) *
      Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (4 * u))

/-- The exact Polymath/de Bruijn--Newman heat family used as the standard
normalization carrier for Claim 40889. -/
private def heatFamily40889 (t : ℝ) (z : ℂ) : ℂ :=
  ∫ u in Set.Ici (0 : ℝ),
    Complex.exp (((t * u ^ 2 : ℝ) : ℂ)) *
      (phi40889 u : ℂ) * Complex.cos (z * (u : ℂ))

private def allZerosReal40889 (t : ℝ) : Prop :=
  ∀ z : ℂ, heatFamily40889 t z = 0 → z.im = 0

private noncomputable def lambda40889 : ℝ :=
  sInf {t : ℝ | allZerosReal40889 t}

/-- Claim 40889: the certified bound is attached to the exact standard
heat-family zero threshold, rather than to an arbitrary real parameter; the
numerical parameter certificate and its improvement are retained alongside
it. -/
def claim40889_certifiedDeBruijnNewmanUpperBound : Prop :=
  lambda40889 ≤ (1729 : ℝ) / 10000 ∧
    let X : ℕ := 6000000185827
    let t₀ : ℚ := 3377 / 20000
    let y₀ : ℚ := 9 / 100
    X = 6000000185827 ∧
      t₀ + y₀ ^ 2 / 2 = 1729 / 10000 ∧
      (11 : ℚ) / 50 - (t₀ + y₀ ^ 2 / 2) = 471 / 10000

end
end MathlibPlus.Open.ResearchFormalization.BatchR2411R2412

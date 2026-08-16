import Mathlib

open scoped BigOperators
open Polynomial

namespace MathlibPlus.Open.NewResearch2.RationalHankelCertification15113

noncomputable section

/-- The finite index of normalized numerator jets at the roots of a shell. -/
abbrev JetIndex (J : ℕ) (m : Fin J → ℕ) := Σ j : Fin J, Fin (m j)

/-- The jet index with one copy for each numerator channel. -/
abbrev JetChannelIndex (d J : ℕ) (m : Fin J → ℕ) :=
  JetIndex J m × Fin d

/-- The Euclidean norm on a finite complex vector. -/
def euclideanNorm {ι : Type*} [Fintype ι] (x : ι → ℂ) : ℝ :=
  Real.sqrt (∑ i, ‖x i‖ ^ 2)

/-- Singular values of a finite complex matrix, in Mathlib's nonincreasing
finite-support sequence. -/
noncomputable def singularValue {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] (M : Matrix m n ℂ) (k : ℕ) : ℝ :=
  (Matrix.toEuclideanLin M).singularValues k

/-- The normalized Taylor coefficient of a polynomial at a complex point. -/
def taylorCoefficient (F : Polynomial ℂ) (ζ : ℂ) (k : ℕ) : ℂ :=
  (Polynomial.derivative^[k] F).eval ζ / (Nat.factorial k : ℂ)

/-- The local unit of `Q` at a root of the shell.  Dividing by the complete
local factor, rather than only by `T`, retains the scalar and every other
factor of `S`. -/
def localUnitAt {J : ℕ} (m : Fin J → ℕ) (ζ : Fin J → ℂ)
    (Q : Polynomial ℂ) (j : Fin J) : Polynomial ℂ :=
  Q / ((Polynomial.X - Polynomial.C (ζ j)) ^ m j)

/-- Coefficients of the truncated Taylor series of the reciprocal local unit. -/
noncomputable def reciprocalLocalUnitCoefficient {J : ℕ}
    (m : Fin J → ℕ) (ζ : Fin J → ℂ) (Q : Polynomial ℂ)
    (j : Fin J) (k : ℕ) : ℂ :=
  PowerSeries.coeff k
    ((PowerSeries.mk (fun ℓ =>
      taylorCoefficient (localUnitAt m ζ Q j) (ζ j) ℓ))⁻¹)

/-- Coefficients of the local unit itself, used for the inverse truncated map. -/
def localUnitCoefficient {J : ℕ}
    (m : Fin J → ℕ) (ζ : Fin J → ℂ) (Q : Polynomial ℂ)
    (j : Fin J) (k : ℕ) : ℂ :=
  taylorCoefficient (localUnitAt m ζ Q j) (ζ j) k

def jetRoot {d J : ℕ} {m : Fin J → ℕ}
    (x : JetChannelIndex d J m) : Fin J := x.1.1

def jetOrder {d J : ℕ} {m : Fin J → ℕ}
    (x : JetChannelIndex d J m) : ℕ := x.1.2.1

def jetChannel {d J : ℕ} {m : Fin J → ℕ}
    (x : JetChannelIndex d J m) : Fin d := x.2

/-- The block lower-triangular Toeplitz map from normalized numerator jets to
principal-part coefficients.  At `ζ j`, output order `t` is the coefficient
of `(z - ζ j)^(t - m j)` in the Laurent principal part. -/
noncomputable def shellJetMap {d J : ℕ} (m : Fin J → ℕ)
    (ζ : Fin J → ℂ) (Q : Polynomial ℂ) :
    Matrix (JetChannelIndex d J m) (JetChannelIndex d J m) ℂ := by
  classical
  exact fun x y =>
    if jetChannel x = jetChannel y ∧ jetRoot x = jetRoot y ∧
        jetOrder y ≤ jetOrder x then
      reciprocalLocalUnitCoefficient m ζ Q (jetRoot x)
        (jetOrder x - jetOrder y)
    else 0

/-- The inverse lower-triangular Toeplitz map, obtained by multiplying by the
local unit rather than its reciprocal. -/
def shellJetMapInverse {d J : ℕ} (m : Fin J → ℕ)
    (ζ : Fin J → ℂ) (Q : Polynomial ℂ) :
    Matrix (JetChannelIndex d J m) (JetChannelIndex d J m) ℂ := by
  classical
  exact fun x y =>
    if jetChannel x = jetChannel y ∧ jetRoot x = jetRoot y ∧
        jetOrder y ≤ jetOrder x then
      localUnitCoefficient m ζ Q (jetRoot x)
        (jetOrder x - jetOrder y)
    else 0

/-- Normalized numerator Hermite jets, retaining root, derivative order, and
channel. -/
def numeratorJet {d J : ℕ} (m : Fin J → ℕ)
    (ζ : Fin J → ℂ) (P : Fin d → Polynomial ℂ) :
    JetChannelIndex d J m → ℂ :=
  fun x =>
    taylorCoefficient (P (jetChannel x)) (ζ (jetRoot x)) (jetOrder x)

/-- The Laurent principal-part residue jet obtained by the local-unit map. -/
def principalPartJet {d J : ℕ} (m : Fin J → ℕ)
    (ζ : Fin J → ℂ) (Q : Polynomial ℂ) (P : Fin d → Polynomial ℂ) :
    JetChannelIndex d J m → ℂ :=
  (shellJetMap m ζ Q).mulVec (numeratorJet m ζ P)

/-- Numerator jets and principal-part residue geometry at a repeated-root
shell.  The local unit is the complete quotient of `Q` by the root factor, so
its reciprocal includes the scalar and all other shell factors. -/
def claim_15113 : Prop :=
  ∀ (d J : ℕ) (m : Fin J → ℕ) (ζ : Fin J → ℂ) (a : ℂ)
    (S T Q : Polynomial ℂ) (P : Fin d → Polynomial ℂ),
    0 < d → 0 < J → a ≠ 0 →
    (∀ j, 0 < m j) →
    (∀ j k, j ≠ k → ζ j ≠ ζ k) →
    S = Polynomial.C a *
      ∏ j : Fin J, (Polynomial.X - Polynomial.C (ζ j)) ^ m j →
    Q = S * T →
    Q ≠ 0 → Q.coeff 0 = 1 →
    (∀ i : Fin d, (P i).degree < Q.degree) →
    (∀ j, T.eval (ζ j) ≠ 0) →
    let U := shellJetMap (d := d) m ζ Q
    let Uinv := shellJetMapInverse (d := d) m ζ Q
    let jp := numeratorJet m ζ P
    let rp := principalPartJet m ζ Q P
    U * Uinv = 1 ∧
      Uinv * U = 1 ∧
      singularValue U (Fintype.card (JetChannelIndex d J m) - 1) *
          euclideanNorm jp ≤ euclideanNorm rp ∧
      euclideanNorm rp ≤ singularValue U 0 * euclideanNorm jp ∧
      ((euclideanNorm rp = 0) ↔ ∀ i : Fin d, S ∣ P i)

end
end MathlibPlus.Open.NewResearch2.RationalHankelCertification15113

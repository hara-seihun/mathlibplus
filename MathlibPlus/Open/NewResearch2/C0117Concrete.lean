import Mathlib

namespace MathlibPlus.Open.NewResearch2.C0117Concrete

open DirichletCharacter

/-- The height factor used by the C-0117 zero-free-region statements. -/
noncomputable def V (u : ℝ) : ℝ :=
  Real.rpow (Real.log u) (2 / 3 : ℝ) *
    Real.rpow (Real.log (Real.log u)) (1 / 3 : ℝ)

/-- The canonical Dirichlet L-function, rather than an unconstrained function
symbol. -/
noncomputable def dirichletL (q : ℕ) (hq : 0 < q)
    (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ := by
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  exact DirichletCharacter.LFunction χ s

/-- Claim 1830: the displayed global Dirichlet-L zero-free region on the exact
same character and height domain. -/
def explicitGlobalDirichletLZeroFreeRegion_claim1830 : Prop :=
  ∀ (q : ℕ), ∀ hq : 3 ≤ q,
    ∀ (χ : DirichletCharacter ℂ q) (t σ : ℝ),
      10 ≤ |t| →
      σ ≥ 1 - 1 /
        (10.5 * Real.log (q : ℝ) + 61.29647 * V |t|) →
      dirichletL q (by omega) χ ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0

/-- Claim 1842: an absolute positive effective-height threshold with the
improved coefficient pair, using the canonical Dirichlet L-function. -/
def effectiveLargeHeightDirichletLZeroFreeRegion_claim1842 : Prop :=
  ∃ Y : ℕ, 0 < Y ∧
    (∀ (q : ℕ), ∀ hq : 3 ≤ q,
      ∀ (χ : DirichletCharacter ℂ q) (t σ : ℝ),
        (Y : ℝ) ≤ |t| →
        σ ≥ 1 - 1 /
          (10 * Real.log (q : ℝ) + 48.08 * V |t|) →
        dirichletL q (by omega) χ ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0) ∧
    (10 < 10.1 ∧ 48.08 < 49.13)

/-- Claim 1904: the all-character region at the exact displayed constants;
quantifying over both signs of `t` leaves the height-zero exceptional case
outside the statement. -/
def allCharacterDirichletLZeroFreeRegion_claim1904 : Prop :=
  ∃ Y : ℕ, 0 < Y ∧
    ∀ (q : ℕ), ∀ hq : 3 ≤ q,
      ∀ (χ : DirichletCharacter ℂ q) (t σ : ℝ),
        (Y : ℝ) ≤ |t| →
        σ ≥ 1 - 1 /
          (9.93082 * Real.log (q : ℝ) + 48.07157 * V |t|) →
        dirichletL q (by omega) χ ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0

end MathlibPlus.Open.NewResearch2.C0117Concrete

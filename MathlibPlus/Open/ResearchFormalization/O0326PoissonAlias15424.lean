import Mathlib

open Asymptotics Filter MeasureTheory Set
open scoped BigOperators Topology

namespace MathlibPlus.Open.ResearchFormalization.O0326PoissonAlias

noncomputable section

/-- An explicit one-dimensional `W^{N,1}` chain: all representatives are
integrable, are the iterated derivatives of the source, and satisfy the
absolute-continuity/integration-by-parts identity on every interval. -/
def wN1Chain (N : ℕ) (q : ℝ → ℝ) : Prop :=
  ∃ d : ℕ → ℝ → ℝ,
    d 0 = q ∧
      (∀ r : ℕ, r ≤ N → d r = iteratedDeriv r q) ∧
        (∀ r : ℕ, r ≤ N → Integrable (d r) volume) ∧
          (∀ r : ℕ, r < N →
            ∀ a b : ℝ, a ≤ b →
              d r b - d r a =
                ∫ t in Set.Ioc a b, d (r + 1) t)

/-- The exact-S0 endpoint-flat source at logarithmic scale `L`.  Its support
is the compact rescaled interval supplied by the Poisson carrier, while the
Sobolev chain and endpoint traces retain the regularity used for repeated
Fourier integration by parts. -/
def exactS0EndpointFlatSource (L : ℝ) (q : ℝ → ℝ) : Prop :=
  Function.Even q ∧
    q 0 = 0 ∧
      (∫ t : ℝ, q t) = 0 ∧
        Function.support q ⊆ Set.Icc (-(Real.exp L)) (Real.exp L) ∧
          ∀ N : ℕ, 2 ≤ N →
            wN1Chain N q ∧
              ∀ r : ℕ, r < N →
                iteratedDeriv r q (Real.exp L) = 0 ∧
                  iteratedDeriv r q (-(Real.exp L)) = 0

/-- The positive logarithmic part and the derivative `L¹` size used by the
little-o hypothesis. -/
def logPlusOne (x : ℝ) : ℝ :=
  max (Real.log x) 0

noncomputable def derivativeL1Norm (N : ℕ) (q : ℝ → ℝ) : ℝ :=
  ∫ t : ℝ, ‖iteratedDeriv N q t‖

/-- Global Sobolev tameness of the exact-S0 family. -/
def globallySobolevTameExactS0 (q : ℝ → ℝ → ℝ) : Prop :=
  (∀ L : ℝ, 0 < L → exactS0EndpointFlatSource L (q L)) ∧
    ∀ N : ℕ, 2 ≤ N →
      IsLittleO atTop
        (fun L : ℝ =>
          logPlusOne (1 + derivativeL1Norm N (q L)))
        (fun L : ℝ => L)

/-- The Fourier transform of a real source in the Poisson summation carrier. -/
noncomputable def poissonFourierTransform
    (q : ℝ → ℝ) (ξ : ℝ) : ℂ :=
  ∫ t : ℝ,
    (q t : ℂ) *
      Complex.exp (-Complex.I * (ξ : ℂ) * (t : ℂ))

/-- The exact rescaled logarithmic Poisson kernel, including the Dini term. -/
noncomputable def poissonKernel
    (q : ℝ → ℝ) (x : ℝ) : ℂ :=
  -((q 0 / 2 : ℝ) : ℂ) * Complex.exp (x / 2) +
    Complex.exp (-x / 2) *
      ∑' n : {n : ℕ // 1 ≤ n},
        poissonFourierTransform q ((n.1 : ℝ) * Real.exp (-x))

/-- The real-even logarithmic density used by the full Mellin channel. -/
noncomputable def evenPoissonKernel
    (q : ℝ → ℝ) (x : ℝ) : ℂ :=
  (poissonKernel q x + poissonKernel q (-x)) / 2

/-- The full Mellin channel and its literal `[-L,L]` truncation. -/
noncomputable def fullMellinChannel
    (q : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ t : ℝ,
    evenPoissonKernel q t *
      Complex.exp (Complex.I * z * (t : ℂ))

noncomputable def literalMellinChannel
    (q : ℝ → ℝ) (L : ℝ) (z : ℂ) : ℂ :=
  ∫ t : ℝ in Set.Icc (-L) L,
    evenPoissonKernel q t *
      Complex.exp (Complex.I * z * (t : ℂ))

/-- The canonical Poisson defect `D_L^P = F_L^lit - H_q`. -/
noncomputable def poissonDefect
    (q : ℝ → ℝ) (L : ℝ) (z : ℂ) : ℂ :=
  literalMellinChannel q L z - fullMellinChannel q z

/-- The value set whose supremum is taken on a closed horizontal substrip. -/
def closedStripValueSet
    (f : ℂ → ℂ) (Y : ℝ) : Set ℝ :=
  {r : ℝ | ∃ z : ℂ, ‖z.im‖ ≤ Y ∧ r = ‖f z‖}

/-- The strip supremum; the claim separately asserts boundedness of this value
set, so `sSup` is not being used as a totalized substitute for an unbounded
supremum. -/
noncomputable def closedStripSup
    (f : ℂ → ℂ) (Y : ℝ) : ℝ :=
  sSup (closedStripValueSet f Y)

/-- A finite-action leading alias for the canonical Poisson defect. -/
def hasFiniteActionLeadingPoissonAlias
    (q : ℝ → ℝ → ℝ) : Prop :=
  ∃ (Y β : ℝ) (z : ℝ → ℂ),
    Y < 1 / 2 ∧
      ∀ᶠ L : ℝ in atTop,
        ‖(z L).im‖ ≤ Y ∧
          Real.exp (-β * L) ≤
            ‖poissonDefect (q L) L (z L)‖

/-- Claim 15424: arbitrary fixed exponential decay of every fixed derivative
on every subcritical closed strip, with the canonical literal/full Poisson
defect and the resulting exclusion of a finite-action leading alias. -/
def claim15424_globallySobolevTameExactS0NoFiniteActionAlias : Prop :=
  ∀ q : ℝ → ℝ → ℝ,
    globallySobolevTameExactS0 q →
      (∀ (Y : ℝ), Y < 1 / 2 →
        ∀ (j : ℕ) (A : ℝ), 0 < A →
          (∀ L : ℝ,
            BddAbove
              (closedStripValueSet
                (fun z : ℂ =>
                  iteratedDeriv j (poissonDefect (q L) L) z) Y)) ∧
            IsBigO atTop
              (fun L : ℝ =>
                closedStripSup
                  (fun z : ℂ =>
                    iteratedDeriv j (poissonDefect (q L) L) z) Y)
              (fun L : ℝ => Real.exp (-A * L))) ∧
        ¬ hasFiniteActionLeadingPoissonAlias q

end

end MathlibPlus.Open.ResearchFormalization.O0326PoissonAlias

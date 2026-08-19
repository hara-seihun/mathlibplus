import MathlibPlus.Open.ResearchFormalization.GrowingOrbitTheoremClaim35101

namespace MathlibPlus.Open.ResearchFormalization.R1980.Claim36730

noncomputable section

open Filter
open Asymptotics
open MathlibPlus.Open.ResearchFormalization.GrowingOrbitTheoremClaim35101
open MathlibPlus.Open.ResearchFormalization.SharpenedRREFColourCountClaim35100

/-- The finite edge carrier used in the standard definition of a Ramsey
number. -/
abbrev TwoSubset (n : ℕ) := {e : Finset (Fin n) // e.card = 2}

/-- Every `c`-coloring of the edges of `K_n` has a monochromatic `K_k`. -/
def monochromaticClique (c k n : ℕ) : Prop :=
  ∀ color : TwoSubset n → Fin c,
    ∃ S : Finset (Fin n),
      S.card = k ∧
        ∃ q : Fin c, ∀ e : TwoSubset n, e.1 ⊆ S → color e = q

/-- The standard Ramsey number `R_c(k)`, written from its exact coloring
property rather than as an unconstrained numerical parameter. -/
noncomputable def ramseyNumber (c k : ℕ) : ℕ :=
  sInf {n : ℕ | monochromaticClique c k n}

/-- The exact coarse pair-color palette supplied by the quotient-space
construction, with the two-color lower cutoff used by the Ramsey step. -/
def colourPaletteSize (M : ℕ) : ℕ :=
  max 2 (coarsePairColourCount (Nat.log 2 M))

/-- The heavy-direction bound `B_M = R_{max(2,c_M)}(7)-1`. -/
def heavyDirectionBound (M : ℕ) : ℕ :=
  ramseyNumber (colourPaletteSize M) 7 - 1

/-- The displayed growing orbit parameter in Claim 36730. -/
def displayedOrbitCap (n : ℕ) : ℝ :=
  (1 / 28 : ℝ) * log2Value (log2Value (n : ℝ))

/-- Since an orbit cardinality is integral, this is the integer parameter
associated with the displayed real cap; the harmless lower cutoff makes the
Ramsey parameter valid before the eventual range begins. -/
def growingOrbitParameter (n : ℕ) : ℕ :=
  max 1 (Nat.floor (max 0 (displayedOrbitCap n)))

/-- The `B_{M_n}` sequence in the growing-orbit conclusion. -/
def growingHeavyBound (n : ℕ) : ℕ :=
  heavyDirectionBound (growingOrbitParameter n)

/-- The exact eventual hypothesis that every literal directional translation
orbit has the displayed size bound. -/
def eventualDisplayedOrbitBound
    (f : DirectionalFamily) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ i : Fin n,
      (literalDirectionalOrbitCard (i := i) (f n i) : ℝ) ≤
        displayedOrbitCap n

/-- A logarithmic formulation of `b=n^{o(1)}` for nonnegative sequences. -/
def subpolynomialSequence (b : ℕ → ℕ) : Prop :=
  IsLittleO atTop
    (fun n : ℕ => Real.log (1 + (b n : ℝ)))
    (fun n : ℕ => Real.log (1 + (n : ℝ)))

/-- The ordinary `o(n)` formulation used for the heavy-direction bound. -/
def sublinearSequence (b : ℕ → ℕ) : Prop :=
  IsLittleO atTop
    (fun n : ℕ => (b n : ℝ))
    (fun n : ℕ => (n : ℝ))

/-- Claim 36730: the displayed growing orbit cap makes the Ramsey heavy
bound subpolynomial and sublinear, and the exact literal cube carrier then
has the half-density and edge-count asymptotics. -/def claim36730_growingOrbitCorollary : Prop :=
  ∀ f : DirectionalFamily,
    familyC4Free f →
      eventualDisplayedOrbitBound f →
        subpolynomialSequence growingHeavyBound ∧
          sublinearSequence growingHeavyBound ∧
            densityUpperAsymptotic f ∧
              edgeUpperAsymptotic f

end

end MathlibPlus.Open.ResearchFormalization.R1980.Claim36730

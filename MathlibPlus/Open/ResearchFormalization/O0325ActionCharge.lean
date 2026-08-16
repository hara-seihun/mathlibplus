import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.O0325

noncomputable section

/-- Source label `0` is the shadow; labels `1` through `4` are the four
    non-shadow channels in the exact boundary aggregate. -/
abbrev SourceChannel := Fin 5

/-- The non-shadow source labels. -/
def boundaryChannels : Finset SourceChannel := Finset.univ.erase 0

/-- A source-labelled family at a fixed scale `L`. -/
abbrev ChannelFamily := SourceChannel → ℂ → ℂ

/-- The shadow channel `V₀`. -/
def shadowChannel (V : ChannelFamily) : ℂ → ℂ := V 0

/-- The aggregate `B = sum_(ν ≠ 0) V_ν`. -/
def boundaryChannel (V : ChannelFamily) : ℂ → ℂ :=
  fun z => ∑ ν ∈ boundaryChannels, V ν z

/-- The action `-(1/L) log |V|`. -/
noncomputable def channelAction (L : ℝ) (V : ℂ → ℂ) (z : ℂ) : ℝ :=
  -(1 / L) * Real.log ‖V z‖

/-- The normalized charge `(1/(iL)) V'/V`. -/
noncomputable def channelCharge (L : ℝ) (V : ℂ → ℂ) (z : ℂ) : ℂ :=
  (1 / (Complex.I * (L : ℂ))) * (deriv V z / V z)

/-- The charge of the aggregate boundary channel. -/
noncomputable def aggregateCharge (L : ℝ) (V : ChannelFamily) (z : ℂ) : ℂ :=
  channelCharge L (boundaryChannel V) z

/-- The logarithmic one-form `d log(-B/S)`, represented in the coordinate `dz`. -/
noncomputable def projectiveLogOneForm
    (S B : ℂ → ℂ) (z : ℂ) : ℂ → ℂ :=
  fun dz =>
    (deriv (fun w : ℂ => -B w / S w) z / (-B z / S z)) * dz

/-- The relative charge one-form `η_L`. -/
noncomputable def relativeChargeOneForm
    (_L : ℝ) (V : ChannelFamily) (z : ℂ) : ℂ → ℂ :=
  projectiveLogOneForm (shadowChannel V) (boundaryChannel V) z

/-- The source-labelled normalized first-jet matrix, with columns
    `(V_ν, L⁻¹ V'_ν)`. -/
noncomputable def sourceFirstJetMatrix
    (L : ℝ) (V : ChannelFamily) (z : ℂ) : Matrix (Fin 2) SourceChannel ℂ :=
  fun row ν =>
    if row = 0 then V ν z else (L : ℂ)⁻¹ * deriv (V ν) z

/-- The pairwise first-jet minor
    `Δ_{μν}=V_μ V'_ν-V'_μ V_ν`. -/
noncomputable def pairwiseMinor
    (V : ChannelFamily) (μ ν : SourceChannel) (z : ℂ) : ℂ :=
  V μ z * deriv (V ν) z - deriv (V μ) z * V ν z

/-- The analytic-order divisor of a source channel. -/
noncomputable def channelDivisor
    (V : ChannelFamily) (ν : SourceChannel) :
    Function.locallyFinsuppWithin (Set.univ : Set ℂ) ℤ :=
  MeromorphicOn.divisor (V ν) Set.univ

/-- The analytic-order divisor of a pairwise first-jet minor. -/
noncomputable def pairwiseMinorDivisor
    (V : ChannelFamily) (μ ν : SourceChannel) :
    Function.locallyFinsuppWithin (Set.univ : Set ℂ) ℤ :=
  MeromorphicOn.divisor (pairwiseMinor V μ ν) Set.univ

/-- The complete source-labelled action/charge and first-jet data retained by
    the claim. The divisor fields record zero orders, not merely zero sets. -/
structure SourceLabeledFirstJetData (L : ℝ) (V : ChannelFamily) where
  action : SourceChannel → ℂ → ℝ
  charge : SourceChannel → ℂ → ℂ
  eta : ℂ → (ℂ → ℂ)
  matrix : ℂ → Matrix (Fin 2) SourceChannel ℂ
  channelDivisors : SourceChannel →
    Function.locallyFinsuppWithin (Set.univ : Set ℂ) ℤ
  minors : SourceChannel → SourceChannel → ℂ → ℂ
  minorDivisors : SourceChannel → SourceChannel →
    Function.locallyFinsuppWithin (Set.univ : Set ℂ) ℤ

/-- Canonical data attached to the exact source-labelled channels. -/
noncomputable def sourceLabeledFirstJetData
    (L : ℝ) (V : ChannelFamily) : SourceLabeledFirstJetData L V where
  action := fun ν z => channelAction L (V ν) z
  charge := fun ν z => channelCharge L (V ν) z
  eta := relativeChargeOneForm L V
  matrix := sourceFirstJetMatrix L V
  channelDivisors := channelDivisor V
  minors := pairwiseMinor V
  minorDivisors := pairwiseMinorDivisor V

/-- Claim 15405: every nonzero source channel has the displayed action and
    charge; the aggregate charge is the exact weighted sum; the relative
    one-form is `i L (c_B-c_S) dz`; and the source-labelled first-jet data
    retain channel and pairwise-minor divisors. -/
def actionChargeSpectrumAndAggregateCharge_claim15405 : Prop :=
  ∀ (L : ℝ) (V : ChannelFamily),
    L ≠ 0 →
    (∀ ν : SourceChannel, Differentiable ℂ (V ν)) →
    ∀ z : ℂ,
      (∀ ν : SourceChannel, ν ∈ boundaryChannels → V ν z ≠ 0) →
      shadowChannel V z ≠ 0 →
      boundaryChannel V z ≠ 0 →
      let data := sourceLabeledFirstJetData L V
      aggregateCharge L V z =
        ∑ ν ∈ boundaryChannels,
          (V ν z / boundaryChannel V z) * data.charge ν z ∧
      data.eta z =
        (fun dz =>
          Complex.I * (L : ℂ) *
            (aggregateCharge L V z - data.charge (0 : SourceChannel) z) * dz)

end

end MathlibPlus.Open.ResearchFormalization.O0325

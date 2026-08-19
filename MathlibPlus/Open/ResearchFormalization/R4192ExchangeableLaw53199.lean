import MathlibPlus.Open.ResearchFormalization.R4192BetaPosterior

open MeasureTheory
open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R4192ExchangeableLaw53199

noncomputable section

open MathlibPlus.Open
open MathlibPlus.Open.ResearchFormalization.R4192BetaPosterior

abbrev OutputWord (n : ℕ) := SignWord n

/-- The uniform law of the common parameter on the unit interval. -/
noncomputable def thetaUniformMeasure : Measure ℝ :=
  Measure.restrict volume (Set.Icc (0 : ℝ) 1)

def thetaUniformOnUnitInterval : Prop :=
  MeasureTheory.IsProbabilityMeasure thetaUniformMeasure ∧
    thetaUniformMeasure (Set.Icc (0 : ℝ) 1)ᶜ = 0

/-- The finite conditional probability mass of a sign word. -/
def conditionalWordMass {n : ℕ} (theta : ℝ)
    (x : OutputWord n) : ℝ :=
  ∏ i : Fin n, singleSignProbability theta (x i)

def finiteProbabilityMass {α : Type*} [Fintype α]
    (mass : α → ℝ) : Prop :=
  (∀ x, 0 ≤ mass x) ∧ ∑ x : α, mass x = 1

/-- Conditional independence and the prescribed one-coordinate probability
for the beta--Bernoulli signs. -/
def conditionalBetaBernoulliLaw (n : ℕ) : Prop :=
  ∀ theta : ℝ, theta ∈ Set.Icc (0 : ℝ) 1 →
    finiteProbabilityMass (α := OutputWord n)
        (conditionalWordMass (n := n) theta) ∧
      (∀ i : Fin n,
        (∑ x : OutputWord n,
          (if x i = true then
              conditionalWordMass (n := n) theta x
            else 0)) = theta)

/-- The count form of the conditional independent word law. -/
def betaBernoulliExchangeableModel (n : ℕ) : Prop :=
  conditionalBetaBernoulliLaw n ∧
    ∀ theta : ℝ, theta ∈ Set.Icc (0 : ℝ) 1 →
      ∀ x : OutputWord n,
        conditionalWordMass theta x = countWordLikelihood theta x

/-- The normalized output sample mean, with `true` encoding `+1`. -/
def muN (n : ℕ) (x : OutputWord n) : ℝ :=
  (∑ i : Fin n, signValue (x i)) / (n : ℝ)

/-- The outputs observed by an output-only policy after `m` queries.  The
policy input is only this list of values; no seed or coordinate transcript is
part of the carrier. -/
def outputTranscript {n : ℕ} (q : List Bool → Fin n)
    (x : OutputWord n) : ℕ → List Bool
  | 0 => []
  | m + 1 =>
      let h := outputTranscript q x m
      h ++ [x (q h)]

/-- The labels selected during the same output-only run. -/
def queryTranscript {n : ℕ} (q : List Bool → Fin n)
    (x : OutputWord n) : ℕ → List (Fin n)
  | 0 => []
  | m + 1 =>
      let h := outputTranscript q x m
      queryTranscript q x m ++ [q h]

/-- A deterministic output-only policy queries a fresh output label at every
stage on every possible finite output word. -/
def distinctOutputQueries {n : ℕ}
    (q : List Bool → Fin n) : Prop :=
  ∀ (x : OutputWord n) (m : ℕ), m < n →
    q (outputTranscript q x m) ∉ queryTranscript q x m

/-- The exact deterministic output-only policy carrier. -/
abbrev OutputOnlyPolicy (n : ℕ) := List Bool → Fin n

abbrev OutputOnlyPolicyClass (n : ℕ) :=
  {q : OutputOnlyPolicy n // distinctOutputQueries q}

/-- Optional private randomization is a probability mass on output-only
policies, independent of the common parameter, whose supported policies all
query distinct labels. -/
def PrivateRandomizedOutputOnlyPolicy (n : ℕ) :=
  {μ : PMF (OutputOnlyPolicy n) //
    ∀ q : OutputOnlyPolicy n, q ∈ μ.support → distinctOutputQueries q}

/--
R-4192.1 (claim 53199): the common parameter is uniform on `[0,1]`, the
conditional signs have the independent beta--Bernoulli law, the normalized
sample mean is the displayed sign average, and the output-only abstraction
uses only observed values, with distinct labels and optional private
randomization but no common-seed or coordinate-transcript input.
-/
def claim53199 : Prop :=
  ∀ n : ℕ, 0 < n →
    thetaUniformOnUnitInterval ∧
      betaBernoulliExchangeableModel n ∧
      (∀ x : OutputWord n,
        muN n x = (∑ i : Fin n, signValue (x i)) / (n : ℝ)) ∧
      Nonempty (OutputOnlyPolicyClass n) ∧
      Nonempty (PrivateRandomizedOutputOnlyPolicy n)

end

end MathlibPlus.Open.ResearchFormalization.R4192ExchangeableLaw53199

import MathlibPlus.Open.ResearchBatch.Probability

namespace MathlibPlus.Open.ResearchFormalization.R4192BetaPosterior

open scoped BigOperators
open MathlibPlus.Open

noncomputable section

/-- A conditional sign probability for the two signs in the beta--Bernoulli
model. -/
abbrev SignWord (m : ℕ) := Fin m → Bool

/-- The Boolean encoding uses `true` for `+1` and `false` for `-1`. -/
def signValue (s : Bool) : ℝ := if s then 1 else -1

def signPlusCount {m : ℕ} (x : SignWord m) : ℕ :=
  (Finset.filter (fun i : Fin m => x i = true) Finset.univ).card

/-- A conditional sign probability in the beta--Bernoulli model. -/
def singleSignProbability (theta : ℝ) (s : Bool) : ℝ :=
  if s then theta else 1 - theta

/-- The conditional likelihood of a sign word, written as the product of its
independent coordinate likelihoods. -/
def conditionalWordLikelihood {m : ℕ} (theta : ℝ)
    (x : SignWord m) : ℝ :=
  ∏ i : Fin m, singleSignProbability theta (x i)

/-- The same likelihood in its count form. -/
def countWordLikelihood {m : ℕ} (theta : ℝ)
    (x : SignWord m) : ℝ :=
  theta ^ signPlusCount x * (1 - theta) ^ (m - signPlusCount x)

/-- The beta--Bernoulli conditional-independence model: the conditional joint
word likelihood factors over the observed signs, and its count form is the
usual plus/minus likelihood. -/
def betaBernoulliModel (m : ℕ) : Prop :=
  ∀ theta : ℝ, ∀ x : SignWord m,
    conditionalWordLikelihood theta x = countWordLikelihood theta x

/-- A word's marginal mass under the uniform prior for `Theta` on `[0,1]`.
The integral over the unit interval is the uniform-prior mixture. -/
def uniformPriorWordMass {m : ℕ} (x : SignWord m) : ℝ :=
  ∫ theta in Set.Icc (0 : ℝ) 1, conditionalWordLikelihood theta x

/-- The marginal law of the positive-output count `S_m`. -/
def observedCountMass (m s : ℕ) : ℝ :=
  ∑ x : SignWord m,
    if signPlusCount x = s then uniformPriorWordMass x else 0

/-- The transcript posterior density obtained from the uniform prior and a
word of observed signs. -/
def transcriptPosteriorDensity {m : ℕ} (x : SignWord m)
    (theta : ℝ) : ℝ :=
  if theta ∈ Set.Icc (0 : ℝ) 1 then
    conditionalWordLikelihood theta x / uniformPriorWordMass x
  else 0

/-- Pull a distinct ordered list of output labels out of a full sign word. -/
def observedTranscript {n m : ℕ} (labels : Fin m → Fin n)
    (x : SignWord n) : SignWord m :=
  fun i => x (labels i)

/-- The posterior is insensitive to the ordering and to any private
randomization of an output-only policy: once the number of observations and
its positive count are fixed, the density is fixed. -/
def posteriorDependsOnlyOnCount (n m : ℕ) (hmn : m ≤ n) : Prop :=
  ∀ (labels : Fin m → Fin n), Function.Injective labels →
    ∀ (x : SignWord n) (y : SignWord m),
      signPlusCount (observedTranscript labels x) = signPlusCount y →
        ∀ theta : ℝ,
          transcriptPosteriorDensity (observedTranscript labels x) theta =
            transcriptPosteriorDensity y theta

/-- Claim 53200: under the uniform latent `Theta` and conditionally
independent sign outputs, the posterior after `m` distinct outputs with
positive count `s` is the Beta density `Beta(s+1,m-s+1)`, while `S_m` is
uniform on `{0,...,m}`; the posterior depends only on `m` and `S_m`. -/
def claim53200 : Prop :=
  (∀ m : ℕ, betaBernoulliModel m) ∧
  ∀ (n m : ℕ) (hmn : m ≤ n),
    (∀ (labels : Fin m → Fin n), Function.Injective labels →
      ∀ x : SignWord n,
        ∀ theta : ℝ,
          transcriptPosteriorDensity (observedTranscript labels x) theta =
            betaDensity
              (signPlusCount (observedTranscript labels x))
              (m - signPlusCount (observedTranscript labels x)) theta) ∧
    (∀ s : ℕ,
      observedCountMass m s = uniformCountMass m s ∧
        (s ≤ m → observedCountMass m s = (1 : ℝ) / (m + 1 : ℝ))) ∧
    posteriorDependsOnlyOnCount n m hmn

end
end MathlibPlus.Open.ResearchFormalization.R4192BetaPosterior

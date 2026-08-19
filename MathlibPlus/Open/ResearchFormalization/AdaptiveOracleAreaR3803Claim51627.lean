import MathlibPlus.Open.ResearchFormalization.AdaptiveOracleAreaR3803

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.AdaptiveOracleAreaR3803

open MathlibPlus.Open.OracleAreaOccupation

/-- The directional active-policy term used for a row of the signed route. -/
def claim51627DirectionalTerm (K h : Driver n)
    (u : Configuration n → ℝ) (d : DeterministicPolicy n) : ℝ :=
  2 * policyBilinear d u (driverValue h) - policyArea d u - qCost K

/-- Every active cross pair has the displayed value, with the active rows
retained rather than replaced with an unattached numerical surrogate. -/
def claim51627ActiveCrossRow (K h : Driver n)
    (u : Configuration n → ℝ) : Prop :=
  (∃ dK : DeterministicPolicy n, directionalActive K h u dK) ∧
    (∃ dh : DeterministicPolicy n, directionalActive h K u dh) ∧
    (∀ dK dh : DeterministicPolicy n,
      directionalActive K h u dK →
      directionalActive h K u dh →
      claim51627DirectionalTerm K h u dK +
          claim51627DirectionalTerm h K u dh = (7 / 9 : ℝ) ∧
        0 < claim51627DirectionalTerm K h u dK +
          claim51627DirectionalTerm h K u dh)

/-- The active self row has the displayed exact value. -/
def claim51627ActiveSelfRow (H : Driver n)
    (u : Configuration n → ℝ) : Prop :=
  (∃ d : DeterministicPolicy n, directionalActive H H u d) ∧
    (∀ d : DeterministicPolicy n,
      directionalActive H H u d →
        claim51627DirectionalTerm H H u d = (-128 / 81 : ℝ))

/-- The two-atom signed score uses the stated law weights and value. -/
def claim51627ScoreRow : Prop :=
  score targetLaw targetH85 =
      (5 / 9 : ℝ) * (-128 / 81 : ℝ) +
        (4 / 9 : ℝ) * (7 / 9 : ℝ) ∧
    score targetLaw targetH85 = (-388 / 729 : ℝ) ∧
    score targetLaw targetH85 < 0

/-- The inclusion of the first three coordinates into `Fin n`, used to
retain the two masks while adding dummy coordinates. -/
def claim51627LiftConfiguration {n : ℕ} (hn : 3 ≤ n)
    (ω : Configuration n) : Configuration 3 :=
  fun i => ω ⟨i.1, Nat.lt_of_lt_of_le i.2 hn⟩

/-- A lifted driver ignores every coordinate after the original three. -/
def claim51627LiftDriver {n : ℕ} (hn : 3 ≤ n)
    (H : Driver 3) : Driver n :=
  fun ω => H (claim51627LiftConfiguration hn ω)

/-- The lifted two-atom law at weights `5/9` and `4/9`. -/
def claim51627LiftedLaw {n : ℕ} (hn : 3 ≤ n) : BooleanLaw n :=
  [(claim51627LiftDriver hn targetH85, (5 / 9 : ℝ)),
    (claim51627LiftDriver hn targetH195, (4 / 9 : ℝ))]

/-- Its barycentre is the lifted copy of the prescribed two-atom barycentre. -/
noncomputable def claim51627LiftedBarycentre {n : ℕ} (hn : 3 ≤ n) :
    Configuration n → ℝ :=
  lawBarycentre (claim51627LiftedLaw hn)

/-- A dummy query made before the stopped prefix has determined the lifted
mask. -/
def claim51627DummyQueryBeforeStopping {n : ℕ} (hn : 3 ≤ n)
    (H : Driver 3) (d : DeterministicPolicy n) : Prop :=
  ∃ (ω : Configuration n) (m : ℕ)
    (hs : (policyState d ω m).1.card < n),
    m < stoppingTime (claim51627LiftDriver hn H) d ω ∧
      ¬ ((d ⟨policyState d ω m, hs⟩).1 : ℕ) < 3

/-- The lifted row and its dummy-coordinate cost separation. -/
def claim51627LiftedRows {n : ℕ} (hn : 3 ≤ n) : Prop :=
  claim51627ActiveCrossRow
      (claim51627LiftDriver hn targetH195)
      (claim51627LiftDriver hn targetH85)
      (claim51627LiftedBarycentre hn) ∧
    claim51627ActiveSelfRow
      (claim51627LiftDriver hn targetH85)
      (claim51627LiftedBarycentre hn) ∧
    score (claim51627LiftedLaw hn) (claim51627LiftDriver hn targetH85) =
        (5 / 9 : ℝ) * (-128 / 81 : ℝ) +
          (4 / 9 : ℝ) * (7 / 9 : ℝ) ∧
    score (claim51627LiftedLaw hn) (claim51627LiftDriver hn targetH85) =
        (-388 / 729 : ℝ) ∧
    score (claim51627LiftedLaw hn) (claim51627LiftDriver hn targetH85) < 0

/-- Querying a dummy before determination is strictly worse than the
q-optimal cost, so q-optimal lifted policies ignore dummies. -/
def claim51627DummyCostSeparation {n : ℕ} (hn : 3 ≤ n)
    (H : Driver 3) : Prop :=
  (∀ d : DeterministicPolicy n,
    qOptimal (claim51627LiftDriver hn H) d →
      ¬ claim51627DummyQueryBeforeStopping hn H d) ∧
  (∀ d : DeterministicPolicy n,
    claim51627DummyQueryBeforeStopping hn H d →
      expectedStoppingCost (claim51627LiftDriver hn H) d >
        qCost (claim51627LiftDriver hn H)) ∧
  (∃ d : DeterministicPolicy n,
    qOptimal (claim51627LiftDriver hn H) d ∧
      ¬ claim51627DummyQueryBeforeStopping hn H d)

/-- Claim 51627: the exact `85`/`195` active rows, signed score, and their
q-optimal dummy-coordinate lift in every dimension at least three. -/
def claim51627 : Prop :=
  claim51627ActiveCrossRow targetH195 targetH85 targetU ∧
    claim51627ActiveSelfRow targetH85 targetU ∧
    claim51627ScoreRow ∧
    ∀ (n : ℕ) (hn : 3 ≤ n),
      claim51627LiftedRows hn ∧
      claim51627DummyCostSeparation hn targetH85 ∧
      claim51627DummyCostSeparation hn targetH195

end MathlibPlus.Open.ResearchFormalization.AdaptiveOracleAreaR3803

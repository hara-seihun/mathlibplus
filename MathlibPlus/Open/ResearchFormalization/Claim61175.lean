import Mathlib

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization

/-- A sign is represented by `false = -1` and `true = 1`. -/
abbrev claim61175Sign := Bool

/-- The uniform sign cube in dimension `n`. -/
abbrev claim61175Omega (n : ℕ) := Fin n → claim61175Sign

/-- Boolean tables with values in the two signs. -/
abbrev claim61175BooleanTable (n : ℕ) :=
  claim61175Omega n → claim61175Sign

/-- The real value represented by a sign. -/
def claim61175SignReal (s : claim61175Sign) : ℝ :=
  if s then 1 else -1

/-- The negative and positive signs used in coordinate restrictions. -/
def claim61175NegativeSign : claim61175Sign := false

def claim61175PositiveSign : claim61175Sign := true

/-- Uniform expectation on a finite carrier. -/
noncomputable def claim61175UniformAverage {α : Type*} [Fintype α]
    (f : α → ℝ) : ℝ :=
  (∑ x, f x) / (Fintype.card α : ℝ)

/-- A deterministic finite decision tree with coordinate queries. -/
inductive claim61175QueryTree (n : ℕ) where
  | leaf : claim61175Sign → claim61175QueryTree n
  | query : Fin n → claim61175QueryTree n → claim61175QueryTree n →
      claim61175QueryTree n

/-- Evaluation of a query tree on a sign cube input. -/
def claim61175QueryTreeEvaluate {n : ℕ} :
    claim61175QueryTree n → claim61175Omega n → claim61175Sign
  | .leaf value, _ => value
  | .query coordinate negative positive, input =>
      match input coordinate with
      | false => claim61175QueryTreeEvaluate negative input
      | true => claim61175QueryTreeEvaluate positive input

/-- Number of fresh coordinates queried after a set of already known coordinates. -/
def claim61175FreshQueryCountFrom {n : ℕ} (seen : Finset (Fin n)) :
    claim61175QueryTree n → claim61175Omega n → ℕ
  | .leaf _, _ => 0
  | .query coordinate negative positive, input =>
      (if coordinate ∈ seen then 0 else 1) +
        match input coordinate with
        | false =>
            claim61175FreshQueryCountFrom (insert coordinate seen) negative input
        | true =>
            claim61175FreshQueryCountFrom (insert coordinate seen) positive input

/-- Fresh-coordinate query count along a complete input path. -/
def claim61175FreshQueryCount {n : ℕ}
    (tree : claim61175QueryTree n) (input : claim61175Omega n) : ℕ :=
  claim61175FreshQueryCountFrom ∅ tree input

/-- The predicate that a tree computes a Boolean table. -/
def claim61175Computes {n : ℕ} (tree : claim61175QueryTree n)
    (h : claim61175BooleanTable n) : Prop :=
  ∀ input, claim61175QueryTreeEvaluate tree input = h input

/-- Expected fresh-coordinate query cost under the uniform sign law. -/
noncomputable def claim61175ExpectedQueryCost {n : ℕ}
    (tree : claim61175QueryTree n) : ℝ :=
  (∑ input : claim61175Omega n,
      (claim61175FreshQueryCount tree input : ℝ)) /
    (Fintype.card (claim61175Omega n) : ℝ)

/-- The minimum expected number of fresh coordinate queries computing a table. -/
noncomputable def claim61175QueryCost {n : ℕ}
    (h : claim61175BooleanTable n) : ℝ :=
  sInf {value : ℝ |
    ∃ tree : claim61175QueryTree n,
      claim61175Computes tree h ∧ value = claim61175ExpectedQueryCost tree}

/-- The expected pairing of a Boolean table with a real table. -/
noncomputable def claim61175Pairing {n : ℕ}
    (h : claim61175BooleanTable n) (z : claim61175Omega n → ℝ) : ℝ :=
  claim61175UniformAverage (fun input =>
    claim61175SignReal (h input) * z input)

/-- The polar value, defined as the finite maximum over Boolean tables. -/
noncomputable def claim61175Psi (n : ℕ) (z : claim61175Omega n → ℝ) : ℝ :=
  sSup (Set.range (fun h : claim61175BooleanTable n =>
    claim61175Pairing h z - claim61175QueryCost h))

/-- The unique sign-cube input in dimension zero. -/
def claim61175ZeroInput : claim61175Omega 0 :=
  fun i => Fin.elim0 i

/-- Insert a specified sign at coordinate `i` into a child-cube input. -/
def claim61175InsertSign {m : ℕ} (i : Fin (m + 1))
    (value : claim61175Sign) (input : claim61175Omega m) :
    claim61175Omega (m + 1) :=
  Fin.insertNth i value input

/-- Restriction of a real table to a coordinate sign. -/
def claim61175Restriction {m : ℕ}
    (z : claim61175Omega (m + 1) → ℝ) (i : Fin (m + 1))
    (value : claim61175Sign) : claim61175Omega m → ℝ :=
  fun input => z (claim61175InsertSign i value input)

/-- The right-hand side of the exact polar Bellman recursion. -/
noncomputable def claim61175BellmanRhs (m : ℕ)
    (z : claim61175Omega (m + 1) → ℝ) : ℝ :=
  sSup (Set.insert
    |claim61175UniformAverage z|
    (Set.range (fun i : Fin (m + 1) =>
      -1 +
        (claim61175Psi m (claim61175Restriction z i claim61175NegativeSign) +
          claim61175Psi m (claim61175Restriction z i claim61175PositiveSign)) / 2)))

/-- The inequalities defining the expected-query-cost polar. -/
def claim61175PolarInequalities (n : ℕ)
    (z : claim61175Omega n → ℝ) : Prop :=
  ∀ h : claim61175BooleanTable n,
    claim61175Pairing h z ≤ claim61175QueryCost h

/-- Covariance of a Boolean table and a real table under the uniform law. -/
noncomputable def claim61175Covariance {n : ℕ}
    (h : claim61175BooleanTable n) (z : claim61175Omega n → ℝ) : ℝ :=
  claim61175UniformAverage (fun input =>
    (claim61175SignReal (h input) -
        claim61175UniformAverage (fun input' =>
          claim61175SignReal (h input'))) *
      (z input - claim61175UniformAverage z))

/-- Claim 61175: exact polar Bellman recursion and its separation consequence. -/
def claim61175 : Prop :=
  (∀ z : claim61175Omega 0 → ℝ,
    claim61175Psi 0 z = |z claim61175ZeroInput|) ∧
  (∀ (m : ℕ) (z : claim61175Omega (m + 1) → ℝ),
    claim61175Psi (m + 1) z = claim61175BellmanRhs m z) ∧
  (∀ (n : ℕ) (z : claim61175Omega n → ℝ),
    claim61175PolarInequalities n z ↔ claim61175Psi n z ≤ 0) ∧
  (∀ (n : ℕ) (z : claim61175Omega n → ℝ),
    claim61175Psi n z ≤ 0 →
      claim61175UniformAverage z = 0 ∧
        (∀ h : claim61175BooleanTable n,
          claim61175Pairing h z = claim61175Covariance h z) ∧
        ((∀ h : claim61175BooleanTable n,
            claim61175Pairing h z ≤ claim61175QueryCost h) ↔
          (∀ h : claim61175BooleanTable n,
            claim61175Covariance h z ≤ claim61175QueryCost h)))

end MathlibPlus.Open.ResearchFormalization

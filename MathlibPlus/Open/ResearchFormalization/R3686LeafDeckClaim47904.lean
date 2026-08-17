import MathlibPlus.Open.Combinatorics.TreeDeck

namespace MathlibPlus.Open.ResearchFormalization.R3686

open ProjectsResearch.TreeDeck

/-- The integral ordinary leaf-deck vector of an order-`n` unlabelled tree.
Its coordinates are indexed by order-`(n-1)` unlabelled tree types, and the
coefficient is the multiplicity of that leaf card. -/
noncomputable def ordinaryLeafDeck (n : ℕ) (T : UnlabelledTree n) :
    UnlabelledTree (n - 1) → ℤ := by
  classical
  exact fun H => Fintype.card {v : leafVertices T // leafCard T v = H}

/-- The source carrier `D_n` of all ordinary integral leaf-deck vectors. -/
def ordinaryLeafDeckVectors (n : ℕ) :
    Set (UnlabelledTree (n - 1) → ℤ) :=
  Set.range (ordinaryLeafDeck n)

/-- Coordinatewise positive and negative parts of an integral boundary. -/
def positivePart {ι : Type*} (v : ι → ℤ) : ι → ℤ :=
  fun i => max (v i) 0

def negativePart {ι : Type*} (v : ι → ℤ) : ι → ℤ :=
  fun i => max (-v i) 0

/-- The common nonnegative completion carrier `Comp_n(v)`. -/
def completionSet (n : ℕ) (v : UnlabelledTree (n - 1) → ℤ) :
    Set (UnlabelledTree (n - 1) → ℤ) :=
  {z |
    (∀ H, 0 ≤ z H) ∧
      (fun H => positivePart v H + z H) ∈ ordinaryLeafDeckVectors n ∧
      (fun H => negativePart v H + z H) ∈ ordinaryLeafDeckVectors n}

/-- Ordered order-`n` parent pairs with signed leaf-deck boundary `v`. -/
def orderedParentPairs (n : ℕ)
    (v : UnlabelledTree (n - 1) → ℤ) :=
  {p : UnlabelledTree n × UnlabelledTree n //
    ordinaryLeafDeck n p.1 - ordinaryLeafDeck n p.2 = v}

/-- The coordinatewise-minimum completion of an ordered parent pair. -/
noncomputable def completionOfPair {n : ℕ} {v : UnlabelledTree (n - 1) → ℤ}
    (p : orderedParentPairs n v) : UnlabelledTree (n - 1) → ℤ :=
  fun H => min (ordinaryLeafDeck n p.1.1 H) (ordinaryLeafDeck n p.1.2 H)

/-- Claim 47904: for `n ≥ 4`, the minimum-completion map is a bijection
between the exact ordered parent-pair carrier and `Comp_n(v)`.  The explicit
injectivity and unique-parent clauses retain the two reconstruction conclusions
about completed decks. -/
def claim47904 : Prop :=
  ∀ n : ℕ, 4 ≤ n →
    ∀ v : UnlabelledTree (n - 1) → ℤ,
      (∀ p : orderedParentPairs n v,
        completionOfPair p ∈ completionSet n v) ∧
      (∀ z : UnlabelledTree (n - 1) → ℤ,
        z ∈ completionSet n v →
          ∃! p : orderedParentPairs n v, completionOfPair p = z) ∧
      (∀ p q : orderedParentPairs n v,
        completionOfPair p = completionOfPair q → p = q)

end MathlibPlus.Open.ResearchFormalization.R3686

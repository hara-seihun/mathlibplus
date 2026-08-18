import MathlibPlus.Open.ResearchFormalization.GraphDeckRowsClaim15999
import MathlibPlus.Open.ResearchFormalization.GraphDeckFiberSupportClaim16003

namespace MathlibPlus.Open.ResearchFormalization.Q0037Claim16007

noncomputable section

open MathlibPlus.Combinatorics.Claim44521

abbrev GraphType (n : ℕ) := finiteSimpleGraphType n

noncomputable def graphRepresentative {n : ℕ} (G : GraphType n) :
    SimpleGraph (Fin n) :=
  Quotient.out G

/-- The labelled graph left after deleting a vertex through `succAbove`. -/
def deletedVertexGraph {m : ℕ} (G : SimpleGraph (Fin (m + 1)))
    (v : Fin (m + 1)) : SimpleGraph (Fin m) :=
  G.comap v.succAbove

/-- The exact unlabeled one-vertex-deletion multiplicity on graph types. -/
def cardMultiplicity {m : ℕ} (F : GraphType m)
    (G : GraphType (m + 1)) : ℕ :=
  Nat.card {v : Fin (m + 1) //
    graphTypeOf m (deletedVertexGraph (graphRepresentative G) v) = F}

/-- The exact falling-quadratic row, including the falling square on the
    diagonal and the product of distinct card multiplicities off it. -/
def quadraticCardRow {m : ℕ} (F H : GraphType m) :
    GraphType (m + 1) → ℚ :=
  letI : DecidableEq (GraphType m) := Classical.decEq _
  fun G =>
    if F = H then
      (cardMultiplicity F G : ℚ) *
        ((cardMultiplicity F G - 1 : ℕ) : ℚ)
    else
      (cardMultiplicity F G : ℚ) * (cardMultiplicity H G : ℚ)

/-- A star with `a` leaves and all remaining labelled vertices isolated. -/
def starWithIsolates (m a : ℕ) : SimpleGraph (Fin m) :=
  SimpleGraph.fromRel (fun v w : Fin m =>
    (v.1 = 0 ∧ 1 ≤ w.1 ∧ w.1 ≤ a) ∨
      (w.1 = 0 ∧ 1 ≤ v.1 ∧ v.1 ≤ a))

noncomputable def emptyCard (m : ℕ) : GraphType m :=
  graphTypeOf m (⊥ : SimpleGraph (Fin m))

noncomputable def starCard (m a : ℕ) : GraphType m :=
  graphTypeOf m (starWithIsolates m a)

/-- The source's `n` is the host order `m+1`; these are its `(n-1)`-cards. -/
noncomputable def T0 (m : ℕ) : GraphType m := emptyCard m

noncomputable def Ta (m a : ℕ) : GraphType m := starCard m a

noncomputable def Sa (m a : ℕ) : GraphType (m + 1) := starCard (m + 1) a

/-- Complementation on the canonical labelled graph carrier. -/
def graphComplement {m : ℕ} (G : SimpleGraph (Fin m)) :
    SimpleGraph (Fin m) := Gᶜ

noncomputable def complementCard {m : ℕ} (F : GraphType m) : GraphType m :=
  graphTypeOf m (graphComplement (graphRepresentative F))

/-- The two support rows form the star-with-isolates contraction path. -/
def starContractionPath (m : ℕ) : Prop :=
  Function.support (quadraticCardRow (T0 m) (T0 m)) =
      ({Sa m 0, Sa m 1} : Set (GraphType (m + 1))) ∧
    ∀ a : ℕ, 1 ≤ a → a ≤ m - 1 →
      Function.support (quadraticCardRow (T0 m) (Ta m a)) =
        ({Sa m a, Sa m (a + 1)} : Set (GraphType (m + 1)))

/-- Complementing every graph type gives the corresponding complement-star
    support path. -/
def complementStarContractionPath (m : ℕ) : Prop :=
  Function.support
      (quadraticCardRow (complementCard (T0 m)) (complementCard (T0 m))) =
      ({complementCard (Sa m 0), complementCard (Sa m 1)} :
        Set (GraphType (m + 1))) ∧
    ∀ a : ℕ, 1 ≤ a → a ≤ m - 1 →
      Function.support
          (quadraticCardRow (complementCard (T0 m))
            (complementCard (Ta m a))) =
        ({complementCard (Sa m a), complementCard (Sa m (a + 1))} :
          Set (GraphType (m + 1)))

/-- Claim 16007: with host order `n=m+1`, the empty-card falling square and
    the mixed rows have exactly the consecutive star-with-isolates supports;
    these are the star contraction path and its complement. -/
def claim16007 : Prop :=
  ∀ m : ℕ, 1 ≤ m →
    starContractionPath m ∧ complementStarContractionPath m

end

end MathlibPlus.Open.ResearchFormalization.Q0037Claim16007

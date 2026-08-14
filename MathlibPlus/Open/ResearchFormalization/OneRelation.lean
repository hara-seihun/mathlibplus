import Mathlib

noncomputable section
open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization

/-- The coordinate vector belonging to one coordinate of `Fin m → F`. -/
def coordinateVector (F : Type*) [Field F] {m : ℕ} (i : Fin m) : Fin m → F :=
  Pi.single i 1

/-- The one-relation quotient of the coordinate space. -/
abbrev oneRelationQuotient (F : Type*) [Field F] (m : ℕ) (a : Fin m → F) :=
  (Fin m → F) ⧸ Submodule.span F ({a} : Set (Fin m → F))

/-- The coordinate class in the one-relation quotient. -/
def coordinateClass (F : Type*) [Field F] (m : ℕ) (a : Fin m → F)
    (i : Fin m) : oneRelationQuotient F m a :=
  Submodule.Quotient.mk (coordinateVector F i)

/-- The prefix current with prefix length `j+1` in an ordering of the
relation support. -/
def prefixCurrent (F : Type*) [Field F] (m : ℕ) (a : Fin m → F)
    (σ : Equiv.Perm (Fin m)) (j : Fin (m - 1)) : oneRelationQuotient F m a :=
  Finset.sum (Finset.univ.filter
    (fun k : Fin m => k ≤ Fin.castLE (Nat.sub_le m 1) j))
    (fun k => a (σ k) • coordinateClass F m a (σ k))

/-- Claim 25513: every ordering of the relation support gives the prefix
currents as a basis of the one-relation quotient. -/
def prefixCurrentsBasis (F : Type*) [Field F] (m : ℕ) (a : Fin m → F) : Prop :=
  (∀ i, a i ≠ 0) →
    ∀ σ : Equiv.Perm (Fin m),
      LinearIndependent F (prefixCurrent F m a σ) ∧
        Submodule.span F (Set.range (prefixCurrent F m a σ)) = ⊤

/-- The support of the coordinate classes in a chosen quotient basis. -/
def coordinateSupportSize (F : Type*) [Field F] (m : ℕ) (a : Fin m → F)
    (B : Module.Basis (Fin (m - 1)) F (oneRelationQuotient F m a))
    (i : Fin m) : ℕ :=
  (B.repr (coordinateClass F m a i)).support.card

/-- All coordinate classes are at most `n`-sparse in a chosen basis. -/
def allCoordinateSupportsAtMost (F : Type*) [Field F] (m : ℕ) (a : Fin m → F)
    (B : Module.Basis (Fin (m - 1)) F (oneRelationQuotient F m a))
    (n : ℕ) : Prop :=
  ∀ i : Fin m, coordinateSupportSize F m a B i ≤ n

/-- A prefix-current basis has the indicated two-sparse bound. -/
def prefixSupportAtMostTwo (F : Type*) [Field F] (m : ℕ) (a : Fin m → F) : Prop :=
  ∀ σ : Equiv.Perm (Fin m),
    ∃ B : Module.Basis (Fin (m - 1)) F (oneRelationQuotient F m a),
      (∀ j, B j = prefixCurrent F m a σ j) ∧
        allCoordinateSupportsAtMost F m a B 2

/-- Claim 25515: the prefix-current coordinates have width two, while the
minimum possible width is two for `m ≥ 3` and one for `m = 2`. -/
def optimalTwoSparseQuotientWidth (F : Type*) [Field F] (m : ℕ) (a : Fin m → F) : Prop :=
  (∀ i, a i ≠ 0) →
    prefixSupportAtMostTwo F m a ∧
      (m ≥ 3 →
        (∀ i : Fin m, coordinateClass F m a i ≠ 0) ∧
        (∀ ⦃i j : Fin m⦄, i ≠ j →
          ∀ c : F, coordinateClass F m a i ≠ c • coordinateClass F m a j) ∧
        (∀ B : Module.Basis (Fin (m - 1)) F (oneRelationQuotient F m a),
          ¬ allCoordinateSupportsAtMost F m a B 1) ∧
        (∃ B : Module.Basis (Fin (m - 1)) F (oneRelationQuotient F m a),
          allCoordinateSupportsAtMost F m a B 2)) ∧
      (m = 2 →
        (∃ B : Module.Basis (Fin (m - 1)) F (oneRelationQuotient F m a),
          allCoordinateSupportsAtMost F m a B 1) ∧
        (∀ B : Module.Basis (Fin (m - 1)) F (oneRelationQuotient F m a),
          ¬ allCoordinateSupportsAtMost F m a B 0))

end MathlibPlus.Open.ResearchFormalization

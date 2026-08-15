import Mathlib

namespace MathlibPlus.Open

/-- The one-dimensional subspaces of `K^s` for a positive dimension `s`. -/
def Claim41172OneDimensional
    (K : Type*) [Field K] [Fintype K] (s : ℕ+) :=
  {W : Submodule K (Fin s → K) // Module.finrank K W = 1}

/-- A subspace has a representative whose every coordinate is nonzero. -/
def Claim41172HasNonzeroRepresentative
    (K : Type*) [Field K] [Fintype K] (s : ℕ+)
    (W : Submodule K (Fin s → K)) : Prop :=
  ∃ v : Fin s → K, v ∈ W ∧ ∀ i, v i ≠ 0

/-- The constant/source diagonal line in `K^s`. -/
def Claim41172DiagonalLine
    (K : Type*) [Field K] [Fintype K] (s : ℕ+) : Submodule K (Fin s → K) :=
  Submodule.span K {fun _ : Fin s => (1 : K)}

/-- A subspace is the constant/source diagonal line. -/
def Claim41172IsConstantDiagonal
    (K : Type*) [Field K] [Fintype K] (s : ℕ+)
    (W : Submodule K (Fin s → K)) : Prop :=
  W = Claim41172DiagonalLine K s

/-- Claim 41172: for every finite field and positive dimension, the
nonzero-coordinate one-dimensional subspaces have the stated cardinality,
and exactly one of them is the constant/source diagonal line. -/
def claim41172 : Prop :=
  ∀ (K : Type*) [Field K] [Fintype K] (s : ℕ+),
    Nat.card
        {W : Claim41172OneDimensional K s //
          Claim41172HasNonzeroRepresentative K s W.1} =
      (Fintype.card K - 1) ^ (s.val - 1) ∧
    ∃! W : Claim41172OneDimensional K s,
      Claim41172HasNonzeroRepresentative K s W.1 ∧
        Claim41172IsConstantDiagonal K s W.1

end MathlibPlus.Open

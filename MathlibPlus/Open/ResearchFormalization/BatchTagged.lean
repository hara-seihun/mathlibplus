import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.BatchTagged

abbrev TaggedProduct (ι : Type*) (X : ι → Type*) := ∀ i, X i

def taggedLambda {ι : Type*} [Fintype ι]
    {C V : ι → Type*}
    [∀ i, AddCommGroup (C i)] [∀ i, Module ℚ (C i)]
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℚ (V i)]
    (L : ∀ i, C i →ₗ[ℚ] V i) :
    TaggedProduct ι C →ₗ[ℚ] TaggedProduct ι V :=
  { toFun := fun x i => L i (x i)
    map_add' := by
      intro x y
      funext i
      exact (L i).map_add (x i) (y i)
    map_smul' := by
      intro a x
      funext i
      exact (L i).map_smul a (x i) }

/-- The tagged direct-sum assertion, with finite direct sums represented by
finite dependent products.  Each local codomain is required to be its image,
which is the displayed surjectivity hypothesis. -/
def taggedLocalSystemsNoCross
    (ι : Type*) [Fintype ι]
    (C V : ι → Type*)
    [∀ i, AddCommGroup (C i)] [∀ i, Module ℚ (C i)]
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℚ (V i)]
    [∀ i, FiniteDimensional ℚ (C i)] [∀ i, FiniteDimensional ℚ (V i)]
    (L : ∀ i, C i →ₗ[ℚ] V i) : Prop :=
  (∀ i, Function.Surjective (L i)) ∧
    Function.Surjective (taggedLambda L) ∧
    ((taggedLambda L).ker : Set (TaggedProduct ι C)) =
      {x | ∀ i, x i ∈ (L i).ker}

/-- Schur--Wedderburn conclusion for a finite-dimensional simple module over
an `F₂`-algebra, expressed by the elementary field laws on its endomorphism
ring. -/
def binarySimpleModuleEndomorphismField : Prop :=
  ∀ (A V : Type*)
    [Semiring A] [AddCommGroup V] [Module A V]
    [Algebra (ZMod 2) A] [Module (ZMod 2) V]
    [IsScalarTower (ZMod 2) A V] [Nontrivial V]
    [FiniteDimensional (ZMod 2) V],
    (∀ N : Submodule A V, N = ⊥ ∨ N = ⊤) →
      let D := Module.End A V
      Finite D ∧
        (∀ x : D, x ≠ 0 → ∃ y : D, x * y = 1 ∧ y * x = 1) ∧
        (∀ x y : D, x * y = y * x)

end MathlibPlus.Open.ResearchFormalization.BatchTagged

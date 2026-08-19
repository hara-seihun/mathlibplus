import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1371

def pairProjection38335 {K : Type*} [Semiring K]
    {I : Type*} {V : I → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    (M : Submodule K (∀ i, V i)) (i j : I) : Set (V i × V j) :=
  {p | ∃ m : M, (m.1 i, m.1 j) = p}

def subdirectTranslationModule38335 {K : Type*} [Semiring K]
    {I : Type*} {V : I → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    (M : Submodule K (∀ i, V i)) : Prop :=
  ∀ i : I, ∀ x : V i, ∃ m : M, m.1 i = x

def goursatPairMarks38335 {K : Type*} [Semiring K]
    {I : Type*} {V : I → Type*} {Q : I → I → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i j, AddCommGroup (Q i j)]
    [∀ i, Module K (V i)]
    (M : Submodule K (∀ i, V i))
    (α : ∀ i j, V i →+ Q i j) (β : ∀ i j, V j →+ Q i j) : Prop :=
  ∀ i j : I, i ≠ j →
    pairProjection38335 (K := K) (I := I) (V := V) M i j =
      {p | α i j p.1 = β i j p.2}

def markInvisibleDisplacement38335 {I : Type*} {V : I → Type*}
    {Q : I → I → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i j, AddCommGroup (Q i j)]
    (α : ∀ i j, V i →+ Q i j) (β : ∀ i j, V j →+ Q i j)
    (u : ∀ i, Equiv.Perm (V i)) : Prop :=
  ∀ i j : I, i ≠ j →
    (∀ x : V i, u i x - x ∈ (α i j).ker) ∧
      ∀ y : V j, u j y - y ∈ (β i j).ker

def commonMarkBijection38335 {I : Type*} {V : I → Type*}
    {Q : I → I → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i j, AddCommGroup (Q i j)]
    (α : ∀ i j, V i →+ Q i j) (β : ∀ i j, V j →+ Q i j)
    (u : ∀ i, Equiv.Perm (V i)) : Prop :=
  ∃ θ : ∀ i j, Equiv.Perm (Q i j),
    ∀ i j : I, i ≠ j →
      (∀ x : V i, α i j (u i x) = θ i j (α i j x)) ∧
        ∀ y : V j, β i j (u j y) = θ i j (β i j y)

def goursatDescent38335 {K : Type*} [Semiring K]
    {I : Type*} {V : I → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    (M : Submodule K (∀ i, V i))
    (u : ∀ i, Equiv.Perm (V i)) : Prop :=
  ∀ i j : I, i ≠ j →
    Set.image (fun p : V i × V j => (u i p.1, u j p.2))
        (pairProjection38335 (K := K) (I := I) (V := V) M i j) =
      pairProjection38335 (K := K) (I := I) (V := V) M i j

/-- Claim 38335: identity block permutation and identity quotient marks give
Goursat descent when every local displacement is invisible to every incident
quotient kernel; the same descent holds when both endpoints induce one common
bijection on each quotient mark. -/
def claim38335 : Prop :=
  ∀ {K : Type*} [Semiring K]
    {I : Type*}
    {V : I → Type*} [∀ i : I, AddCommGroup (V i)]
    [∀ i : I, Module K (V i)]
    {Q : I → I → Type*} [∀ i j : I, AddCommGroup (Q i j)]
    (M : Submodule K (∀ i, V i))
    (α : ∀ i j, V i →+ Q i j) (β : ∀ i j, V j →+ Q i j)
    (u : ∀ i, Equiv.Perm (V i)),
    subdirectTranslationModule38335 M →
      goursatPairMarks38335 M α β →
        (markInvisibleDisplacement38335 α β u ∨
          commonMarkBijection38335 α β u) →
          goursatDescent38335 (K := K) (I := I) (V := V) M u

end MathlibPlus.Open.ResearchFormalization.R1371

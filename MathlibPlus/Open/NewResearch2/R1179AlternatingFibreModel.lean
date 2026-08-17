import Mathlib

namespace MathlibPlus.Open.NewResearch2.R1179AlternatingFibreModel

private def dihedralS (m : ℕ) : DihedralGroup m :=
  DihedralGroup.sr 0

private def rotationFiber {A : Type*} {m : ℕ} [Group A]
    (i : ZMod m) : Set (A × DihedralGroup m) :=
  {x | ∃ a : A, x = (a, DihedralGroup.r i)}

private def reflectionFiber {A : Type*} {m : ℕ} [Group A]
    (i : ZMod m) : Set (A × DihedralGroup m) :=
  {x | ∃ a : A, x = (a, DihedralGroup.r i * dihedralS m)}

private def thickConnection {A : Type*} {m : ℕ} [Group A] :
    Set (A × DihedralGroup m) :=
  (Set.univ : Set A) ×ˢ {dihedralS m}

private def thinConnection {A : Type*} {m : ℕ} [Group A] :
    Set (A × DihedralGroup m) :=
  {(1, DihedralGroup.r 1 * dihedralS m)}

private def leftStep {M : Type*} [Mul M] (S : Set M) (x y : M) : Prop :=
  ∃ g ∈ S, g * x = y

private def leftCayley {M : Type*} [Mul M] (S : Set M) : SimpleGraph M :=
  SimpleGraph.fromRel (leftStep S)

private def alternatingGraph {A : Type*} {m : ℕ} [Group A] :
    SimpleGraph (A × DihedralGroup m) :=
  leftCayley (thickConnection (A := A) (m := m) ∪
    thinConnection (A := A) (m := m))

/-- Claim 41665: the actual left-multiplication Cayley graph on
`A × D₂ₘ` with connection set `(A × {s}) ∪ {(1,rs)}` has complete
relations from `R_i` to `S_(-i)`, matching relations from `R_i` to
`S_(1-i)`, and no other fibre incidences. -/
def claim41665 : Prop :=
  ∀ {A : Type*} [Group A] [Fintype A] [Nontrivial A]
    {m : ℕ},
    3 ≤ m →
    Nat.Coprime (Fintype.card A) (2 * m) →
      (∀ x y : A × DihedralGroup m,
        (alternatingGraph (A := A) (m := m)).Adj x y ↔
          x ≠ y ∧
            (leftStep (thickConnection (A := A) (m := m)) x y ∨
              leftStep (thickConnection (A := A) (m := m)) y x ∨
              leftStep (thinConnection (A := A) (m := m)) x y ∨
              leftStep (thinConnection (A := A) (m := m)) y x)) ∧
      (∀ i j : ZMod m, ∀ a b : A,
        leftStep (thickConnection (A := A) (m := m))
            (a, DihedralGroup.r i) (b, DihedralGroup.r j * dihedralS m) ↔
          j = -i) ∧
      (∀ i j : ZMod m, ∀ a b : A,
        leftStep (thinConnection (A := A) (m := m))
            (a, DihedralGroup.r i) (b, DihedralGroup.r j * dihedralS m) ↔
          a = b ∧ j = 1 - i) ∧
      (∀ i : ZMod m, ∀ x ∈ rotationFiber i, ∀ y ∈ reflectionFiber (-i),
        (alternatingGraph (A := A) (m := m)).Adj x y) ∧
      (∀ i : ZMod m, ∀ a b : A,
        (alternatingGraph (A := A) (m := m)).Adj
            (a, DihedralGroup.r i)
            (b, DihedralGroup.r (1 - i) * dihedralS m) ↔
          a = b) ∧
      (∀ i j : ZMod m, j ≠ -i → j ≠ 1 - i → ∀ x y,
        x ∈ rotationFiber i → y ∈ reflectionFiber j →
          ¬ (alternatingGraph (A := A) (m := m)).Adj x y) ∧
      (∀ i j : ZMod m, ∀ x y,
        x ∈ rotationFiber i → y ∈ rotationFiber j →
          ¬ (alternatingGraph (A := A) (m := m)).Adj x y) ∧
      (∀ i j : ZMod m, ∀ x y,
        x ∈ reflectionFiber i → y ∈ reflectionFiber j →
          ¬ (alternatingGraph (A := A) (m := m)).Adj x y) ∧
      (∀ i : ZMod m, ∀ a : A,
        ∃! b : A,
          (alternatingGraph (A := A) (m := m)).Adj
            (a, DihedralGroup.r i)
            (b, DihedralGroup.r (1 - i) * dihedralS m)) ∧
      (∀ i : ZMod m, ∀ b : A,
        ∃! a : A,
          (alternatingGraph (A := A) (m := m)).Adj
            (a, DihedralGroup.r i)
            (b, DihedralGroup.r (1 - i) * dihedralS m)) ∧
      (∀ i j : ZMod m, ∀ a b : A,
        (alternatingGraph (A := A) (m := m)).Adj
            (a, DihedralGroup.r i)
            (b, DihedralGroup.r j * dihedralS m) ↔
          j = -i ∨ (a = b ∧ j = 1 - i))

end MathlibPlus.Open.NewResearch2.R1179AlternatingFibreModel

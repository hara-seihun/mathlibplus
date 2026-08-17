import MathlibPlus.Open.ResearchFormalization.R1179.Claim41666

namespace MathlibPlus.Open.ResearchFormalization.R1179.Claim31898

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R1179.Claim41666

abbrev FiberLabel (m : ℕ) := ZMod m × Bool

/-- The thick edge relation on the two kinds of quotient fibre labels. -/
def quotientThick {m : ℕ} (x y : FiberLabel m) : Prop :=
  (x.2 = false ∧ y.2 = true ∧ y.1 = -x.1) ∨
    (x.2 = true ∧ y.2 = false ∧ x.1 = -y.1)

/-- The thin edge relation on the two kinds of quotient fibre labels. -/
def quotientThin {m : ℕ} (x y : FiberLabel m) : Prop :=
  (x.2 = false ∧ y.2 = true ∧ y.1 = 1 - x.1) ∨
    (x.2 = true ∧ y.2 = false ∧ x.1 = 1 - y.1)

/-- The quotient graph obtained from the two labelled fibre relations. -/
def quotientGraph (m : ℕ) : SimpleGraph (FiberLabel m) :=
  SimpleGraph.fromRel (fun x y => quotientThick x y ∨ quotientThin x y)

/-- Claim 31898: the exact left-action Cayley carrier has complete
`R_i`--`S_(-i)` thick fibres, coordinatewise `R_i`--`S_(1-i)` thin
matchings, no same-side incidences, and the resulting two-coloured quotient
is the alternating `2m`-cycle. -/
def claim31898 : Prop :=
  ∀ (A : Type*) [Group A] [Fintype A] [Nontrivial A]
    (m : ℕ),
    3 ≤ m →
      Nat.Coprime (Fintype.card A) (2 * m) →
        (∀ i j : ZMod m, ∀ a b : A,
          leftStep (thickConnection (A := A) (m := m))
              (a, DihedralGroup.r i)
              (b, DihedralGroup.r j * DihedralGroup.sr 0) ↔
            j = -i) ∧
        (∀ i j : ZMod m, ∀ a b : A,
          leftStep (thinConnection (A := A) (m := m))
              (a, DihedralGroup.r i)
              (b, DihedralGroup.r j * DihedralGroup.sr 0) ↔
            a = b ∧ j = 1 - i) ∧
        (∀ i j : ZMod m, ∀ x y,
          x ∈ rotationFiber (A := A) i →
            y ∈ reflectionFiber (A := A) j →
              (alternatingGraph (A := A) (m := m)).Adj x y ↔
                (∃ a b : A,
                  x = (a, DihedralGroup.r i) ∧
                    y = (b, DihedralGroup.r j * DihedralGroup.sr 0) ∧
                    (j = -i ∨ (a = b ∧ j = 1 - i)))) ∧
        (∀ i j : ZMod m, ∀ x y,
          x ∈ rotationFiber (A := A) i →
            y ∈ reflectionFiber (A := A) j →
              (alternatingGraph (A := A) (m := m)).Adj x y ↔
                j = -i ∨ (x.1 = y.1 ∧ j = 1 - i)) ∧
        (∀ i j : ZMod m, ∀ x y,
          x ∈ rotationFiber (A := A) i →
            y ∈ rotationFiber (A := A) j →
              ¬ (alternatingGraph (A := A) (m := m)).Adj x y) ∧
        (∀ i j : ZMod m, ∀ x y,
          x ∈ reflectionFiber (A := A) i →
            y ∈ reflectionFiber (A := A) j →
              ¬ (alternatingGraph (A := A) (m := m)).Adj x y) ∧
        (∀ i j : ZMod m, j ≠ -i → j ≠ 1 - i →
          ∀ x y,
            x ∈ rotationFiber (A := A) i →
              y ∈ reflectionFiber (A := A) j →
                ¬ (alternatingGraph (A := A) (m := m)).Adj x y) ∧
        (∀ i : ZMod m, ∀ a : A,
          ∃! b : A,
            (alternatingGraph (A := A) (m := m)).Adj
              (a, DihedralGroup.r i)
              (b, DihedralGroup.r (1 - i) * DihedralGroup.sr 0)) ∧
        (∀ i : ZMod m, ∀ b : A,
          ∃! a : A,
            (alternatingGraph (A := A) (m := m)).Adj
              (a, DihedralGroup.r i)
              (b, DihedralGroup.r (1 - i) * DihedralGroup.sr 0)) ∧
        (∀ x y : FiberLabel m,
          quotientThick x y → ¬ quotientThin x y) ∧
        (∀ x : FiberLabel m, ∃! y : FiberLabel m, quotientThick x y) ∧
        (∀ x : FiberLabel m, ∃! y : FiberLabel m, quotientThin x y) ∧
        Nonempty ((quotientGraph m).Iso (SimpleGraph.cycleGraph (2 * m)))

end

end MathlibPlus.Open.ResearchFormalization.R1179.Claim31898

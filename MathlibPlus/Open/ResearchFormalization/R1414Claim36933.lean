import Mathlib
import Mathlib.Combinatorics.SimpleGraph.Cayley

namespace MathlibPlus.Open.ResearchFormalization.R1414Claim36933

noncomputable section

abbrev CrownBase (n : ℕ) := ZMod 2 × ZMod n
abbrev BlowupVertex (n : ℕ) := CrownBase n × ZMod 2

def crownAdj {n : ℕ} (x y : CrownBase n) : Prop :=
  x.1 ≠ y.1 ∧ x.2 ≠ y.2

def crownGraph (n : ℕ) : SimpleGraph (CrownBase n) :=
  SimpleGraph.fromRel (crownAdj (n := n))

def blowupAdj {n : ℕ} (x y : BlowupVertex n) : Prop :=
  crownAdj x.1 y.1

def blowupGraph (n : ℕ) : SimpleGraph (BlowupVertex n) :=
  SimpleGraph.fromRel (blowupAdj (n := n))

def blowupFiber {n : ℕ} (b : CrownBase n) : Set (BlowupVertex n) :=
  {x | x.1 = b}

def falseTwinRelation {n : ℕ}
    (G : SimpleGraph (BlowupVertex n))
    (x y : BlowupVertex n) : Prop :=
  x = y ∨
    (x ≠ y ∧ ¬ G.Adj x y ∧
      ∀ z : BlowupVertex n, G.Adj x z ↔ G.Adj y z)

def quotientProjection {n : ℕ} :
    BlowupVertex n → CrownBase n := fun x => x.1

/-- Claim 36933: the reflexive false-twin relation has exactly the displayed
size-two fibers as its classes, and the explicit quotient is the crown graph. -/
def claim36933 : Prop :=
  ∀ (n : ℕ), 3 ≤ n →
    (∀ x y : BlowupVertex n,
      falseTwinRelation (blowupGraph n) x y ↔
        ∃ b : CrownBase n,
          x ∈ blowupFiber b ∧ y ∈ blowupFiber b) ∧
      (∀ x : BlowupVertex n,
        {y : BlowupVertex n |
          falseTwinRelation (blowupGraph n) x y} =
          blowupFiber x.1) ∧
      (∀ b : CrownBase n, (blowupFiber b).ncard = 2) ∧
      (∀ [NeZero n], Fintype.card (CrownBase n) = 2 * n) ∧
      Function.Surjective (quotientProjection (n := n)) ∧
      (∀ x y : BlowupVertex n,
        (blowupGraph n).Adj x y ↔
          (crownGraph n).Adj (quotientProjection x) (quotientProjection y))

end

end MathlibPlus.Open.ResearchFormalization.R1414Claim36933

import Mathlib
import Mathlib.Combinatorics.SimpleGraph.Cayley

namespace MathlibPlus.Open.ResearchFormalization.R1414Claim36931

noncomputable section

abbrev Binary3 := Fin 3 → ZMod 2
abbrev GroupN (n : ℕ) := Binary3 × ZMod n

def binaryBasis (j : Fin 3) : Binary3 :=
  fun i => if i = j then 1 else 0

def e1 : Binary3 := binaryBasis 0
def e2 : Binary3 := binaryBasis 1
def e3 : Binary3 := binaryBasis 2

def connectionSet (n : ℕ) : Set (GroupN n) :=
  {g | (g.1 = e1 ∧ g.2 ≠ 0) ∨
    (g.1 = e2 ∧ g.2 ≠ 0) ∨
    (g.1 = e3 ∧ g.2 = 0)}

def cayleyFamilyGraph (n : ℕ) : SimpleGraph (GroupN n) :=
  SimpleGraph.addCayley (connectionSet n)

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

def productAdj {n : ℕ}
    (x y : ZMod 2 × BlowupVertex n) : Prop :=
  (x.1 ≠ y.1 ∧ x.2 = y.2) ∨
    (x.1 = y.1 ∧ blowupAdj x.2 y.2)

def productGraph (n : ℕ) :
    SimpleGraph (ZMod 2 × BlowupVertex n) :=
  SimpleGraph.fromRel (productAdj (n := n))

/-- The exact coordinate map `(x₁,x₂,x₃,z) ↦ (x₃,x₁+x₂,z,x₁)`. -/
def productCoordinateMap (n : ℕ) :
    GroupN n → ZMod 2 × BlowupVertex n :=
  fun g =>
    (g.1 2, ((g.1 0 + g.1 1, g.2), g.1 0))

/-- Claim 36931: the displayed map is a graph recognition between the exact
Cayley graph and the Cartesian product with the independent crown blow-up. -/
def claim36931 : Prop :=
  ∀ (n : ℕ), 3 ≤ n → Odd n →
    Function.Bijective (productCoordinateMap n) ∧
      ∀ x y : GroupN n,
        (cayleyFamilyGraph n).Adj x y ↔
          (productGraph n).Adj
            (productCoordinateMap n x) (productCoordinateMap n y)

end

end MathlibPlus.Open.ResearchFormalization.R1414Claim36931

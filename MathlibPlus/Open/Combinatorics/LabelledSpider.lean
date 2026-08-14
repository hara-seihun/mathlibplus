import Mathlib

namespace MathlibPlus.Open.Combinatorics

private def spiderRelation (a b c x y : Fin 5) : Prop :=
  (x = a ∧ y = b) ∨
    (x = b ∧ y = c) ∨
    (x = a ∧ y ∉ ({a, b, c} : Finset (Fin 5)))

def labelled112Spider (a b c : Fin 5) : SimpleGraph (Fin 5) :=
  SimpleGraph.fromRel (spiderRelation a b c)

noncomputable def graphDegree (S : SimpleGraph (Fin 5)) (v : Fin 5) : ℕ :=
  letI : Fintype {w : Fin 5 // S.Adj v w} := Fintype.ofFinite _
  Fintype.card {w : Fin 5 // S.Adj v w}

def IsLabelled112Spider (S : SimpleGraph (Fin 5)) (a b c : Fin 5) : Prop :=
  S = labelled112Spider a b c ∧
    graphDegree S a = 3 ∧
    graphDegree S b = 2 ∧
    graphDegree S c = 1 ∧
    ∀ x : Fin 5, x ∉ ({a, b, c} : Finset (Fin 5)) →
      S.Adj a x ∧ graphDegree S x = 1

def labelled112SpiderConstruction : Prop :=
  ∀ a b c : Fin 5, a ≠ b → a ≠ c → b ≠ c →
    ∃! S : SimpleGraph (Fin 5), IsLabelled112Spider S a b c

end MathlibPlus.Open.Combinatorics

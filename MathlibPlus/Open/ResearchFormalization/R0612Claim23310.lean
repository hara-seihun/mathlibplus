import MathlibPlus.Open.ResearchFormalization.GraphClaims01a00bdd
import MathlibPlus.Combinatorics.Claim23309

open Classical
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

namespace MathlibPlus.Open.ResearchFormalization.R0612Claim23310

noncomputable section

abbrev GraphClass :=
  MathlibPlus.Open.ResearchFormalization.GraphClaims01a00bdd.GraphClass

open MathlibPlus.Open.ResearchFormalization.GraphClaims01a00bdd

def deletedCardGraph {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) :
    SimpleGraph {x : Fin n // x ≠ v} :=
  G.induce {x : Fin n | x ≠ v}

def deletedCardType {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) :
    GraphClass :=
  graphClassFinite (deletedCardGraph G v)

def deckCount {n : ℕ} (G : SimpleGraph (Fin n))
    (F : GraphClass) : ℕ :=
  ∑ v : Fin n, if deletedCardType G v = F then 1 else 0

def fallingCardRow {n : ℕ} (S : Multiset GraphClass)
    (G : SimpleGraph (Fin n)) : ℕ :=
  ∏ F ∈ S.toFinset, (deckCount G F).descFactorial (S.count F)

def cardSubmultisetOfDeck {n : ℕ} (S : Multiset GraphClass)
    (G : SimpleGraph (Fin n)) : Prop :=
  ∀ F : GraphClass, S.count F ≤ deckCount G F

def graphColumnNonisomorphic {n : ℕ}
    (T G : SimpleGraph (Fin n)) : Prop :=
  ¬Nonempty (T ≃g G)

/-- Every tree column in the complete graph-column carrier has a positive
falling cubic card row private from every nonisomorphic graph column. -/
def claim23310 : Prop :=
  ∀ (n : ℕ),
    5 ≤ n →
      ∀ T : SimpleGraph (Fin n),
        T.IsTree →
          ∃ S : Multiset GraphClass,
            S.card = 3 ∧
              cardSubmultisetOfDeck S T ∧
                0 < fallingCardRow S T ∧
                  ∀ G : SimpleGraph (Fin n),
                    graphColumnNonisomorphic T G →
                      fallingCardRow S G = 0

end

end MathlibPlus.Open.ResearchFormalization.R0612Claim23310

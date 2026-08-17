import MathlibPlus.Open.Combinatorics.TreeDeck

namespace MathlibPlus.Open.Combinatorics

open ProjectsResearch.TreeDeck

/--
Claim 5075: the canonical rational finitely-supported state space on
unlabelled tree shapes, together with the leaf-deck action on each basis tree.
The sum is indexed by leaf occurrences, so equal card shapes contribute with
 their occurrence multiplicity.
-/
def treeStateSpaceAndLeafDeck_5075 : Prop :=
  ∀ n : ℕ,
    (TreeState n = (UnlabelledTree n →₀ ℚ)) ∧
      ∀ T : UnlabelledTree n,
        leafDeck n (Finsupp.single T (1 : ℚ)) =
          ∑ v : leafVertices T,
            Finsupp.single (leafCard T v) (1 : ℚ)

end MathlibPlus.Open.Combinatorics

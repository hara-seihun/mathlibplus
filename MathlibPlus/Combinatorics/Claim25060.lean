import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace MathlibPlus.Combinatorics.Claim25060

/--
The ten unordered bipartitions of six labels into complementary triples are
represented canonically by the triple containing label `0`.
-/
theorem unorderedComplementaryTripleCount_claim25060 :
    (Finset.univ.filter
      (fun E : Finset (Fin 6) => E.card = 3 ∧ (0 : Fin 6) ∈ E)).card = 10 := by
  decide

end MathlibPlus.Combinatorics.Claim25060

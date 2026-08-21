-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is a root of the Unverified library rather than of MathlibPlus and no build here depends on it. See unverified.txt.
import MathlibPlus.Basic

namespace MathlibPlus.Combinatorics

/-- Claim 24070: the exact one-card/two-card deletion-origin census on a
15-vertex base, and its total over any 455-element target index.  A deletion
triple is represented by a distinguished vertex and a disjoint unordered
2-subset; no graph-specific structure is supplied by the source statement. -/
theorem deletionTripleCensus_claim24070 :
    let Triple :=
      {p : Fin 15 × Finset (Fin 15) // p.2.card = 2 ∧ p.1 ∉ p.2}
    Fintype.card Triple = 15 * Nat.choose 14 2 ∧
      15 * Nat.choose 14 2 = 1365 ∧
      ∀ (Target : Type) [Fintype Target], Fintype.card Target = 455 →
        Fintype.card (Target × Triple) = 621075 := by
  dsimp
  let Triple :=
    {p : Fin 15 × Finset (Fin 15) // p.2.card = 2 ∧ p.1 ∉ p.2}
  have hTriple : Fintype.card Triple = 15 * Nat.choose 14 2 := by
    native_decide
  have hCount : 15 * Nat.choose 14 2 = 1365 := by
    norm_num [Nat.choose]
  refine ⟨hTriple, hCount, ?_⟩
  intro Target _ hTarget
  rw [Fintype.card_prod, hTarget, hTriple, hCount]

end MathlibPlus.Combinatorics

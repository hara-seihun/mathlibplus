import Mathlib

namespace MathlibPlus.Open.Research

private def parityRoot : Fin 3 → Fin 7 :=
  ![0, 1, 2]

private def parityOutside : Fin 4 → Fin 7 :=
  ![3, 4, 5, 6]

private def evenParityTable : Fin 4 → Fin 3 → Bool :=
  ![![false, false, false],
    ![false, true, true],
    ![true, false, true],
    ![true, true, false]]

private def oddParityTable : Fin 4 → Fin 3 → Bool :=
  ![![false, false, true],
    ![false, true, false],
    ![true, false, false],
    ![true, true, true]]

private def singletonMargin (table : Fin 4 → Fin 3 → Bool) (i : Fin 3) : ℕ :=
  (Finset.univ.filter (fun j => table j i = true)).card

private def pairMargin (table : Fin 4 → Fin 3 → Bool) (i k : Fin 3) : ℕ :=
  (Finset.univ.filter (fun j => table j i = true ∧ table j k = true)).card

private def realizesParityTable (G : SimpleGraph (Fin 7))
    (table : Fin 4 → Fin 3 → Bool) : Prop :=
  ∀ (j : Fin 4) (i : Fin 3),
    G.Adj (parityRoot i) (parityOutside j) ↔ table j i = true

def parityMarginBooleanAmbiguity : Prop :=
  evenParityTable ≠ oddParityTable ∧
    (∀ i : Fin 3,
      singletonMargin evenParityTable i = 2 ∧
      singletonMargin oddParityTable i = 2) ∧
    (pairMargin evenParityTable 0 1 = 1 ∧
      pairMargin evenParityTable 0 2 = 1 ∧
      pairMargin evenParityTable 1 2 = 1) ∧
    (pairMargin oddParityTable 0 1 = 1 ∧
      pairMargin oddParityTable 0 2 = 1 ∧
      pairMargin oddParityTable 1 2 = 1) ∧
    (∃ G : SimpleGraph (Fin 7), realizesParityTable G evenParityTable) ∧
    ∃ G : SimpleGraph (Fin 7), realizesParityTable G oddParityTable

end MathlibPlus.Open.Research

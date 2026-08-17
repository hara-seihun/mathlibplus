import Mathlib

namespace MathlibPlus.Open.Combinatorics

/-- Claim 34988: balanced two-clique extremizers at the 45 floor realize the
separate root-neighbor and root-nonneighbor signed-cycle premises with the
constant signs zero and one, respectively. -/
def separateSignedCycleSharpness_claim34988 : Prop :=
  (∀ (m : ℕ), 9 ≤ m → m ≤ 12 →
      ∀ (H : SimpleGraph (Fin m)),
        (∀ a b : Fin m,
          H.Adj a b ↔
            (a ≠ b ∧
              ((a.val < m / 2 ∧ b.val < m / 2) ∨
                (m / 2 ≤ a.val ∧ m / 2 ≤ b.val)))) →
        H.edgeSet.ncard = (m * (m - 2) + 3) / 4 ∧
          (∀ s : Finset (Fin m), s.card = 5 →
            (∃ (v : (↑s : Set (Fin m))),
              ∃ w : (H.induce (↑s : Set (Fin m))).Walk v v,
                w.IsCycle ∧
                  ((w.length : ZMod 2) +
                    (w.edges.map (fun _ => (0 : ZMod 2))).sum = 1)) ∧
            (∃ (v : (↑s : Set (Fin m))),
              ∃ w : (H.induce (↑s : Set (Fin m))).Walk v v,
                w.IsCycle ∧
                  (w.edges.map (fun _ => (1 : ZMod 2))).sum = 1))) ∧
    ∃ (A : SimpleGraph (Fin 10)) (B : SimpleGraph (Fin 11)),
      (∀ a b : Fin 10,
        A.Adj a b ↔
          (a ≠ b ∧
            ((a.val < 10 / 2 ∧ b.val < 10 / 2) ∨
              (10 / 2 ≤ a.val ∧ 10 / 2 ≤ b.val)))) ∧
      (∀ a b : Fin 11,
        B.Adj a b ↔
          (a ≠ b ∧
            ((a.val < 11 / 2 ∧ b.val < 11 / 2) ∨
              (11 / 2 ≤ a.val ∧ 11 / 2 ≤ b.val)))) ∧
      A.edgeSet.ncard + B.edgeSet.ncard = 45 ∧
      (∀ s : Finset (Fin 10), s.card = 5 →
        ∃ (v : (↑s : Set (Fin 10))),
          ∃ w : (A.induce (↑s : Set (Fin 10))).Walk v v,
            w.IsCycle ∧
              ((w.length : ZMod 2) +
                (w.edges.map (fun _ => (0 : ZMod 2))).sum = 1)) ∧
      (∀ s : Finset (Fin 11), s.card = 5 →
        ∃ (v : (↑s : Set (Fin 11))),
          ∃ w : (B.induce (↑s : Set (Fin 11))).Walk v v,
            w.IsCycle ∧
              (w.edges.map (fun _ => (1 : ZMod 2))).sum = 1)

end MathlibPlus.Open.Combinatorics

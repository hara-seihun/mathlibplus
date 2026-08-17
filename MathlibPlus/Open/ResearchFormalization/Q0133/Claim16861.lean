import Mathlib

open scoped Classical BigOperators

namespace MathlibPlus.Open.ResearchFormalization.Q0133.Claim16861

noncomputable section

private def edgeCount {N : ℕ} (G : SimpleGraph (Fin N)) : ℕ :=
  (Finset.univ.filter (fun p : Fin N × Fin N => G.Adj p.1 p.2)).card / 2

private def monoCount {N : ℕ} (G : SimpleGraph (Fin N)) (s : Fin N → Bool) : ℕ :=
  (Finset.univ.filter (fun p : Fin N × Fin N =>
    G.Adj p.1 p.2 ∧ s p.1 = s p.2)).card / 2

private def beta {N : ℕ} (G : SimpleGraph (Fin N)) : ℕ :=
  sInf {k : ℕ | ∃ s : Fin N → Bool, monoCount G s = k}

private def crossingAdj {N : ℕ} (G : SimpleGraph (Fin N)) (s : Fin N → Bool)
    (u v : Fin N) : Prop :=
  G.Adj u v ∧ s u ≠ s v

private def connected {N : ℕ} (G : SimpleGraph (Fin N)) : Prop :=
  ∀ u v : Fin N, Relation.ReflTransGen G.Adj u v

private def degree {N : ℕ} (B : SimpleGraph (Fin N)) (v : Fin N) : ℕ :=
  (Finset.univ.filter (fun w : Fin N => B.Adj v w)).card

private def sideA {N : ℕ} (s : Fin N → Bool) : Finset (Fin N) :=
  Finset.univ.filter (fun v => s v = false)

private def sideC {N : ℕ} (s : Fin N → Bool) : Finset (Fin N) :=
  Finset.univ.filter (fun v => s v = true)

private structure CutPresentation where
  N : ℕ
  G : SimpleGraph (Fin N)
  side : Fin N → Bool
  B : SimpleGraph (Fin N)
  crossing : ∀ u v, B.Adj u v ↔ crossingAdj G side u v
  maximum : monoCount G side = beta G

/-- The exact degree-deficit and uniform singleton-cut certificates. -/
def claim_16861_degree_deficit_singleton_cut_certificate : Prop :=
  ∀ (P : CutPresentation), connected P.B →
    let A := sideA P.side
    let C := sideC P.side
    let a := A.card
    let c := C.card
    let m := edgeCount P.B
    (0 < a ∧ 0 < c) →
      (beta P.G : ℚ) ≤
        (2 * m : ℚ) -
          (A.sum (fun x => (degree P.B x : ℚ) ^ 2)) / c -
          (C.sum (fun y => (degree P.B y : ℚ) ^ 2)) / a ∧
      (beta P.G : ℚ) ≤ m

end

end MathlibPlus.Open.ResearchFormalization.Q0133.Claim16861

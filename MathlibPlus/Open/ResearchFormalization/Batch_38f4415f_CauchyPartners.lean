import Mathlib

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.Batch_38f4415f.CauchyPartners

abbrev Pairing (d : ℕ) := Equiv (Fin (2 * d)) (Fin d × Fin 2)

noncomputable def sideSwap : Fin 2 ≃ Fin 2 :=
  Equiv.swap 0 1

def pairingMate {d : ℕ} (p : Pairing d) (v : Fin (2 * d)) : Fin (2 * d) :=
  p.symm (⟨(p v).1, sideSwap (p v).2⟩)

def cavityLinear {K : Type*} [CommRing K] (a : K) : Polynomial K :=
  Polynomial.X + Polynomial.C a

def pairStateFactor {K : Type*} [CommRing K] (a b : K) : Polynomial (Polynomial K) :=
  Polynomial.X + Polynomial.C (cavityLinear a * cavityLinear b)

def completePairingPolynomial {K : Type*} [CommRing K] {d : ℕ}
    (occurrences : Fin (2 * d) → K) (p : Pairing d) : Polynomial (Polynomial K) :=
  ∏ j : Fin d,
    pairStateFactor
      (occurrences (p.symm (j, (0 : Fin 2))))
      (occurrences (p.symm (j, (1 : Fin 2))))

def synchronizedSquarefreeRows {K : Type*} {d : ℕ}
    (values : Fin 3 → Fin (2 * d) → K)
    (rowOrder : Fin 3 → Equiv (Fin (2 * d)) (Fin (2 * d)))
    (occurrences : Fin (2 * d) → K)
    (retained : Set K) : Prop :=
  Function.Injective occurrences ∧
    (∀ (i : Fin 3) (v : Fin (2 * d)),
      values i (rowOrder i v) = occurrences v) ∧
    (∀ a : K, a ∈ retained → ∃ v : Fin (2 * d), occurrences v = a)

def purePairingSurvivor {K : Type*} [CommRing K] {d : ℕ}
    (c : Fin 3 → K)
    (values : Fin 3 → Fin (2 * d) → K)
    (rowOrder : Fin 3 → Equiv (Fin (2 * d)) (Fin (2 * d)))
    (occurrences : Fin (2 * d) → K)
    (pairings : Fin 3 → Pairing d)
    (retained : Set K) : Prop :=
  synchronizedSquarefreeRows values rowOrder occurrences retained ∧
    (∑ i : Fin 3,
        Polynomial.C (Polynomial.C (c i)) *
          completePairingPolynomial occurrences (pairings i)) = 0

/-- Every squarefree pure-pairing survivor obeys the exact Cauchy partner
    equation at each retained cavity occurrence. -/
def claim24634 : Prop :=
  ∀ {K : Type*} [Field K] {d : ℕ}
    (c : Fin 3 → K)
    (values : Fin 3 → Fin (2 * d) → K)
    (rowOrder : Fin 3 → Equiv (Fin (2 * d)) (Fin (2 * d)))
    (occurrences : Fin (2 * d) → K)
    (pairings : Fin 3 → Pairing d)
    (retained : Set K),
    purePairingSurvivor c values rowOrder occurrences pairings retained →
    ∀ a : K, a ∈ retained →
      ∀ v : Fin (2 * d), occurrences v = a →
        ∑ i : Fin 3,
          c i /
            (values i (rowOrder i (pairingMate (pairings i) v)) - a) = 0

end MathlibPlus.Open.ResearchFormalization.Batch_38f4415f.CauchyPartners

import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open

def claim50102 : Prop :=
  ∀ (S : Finset {p : ℕ // p.Prime}) (q : ℕ),
    q.Prime →
    Odd q →
    (∀ p ∈ S, (p : ℕ) ≠ q) →
    ∀ (a_q : ZMod q) (A : ℤ),
      (A : ZMod q) = a_q →
      Irreducible
          (Polynomial.X ^ 2 - Polynomial.C a_q * Polynomial.X + Polynomial.C 1) →
      Irreducible
          (Polynomial.map (Int.castRingHom (ZMod q))
            (Polynomial.X ^ 2 - Polynomial.C A * Polynomial.X + Polynomial.C 1)) ∧
        Irreducible
          (Polynomial.map (Int.castRingHom ℚ)
            (Polynomial.X ^ 2 - Polynomial.C A * Polynomial.X + Polynomial.C 1))

def claim50104 : Prop :=
  ∀ (S : Finset {p : ℕ // p.Prime}) (q : ℕ),
    q.Prime →
    Odd q →
    (∀ p ∈ S, (p : ℕ) ≠ q) →
    ∀ (a_q : ZMod q),
      ∃ A_0 : ℤ,
        (A_0 : ZMod q) = a_q ∧
        (∀ p ∈ S, (A_0 : ZMod (p : ℕ)) = 0) ∧
        ∀ k : ℤ,
          let m : ℤ := q * S.prod (fun p => (p : ℤ))
          let A : ℤ := A_0 + k * m
          (A : ZMod q) = a_q ∧
          (∀ p ∈ S, (A : ZMod (p : ℕ)) = 0) ∧
          ∀ p ∈ S,
            Polynomial.map (Int.castRingHom (ZMod (p : ℕ)))
                (Polynomial.X ^ 2 - Polynomial.C A * Polynomial.X + Polynomial.C 1) =
              Polynomial.X ^ 2 + Polynomial.C 1 ∧
            Polynomial.X ^ 2 + Polynomial.C 1 =
              Polynomial.map (Int.castRingHom (ZMod (p : ℕ)))
                (Polynomial.cyclotomic 4 ℤ)

end MathlibPlus.Open

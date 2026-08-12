import Mathlib

namespace MathlibPlus.Algebra.Claim53470

private theorem square_eq_self (a : ZMod 2) : a ^ 2 = a := by
  simpa using (FiniteField.pow_card a)

theorem frobeniusSquare_coordinatewise_claim53470 (n : ℕ) :
    ∀ u : Fin n → ZMod 2, (fun i => u i ^ 2) = u := by
  intro u
  funext i
  exact square_eq_self (u i)

theorem frobeniusSquare_preserves_independent_pair_claim53470
    (n : ℕ) (P Q : Fin n → ZMod 2)
    (hPQ : LinearIndependent (ZMod 2) ![P, Q]) :
    LinearIndependent (ZMod 2)
      ![(fun i => P i ^ 2), (fun i => Q i ^ 2)] := by
  simpa [frobeniusSquare_coordinatewise_claim53470] using hPQ

theorem frobeniusSquare_as_linearMap_claim53470 (n : ℕ) :
    ∃ F : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2),
      (∀ u, F u = (fun i => u i ^ 2)) ∧ Function.Injective F := by
  refine ⟨LinearMap.id, ?_, ?_⟩
  · intro u
    exact (frobeniusSquare_coordinatewise_claim53470 n u).symm
  · intro u v h
    exact h

theorem frobeniusSquare_linear_injective_claim53470 (n : ℕ) :
    (∀ u v : Fin n → ZMod 2,
      (fun i => (u i + v i) ^ 2) =
        (fun i => u i ^ 2 + v i ^ 2)) ∧
    (∀ a : ZMod 2, ∀ u : Fin n → ZMod 2,
      (fun i => (a * u i) ^ 2) =
        (fun i => a * u i ^ 2)) ∧
    Function.Injective (fun u : Fin n → ZMod 2 =>
      (fun i => u i ^ 2)) := by
  have hcoord := frobeniusSquare_coordinatewise_claim53470 n
  constructor
  · intro u v
    simpa [hcoord]
  constructor
  · intro a u
    simpa [hcoord]
  · intro u v h
    simpa [hcoord] using h

end MathlibPlus.Algebra.Claim53470

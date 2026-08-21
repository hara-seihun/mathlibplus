-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is a root of the Unverified library rather than of MathlibPlus and no build here depends on it. See unverified.txt.
import Mathlib

open scoped BigOperators

namespace MathlibPlus.LinearAlgebra

/-- Claim 50371: exact ambient incidence countermodel.  The two column sums are
 the support-two top boundary and its lower image, while the three displayed
 vectors have a vanishing lower relation despite pairwise independence. -/
theorem claim50371_certificate :
    let partial_top : Matrix (Fin 3) (Fin 2) ℤ := !![
      1, 0;
      -1, 1;
      0, -1]
    let partial_low : Matrix (Fin 3) (Fin 2) ℤ := !![
      1, 0;
      0, 1;
      -1, -1]
    let sigma : Matrix (Fin 3) (Fin 3) ℤ := !![
      1, 0, 0;
      1, 1, 0;
      0, 1, 2]
    let topBoundary : Fin 3 → ℤ := ![1, 0, -1]
    let lowerBoundary : Fin 3 → ℤ := ![1, 1, -2]
    let xiA : Fin 2 → ℚ := ![1, 1]
    let xiB : Fin 2 → ℚ := ![1, -1]
    let xiC : Fin 2 → ℚ := ![1, 0]
    sigma * partial_top = partial_low ∧
      (∀ i, (∑ j : Fin 2, partial_top i j) = topBoundary i) ∧
      (∀ i, (∑ j : Fin 2, partial_low i j) = lowerBoundary i) ∧
      xiA + xiB - 2 • xiC = 0 ∧
      LinearIndependent ℚ (fun i : Fin 2 => ![xiA, xiB] i) ∧
      LinearIndependent ℚ (fun i : Fin 2 => ![xiA, xiC] i) ∧
      LinearIndependent ℚ (fun i : Fin 2 => ![xiB, xiC] i) := by
  dsimp
  constructor
  · native_decide
  constructor
  · intro i
    fin_cases i <;> native_decide
  constructor
  · intro i
    fin_cases i <;> native_decide
  constructor
  · native_decide
  repeat' constructor
  · rw [linearIndependent_fin2]
    constructor
    · norm_num
    · intro a h
      have h0 := congr_fun h 0
      have h1 := congr_fun h 1
      norm_num at h0 h1
      linarith
  · rw [linearIndependent_fin2]
    constructor
    · norm_num
    · intro a h
      have h0 := congr_fun h 0
      have h1 := congr_fun h 1
      norm_num at h0 h1
  · rw [linearIndependent_fin2]
    constructor
    · norm_num
    · intro a h
      have h0 := congr_fun h 0
      have h1 := congr_fun h 1
      norm_num at h0 h1

end MathlibPlus.LinearAlgebra

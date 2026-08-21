-- UNVERIFIED (does-not-elaborate): submitted but not kernel-verified, so it is not built and MathlibPlus.lean does not import it. See unverified.txt.
import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim57965

/-- The exact mixed-difference expansion and forward-span containment from the
p≥5 polynomial fibre calculation. -/
theorem mixedDifference_expansion_and_mem
    (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (d : Fin 3 → ZMod p) :
    let F : (Fin 3 → ZMod p) → (Fin 3 → ZMod p) := fun x =>
      ![x 0 ^ 2 + x 0 * x 1 * x 2, x 1 ^ 2, x 2 ^ 2]
    let A := d 0 ^ 2
    let B := d 0 * d 1 * d 2
    let C := d 1 ^ 2
    let D := d 2 ^ 2
    let K : Submodule (ZMod p) (Fin 3 → ZMod p) :=
      Submodule.span (ZMod p)
        (Set.range (fun a : Fin 3 → ZMod p =>
          F (a + d) - F a - F d) ∪
          Set.range (fun a : Fin 3 → ZMod p =>
            F (a - d) - F a - F (-d)))
    F d ∈ K ∧
      ∀ t : ZMod p,
        F (t • d + d) - F (t • d) - F d =
          t • ![2 * A + 3 * B, 2 * C, 2 * D] +
            t ^ 2 • ![3 * B, 0, 0] := by
  letI : Fact p.Prime := ⟨hp⟩
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have hd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hd
    omega
  have h3 : (3 : ZMod p) ≠ 0 := by
    intro h
    have hd : p ∣ 3 := (CharP.cast_eq_zero_iff (ZMod p) p 3).mp h
    have hle : p ≤ 3 := Nat.le_of_dvd (by norm_num) hd
    omega
  dsimp
  let F : (Fin 3 → ZMod p) → (Fin 3 → ZMod p) := fun x =>
    ![x 0 ^ 2 + x 0 * x 1 * x 2, x 1 ^ 2, x 2 ^ 2]
  let A : ZMod p := d 0 ^ 2
  let B : ZMod p := d 0 * d 1 * d 2
  let C : ZMod p := d 1 ^ 2
  let D : ZMod p := d 2 ^ 2
  let K : Submodule (ZMod p) (Fin 3 → ZMod p) :=
    Submodule.span (ZMod p)
      (Set.range (fun a : Fin 3 → ZMod p =>
        F (a + d) - F a - F d) ∪
        Set.range (fun a : Fin 3 → ZMod p =>
          F (a - d) - F a - F (-d)))
  have hformula (t : ZMod p) :
      F (t • d + d) - F (t • d) - F d =
        t • ![2 * A + 3 * B, 2 * C, 2 * D] +
          t ^ 2 • ![3 * B, 0, 0] := by
    funext k
    fin_cases k <;> simp [F, A, B, C, D]
    all_goals ring
  have hm (t : ZMod p) :
      F (t • d + d) - F (t • d) - F d ∈ K := by
    apply Submodule.subset_span
    exact Or.inl ⟨t • d, rfl⟩
  have hfd : F d =
      (2 : ZMod p)⁻¹ • (F (1 • d + d) - F (1 • d) - F d) -
        (3 : ZMod p)⁻¹ •
          ((F (2 • d + d) - F (2 • d) - F d) -
            (2 : ZMod p) • (F (1 • d + d) - F (1 • d) - F d)) := by
    rw [hformula 1, hformula 2]
    ext k
    fin_cases k <;> simp [F, A, B, C, D, smul_add, add_smul, sub_eq_add_neg]
    all_goals field_simp [h2, h3] <;> ring
  constructor
  · rw [hfd]
    apply K.sub_mem
    · exact K.smul_mem _ (hm 1)
    · apply K.smul_mem _
      apply K.sub_mem
      · exact hm 2
      · exact K.smul_mem _ (hm 1)
  · exact hformula

end MathlibPlus.LinearAlgebra.Claim57965

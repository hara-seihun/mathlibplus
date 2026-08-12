import Mathlib.Tactic

namespace MathlibPlus.LinearAlgebra.Claim57968

theorem homogeneous_cubic_mem_mixed_span
    (p : ℕ) [hp : Fact (Nat.Prime p)] (hp5 : 5 ≤ p)
    (A B : Type*) [AddCommGroup A] [AddCommGroup B]
    [Module (ZMod p) A] [Module (ZMod p) B]
    [FiniteDimensional (ZMod p) A] [FiniteDimensional (ZMod p) B]
    (F : B → A)
    (hF : ∀ (t : ZMod p) (b : B), F (t • b) = t ^ 3 • F b)
    (d : B) :
    F d ∈ Submodule.span (ZMod p)
      {x : A | ∃ b : B, F (b + d) - F b - F d = x} := by
  have hp : Nat.Prime p := Fact.out
  let Wd : Submodule (ZMod p) A :=
    Submodule.span (ZMod p)
      {x : A | ∃ b : B, F (b + d) - F b - F d = x}
  change F d ∈ Wd
  have hgen : F (d + d) - F d - F d ∈ Wd := by
    apply Submodule.subset_span
    exact ⟨d, rfl⟩
  have hhom : F (d + d) = (8 : ZMod p) • F d := by
    convert hF (2 : ZMod p) d using 1 <;> norm_num [two_smul, pow_succ, add_smul]
  have hscaled : (6 : ZMod p) • F d ∈ Wd := by
    rw [hhom] at hgen
    convert hgen using 1 <;> module
  have h6 : (6 : ZMod p) ≠ 0 := by
    change ¬ ((6 : ℕ) : ZMod p) = 0
    rw [ZMod.natCast_eq_zero_iff]
    intro hdiv
    have hple : p ≤ 6 := Nat.le_of_dvd (by decide) hdiv
    interval_cases p
    · norm_num at hdiv
    · norm_num at hp
  have hinv : (6 : ZMod p)⁻¹ • ((6 : ZMod p) • F d) = F d :=
    inv_smul_smul₀ h6 (F d)
  have hscaled' : (6 : ZMod p)⁻¹ • ((6 : ZMod p) • F d) ∈ Wd :=
    Wd.smul_mem _ hscaled
  simpa [hinv] using hscaled'

end MathlibPlus.LinearAlgebra.Claim57968

import Mathlib

namespace MathlibPlus.Algebra

/--
Claim 37354.  The true left-period set of a nonconstant function is a proper
subgroup.  The formulation is generic in the group and codomain; the retained
`E(C₇,3)`/`𝔽₇ˣ` instance is a specialization.
-/
theorem trueLeftPeriodSubgroup_isProper
    {H α : Type*} [Group H] (lam : H → α)
    (hlam : ∃ x y : H, lam x ≠ lam y) :
    let Q : Subgroup H :=
      { carrier := {h | ∀ k, lam (h * k) = lam k}
        one_mem' := by
          intro k
          simp
        mul_mem' := by
          intro a b ha hb k
          rw [mul_assoc, ha, hb]
        inv_mem' := by
          intro a ha k
          have h := ha (a⁻¹ * k)
          simpa [mul_assoc] using h.symm }
    Q ≠ ⊤ := by
  let Q : Subgroup H :=
    { carrier := {h | ∀ k, lam (h * k) = lam k}
      one_mem' := by
        intro k
        simp
      mul_mem' := by
        intro a b ha hb k
        rw [mul_assoc, ha, hb]
      inv_mem' := by
        intro a ha k
        have h := ha (a⁻¹ * k)
        simpa [mul_assoc] using h.symm }
  change Q ≠ ⊤
  intro hQ
  obtain ⟨x, y, hxy⟩ := hlam
  have hxQ : x ∈ Q := by
    rw [hQ]
    exact (Subgroup.mem_top x : x ∈ (⊤ : Subgroup H))
  have hyQ : y ∈ Q := by
    rw [hQ]
    exact (Subgroup.mem_top y : y ∈ (⊤ : Subgroup H))
  have hx : lam x = lam 1 := by simpa using hxQ (1 : H)
  have hy : lam y = lam 1 := by simpa using hyQ (1 : H)
  exact hxy (hx.trans hy.symm)

end MathlibPlus.Algebra

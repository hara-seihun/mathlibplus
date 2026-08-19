import Mathlib

namespace MathlibPlus.Algebra.Claim30791Cocycle

/-- A finite additive cocycle is a coboundary whenever multiplication by the
cardinality of the acting group is invertible on the coefficient group. -/
theorem finiteCocycle_isCoboundary_claim30791
    {G M : Type*} [Group G] [Fintype G] [AddCommGroup M]
    [DistribMulAction G M]
    (b : G → M)
    (hcocycle : ∀ g h : G, b (g * h) = b g + g • b h)
    (hinv : Function.Bijective (fun x : M => Fintype.card G • x)) :
    ∃ s : M, Fintype.card G • s = ∑ h : G, b h ∧
      ∀ g : G, b g = s - g • s := by
  let S : M := ∑ h : G, b h
  obtain ⟨s, hs⟩ := hinv.2 S
  change Fintype.card G • s = S at hs
  refine ⟨s, hs, ?_⟩
  intro g
  have hsum : ∑ h : G, b (g * h) = S := by
    simpa [S] using (Equiv.sum_comp (Equiv.mulLeft g) b)
  have hcalc : S = Fintype.card G • b g + g • S := by
    calc
      S = ∑ h : G, b (g * h) := hsum.symm
      _ = ∑ h : G, (b g + g • b h) := by
        apply Fintype.sum_congr
        intro h
        rw [hcocycle]
      _ = Fintype.card G • b g + g • S := by
        rw [Finset.sum_add_distrib]
        have hconst : (∑ _ : G, b g) = Fintype.card G • b g := by simp
        have hsmulsum : (∑ h : G, g • b h) = g • S := by
          change (∑ h : G, (DistribSMul.toAddMonoidHom M g) (b h)) = g • S
          rw [← map_sum]
          rfl
        rw [hconst, hsmulsum]
  have hsmul : g • (Fintype.card G • s) = Fintype.card G • (g • s) := by
    simpa [DistribSMul.toAddMonoidHom_apply] using
      map_nsmul (DistribSMul.toAddMonoidHom M g) (Fintype.card G) s
  have hcalc' : S - g • S = Fintype.card G • b g := by
    calc
      S - g • S = (Fintype.card G • b g + g • S) - g • S :=
        congrArg (fun x : M => x - g • S) hcalc
      _ = Fintype.card G • b g := by abel
  have hscaled : Fintype.card G • (s - g • s) = Fintype.card G • b g := by
    calc
      Fintype.card G • (s - g • s) =
          Fintype.card G • s - Fintype.card G • (g • s) :=
        nsmul_sub s (g • s) (Fintype.card G)
      _ = S - g • S := by
        rw [hs]
        congr 1
        calc
          Fintype.card G • (g • s) = g • (Fintype.card G • s) := hsmul.symm
          _ = g • S := congrArg (fun x : M => g • x) hs
      _ = Fintype.card G • b g := hcalc'
  exact (hinv.1 hscaled).symm

end MathlibPlus.Algebra.Claim30791Cocycle

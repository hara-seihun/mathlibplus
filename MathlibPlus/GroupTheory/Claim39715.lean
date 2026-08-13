import Mathlib

namespace MathlibPlus.GroupTheory

/--
Claim 39715: a finite `p`-group action on a finite invariant carrier whose
cardinality is divisible by `p` has a fixed point other than zero.  The
additive ambient action supplies the distinguished fixed point `0`.
-/
theorem exists_nonzero_fixedPoint_of_prime_dvd_card_claim39715
    {p : ℕ} {G V : Type*} [Fact (Nat.Prime p)] [Group G] [Finite G]
    [AddMonoid V] [DistribMulAction G V]
    (hG : IsPGroup p G)
    (F : Set V) [Finite F]
    (hF : ∀ (g : G) (v : V), v ∈ F → g • v ∈ F)
    (hzero : (0 : V) ∈ F)
    (hp : p ∣ Nat.card F) :
    ∃ v : V, v ∈ F ∧ (∀ g : G, g • v = v) ∧ v ≠ 0 := by
  let smulF : G → F → F := fun g v => ⟨g • (v : V), hF g (v : V) v.property⟩
  letI : MulAction G F :=
    { smul := smulF
      one_smul := by
        intro v
        apply Subtype.ext
        change (1 : G) • (v : V) = (v : V)
        exact one_smul G (v : V)
      mul_smul := by
        intro g h v
        apply Subtype.ext
        change (g * h) • (v : V) = g • h • (v : V)
        exact mul_smul g h (v : V) }
  have hzeroF : (⟨(0 : V), hzero⟩ : F) ∈ MulAction.fixedPoints G F := by
    change ∀ g : G, g • (⟨(0 : V), hzero⟩ : F) = ⟨0, hzero⟩
    intro g
    apply Subtype.ext
    change g • (0 : V) = 0
    exact smul_zero g
  obtain ⟨v, hv, hvne⟩ :=
    (IsPGroup.exists_fixed_point_of_prime_dvd_card_of_fixed_point
      (G := G) (p := p) hG F hp (a := (⟨(0 : V), hzero⟩ : F)) hzeroF)
  refine ⟨(v : V), v.property, ?_, ?_⟩
  · change ∀ g : G, smulF g v = v at hv
    intro g
    have h := congrArg Subtype.val (hv g)
    simpa [smulF] using h
  · intro hv0
    apply hvne
    apply Subtype.ext
    exact hv0.symm

end MathlibPlus.GroupTheory

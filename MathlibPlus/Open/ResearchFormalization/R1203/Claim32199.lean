import MathlibPlus.Open.ResearchFormalization.R1203.Claim41970

namespace MathlibPlus.Open.ResearchFormalization.R1203

open MathlibPlus.ResearchFormalization.R1203Claim41970

/-- Claim 32199: cocycles on projected subgroups extend after a coboundary. -/
def claim32199 : Prop :=
  ∀ (p : ℕ) [Fact (Nat.Prime p)], Nat.ModEq 3 p 1 →
    ∀ (A : Type*) [CommGroup A] [Fintype A]
      (rho : c3 →* MulAut A) (omega : ZMod p)
      (V : Sylow p A),
      MathlibPlus.Open.Research.elementaryAbelianSylow p V →
      matchingScalarAction (rho := rho) p omega V →
      ∀ (L : Subgroup (eGroup A rho)),
        Function.Surjective (restrictedProjection L) →
        ∀ (z : L → ZMod p),
          subgroupCocycle (omega := omega) L z →
          ∃ (g : eGroup A rho → ZMod p) (s : ZMod p)
            (e : (L ⧸ kernelInL L) ≃* c3)
            (q : (L ⧸ kernelInL L) → ZMod p) (t : L) (a : A)
            (epsilon : ZMod 3),
            matchingScalarCocycle (omega := omega) g ∧
            (∀ u : kernelInL L, g (u : eGroup A rho) = z u) ∧
            (∀ x : L,
              e (QuotientGroup.mk' (kernelInL L) x) = restrictedProjection L x) ∧
            (∀ x : L,
              z x - g x = q (QuotientGroup.mk' (kernelInL L) x)) ∧
            t.1 = SemidirectProduct.mk a (Multiplicative.ofAdd epsilon) ∧
            (epsilon = 1 ∨ epsilon = 2) ∧
            IsUnit (1 - omega ^ epsilon.val) ∧
            matchingCharacter (A := A) (rho := rho) p omega
                (t : eGroup A rho) = omega ^ epsilon.val ∧
            coboundary (A := A) (rho := rho) omega s
                (t : eGroup A rho) = z t - g t ∧
            matchingScalarCocycle (omega := omega)
              (fun h : eGroup A rho =>
                g h + coboundary (A := A) (rho := rho) omega s h) ∧
            (∀ x : L,
              g x + coboundary (A := A) (rho := rho) omega s
                (x : eGroup A rho) = z x)

end MathlibPlus.Open.ResearchFormalization.R1203

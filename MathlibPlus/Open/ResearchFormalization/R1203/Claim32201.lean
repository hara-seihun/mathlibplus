import Mathlib
import MathlibPlus.Open.ResearchFormalization.R1203.Claim41970
import MathlibPlus.Open.ResearchFormalization.R1203.Claim41973

namespace MathlibPlus.ResearchFormalization.R1203Claim32201

abbrev c3 := MathlibPlus.ResearchFormalization.R1203.c3

abbrev eGroup (A : Type*) [CommGroup A]
    (rho : c3 →* MulAut A) :=
  MathlibPlus.ResearchFormalization.R1203.eGroup A rho

abbrev ScalarGlobalCocycles {p : ℕ} {A : Type*} [CommGroup A]
    {rho : c3 →* MulAut A} {omega : ZMod p} :=
  {f : eGroup A rho → ZMod p //
    MathlibPlus.ResearchFormalization.R1203Claim41970.matchingScalarCocycle
      (omega := omega) f}

abbrev ScalarSubgroupCocycles {p : ℕ} {A : Type*} [CommGroup A]
    {rho : c3 →* MulAut A} {omega : ZMod p}
    (L : Subgroup (eGroup A rho)) :=
  {f : L → ZMod p //
    MathlibPlus.ResearchFormalization.R1203Claim41970.subgroupCocycle
      (omega := omega) L f}

abbrev VectorGlobalCocycles {p : ℕ} {A : Type*} [CommGroup A]
    {rho : c3 →* MulAut A} {W : Type*} [AddCommGroup W]
    [DistribMulAction (eGroup A rho) W] :=
  {f : eGroup A rho → W //
    MathlibPlus.ResearchFormalization.R1203.vectorCocycle
      (p := p) f}

abbrev VectorSubgroupCocycles {p : ℕ} {A : Type*} [CommGroup A]
    {rho : c3 →* MulAut A} {W : Type*} [AddCommGroup W]
    [DistribMulAction (eGroup A rho) W]
    (L : Subgroup (eGroup A rho)) :=
  {f : L → W //
    MathlibPlus.ResearchFormalization.R1203.subgroupCocycle
      (p := p) L f}

def scalarRestrictionAlignment {p : ℕ} {A : Type*} [CommGroup A]
    {rho : c3 →* MulAut A} {omega : ZMod p}
    (L : Subgroup (eGroup A rho))
    (r : ScalarGlobalCocycles (p := p) (A := A) (rho := rho) (omega := omega) →
      ScalarSubgroupCocycles (p := p) (A := A) (rho := rho) (omega := omega) L) : Prop :=
  ∀ f x, (r f).1 x = f.1 x

def vectorRestrictionAlignment {p : ℕ} {A : Type*} [CommGroup A]
    {rho : c3 →* MulAut A} {W : Type*} [AddCommGroup W]
    [DistribMulAction (eGroup A rho) W]
    (L : Subgroup (eGroup A rho))
    (r : VectorGlobalCocycles (p := p) (A := A) (rho := rho) (W := W) →
      VectorSubgroupCocycles (p := p) (A := A) (rho := rho) (W := W) L) : Prop :=
  ∀ f x, (r f).1 x = f.1 x

def directSumScalarRestriction {p d : ℕ} {A : Type*} [CommGroup A]
    {rho : c3 →* MulAut A} {omega : ZMod p}
    (L : Subgroup (eGroup A rho))
    (r : ScalarGlobalCocycles (A := A) (rho := rho) (omega := omega) →
      ScalarSubgroupCocycles (A := A) (rho := rho) (omega := omega) L) :
    (Fin d → ScalarGlobalCocycles (A := A) (rho := rho) (omega := omega)) →
      (Fin d → ScalarSubgroupCocycles (A := A) (rho := rho) (omega := omega) L) :=
  fun q i => r (q i)

def coordinateCocycleSplitting {p d : ℕ} [Fact (Nat.Prime p)]
    (A : Type*) [CommGroup A] [Fintype A]
    (rho : c3 →* MulAut A) (omega : ZMod p)
    (W : Type*) [AddCommGroup W] [Module (ZMod p) W]
    [FiniteDimensional (ZMod p) W]
    [DistribMulAction (eGroup A rho) W]
    (L : Subgroup (eGroup A rho)) : Prop :=
  ∀ b : Module.Basis (Fin d) (ZMod p) W,
    ∃ (eH : VectorGlobalCocycles (p := p) (A := A) (rho := rho) (W := W) ≃
          (Fin d → ScalarGlobalCocycles (p := p) (A := A) (rho := rho)
            (omega := omega)))
      (eL : VectorSubgroupCocycles (p := p) (A := A) (rho := rho) (W := W) L ≃
          (Fin d → ScalarSubgroupCocycles (p := p) (A := A) (rho := rho)
            (omega := omega) L))
      (rW : VectorGlobalCocycles (p := p) (A := A) (rho := rho) (W := W) →
        VectorSubgroupCocycles (p := p) (A := A) (rho := rho) (W := W) L)
      (rM : ScalarGlobalCocycles (p := p) (A := A) (rho := rho) (omega := omega) →
        ScalarSubgroupCocycles (p := p) (A := A) (rho := rho) (omega := omega) L),
      (∀ f i h, (eH f i).1 h = b.repr (f.1 h) i) ∧
      (∀ z i x, (eL z i).1 x = b.repr (z.1 x) i) ∧
      scalarRestrictionAlignment (p := p) (A := A) (rho := rho)
        (omega := omega) L rM ∧
      vectorRestrictionAlignment (p := p) (A := A) (rho := rho)
        (W := W) L rW ∧
      (∀ f,
        eL (rW f) = directSumScalarRestriction (p := p) (d := d)
          (A := A) (rho := rho) (omega := omega) L rM (eH f))

end MathlibPlus.ResearchFormalization.R1203Claim32201

namespace MathlibPlus.Open.ResearchFormalization.R1203

open MathlibPlus.ResearchFormalization.R1203Claim32201

 def claim32201 : Prop :=
  ∀ (p : ℕ) [Fact (Nat.Prime p)], Nat.ModEq 3 p 1 →
    ∀ (A : Type*) [CommGroup A] [Fintype A]
      (rho : c3 →* MulAut A) (omega : ZMod p)
      (V : Sylow p A),
      MathlibPlus.ResearchFormalization.R1203.matchingScalarAction
        (rho := rho) p omega V →
      ∀ (d : ℕ) (W : Type*) [AddCommGroup W]
        [Module (ZMod p) W] [FiniteDimensional (ZMod p) W]
        [DistribMulAction (eGroup A rho) W],
        1 ≤ d → Module.finrank (ZMod p) W = d →
        MathlibPlus.ResearchFormalization.R1203.matchingModule
          (p := p) (omega := omega) (A := A) (rho := rho) W →
        ∀ (L : Subgroup (eGroup A rho)),
          coordinateCocycleSplitting (p := p) (d := d) A rho omega W L

end MathlibPlus.Open.ResearchFormalization.R1203

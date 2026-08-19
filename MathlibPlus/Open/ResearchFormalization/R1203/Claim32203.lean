import Mathlib
import MathlibPlus.Open.ResearchFormalization.R1203.Claim41970
import MathlibPlus.Open.ResearchFormalization.R1203.Claim41973

namespace MathlibPlus.ResearchFormalization.R1203Claim32203

abbrev c3 := MathlibPlus.ResearchFormalization.R1203.c3
abbrev a49 := Multiplicative (ZMod 49)
abbrev w7 := Fin 3 → ZMod 7

abbrev e49 (rho : c3 →* MulAut a49) :=
  MathlibPlus.ResearchFormalization.R1203.eGroup a49 rho

abbrev sevenA : Subgroup a49 :=
  Subgroup.closure ({Multiplicative.ofAdd (7 : ZMod 49)} : Set a49)

abbrev sevenInE (rho : c3 →* MulAut a49) : Subgroup (e49 rho) :=
  Subgroup.map (SemidirectProduct.inl : a49 →* e49 rho) sevenA

def exactC49GeneratorAction (rho : c3 →* MulAut a49) : Prop :=
  ∀ x : a49,
    rho MathlibPlus.ResearchFormalization.R1203.cGenerator x =
      Multiplicative.ofAdd
        ((30 : ZMod 49) * Multiplicative.toAdd x)

def exactC49FixedPointFree (rho : c3 →* MulAut a49) : Prop :=
  ∀ x : a49,
    rho MathlibPlus.ResearchFormalization.R1203.cGenerator x = x → x = 1

def targetMatchingAction {rho : c3 →* MulAut a49}
    [Fact (Nat.Prime 7)]
    (act : DistribMulAction (e49 rho) w7) : Prop :=
  letI := act
  (30 : ZMod 7) = 2 ∧
    MathlibPlus.ResearchFormalization.R1203.matchingModule
      (p := 7) (omega := (2 : ZMod 7)) (A := a49) (rho := rho) w7 ∧
    ∀ h : e49 rho, ∀ w : w7,
      h • w =
        MathlibPlus.ResearchFormalization.R1203.matchingCharacter
          7 (2 : ZMod 7) h • w

def targetSubgroupCocycle {rho : c3 →* MulAut a49}
    (act : DistribMulAction (e49 rho) w7)
    (z : sevenInE rho →* Multiplicative w7) : Prop :=
  letI := act
  MathlibPlus.ResearchFormalization.R1203.subgroupCocycle
    (p := 7) (sevenInE rho)
    (fun x : sevenInE rho => Multiplicative.toAdd (z x))

def scalarSubgroupCocycle {rho : c3 →* MulAut a49}
    (s : sevenInE rho →* Multiplicative (ZMod 7)) : Prop :=
  MathlibPlus.ResearchFormalization.R1203Claim41970.subgroupCocycle
    (omega := (2 : ZMod 7)) (sevenInE rho)
    (fun x : sevenInE rho => Multiplicative.toAdd (s x))

def claim32203 : Prop :=
  ∀ [Fact (Nat.Prime 7)],
  ∀ (rho : c3 →* MulAut a49),
    exactC49GeneratorAction rho →
    exactC49FixedPointFree rho →
    ∀ (act : DistribMulAction (e49 rho) w7),
      targetMatchingAction act →
      Module.finrank (ZMod 7) w7 = 3 →
      ∃ (z : sevenInE rho →* Multiplicative w7) (g : sevenInE rho),
        g.1 = SemidirectProduct.inl
            (Multiplicative.ofAdd (7 : ZMod 49)) ∧
        z g = Multiplicative.ofAdd ![1, 0, 0] ∧
        targetSubgroupCocycle act z ∧
        (¬ ∃ F : a49 →* Multiplicative w7,
          ∀ x : sevenInE rho, F x.1.left = z x) ∧
        (∀ F : a49 →* Multiplicative w7,
          F (Multiplicative.ofAdd (7 : ZMod 49)) =
            Multiplicative.ofAdd 0) ∧
        ∃ s : sevenInE rho →* Multiplicative (ZMod 7),
          s g = Multiplicative.ofAdd 1 ∧
          scalarSubgroupCocycle s ∧
          (∀ k : ZMod 7, ∃ x : sevenInE rho,
            x.1 = SemidirectProduct.inl
                (Multiplicative.ofAdd
                  ((7 : ZMod 49) * (k.val : ZMod 49))) ∧
            s x = Multiplicative.ofAdd k) ∧
          (¬ ∃ F : a49 →* Multiplicative (ZMod 7),
            ∀ x : sevenInE rho, F x.1.left = s x) ∧
          (∀ F : a49 →* Multiplicative (ZMod 7),
            F (Multiplicative.ofAdd (7 : ZMod 49)) =
              Multiplicative.ofAdd 0)

end MathlibPlus.ResearchFormalization.R1203Claim32203

namespace MathlibPlus.Open.ResearchFormalization.R1203

open MathlibPlus.ResearchFormalization.R1203Claim32203

def claim32203 : Prop :=
  MathlibPlus.ResearchFormalization.R1203Claim32203.claim32203

end MathlibPlus.Open.ResearchFormalization.R1203

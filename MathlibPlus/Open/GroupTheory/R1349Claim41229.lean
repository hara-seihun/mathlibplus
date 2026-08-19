import MathlibPlus.Open.GroupTheory.R1349Claim41243

namespace MathlibPlus.Open.GroupTheory.R1349Claim41229

open MathlibPlus.Open.GroupTheory.R1349Claim41243

noncomputable section

def blockAction
    (K : Subgroup (Equiv.Perm G))
    (B : Finset (Set G))
    (U : MathlibPlus.Open.blockType B)
    (k : K) (σ : Equiv.Perm U.1) : Prop :=
  ∀ x : U.1, (σ x : G) = (k : Equiv.Perm G) (x : G)

def blockProjection
    (K : Subgroup (Equiv.Perm G))
    (B : Finset (Set G))
    (U : MathlibPlus.Open.blockType B) : Set (Equiv.Perm U.1) :=
  {σ | ∃ k : K, blockAction K B U k σ}

def sevenCycle {U : Type*}
    (σ : Equiv.Perm U) : Prop :=
  orderOf σ = 7

def transportedSevenCycle
    (K : Subgroup (Equiv.Perm G))
    (B : Finset (Set G))
    (R : Subgroup (Equiv.Perm G))
    (k : K) (U : MathlibPlus.Open.blockType B) : Prop :=
  ∀ V : MathlibPlus.Open.blockType B,
    ∃ r : R,
      (r : Equiv.Perm G) '' U.1 = V.1 ∧
        ∃ kV : K,
          (kV : Equiv.Perm G) =
              (r : Equiv.Perm G) * (k : Equiv.Perm G) * (r : Equiv.Perm G)⁻¹ ∧
            ∃ σV : Equiv.Perm V.1,
              blockAction K B V kV σV ∧ sevenCycle σV

def claim41229 : Prop :=
  ∀ (S : Set G) (B : Finset (Set G))
    (R T : Subgroup (Equiv.Perm G)),
    pureQ12SevenBlockPair S B R T →
      let Y := pairGeneratedGroup R T
      let K := blockKernel Y B
      7 ∣ Nat.card K →
        ∃ k : K,
          orderOf (k : Equiv.Perm G) = 7 ∧
            ∃ U : MathlibPlus.Open.blockType B,
              (∃ σ : Equiv.Perm U.1,
                blockAction K B U k σ ∧ sevenCycle σ) ∧
                transportedSevenCycle K B R k U ∧
                ∀ V : MathlibPlus.Open.blockType B,
                  ∃ σ : Equiv.Perm V.1,
                    σ ∈ blockProjection K B V ∧ sevenCycle σ

end
end MathlibPlus.Open.GroupTheory.R1349Claim41229

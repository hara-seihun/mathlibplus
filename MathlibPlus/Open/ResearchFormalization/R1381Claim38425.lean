import MathlibPlus.Open.ResearchFormalization.R1381PrimitiveAffineCounterexample

namespace MathlibPlus.Open.ResearchFormalization.R1381Claim38425

open MathlibPlus.Open.RepresentationTheory.R1381
open MathlibPlus.Open.Research.R1661
open MathlibPlus.Open.ResearchFormalization
open MathlibPlus.Open.ResearchFormalization.R1381PrimitiveAffineCounterexample

noncomputable section

abbrev Q8 := QuaternionGroup 2
abbrev Plane (p : ℕ) := Fin 2 → ZMod p
abbrev GL2 (p : ℕ) := Matrix.GeneralLinearGroup (Fin 2) (ZMod p)
abbrev ProductGroup (p : ℕ) := Multiplicative (Plane p) × Q8

def minimumCommonFibers_claim38425 : Prop :=
  ∀ (p : ℕ) (hp : Nat.Prime p), Odd p →
    letI : NeZero p := ⟨hp.ne_zero⟩
    ∃ a b : ZMod p, ∃ ρ : Q8 →* GL2 p,
      q8RepresentationData p a b ρ ∧
        let R := standardRegularCopy p
        ∃ f : Equiv.Perm (ProductGroup p),
          chartPermutation ρ f ∧
            let T := twistedRegularCopy f R
            let X := R ⊔ T
            let 𝓑 := q8FiberSystem p
            let N := translationLayer p
            isRegular R ∧
              isRegular T ∧
                commonBlockSystem R T 𝓑 ∧
                  minimumCommonBlockSize p R T ∧
                    (∀ h : Q8,
                      commonBlock R T (q8Fiber p h) ∧
                        Set.ncard (q8Fiber p h) = p ^ 2) ∧
                      (∀ h : Q8, primitiveAffineLocalKernel ρ X 𝓑 h) ∧
                        ¬ commonPrimeLineRefinement p f ∧
                          normalIn N X ∧
                            isElementaryAbelian p N ∧
                              subdirectTranslationLayer N ∧
                                translationLayerInsideBlockKernel N X 𝓑

end

end MathlibPlus.Open.ResearchFormalization.R1381Claim38425

import MathlibPlus.Open.ResearchBatch.ColoredAffine

namespace MathlibPlus.Open.ResearchFormalization.R2733

open MathlibPlus.Open.ResearchBatch.ColoredAffine

/-- Claim 42455: a five-colour component labeling is a genuine CI defect only
when no invertible linear map on the nonzero difference atoms carries every
source colour to its target colour. -/
def genuineFiveColorLinearShadow_claim42455
    (f : Equiv.Perm V7) (c d : V7 → Color) : Prop :=
  f 0 = 0 ∧
    InverseClosed c ∧
    InverseClosed d ∧
    ComponentLabeling f c d ∧
    ¬ ∃ M : Matrix.GeneralLinearGroup (Fin 2) (ZMod 7),
      ∀ v : V7, v ≠ 0 →
        c v = d
          (let w :=
            (M : Matrix (Fin 2) (Fin 2) (ZMod 7)).mulVec ![v.1, v.2]
           (w 0, w 1))

end MathlibPlus.Open.ResearchFormalization.R2733

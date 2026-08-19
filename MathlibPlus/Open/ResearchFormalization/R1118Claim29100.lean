import MathlibPlus.Open.ResearchFormalizationBatch_01a000eb

namespace MathlibPlus.Open.ResearchFormalization.R1118

noncomputable section

open MathlibPlus.Open.ResearchFormalizationBatch_01a000eb

/-- A central translation in the `z` coordinate, acting on every fibre. -/
def centralZTranslation (a : F3) : Equiv.Perm (F3 × F3Cube) :=
  Equiv.addRight (a, 0)

/-- The corrected coefficient translation at `s=0`, whose central increment
on the fibre over `x` is `(F(x)-F(0))·w`. -/
def correctedCoefficientTranslation
    (Fmap : F3Square → F3Cube) (x s : F3Square) (w : F3Cube) :
    Equiv.Perm (F3 × F3Cube) :=
  Equiv.addRight (dot3 (Fmap (x + s) - Fmap s) w, 0)

/-- Claim 29100: on every nonzero coefficient fibre, the corrected coefficient
translations generate every central `z` translation. -/
def claim29100 : Prop :=
  ∀ (f : F3Square → F3) (Fmap : F3Square → F3Cube),
    f 0 = 0 →
      Fmap 0 = 0 →
        ∀ x : F3Square, Fmap x ≠ 0 →
          ∀ a : F3,
            centralZTranslation a ∈
              Subgroup.closure
                (Set.range
                  (fun w : F3Cube =>
                    correctedCoefficientTranslation Fmap x 0 w))

end
end MathlibPlus.Open.ResearchFormalization.R1118

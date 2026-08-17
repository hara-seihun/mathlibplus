import MathlibPlus.Open.ResearchFormalizationBatch01_01a0014f
import MathlibPlus.Algebra.CrossFamilyTranslation

namespace MathlibPlus.Open.Research.R1388FullRow38501

open MathlibPlus.Open.ResearchFormalizationBatch01_01a0014f

/-- Translation amounts in the local cross-derivative family. -/
def crossTranslationSubgroup {B : Type*} [AddCommGroup B]
    (q : Equiv.Perm B) (s : B) : AddSubgroup B :=
  AddSubgroup.closure {d | ∃ t : B, d = t + s - q t}

/-- Claim 38501: the full displacement subgroup is contained in the subgroup
of local translation amounts, and full displacement makes the cross action
transitive. -/
def claim38501 : Prop :=
  ∀ {B : Type*} [AddCommGroup B]
    (q : Equiv.Perm B) (s : B),
    displacement_subgroup q ≤ crossTranslationSubgroup q s ∧
      (full_displacement q →
        ∀ x y : B,
          y - x ∈ crossTranslationSubgroup q s)

end MathlibPlus.Open.Research.R1388FullRow38501

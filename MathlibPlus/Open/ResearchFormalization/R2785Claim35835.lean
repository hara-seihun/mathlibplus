import MathlibPlus.Open.Research.QuaternionDihedralBatch01

namespace MathlibPlus.Open.ResearchFormalization.R2785Claim35835

noncomputable section

abbrev DihedralSection (n : ℕ) := DihedralGroup n × ZMod 2

noncomputable def quotientNormalizedSectionRelabeling35835
    (n : ℕ) (f : DihedralSection n ≃ DihedralSection n) : Prop :=
  f (1, 0) = (1, 0) ∧
    ∀ h : DihedralGroup n, ∀ e : ZMod 2,
      (f (h, e)).1 = h

/-- Once the actual quotient conjugator has been applied, a normalized point
relabeling in the section coordinates is a Boolean switch on each dihedral
fiber, with the root fiber unswitched. -/
def sectionSwitchNormalForm_claim35835 : Prop :=
  ∀ n : ℕ, n % 2 = 1 →
    ∀ f : DihedralSection n ≃ DihedralSection n,
      quotientNormalizedSectionRelabeling35835 n f →
        ∃ b : DihedralGroup n → ZMod 2,
          b 1 = 0 ∧
            ∀ h : DihedralGroup n, ∀ e : ZMod 2,
              f (h, e) = (h, e + b h)

end

end MathlibPlus.Open.ResearchFormalization.R2785Claim35835

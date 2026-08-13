import MathlibPlus.Basic

namespace MathlibPlus.Analysis.Claim11522

/-- Claim 11522: a positive even two-periodic multiplicative gauge leaves the
 two-step ratio unchanged. -/
theorem twoStepRatio_gaugeInvariant_claim11522
    (P w wP : ℝ → ℝ)
    (_hPpos : ∀ x, 0 < P x)
    (_hPeven : ∀ x, P (-x) = P x)
    (hPperiod : ∀ x, P (x + 2) = P x)
    (hwP : ∀ x, wP x = w x * P x) :
    ∀ x, (wP (x + 2) / wP x) = (w (x + 2) / w x) := by
  intro x
  simp only [hwP (x + 2), hwP x, hPperiod x]
  exact mul_div_mul_right _ _ (ne_of_gt (_hPpos x))

/-- The Ward-identity clause of Claim 11522 is formalized at its stated
level of abstraction: any predicate extensional in the two-step ratio is
unchanged by the gauge. -/
theorem ward_identity_invariant_claim11522
    (P w wP : ℝ → ℝ)
    (hPpos : ∀ x, 0 < P x)
    (hPeven : ∀ x, P (-x) = P x)
    (hPperiod : ∀ x, P (x + 2) = P x)
    (hwP : ∀ x, wP x = w x * P x)
    (Ward : (ℝ → ℝ) → Prop)
    (hWard : ∀ u v, (∀ x, u x = v x) → (Ward u ↔ Ward v)) :
    Ward (fun x => wP (x + 2) / wP x) ↔
      Ward (fun x => w (x + 2) / w x) := by
  apply hWard
  exact twoStepRatio_gaugeInvariant_claim11522 P w wP hPpos hPeven hPperiod hwP

end MathlibPlus.Analysis.Claim11522

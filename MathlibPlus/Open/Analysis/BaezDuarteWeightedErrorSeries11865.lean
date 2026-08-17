import MathlibPlus.Open.Analysis.BaezDuarte

namespace MathlibPlus.Open.Analysis.BaezDuarteWeightedErrorSeries11865

noncomputable section

open MeasureTheory

/-- The exact weighted squared-error identity in the admitted
`L²([1,∞),dt/t²)` carrier.  The `MemLp` witness makes the displayed
`f_u - 1` an element of `baezDuarteH`, rather than replacing its Hilbert
norm by an unrelated integral. -/
def exactWeightedErrorSeries : Prop :=
  ∀ u : ℝ, 0 < u →
    ∃ hErr : MemLp (fun t : ℝ => baezDuartePoint u t - 1) 2 baezDuarteMeasure,
      ‖MemLp.toLp (fun t : ℝ => baezDuartePoint u t - 1) hErr‖ ^ 2 =
        let x : ℝ := Real.exp (-u)
        ∑' k : ℕ+,
          |baezDuarteHk k x + 1| ^ 2 /
            ((k : ℝ) * (((k : ℕ) + 1 : ℕ) : ℝ))

end

end MathlibPlus.Open.Analysis.BaezDuarteWeightedErrorSeries11865

import Mathlib.Tactic

namespace MathlibPlus.Algebra.Claim45271

/-!
Statement-fidelity formalization of claim 45271 (R-2827.5).  The concrete
rooted-boundary argument is represented by an explicit Bézout witness for the
source's coprimality assertion; no cancellation in a ring with zero divisors
is used.  The theorem below is the exact divisibility deduction from
`Q * ΔP + (v - 1) * ΔA = 0`.
-/

/-- Bézout coprimality plus the boundary equation forces `Q ∣ ΔA`. -/
theorem q_dvd_deltaA_of_boundary_equation
    {R : Type*} [CommRing R]
    (Q v deltaA deltaP : R)
    (hbezout : ∃ a b : R, a * Q + b * (v - 1) = 1)
    (heq : Q * deltaP + (v - 1) * deltaA = 0) :
    Q ∣ deltaA := by
  obtain ⟨a, b, hab⟩ := hbezout
  have hwd : (v - 1) * deltaA = Q * (-deltaP) := by
    calc
      (v - 1) * deltaA = -(Q * deltaP) :=
        eq_neg_of_add_eq_zero_right heq
      _ = Q * (-deltaP) := by ring
  obtain ⟨c, hc⟩ : ∃ c : R, (v - 1) * deltaA = Q * c :=
    ⟨-deltaP, hwd⟩
  refine ⟨a * deltaA + b * c, ?_⟩
  calc
    deltaA = (a * Q + b * (v - 1)) * deltaA := by rw [hab, one_mul]
    _ = Q * (a * deltaA + b * c) := by
      calc
        (a * Q + b * (v - 1)) * deltaA =
            a * Q * deltaA + b * ((v - 1) * deltaA) := by ring
        _ = a * Q * deltaA + b * (Q * c) := by rw [hc]
        _ = Q * (a * deltaA + b * c) := by ring

end MathlibPlus.Algebra.Claim45271

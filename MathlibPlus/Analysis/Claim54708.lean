import Mathlib

namespace MathlibPlus.Analysis.Claim54708

/-!
# Reflected-translation identity

Formalization of admitted claim 54708 (packet R-5203, section S1).  The
identity is stated for a positive abstract `q`; the packet's displayed
specialization `q = π x²` is supplied as a second theorem with `x ≠ 0`.
The unspecified positive row factors mentioned by the packet are not silently
modeled: only the displayed identity is formalized.
-/

/-- The reflected-translation identity for every positive `q`. -/
theorem reflectedTranslationIdentity (q u : ℝ) (hq : 0 < q) :
    let a : ℝ := 5 / 4
    let l : ℝ := Real.exp (2 * u)
    let H : ℝ → ℝ → ℝ := fun q l =>
      l ^ (-a) * Real.exp (-q / l) + l ^ a * Real.exp (-q * l)
    let y : ℝ := Real.log q
    let g : ℝ → ℝ := fun z => Real.exp (a * z - Real.exp z)
    q ^ a * H q l = g (y - 2 * u) + g (y + 2 * u) := by
  dsimp
  have hqexp : Real.exp (Real.log q) = q := Real.exp_log hq
  have hqdiv : q / Real.exp (2 * u) = Real.exp (Real.log q - 2 * u) := by
    simpa only [Real.exp_log hq] using
      (Real.exp_sub (Real.log q) (2 * u)).symm
  have hql : q * Real.exp (2 * u) = Real.exp (Real.log q + 2 * u) := by
    simpa only [Real.exp_log hq] using
      (Real.exp_add (Real.log q) (2 * u)).symm
  have hnegdiv : -q / Real.exp (2 * u) = -Real.exp (Real.log q - 2 * u) := by
    calc
      -q / Real.exp (2 * u) = -(q / Real.exp (2 * u)) := by ring
      _ = -Real.exp (Real.log q - 2 * u) := by rw [hqdiv]
  have hnegmul : -q * Real.exp (2 * u) = -Real.exp (Real.log q + 2 * u) := by
    calc
      -q * Real.exp (2 * u) = -(q * Real.exp (2 * u)) := by ring
      _ = -Real.exp (Real.log q + 2 * u) := by rw [hql]
  have hqpow : q ^ (5 / 4 : ℝ) =
      Real.exp (Real.log q * (5 / 4 : ℝ)) := by
    exact Real.rpow_def_of_pos hq _
  have hlneg : (Real.exp (2 * u)) ^ (-(5 / 4 : ℝ)) =
      Real.exp ((2 * u) * (-(5 / 4 : ℝ))) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _) , Real.log_exp]
  have hlpos : (Real.exp (2 * u)) ^ (5 / 4 : ℝ) =
      Real.exp ((2 * u) * (5 / 4 : ℝ)) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  have hminus :
      Real.exp (Real.log q * (5 / 4 : ℝ)) *
          (Real.exp ((2 * u) * (-(5 / 4 : ℝ))) *
            Real.exp (-Real.exp (Real.log q - 2 * u))) =
        Real.exp ((5 / 4 : ℝ) * (Real.log q - 2 * u) -
          Real.exp (Real.log q - 2 * u)) := by
    rw [← Real.exp_add]
    rw [← Real.exp_add]
    congr 1
    ring
  have hplus :
      Real.exp (Real.log q * (5 / 4 : ℝ)) *
          (Real.exp ((2 * u) * (5 / 4 : ℝ)) *
            Real.exp (-Real.exp (Real.log q + 2 * u))) =
        Real.exp ((5 / 4 : ℝ) * (Real.log q + 2 * u) -
          Real.exp (Real.log q + 2 * u)) := by
    rw [← Real.exp_add]
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hqpow, hlneg, hlpos, hnegdiv, hnegmul]
  rw [mul_add]
  rw [hminus, hplus]

/-- The packet's specialization `q = π x²`, with the necessary positivity
condition made explicit. -/
theorem reflectedTranslationIdentityPi (x u : ℝ) (hx : x ≠ 0) :
    let q : ℝ := Real.pi * x ^ 2
    let a : ℝ := 5 / 4
    let l : ℝ := Real.exp (2 * u)
    let H : ℝ → ℝ → ℝ := fun q l =>
      l ^ (-a) * Real.exp (-q / l) + l ^ a * Real.exp (-q * l)
    let y : ℝ := Real.log q
    let g : ℝ → ℝ := fun z => Real.exp (a * z - Real.exp z)
    q ^ a * H q l = g (y - 2 * u) + g (y + 2 * u) := by
  have hq : 0 < Real.pi * x ^ 2 :=
    mul_pos Real.pi_pos (sq_pos_of_ne_zero hx)
  simpa using reflectedTranslationIdentity (Real.pi * x ^ 2) u hq

end MathlibPlus.Analysis.Claim54708

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Pow

namespace MathlibPlus.NumberTheory.CyclicLogLattice

/-- Claim 12795: two positive-integer multiples of one positive logarithmic
lattice element cannot be logarithms of distinct rational primes. -/
theorem prime_eq_of_common_log_lattice_claim12795
    {p r : ℕ} (hp : p.Prime) (hr : r.Prime)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    {L : ℝ} (_hL : 0 < L)
    (hlogp : Real.log (p : ℝ) = (m : ℝ) * L)
    (hlogr : Real.log (r : ℝ) = (n : ℝ) * L) :
    p ^ n = r ^ m ∧ p = r := by
  have hlogs : (n : ℝ) * Real.log (p : ℝ) =
      (m : ℝ) * Real.log (r : ℝ) := by
    rw [hlogp, hlogr]
    ring
  have hpowlog : Real.log ((p : ℝ) ^ n) = Real.log ((r : ℝ) ^ m) := by
    rw [Real.log_pow, Real.log_pow]
    exact hlogs
  have hppos : 0 < (p : ℝ) := Nat.cast_pos.mpr hp.pos
  have hrpos : 0 < (r : ℝ) := Nat.cast_pos.mpr hr.pos
  have hpow : (p : ℝ) ^ n = (r : ℝ) ^ m :=
    Real.log_injOn_pos
      (show 0 < (p : ℝ) ^ n from pow_pos hppos n)
      (show 0 < (r : ℝ) ^ m from pow_pos hrpos m)
      hpowlog
  have hpow_cast : ((p ^ n : ℕ) : ℝ) = ((r ^ m : ℕ) : ℝ) := by
    simpa only [Nat.cast_pow] using hpow
  have hpow_nat : p ^ n = r ^ m := Nat.cast_inj.mp hpow_cast
  have hp_dvd_pow : p ∣ p ^ n := dvd_pow_self p (Nat.ne_of_gt hn)
  have hp_dvd_rpow : p ∣ r ^ m := by simpa [hpow_nat] using hp_dvd_pow
  have hp_dvd_r : p ∣ r := hp.dvd_of_dvd_pow hp_dvd_rpow
  have hr_dvd_pow : r ∣ r ^ m := dvd_pow_self r (Nat.ne_of_gt hm)
  have hr_dvd_ppow : r ∣ p ^ n := by simpa [hpow_nat] using hr_dvd_pow
  have hr_dvd_p : r ∣ p := hr.dvd_of_dvd_pow hr_dvd_ppow
  exact ⟨hpow_nat, Nat.dvd_antisymm hp_dvd_r hr_dvd_p⟩

end MathlibPlus.NumberTheory.CyclicLogLattice

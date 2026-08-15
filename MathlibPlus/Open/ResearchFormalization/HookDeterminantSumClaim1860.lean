import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization

def riordanEntry (e t j : ℕ) : ℚ :=
  if j ≤ t then (Nat.choose (e + j) (t - j) : ℚ) else 0

def riordanDet (e L n : ℕ) : ℚ :=
  Matrix.det (fun (i : Fin (L + 1)) (j : Fin (L + 1)) =>
    riordanEntry e (if i.val < L then i.val + 1 else L + n) j.val)

def hookDeterminantSum_claim1860 (d n ell : ℕ) : Prop :=
  let e := d - ell - 1
  let L := ell + 1
  (2 ≤ n ∧ 1 ≤ ell ∧ Nat.max n (ell + 2) ≤ d ∧ e + L = d) →
    let kappa : ℚ :=
      (e : ℚ) * (d + 1 : ℚ) * (Nat.choose (d + L + 1) L : ℚ)
    let sum : ℚ :=
      ∑ j : Fin (L + 1),
        (Nat.choose L j.val : ℚ) *
          (if j.val ≤ n - 1 then
              (Nat.choose (e - 1) (n - 1 - j.val) : ℚ)
            else 0) /
            (d + j.val + 1 : ℚ)
    riordanDet e L n = kappa / (n + L : ℚ) * sum ∧
      riordanDet e L 1 =
        (e : ℚ) / (L + 1 : ℚ) * (Nat.choose (d + L + 1) L : ℚ)

end MathlibPlus.Open.ResearchFormalization

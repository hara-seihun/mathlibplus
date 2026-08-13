import Mathlib

namespace MathlibPlus.Combinatorics.Claim22892

/-!
The source uses the conventional binomial value `C(n-1,-1)=0`.  Since Lean's
`Nat` subtraction would otherwise turn `0 - 1` into `0`, the `d = 0` case is
spelled out in the right-hand side below.  The vertex `u : Fin n` makes the
`n = 0` case vacuous.
-/

/-- Signed cardinality of the `d`-subsets of `[n]`, according to whether they
contain a fixed vertex. -/
theorem neighborhoodSignSum (n d : ℕ) (u : Fin n) :
    (Finset.sum ((Finset.univ : Finset (Fin n)).powersetCard d)
      (fun S => if u ∈ S then (-1 : ℤ) else 1)) =
      (Nat.choose (n - 1) d : ℤ) -
        (if d = 0 then (0 : ℤ) else (Nat.choose (n - 1) (d - 1) : ℤ)) := by
  classical
  cases n with
  | zero => exact Fin.elim0 u
  | succ n =>
    let Ω : Finset (Finset (Fin (Nat.succ n))) :=
      (Finset.univ : Finset (Fin (Nat.succ n))).powersetCard d
    have hsum (S : Finset (Finset (Fin (Nat.succ n)))) :
        (∑ A ∈ S, if u ∈ A then (-1 : ℤ) else 1) =
          (S.card : ℤ) - 2 * ((S.filter (fun A => u ∈ A)).card : ℤ) := by
      have hpoint : ∀ A : Finset (Fin (Nat.succ n)),
          (if u ∈ A then (-1 : ℤ) else 1) =
            1 - (if u ∈ A then (2 : ℤ) else 0) := by
        intro A
        by_cases hA : u ∈ A <;> simp [hA]
      calc
        (∑ A ∈ S, if u ∈ A then (-1 : ℤ) else 1) =
            ∑ A ∈ S, (1 - (if u ∈ A then (2 : ℤ) else 0)) := by
              apply Finset.sum_congr rfl
              intro A hA
              exact hpoint A
        _ = (∑ _A ∈ S, (1 : ℤ)) -
              ∑ A ∈ S, (if u ∈ A then (2 : ℤ) else 0) := by
              rw [Finset.sum_sub_distrib]
        _ = (S.card : ℤ) -
              2 * ((S.filter (fun A => u ∈ A)).card : ℤ) := by
              have hfilter :
                  (∑ A ∈ S, (if u ∈ A then (2 : ℤ) else 0)) =
                    2 * ((S.filter (fun A => u ∈ A)).card : ℤ) := by
                rw [← Finset.sum_filter]
                simp
                ring
              rw [hfilter]
              simp
    have hΩcard : Ω.card = Nat.choose (Nat.succ n) d := by
      simp [Ω]
    have hcont :
        (Ω.filter (fun A => u ∈ A)).card =
          (if d = 0 then 0 else Nat.choose n (d - 1)) := by
      cases d with
      | zero => simp [Ω]
      | succ d =>
        have h := Finset.card_filter_powersetCard_subset
          ({u} : Finset (Fin (Nat.succ n)))
          (Finset.univ : Finset (Fin (Nat.succ n))) (Nat.succ d)
          (by simp) (by simp)
        simpa [Ω] using h
    rw [show (Nat.succ n - 1) = n by omega]
    calc
      (∑ S ∈ Ω, if u ∈ S then (-1 : ℤ) else 1) =
          (Ω.card : ℤ) - 2 * ((Ω.filter (fun A => u ∈ A)).card : ℤ) := hsum Ω
      _ = (Nat.choose (Nat.succ n) d : ℤ) -
            2 * (if d = 0 then (0 : ℤ) else (Nat.choose n (d - 1) : ℤ)) := by
            rw [hΩcard, hcont]
            simp
      _ = (Nat.choose n d : ℤ) -
            (if d = 0 then (0 : ℤ) else (Nat.choose n (d - 1) : ℤ)) := by
            cases d with
            | zero => norm_num
            | succ d =>
              rw [Nat.choose_succ_succ]
              push_cast
              ring

end MathlibPlus.Combinatorics.Claim22892

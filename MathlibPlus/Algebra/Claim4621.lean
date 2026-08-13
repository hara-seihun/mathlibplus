import Mathlib

namespace MathlibPlus.Algebra.Claim4621

/-!
The source packet uses coefficient/moment notation without fixing a carrier.
Here a packet is a finitely supported signed integer coefficient function on
integer exponents.  Translation acts on exponents, `c0` is the zeroth moment
(total coefficient), and `m1` is the first exponent moment.
-/

noncomputable def translate (a : ℤ) (p : Finsupp ℤ ℤ) : Finsupp ℤ ℤ :=
  p.mapDomain (fun n => n + a)

def c0 (p : Finsupp ℤ ℤ) : ℤ :=
  p.sum (fun _ c => c)

def m1 (p : Finsupp ℤ ℤ) : ℤ :=
  p.sum (fun n c => n * c)

/-- Translation preserves the zeroth moment and shifts the first moment by
`a` times the zeroth moment. -/
theorem translation_moments_claim4621 (a : ℤ) (p : Finsupp ℤ ℤ) :
    c0 (translate a p) = c0 p ∧
      m1 (translate a p) = m1 p + a * c0 p := by
  constructor
  · change (p.mapDomain (fun n => n + a)).sum (fun _ c => c) = _
    rw [Finsupp.sum_mapDomain_index]
    · rfl
    · intro b
      simp
    · intro b x y
      ring
  · change (p.mapDomain (fun n => n + a)).sum (fun n c => n * c) = _
    rw [Finsupp.sum_mapDomain_index]
    · calc
        p.sum (fun n c => (n + a) * c) =
            p.sum (fun n c => n * c + a * c) := by
          apply Finsupp.sum_congr
          intro n hn
          ring
        _ = p.sum (fun n c => n * c) + p.sum (fun n c => a * c) := by
          exact Finsupp.sum_add
        _ = m1 p + a * c0 p := by
          congr 1
          change (Finset.sum p.support (fun n => a * p n)) =
            a * Finset.sum p.support (fun n => p n)
          rw [Finset.mul_sum]
    · intro b
      simp
    · intro b x y
      ring

def balanced (p : Finsupp ℤ ℤ) : Prop :=
  c0 p = 0 ∧ m1 p = 0

/-- A packet balanced in zeroth and first moments stays balanced under a
common translation. -/
theorem balanced_translation_claim4621 (a : ℤ) (p : Finsupp ℤ ℤ)
    (hp : balanced p) : balanced (translate a p) := by
  change c0 p = 0 ∧ m1 p = 0 at hp
  rcases hp with ⟨hc, hm⟩
  change c0 (translate a p) = 0 ∧ m1 (translate a p) = 0
  rcases translation_moments_claim4621 a p with ⟨hc', hm'⟩
  constructor
  · exact hc'.trans hc
  · rw [hm', hc, hm]
    ring

end MathlibPlus.Algebra.Claim4621

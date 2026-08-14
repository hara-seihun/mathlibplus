import Mathlib

namespace MathlibPlus.Open.Frontier

abbrev F3 := ZMod 3
abbrev H3 := F3 × F3

def orderTwoOrbitTelescopingObstruction : Prop :=
  let n : H3 → H3 := fun h => (h.2, h.1)
  let t : H3 → F3 := fun h => h.1 ^ 2 * h.2
  let kappa : H3 → F3 := fun h => t (n h) - t h
  (∀ u v : H3, n (u + v) = n u + n v) ∧
    (∀ a : F3, ∀ u : H3, n (a • u) = a • n u) ∧
    (∀ u : H3, n (n u) = u) ∧
    (∀ u : H3, kappa u = t (n u) - t u) ∧
    (∀ h : H3, kappa h + kappa (n h) = 0) ∧
    ¬ (∃ L : H3 → F3,
      (∀ u v : H3, L (u + v) = L u + L v) ∧
        (∀ a : F3, ∀ u : H3, L (a • u) = a • L u) ∧
          (∀ h : H3, L h = kappa h)) ∧
    ¬ (∃ c : H3 → F3, ∀ x h : H3, c (x + h) - c x = kappa h)

end MathlibPlus.Open.Frontier

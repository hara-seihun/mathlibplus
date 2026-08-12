import Mathlib

namespace MathlibPlus.AlgebraicGeometry

/--
Claim 46205.  The Fermat quintic's coordinate partial derivatives are
`5 * x_i^4`, and they cannot vanish simultaneously at a nonzero homogeneous
coordinate vector.  This is the explicit projective smoothness criterion used
by the source's smoothness assertion.
-/
theorem claim46205_fermatQuinticSmoothCriterion :
    let F : (Fin 4 → ℂ) → ℂ := fun x => ∑ i, x i ^ 5
    (∀ i : Fin 4, ∀ x : Fin 4 → ℂ,
      deriv (fun t : ℂ => F (Function.update x i t)) (x i) =
        (5 : ℂ) * x i ^ 4) ∧
      (∀ x : Fin 4 → ℂ, x ≠ 0 → ∃ i : Fin 4, (5 : ℂ) * x i ^ 4 ≠ 0) := by
  dsimp
  constructor
  · intro i x
    have hterm : ∀ j : Fin 4,
        HasDerivAt (fun t : ℂ => (Function.update x i t j) ^ 5)
          (if j = i then (5 : ℂ) * x i ^ 4 else 0) (x i) := by
      intro j
      by_cases hji : j = i
      · subst j
        simpa [Function.update_self] using (hasDerivAt_pow 5 (x i))
      · simpa [hji, Function.update_of_ne hji] using
          (hasDerivAt_const (x i) ((x j) ^ 5))
    have hsum := (((hterm (0 : Fin 4)).add (hterm (1 : Fin 4))).add
      (hterm (2 : Fin 4))).add (hterm (3 : Fin 4))
    have hderiv := hsum.deriv
    have hsingle :
        (∑ j : Fin 4, if j = i then (5 : ℂ) * x i ^ 4 else 0) =
          (5 : ℂ) * x i ^ 4 := by
      simpa using
        (Fintype.sum_eq_single i (fun j hji => by simp [hji]))
    have hcoef :
        (((if (0 : Fin 4) = i then (5 : ℂ) * x i ^ 4 else 0) +
            (if (1 : Fin 4) = i then (5 : ℂ) * x i ^ 4 else 0)) +
          (if (2 : Fin 4) = i then (5 : ℂ) * x i ^ 4 else 0)) +
            (if (3 : Fin 4) = i then (5 : ℂ) * x i ^ 4 else 0) =
          (5 : ℂ) * x i ^ 4 := by
      simpa only [Fin.sum_univ_four] using hsingle
    rw [hcoef] at hderiv
    have hfun :
        (fun t : ℂ => ∑ j : Fin 4, (Function.update x i t j) ^ 5) =
          (((fun t : ℂ => (Function.update x i t 0) ^ 5) +
              (fun t : ℂ => (Function.update x i t 1) ^ 5)) +
              (fun t : ℂ => (Function.update x i t 2) ^ 5)) +
              (fun t : ℂ => (Function.update x i t 3) ^ 5) := by
      funext t
      simp only [Fin.sum_univ_four, Pi.add_apply]
    rw [hfun]
    exact hderiv
  · intro x hx
    by_contra h
    push_neg at h
    apply hx
    funext i
    have hi : x i ^ 4 = 0 := by
      rcases mul_eq_zero.mp (h i) with hi | hi
      · norm_num at hi
      · exact hi
    by_contra hxi
    exact (pow_ne_zero 4 hxi) hi

end MathlibPlus.AlgebraicGeometry

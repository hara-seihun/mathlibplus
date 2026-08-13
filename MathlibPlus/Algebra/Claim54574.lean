import MathlibPlus.Basic

namespace MathlibPlus.Algebra.Claim54574

/-!
Formalization of admitted claim 54574.  The source's normalized function is
written over an arbitrary additive commutative group and commutative ring;
its finite vector-space context is not needed for the displayed span identity.
The parenthesized sums are the Lean presentation of the source's `b+t+u`.
-/

/-- Normalized first differences and mixed second differences generate the same
local span, with the two displayed identities retained. -/
theorem mixedSecondDifferenceSpan
    {B R : Type*} [AddCommGroup B] [CommRing R]
    (f : B → R) (h₀ : f 0 = 0) :
    let P : B → B → R := fun a b => f b + f a - f (b + a)
    let D : B → B → B → R :=
      fun t u b =>
        f (b + (t + u)) - f (b + t) - f (t + u) + f t
    (∀ b : B, P 0 b = 0) ∧
      (∀ t u b : B, P (t + u) b - P t b = -D t u b) ∧
      Submodule.span R (Set.range (fun p : B × B => P p.1 p.2)) =
        Submodule.span R
          (Set.range (fun q : B × (B × B) => D q.1 q.2.1 q.2.2)) := by
  dsimp
  refine ⟨?_, ?_, ?_⟩
  · intro b
    simp [h₀]
  · intro t u b
    ring
  · apply le_antisymm
    · refine Submodule.span_le.2 ?_
      rintro x ⟨⟨a, b⟩, rfl⟩
      have hd :
          f (b + (0 + a)) - f (b + 0) - f (0 + a) + f 0 ∈
            Submodule.span R
              (Set.range
                (fun q : B × (B × B) =>
                  f (q.2.2 + (q.1 + q.2.1)) - f (q.2.2 + q.1) -
                    f (q.1 + q.2.1) + f q.1)) :=
        Submodule.subset_span ⟨⟨0, (a, b)⟩, rfl⟩
      change f b + f a - f (b + a) ∈ _
      rw [show f b + f a - f (b + a) =
          -(f (b + (0 + a)) - f (b + 0) - f (0 + a) + f 0) by
            simp [h₀]
            ring]
      exact Submodule.neg_mem _ hd
    · refine Submodule.span_le.2 ?_
      rintro x ⟨⟨t, ⟨u, b⟩⟩, rfl⟩
      have hp₁ : f b + f (t + u) - f (b + (t + u)) ∈
          Submodule.span R (Set.range (fun p : B × B =>
            f p.2 + f p.1 - f (p.2 + p.1))) :=
        Submodule.subset_span ⟨(t + u, b), rfl⟩
      have hp₂ : f b + f t - f (b + t) ∈
          Submodule.span R (Set.range (fun p : B × B =>
            f p.2 + f p.1 - f (p.2 + p.1))) :=
        Submodule.subset_span ⟨(t, b), rfl⟩
      have hp :
          (f b + f (t + u) - f (b + (t + u))) -
              (f b + f t - f (b + t)) ∈
            Submodule.span R (Set.range (fun p : B × B =>
              f p.2 + f p.1 - f (p.2 + p.1))) :=
        Submodule.sub_mem
          (Submodule.span R (Set.range (fun p : B × B =>
            f p.2 + f p.1 - f (p.2 + p.1)))) hp₁ hp₂
      change f (b + (t + u)) - f (b + t) - f (t + u) + f t ∈ _
      rw [show f (b + (t + u)) - f (b + t) - f (t + u) + f t =
          -((f b + f (t + u) - f (b + (t + u))) -
            (f b + f t - f (b + t))) by ring]
      exact Submodule.neg_mem _ hp

end MathlibPlus.Algebra.Claim54574

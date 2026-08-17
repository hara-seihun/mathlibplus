import MathlibPlus.Open.Research.GroupTheory.R1343OrbitFiber41142

namespace MathlibPlus.Open.ResearchFormalization.R1343.Claim41143

open MathlibPlus.Open.Research.GroupTheory.R1343OrbitFiber41142

private def derivativeInvariant {r : ℕ}
    (σ : Base ≃ Base) (s : Base → Voltage r)
    (S : Set (FiberState r)) : Prop :=
  ∀ x, x ∈ S → derivativeOrbit σ s x ⊆ S

private def inverseClosed {r : ℕ} (S : Set (FiberState r)) : Prop :=
  ∀ x, x ∈ S → -x ∈ S

/-- Claim 41143: every normalized C₂³-by-C₃^r profile fixes all derivative
orbit unions, so no directed support and no inverse-closed support can witness
an isomorphism failure. -/
def claim41143 : Prop :=
  ∀ (r : ℕ) (σ : Base ≃ Base) (s : Base → Voltage r),
    σ 0 = 0 →
      s 0 = 0 →
        (¬ ∃ S : Set (FiberState r),
          derivativeInvariant σ s S ∧
            Set.image (profileMap σ s) S ≠ S) ∧
          (¬ ∃ S : Set (FiberState r),
            derivativeInvariant σ s S ∧
              inverseClosed S ∧
                Set.image (profileMap σ s) S ≠ S)

end MathlibPlus.Open.ResearchFormalization.R1343.Claim41143

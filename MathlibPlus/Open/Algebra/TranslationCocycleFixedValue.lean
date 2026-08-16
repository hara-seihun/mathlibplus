import Mathlib

namespace MathlibPlus.Open.Algebra

def translationCocycleConstantValue : Prop :=
  ∀ (p : ℕ) [Fact (Nat.Prime p)] (Q : Type)
    [AddCommGroup Q] [Fintype Q],
    let F := Q → ZMod p
    ∀ (K : Submodule (ZMod p) F),
      let τ : Q → F → F := fun q k x => k (x + q)
      let P : Set Q := {h | ∀ k : K, τ h (k : F) = (k : F)}
      (∀ q : Q, ∀ k : K, τ q (k : F) ∈ K) →
      (∀ c : ZMod p, (fun _ : Q => c) ∈ K) →
      ∀ (z : Q → K),
        z 0 = 0 →
        (∀ q r : Q,
          (z (q + r) : F) =
            (z q : F) + τ q (z r : F)) →
        ∃ (P' : AddSubgroup Q),
          (∀ h : Q, h ∈ P' ↔ h ∈ P) ∧
          ∃ (lambda_z : P' →+ ZMod p),
            ∀ h : P', ∀ x : Q,
              (z (h : Q) : F) x = lambda_z h

end MathlibPlus.Open.Algebra

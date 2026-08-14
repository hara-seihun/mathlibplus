import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.SemilatticeTraceDrain

noncomputable section

def IsAntichainFamily {α : Type*} [DecidableEq α]
    (A : Finset (Finset α)) : Prop :=
  ∀ B ∈ A, ∀ C ∈ A, B ≠ C → ¬ B ⊆ C ∧ ¬ C ⊆ B

def AntichainFamily (r : ℕ) :=
  {A : Finset (Finset (Fin r)) // IsAntichainFamily A}

def antichainFamilies (r : ℕ) : Finset (Finset (Finset (Fin r))) := by
  classical
  exact Finset.univ.filter IsAntichainFamily

def MonotoneBooleanFunction (r : ℕ) :=
  {f : Finset (Fin r) → Bool //
    ∀ A B, A ⊆ B → f A ≤ f B}

def monotoneBooleanFunctions (r : ℕ) :
    Finset (Finset (Fin r) → Bool) := by
  classical
  exact Finset.univ.filter (fun f => ∀ A B, A ⊆ B → f A ≤ f B)

def dedekindNumber (r : ℕ) : ℕ := (antichainFamilies r).card

def claim16423 : Prop :=
  ∀ r : ℕ,
    dedekindNumber r = (antichainFamilies r).card ∧
      (antichainFamilies r).card = (monotoneBooleanFunctions r).card ∧
      Nonempty (AntichainFamily r ≃ MonotoneBooleanFunction r)

def RetainedTraceShape (q : ℕ) :=
  Σ S : Finset (Fin q), Finset (Finset {x // x ∈ S})

noncomputable instance (q : ℕ) : Fintype (RetainedTraceShape q) := by
  dsimp [RetainedTraceShape]
  infer_instance

def retainedTraceShapes (q : ℕ) : Finset (RetainedTraceShape q) := by
  classical
  exact Finset.univ.filter (fun p =>
    IsAntichainFamily p.2 ∧ p.2.Nonempty)

def claim16424 : Prop :=
  ∀ q : ℕ,
    (retainedTraceShapes q).card =
      (Finset.range (q + 1)).sum (fun r =>
        Nat.choose q r * (dedekindNumber r - 1))

end
end MathlibPlus.Open.SemilatticeTraceDrain

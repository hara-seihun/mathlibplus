import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Q0065

/-- An antichain of subsets of an `r`-element set. -/
def IsAntichain (r : ℕ) (A : Finset (Finset (Fin r))) : Prop :=
  ∀ ⦃s t : Finset (Fin r)⦄,
    s ∈ A → t ∈ A → s ⊆ t → s = t

def AntichainFamily (r : ℕ) :=
  {A : Finset (Finset (Fin r)) // IsAntichain r A}

/-- Claim 16423: the Dedekind number, counted by antichains of subsets. -/
noncomputable def M (r : ℕ) : ℕ := by
  classical
  letI : Fintype (AntichainFamily r) :=
    Fintype.subtype
      (Finset.univ.filter
        (fun A : Finset (Finset (Fin r)) => IsAntichain r A))
      (by intro A; simp)
  exact Fintype.card (AntichainFamily r)

/-- Monotone Boolean functions on the subset lattice of an `r`-element set. -/
def IsMonotoneBooleanFunction (r : ℕ) (f : Finset (Fin r) → Bool) : Prop :=
  ∀ ⦃s t : Finset (Fin r)⦄,
    s ⊆ t → f s = true → f t = true

def MonotoneBooleanFunctionFamily (r : ℕ) :=
  {f : Finset (Fin r) → Bool // IsMonotoneBooleanFunction r f}

/-- The equivalent monotone-Boolean-function count in Claim 16423. -/
def M_eq_monotoneBooleanFunctionCount : Prop := by
  classical
  exact ∀ r : ℕ,
    M r =
      letI : Fintype (MonotoneBooleanFunctionFamily r) :=
        Fintype.subtype
          (Finset.univ.filter
            (fun f : Finset (Fin r) → Bool =>
              IsMonotoneBooleanFunction r f))
          (by intro f; simp)
      Fintype.card (MonotoneBooleanFunctionFamily r)

end MathlibPlus.Open.ResearchFormalization.Q0065

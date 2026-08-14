import Mathlib

namespace MathlibPlus.Open.Research.Batch1464

abbrev OuterVector (q : Nat) := Fin 8 → ZMod q

def cyclicShift {q : Nat} (v : OuterVector q) (j : Fin 8) : ZMod q :=
  v ⟨(j.val + 1) % 8, Nat.mod_lt _ (by decide)⟩

def shiftPower {q : Nat} : Nat → OuterVector q → OuterVector q
  | 0, v => v
  | n + 1, v => cyclicShift (shiftPower n v)

def nonzeroAlternating {q : Nat} (v : OuterVector q) : Prop :=
  ∃ c : ZMod q,
    (∃ j : Fin 8, v j ≠ 0) ∧
      ∀ j : Fin 8, v j = c * (-1 : ZMod q) ^ j.val

/-- For an odd cyclic separation, precisely the constant-plus-alternating
profiles produce a nonzero alternating shift difference. -/
def oddSeparationProfileClassification : Prop :=
  ∀ {q : Nat}, Odd q → ∀ r : Fin 8, Odd r.val →
    (∀ τ : OuterVector q,
      nonzeroAlternating (fun j => shiftPower r.val τ j - τ j) ↔
        ∃ u v : ZMod q,
          v ≠ 0 ∧
            ∀ j : Fin 8, τ j = u + v * (-1 : ZMod q) ^ j.val) ∧
    (∀ v : OuterVector q,
      (∀ j : Fin 8, shiftPower r.val v j = v j) ↔
        ∃ c : ZMod q, ∀ j : Fin 8, v j = c) ∧
    (∀ c : ZMod q, ∀ j : Fin 8,
      shiftPower r.val (fun k => c * (-1 : ZMod q) ^ k.val) j =
        -(c * (-1 : ZMod q) ^ j.val))

end MathlibPlus.Open.Research.Batch1464

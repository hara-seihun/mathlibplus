import Mathlib

namespace MathlibPlus.Open.Research.R1130

/-- The elementary-abelian quotient `E = C₂²`. -/
abbrev E : Type := Fin 2 → ZMod 2

/-- The regular module `𝔽₂[E]`, written as all binary functions on `E`. -/
abbrev regularModule : Type := E → ZMod 2

def regularFixedSubmodule : Submodule (ZMod 2) regularModule :=
  { carrier := {f | ∀ g x : E, f (x + g) = f x}
    zero_mem' := by
      intro g x
      simp
    add_mem' := by
      intro f g hf hg a x
      simp [hf a x, hg a x]
    smul_mem' := by
      intro c f hf a x
      simp [hf a x] }

def globalSwapSubmodule : Submodule (ZMod 2) regularModule :=
  { carrier := {f | ∃ c : ZMod 2, ∀ x : E, f x = c}
    zero_mem' := by
      refine ⟨0, ?_⟩
      intro x
      simp
    add_mem' := by
      rintro f g ⟨c, hc⟩ ⟨d, hd⟩
      refine ⟨c + d, ?_⟩
      intro x
      simp [hc x, hd x]
    smul_mem' := by
      rintro c f ⟨d, hd⟩
      refine ⟨c * d, ?_⟩
      intro x
      simp [hd x] }

/-- The fixed submodule of the regular `𝔽₂[E]` module is exactly the global
swap line, and that line has dimension one. -/
def fixedSubmoduleOfRegularModule : Prop :=
  regularFixedSubmodule = globalSwapSubmodule ∧
    Module.finrank (ZMod 2) (globalSwapSubmodule : Type) = 1

end MathlibPlus.Open.Research.R1130

import Mathlib

namespace MathlibPlus.Open

/-- The algebraic exactness assertion in admitted claim 60393. -/
def claim60393
    (V E W Z : Type*)
    [Fintype V] [Fintype E]
    [AddCommGroup W] [Module ℚ W]
    [AddCommGroup Z] [Module ℚ Z]
    (D : (E → ℚ) →ₗ[ℚ] (V → ℚ))
    (S : (V → ℚ) →ₗ[ℚ] W)
    (A : (E → ℚ) →ₗ[ℚ] Z) : Prop :=
  let K_cyc : Submodule ℚ (E → ℚ) := LinearMap.ker D
  let K_act : Submodule ℚ (E → ℚ) := LinearMap.ker (S.comp D)
  let B : Submodule ℚ (V → ℚ) := LinearMap.range D ⊓ LinearMap.ker S
  (LinearMap.range (D.domRestrict K_act) = B) ∧
    (Submodule.map K_act.subtype (LinearMap.ker (D.domRestrict K_act)) = K_cyc)

/-- The quotient-holonomy and dimension assertion in admitted claim 60394. -/
def claim60394
    (V E W Z : Type*)
    [Fintype V] [Fintype E]
    [AddCommGroup W] [Module ℚ W]
    [AddCommGroup Z] [Module ℚ Z]
    (D : (E → ℚ) →ₗ[ℚ] (V → ℚ))
    (S : (V → ℚ) →ₗ[ℚ] W)
    (A : (E → ℚ) →ₗ[ℚ] Z) : Prop :=
  let K_cyc : Submodule ℚ (E → ℚ) := LinearMap.ker D
  let K_act : Submodule ℚ (E → ℚ) := LinearMap.ker (S.comp D)
  let B : Submodule ℚ (V → ℚ) := LinearMap.range D ⊓ LinearMap.ker S
  let H_cyc : Submodule ℚ Z := K_cyc.map A
  let H_act : Submodule ℚ Z := K_act.map A
  let H_cyc_in_H_act : Submodule ℚ H_act := H_cyc.comap H_act.subtype
  ∃ barA : B →ₗ[ℚ] (Z ⧸ H_cyc),
    (∀ (b : B) (c : K_act),
      b.1 = D c.1 → barA b = H_cyc.mkQ (A c.1)) ∧
      H_cyc ≤ H_act ∧
      Nonempty ((LinearMap.range barA) ≃ₗ[ℚ] (H_act ⧸ H_cyc_in_H_act)) ∧
      Module.finrank ℚ H_act =
        Module.finrank ℚ H_cyc + Module.finrank ℚ (LinearMap.range barA) ∧
      (H_act ≠ ⊥ ↔ H_cyc ≠ ⊥ ∨ LinearMap.range barA ≠ ⊥)

end MathlibPlus.Open

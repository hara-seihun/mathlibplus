import Mathlib

namespace MathlibPlus.Open.FormalizationBatch.R1242Claim30516

abbrev F3 := ZMod 3
abbrev Plane := Fin 2 → F3
abbrev Vector := Fin 3 → F3
abbrev Table := Plane → Vector

def ell (x : Plane) : Vector :=
  fun k => if k = 0 then x 1 ^ 2 else if k = 1 then -(x 0 * x 1) else x 0 ^ 2

def doublePlane (x : Plane) : Plane := (2 : F3) • x

def delta (x : Plane) (F : Table) (s : Plane) : Vector :=
  F (s + x) - F s

def exceptionalLayer (x : Plane) (H : Plane → F3) (F : Table) (r : F3) : Prop :=
  ∀ s : Plane, delta x F s = r • (H s • ell x)

/-- Claim 30516: the opposite-direction difference identity, periodic layer
correspondence, and preservation of the absence of exceptional layers. -/
def claim30516_oppositeDirection : Prop :=
  ∀ (x : Plane) (H : Plane → F3) (F : Table),
    x ≠ 0 →
    (∀ s : Plane, H (s + x) = H s) →
      (∀ s : Plane,
        delta (doublePlane x) F s = delta x F s + delta x F (s + x)) ∧
      (∀ r : F3,
        exceptionalLayer x H F r ↔
          exceptionalLayer (doublePlane x) H F ((2 : F3) * r)) ∧
      ((∀ r : F3, ¬ exceptionalLayer x H F r) →
        ∀ r : F3, ¬ exceptionalLayer (doublePlane x) H F r)

end MathlibPlus.Open.FormalizationBatch.R1242Claim30516

import Mathlib

namespace MathlibPlus.Open.GroupTheory.R1349Claim41244

abbrev A12 := (Equiv.Perm.sign : Equiv.Perm (Fin 12) →* ℤˣ).ker
abbrev Base := Fin 7 → Equiv.Perm (Fin 12)

def alternatingPower : Subgroup Base :=
  { carrier := {g | ∀ i : Fin 7, g i ∈ A12}
    one_mem' := by
      intro i
      exact A12.one_mem
    mul_mem' := by
      intro g h hg hh i
      exact A12.mul_mem (hg i) (hh i)
    inv_mem' := by
      intro g hg i
      exact A12.inv_mem (hg i) }

def subdirectAlternatingPower
    (H : Subgroup Base) : Prop :=
  ∀ i : Fin 7, ∀ a : A12,
    ∃ h : H, h.1 i = (a : Equiv.Perm (Fin 12))

def sevenTorsionSurjectiveProjections
    (K : Subgroup Base) : Prop :=
  7 ∣ Nat.card K ∧
    ∀ i : Fin 7, ∀ σ : Equiv.Perm (Fin 12),
      ∃ k : K, k.1 i = σ

def regularSevenCycle (σ : Equiv.Perm (Fin 7)) : Prop :=
  orderOf σ = 7 ∧
    ∀ i j : Fin 7, ∃ n : ℕ, (σ ^ n) i = j

def coordinateReindex (σ : Equiv.Perm (Fin 7)) (g : Base) : Base :=
  fun i => g (σ i)

def cyclicInvariantAlternatingPower
    (H : Subgroup Base) (σ : Equiv.Perm (Fin 7)) : Prop :=
  ∀ h : H, coordinateReindex σ (h : Base) ∈ H

def twistedDiagonalHom
    (u : Fin 7 → Equiv.Perm (Fin 12)) : A12 →* Base :=
  { toFun := fun a i => u i * (a : Equiv.Perm (Fin 12)) * (u i)⁻¹
    map_one' := by
      funext i
      simp
    map_mul' := by
      intro a b
      funext i
      simp [mul_assoc] }

/-- A full diagonal alternating strip with independent inner twists in the
seven coordinates; no literal-diagonal normalization is assumed. -/
def twistedDiagonalStrip
    (u : Fin 7 → Equiv.Perm (Fin 12)) : Subgroup Base :=
  Subgroup.map (twistedDiagonalHom u) ⊤

/-- Scott's alternatives retain the full diagonal strip before any explicit
untwisting to a literal diagonal. -/
def scottAlternatingPowerDichotomy : Prop :=
  ∀ K H : Subgroup Base, ∀ σ : Equiv.Perm (Fin 7),
    sevenTorsionSurjectiveProjections K →
    regularSevenCycle σ →
    H = ⁅K, K⁆ →
    H ≤ alternatingPower →
    subdirectAlternatingPower H →
    cyclicInvariantAlternatingPower H σ →
      H = alternatingPower ∨
        ∃ u : Fin 7 → Equiv.Perm (Fin 12),
          H = twistedDiagonalStrip u

/-- A proper full diagonal strip is the non-product branch that must remain
available to the Scott decomposition. -/
def properTwistedDiagonalStrip : Prop :=
  ∃ σ : Equiv.Perm (Fin 7),
    regularSevenCycle σ ∧
      ∃ u : Fin 7 → Equiv.Perm (Fin 12),
        twistedDiagonalStrip u ≤ alternatingPower ∧
          subdirectAlternatingPower (twistedDiagonalStrip u) ∧
            cyclicInvariantAlternatingPower (twistedDiagonalStrip u) σ ∧
              twistedDiagonalStrip u ≠ alternatingPower

/-- The seven-torsion Scott statement preserves the potentially twisted
full diagonal branch rather than silently identifying it with the literal
diagonal subgroup. -/
def claim41244 : Prop :=
  scottAlternatingPowerDichotomy ∧ properTwistedDiagonalStrip

end MathlibPlus.Open.GroupTheory.R1349Claim41244

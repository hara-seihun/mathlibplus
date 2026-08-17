import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Research.GeneratedGroupExact

noncomputable section

attribute [local instance] Classical.propDecidable

abbrev Block := ZMod 8
abbrev Fiber (q : ℕ) := ZMod q
abbrev Omega (q : ℕ) := (j : Block) × Fiber q
abbrev Perm (q : ℕ) := Equiv.Perm (Omega q)
abbrev Mask := Block → ZMod 2

def translationGenerator (q : ℕ) : Perm q :=
  Equiv.sigmaCongrRight (fun _ : Block => Equiv.addRight (1 : Fiber q))

def reflectionGenerator (q : ℕ) : Perm q :=
  (Equiv.sigmaCongrLeft (Equiv.addRight (1 : Block))).trans
    (Equiv.sigmaCongrRight (fun _ : Block => Equiv.neg (Fiber q)))

def fiberFlip (q : ℕ) (a : ZMod 2) : Equiv.Perm (Fiber q) :=
  if a = 0 then Equiv.refl _ else Equiv.swap (0 : Fiber q) 1

def maskEquiv (q : ℕ) (μ : Mask) : Perm q :=
  Equiv.sigmaCongrRight (fun j : Block => fiberFlip q (μ j))

def conjugatePermutation {q : ℕ} (F r : Perm q) : Perm q :=
  F * r * F⁻¹

def conjugateSubgroup {q : ℕ} (F : Perm q)
    (H : Subgroup (Perm q)) : Subgroup (Perm q) :=
  Subgroup.map (MulAut.conj F).toMonoidHom H

def regularSubgroup {q : ℕ} (H : Subgroup (Perm q)) : Prop :=
  ∀ p r : Omega q, ∃! h : Perm q, h ∈ H ∧ h p = r

def regularCopyR (q : ℕ) : Subgroup (Perm q) :=
  Subgroup.closure ({translationGenerator q, reflectionGenerator q} : Set (Perm q))

def regularCopyT (q : ℕ) (μ : Mask) : Subgroup (Perm q) :=
  conjugateSubgroup (maskEquiv q μ) (regularCopyR q)

def generatedGroup (q : ℕ) (μ : Mask) : Subgroup (Perm q) :=
  Subgroup.closure
    ((regularCopyR q : Set (Perm q)) ∪ (regularCopyT q μ : Set (Perm q)))

def cyclicCoreR (q : ℕ) : Subgroup (Perm q) :=
  Subgroup.closure ({translationGenerator q} : Set (Perm q))

def cyclicCoreT (q : ℕ) (μ : Mask) : Subgroup (Perm q) :=
  conjugateSubgroup (maskEquiv q μ) (cyclicCoreR q)

def characteristicSubgroup {P : Type*} [Group P]
    (G : Subgroup P) (K : Subgroup G) : Prop :=
  ∀ e : G ≃* G, ∀ h : G, h ∈ K ↔ e h ∈ K

def orbitRelation {q : ℕ} (K : Subgroup (Perm q))
    (p r : Omega q) : Prop :=
  ∃ h : Perm q, h ∈ K ∧ h p = r

def blockOrbits {q : ℕ} (K : Subgroup (Perm q)) : Prop :=
  ∀ p r : Omega q, orbitRelation K p r ↔ p.1 = r.1

def commonCharacteristicPartition (q : ℕ) (μ : Mask) : Prop :=
  characteristicSubgroup (regularCopyR q)
      (Subgroup.comap (regularCopyR q).subtype (cyclicCoreR q)) ∧
    characteristicSubgroup (regularCopyT q μ)
      (Subgroup.comap (regularCopyT q μ).subtype (cyclicCoreT q μ)) ∧
    blockOrbits (cyclicCoreR q) ∧
    blockOrbits (cyclicCoreT q μ) ∧
    (∀ r : Perm q, r ∈ regularCopyR q → ∀ p : Omega q,
      ((conjugatePermutation (maskEquiv q μ) r) p).1 = (r p).1)

def blockFixingNormalizer (q : ℕ) (h : Perm q) : Prop :=
  (∀ p : Omega q, (h p).1 = p.1) ∧
    conjugateSubgroup h (regularCopyR q) = regularCopyR q

def fiberParity {q : ℕ} [NeZero q] (e : Equiv.Perm (Fiber q)) : ZMod 2 :=
  if Equiv.Perm.sign e = 1 then 0 else 1

def normalizerSignVector {q : ℕ} [NeZero q] (h : Perm q) (ν : Mask) : Prop :=
  ∀ j : Block, ∃ e : Equiv.Perm (Fiber q),
    (∀ x : Fiber q, h (⟨j, x⟩) = ⟨j, e x⟩) ∧
      ν j = fiberParity e

def normalizerSignVectors (q : ℕ) [NeZero q] : Set Mask :=
  {ν | ∃ h : Perm q, blockFixingNormalizer q h ∧ normalizerSignVector h ν}

def constantMask (μ : Mask) : Prop :=
  ∃ a : ZMod 2, ∀ j : Block, μ j = a

def cyclicShift (μ : Mask) : Mask :=
  fun j => μ (j + 1)

def shiftIter (k : Fin 8) (μ : Mask) : Mask :=
  (cyclicShift^[k.val]) μ

def maskAdd (μ ν : Mask) : Mask :=
  fun j => μ j + ν j

def constantVector (a : ZMod 2) : Mask :=
  fun _ => a

def signGenerator (μ : Mask) : Mask :=
  maskAdd μ (cyclicShift μ)

def generatedSignCode (μ : Mask) : Submodule (ZMod 2) Mask :=
  Submodule.span (ZMod 2)
    (Set.range (fun k : Fin 8 => shiftIter k (signGenerator μ)))

def normalizerCoset (μ : Mask) : Set Mask :=
  {ν | ∃ a : ZMod 2, ν = maskAdd μ (constantVector a)}

def conjugateWithinGenerated (q : ℕ) (μ : Mask) : Prop :=
  ∃ h : generatedGroup q μ,
    conjugateSubgroup (h : Perm q) (regularCopyR q) = regularCopyT q μ

def conjugacySignBridge (q : ℕ) (μ : Mask) : Prop :=
  ∀ h : Perm q, h ∈ generatedGroup q μ →
    conjugateSubgroup h (regularCopyR q) = regularCopyT q μ →
      ∃ a : ZMod 2,
        maskAdd μ (constantVector a) ∈ generatedSignCode μ

/-- The explicit eight-block construction, its characteristic block system and
terminal action, the normalizer/sign-code bridge, and the nonconjugacy theorem
with constant-mask controls. -/
def claim38255 : Prop :=
  ∀ q : ℕ, ∀ hq : Nat.Prime q, 2 < q →
    letI : NeZero q := ⟨hq.ne_zero⟩
    ∀ μ : Mask,
      regularSubgroup (regularCopyR q) ∧
        regularSubgroup (regularCopyT q μ) ∧
        commonCharacteristicPartition q μ ∧
        (∀ ν : Mask, ν ∈ normalizerSignVectors q → constantMask ν) ∧
        (Set.Nonempty
            (normalizerCoset μ ∩ (generatedSignCode μ : Set Mask)) ↔
          constantMask μ) ∧
        conjugacySignBridge q μ ∧
        ((¬ constantMask μ → ¬ conjugateWithinGenerated q μ) ∧
          (constantMask μ → conjugateWithinGenerated q μ))

end
end MathlibPlus.Open.Research.GeneratedGroupExact

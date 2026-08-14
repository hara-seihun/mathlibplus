import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.DegreePShear

abbrev ShearSpace (p : ℕ) := Fin 3 → ZMod p

 def shear (p : ℕ) (c : ZMod p) (w : ShearSpace p) : ShearSpace p :=
  ![w 0, w 1, w 2 + c * (w 0) ^ (p - 1) * w 1]

 def shearInverse (p : ℕ) (c : ZMod p) (w : ShearSpace p) : ShearSpace p :=
  ![w 0, w 1, w 2 - c * (w 0) ^ (p - 1) * w 1]

 def transportedMap (p : ℕ) (c : ZMod p)
    (L₁ L₂ : ShearSpace p ≃ₗ[ZMod p] ShearSpace p) :
    ShearSpace p → ShearSpace p :=
  fun x => L₂ (shear p c (L₁ x))

 def transportedInverse (p : ℕ) (c : ZMod p)
    (L₁ L₂ : ShearSpace p ≃ₗ[ZMod p] ShearSpace p) :
    ShearSpace p → ShearSpace p :=
  fun y => L₁.symm (shearInverse p c (L₂.symm y))

 def linearTransport (p : ℕ)
    (L₁ L₂ : ShearSpace p ≃ₗ[ZMod p] ShearSpace p) :
    ShearSpace p → ShearSpace p :=
  fun x => L₂ (L₁ x)

 def transportRelation (p : ℕ) (c : ZMod p)
    (L₁ L₂ : ShearSpace p ≃ₗ[ZMod p] ShearSpace p)
    (a b : ShearSpace p) : Prop :=
  ∃ x s : ShearSpace p,
    a = s ∧
      (b = transportedInverse p c L₁ L₂
          (transportedMap p c L₁ L₂ (x + s) - transportedMap p c L₁ L₂ x) ∨
       b = -transportedInverse p c L₁ L₂
          (transportedMap p c L₁ L₂ (x + s) - transportedMap p c L₁ L₂ x))

 def generatedBlock (r : ShearSpace p → ShearSpace p → Prop)
    (a : ShearSpace p) : Set (ShearSpace p) :=
  {b | Relation.EqvGen r a b}

 def qBlock (p : ℕ) (c : ZMod p)
    (L₁ L₂ : ShearSpace p ≃ₗ[ZMod p] ShearSpace p)
    (a : ShearSpace p) : Set (ShearSpace p) :=
  generatedBlock (transportRelation p c L₁ L₂) a

 def hBlock (p : ℕ) (c : ZMod p) (a : ShearSpace p) : Set (ShearSpace p) :=
  generatedBlock
    (fun x y : ShearSpace p =>
      ∃ base step : ShearSpace p,
        x = step ∧
          (y = shearInverse p c
              (shear p c (base + step) - shear p c base) ∨
           y = -shearInverse p c
              (shear p c (base + step) - shear p c base))) a

 def relativeShear (p : ℕ) (c : ZMod p)
    (x s : ShearSpace p) : ShearSpace p :=
  shear p c (x + s) - shear p c x - shear p c s

 def degreePShearTransportShadow : Prop :=
  ∀ (p : ℕ), Nat.Prime p → 5 ≤ p →
    ∀ (c : ZMod p), c ≠ 0 →
      ∀ (L₁ L₂ : ShearSpace p ≃ₗ[ZMod p] ShearSpace p),
        ∀ a : ShearSpace p,
          Set.image (transportedMap p c L₁ L₂)
              (qBlock p c L₁ L₂ a) =
            Set.image (linearTransport p L₁ L₂)
              (qBlock p c L₁ L₂ a)

 def pairedFibreBlockStructure : Prop :=
  ∀ (p : ℕ), Nat.Prime p → 5 ≤ p →
    ∀ (c : ZMod p), c ≠ 0 →
      (∀ x s : ShearSpace p,
        let r := relativeShear p c x s
        r 0 = 0 ∧
        r 1 = 0 ∧
        r 2 = c *
          ((x 0 + s 0) ^ (p - 1) * (x 1 + s 1) -
            (x 0) ^ (p - 1) * x 1 - (s 0) ^ (p - 1) * s 1)) ∧
      (∀ (a b d : ZMod p), a ≠ 0 ∨ b ≠ 0 →
        hBlock p c ![a, b, d] =
          {w | (w 0 = a ∧ w 1 = b) ∨
            (w 0 = -a ∧ w 1 = -b)}) ∧
      (∀ (t : ZMod p),
        hBlock p c ![0, 0, t] =
          {w | w 0 = 0 ∧ w 1 = 0 ∧ (w 2 = t ∨ w 2 = -t)}) ∧
      (∀ a : ShearSpace p,
        Set.image (shear p c) (hBlock p c a) = hBlock p c a) ∧
      (∀ (L₁ L₂ : ShearSpace p ≃ₗ[ZMod p] ShearSpace p)
          (a : ShearSpace p),
        qBlock p c L₁ L₂ a =
          (fun x => L₁ x) ⁻¹' hBlock p c (L₁ a)) ∧
      (∀ (L₁ L₂ : ShearSpace p ≃ₗ[ZMod p] ShearSpace p)
          (a : ShearSpace p),
        let C := hBlock p c a
        Set.image (transportedMap p c L₁ L₂)
            ((fun x => L₁ x) ⁻¹' C) = Set.image L₂ C ∧
        Set.image (transportedMap p c L₁ L₂)
            ((fun x => L₁ x) ⁻¹' C) =
          Set.image (linearTransport p L₁ L₂)
            ((fun x => L₁ x) ⁻¹' C))

 def productMap {U : Type*} (f : ShearSpace p → ShearSpace p)
    (z : ShearSpace p × U) : ShearSpace p × U :=
  (f z.1, z.2)

 def blockUnion {U : Type*} [AddGroup U]
    (r : ShearSpace p → ShearSpace p → Prop)
    (I : Type*) (blocks : I → ShearSpace p) (us : I → U) :
    Set (ShearSpace p × U) :=
  ⋃ i, Set.prod (generatedBlock r (blocks i)) {us i, -us i}

 def inverseClosed {U : Type*} [AddGroup U]
    (S : Set (ShearSpace p × U)) : Prop :=
  ∀ z, z ∈ S ↔ -z ∈ S

 def inverseClosedBlockUnionSwitch : Prop :=
  ∀ (p : ℕ), Nat.Prime p → 5 ≤ p →
    ∀ (c : ZMod p), c ≠ 0 →
      ∀ (L₁ L₂ : ShearSpace p ≃ₗ[ZMod p] ShearSpace p)
        {U : Type*} [AddCommGroup U] [Module (ZMod p) U]
        (I : Type*) (blocks : I → ShearSpace p) (us : I → U),
        let S := blockUnion (transportRelation p c L₁ L₂) I blocks us
        Set.image (productMap (transportedMap p c L₁ L₂)) S =
          Set.image (productMap (linearTransport p L₁ L₂)) S

end MathlibPlus.Open.ResearchFormalization.DegreePShear

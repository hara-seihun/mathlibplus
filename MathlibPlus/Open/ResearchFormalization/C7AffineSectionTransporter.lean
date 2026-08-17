import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.C7AffineSectionTransporter

abbrev C7Vector := Fin 2 → ZMod 7
abbrev EPoint := C7Vector × Fin 3

/-- The scalar semidirect-product operation for `E(C₇²,3)`. -/
def extensionMul (x y : EPoint) : EPoint :=
  (x.1 + ((2 : ZMod 7) ^ x.2.val) • y.1, x.2 + y.2)

/-- The three kernel-coset shifts `0,c,3c` in the section coordinate. -/
def sectionShift (c : C7Vector) : Fin 3 → C7Vector :=
  ![0, c, 3 • c]

/-- The affine transporter in the three displayed sections. -/
def sectionTransport (L : C7Vector ≃ₗ[ZMod 7] C7Vector) (c : C7Vector) :
    EPoint → EPoint :=
  fun p => (L p.1 + sectionShift c p.2, p.2)

/-- A kernel section of a subset of the `C₇²` factor. -/
def kernelSection (B : Finset C7Vector) (i : Fin 3) : Set EPoint :=
  {p | p.2 = i ∧ p.1 ∈ B}

/-- The inverse-section set `3B`. -/
def tripleImage (B : Finset C7Vector) : Finset C7Vector :=
  B.image (fun b => 3 • b)

/-- The affine image `L(B)+c`. -/
def affineImage (L : C7Vector ≃ₗ[ZMod 7] C7Vector)
    (c : C7Vector) (B : Finset C7Vector) : Finset C7Vector :=
  B.image (fun b => L b + c)

/-- Automorphism means bijective and multiplicative for the displayed group law. -/
def extensionAutomorphism (f : EPoint → EPoint) : Prop :=
  Function.Bijective f ∧ ∀ x y, f (extensionMul x y) = extensionMul (f x) (f y)

/-- Claim 42049: the explicit affine section transporter, including all four
section images and the literal three-coordinate formula. -/
def claim42049 : Prop :=
  ∀ (B C : Finset C7Vector) (L : C7Vector ≃ₗ[ZMod 7] C7Vector)
    (c : C7Vector),
    C = affineImage L c B →
      (∀ a : C7Vector,
        sectionTransport L c (a, (0 : Fin 3)) = (L a, (0 : Fin 3))) ∧
      (∀ a : C7Vector,
        sectionTransport L c (a, (1 : Fin 3)) = (L a + c, (1 : Fin 3))) ∧
      (∀ a : C7Vector,
        sectionTransport L c (a, (2 : Fin 3)) =
          (L a + 3 • c, (2 : Fin 3))) ∧
      extensionAutomorphism (sectionTransport L c) ∧
      Set.image (sectionTransport L c) (kernelSection ∅ 0) =
        kernelSection ∅ 0 ∧
      Set.image (sectionTransport L c) (kernelSection Finset.univ 0) =
        kernelSection Finset.univ 0 ∧
      Set.image (sectionTransport L c) (kernelSection B 1) =
        kernelSection C 1 ∧
      Set.image (sectionTransport L c) (kernelSection (tripleImage B) 2) =
        kernelSection (tripleImage C) 2

end MathlibPlus.Open.ResearchFormalization.C7AffineSectionTransporter

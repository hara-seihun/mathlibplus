import MathlibPlus.Open.GraphTheory.R1168UnresolvedSpace

namespace MathlibPlus.Open.GraphTheory.R1168

/-- The profile in the coordinates obtained after the displayed `q₀` change.
The displayed eight-point action is an involution, so its inverse has the same
coordinate formula. -/
def profileAfterQ0Inverse_41548 (t : Profile) : Profile :=
  fun z => t (baseQ0 z)

/-- The voltage difference used for the two target lifts. -/
def profileVoltageDifference_41548 (s : Profile) (g : Base → Base) : Profile :=
  fun h => s (g h) - s h

/-- An affine lift of a base map with a `C₇` voltage profile. -/
def affineLift_41548 (v : Profile) (g : Base → Base) : Source → Source :=
  fun p => (p.1 + v p.2, g p.2)

/-- The identity base map and zero voltage profile. -/
def baseIdentity : Base → Base := fun z => z

def zeroProfile : Profile := fun _ => 0

/-- The six base maps in the source/target generator display. -/
def affineBaseGenerator_41548 (k : Fin 6) : Base → Base :=
  ![baseIdentity, baseA, baseB, baseIdentity, baseA, baseB2] k

/-- The corresponding inverse base maps. -/
def affineBaseInverse_41548 (k : Fin 6) : Base → Base :=
  ![baseIdentity, baseAInv, baseBInv, baseIdentity, baseAInv, baseB2Inv] k

/-- The six displayed voltage profiles: the common parity translation, the
zero-voltage source lifts, and the two target differences. -/
def affineVoltageGenerator_41548 (s : Profile) (k : Fin 6) : Profile :=
  ![paritySign, zeroProfile, zeroProfile, paritySign,
    profileVoltageDifference_41548 s baseA,
    profileVoltageDifference_41548 s baseB2] k

/-- The inverse of one displayed affine generator, written with its exact
base inverse and the pulled-back voltage. -/
def affineInverseGenerator_41548 (s : Profile) (k : Fin 6) : Source → Source :=
  fun p =>
    let z := affineBaseInverse_41548 k p.2
    (p.1 - affineVoltageGenerator_41548 s k z, z)

/-- A signed affine-Schreier letter. -/
abbrev AffineLetter_41548 := Fin 6 × Bool

/-- One step in the affine-Schreier action. -/
def affineStep_41548 (s : Profile) (l : AffineLetter_41548) :
    Source → Source :=
  if l.2 then affineLift_41548 (affineVoltageGenerator_41548 s l.1)
      (affineBaseGenerator_41548 l.1)
  else affineInverseGenerator_41548 s l.1

/-- The affine-Schreier word action, using the same left-after-the-rest word
convention as the reviewed base action. -/
def affineWordValue_41548 (s : Profile) :
    List AffineLetter_41548 → Source → Source
  | [], p => p
  | l :: w, p => affineStep_41548 s l (affineWordValue_41548 s w p)

/-- The generated affine group, represented by its affine-Schreier word
maps. -/
def generatedAffineGroup_41548 (s : Profile) : Set (Source → Source) :=
  {f | ∃ w : List AffineLetter_41548,
    ∀ p, affineWordValue_41548 s w p = f p}

/-- Agreement of a source map with a base map on every `C₇` fibre. -/
def affineBaseProjectionAgreement_41548
    (f : Source → Source) (g : Base → Base) : Prop :=
  ∀ (x : ZMod 7) (z : Base), (f (x, z)).2 = g z

/-- Claim 41548: after `s=t∘q₀⁻¹`, the generated affine group has the
common parity-sign translation, the two zero-voltage source lifts, and the
specified target voltage differences. Its quotient projection is the
reviewed generated base action. -/
def affineGeneratorVoltages_41548 : Prop :=
  ∀ (t : Profile),
    t baseRoot = 0 →
      let s := profileAfterQ0Inverse_41548 t
      let G := generatedAffineGroup_41548 s
      s baseRoot = 0 ∧
        (∀ f, f ∈ G → Function.Bijective f) ∧
        (∀ f, f ∈ G →
          ∃ g, g ∈ generatedBaseMap ∧
            affineBaseProjectionAgreement_41548 f g) ∧
        (∀ g, g ∈ generatedBaseMap →
          ∃ f, f ∈ G ∧
            affineBaseProjectionAgreement_41548 f g) ∧
        (∀ k : Fin 6,
          affineLift_41548 (affineVoltageGenerator_41548 s k)
              (affineBaseGenerator_41548 k) ∈ G) ∧
        (∀ (x : ZMod 7) (z : Base),
          affineLift_41548 (affineVoltageGenerator_41548 s 0)
              (affineBaseGenerator_41548 0) (x, z) =
            (x + paritySign z, z)) ∧
        (∀ (x : ZMod 7) (z : Base),
          affineLift_41548 (affineVoltageGenerator_41548 s 1)
              (affineBaseGenerator_41548 1) (x, z) =
            (x, baseA z)) ∧
        (∀ (x : ZMod 7) (z : Base),
          affineLift_41548 (affineVoltageGenerator_41548 s 2)
              (affineBaseGenerator_41548 2) (x, z) =
            (x, baseB z)) ∧
        (∀ (x : ZMod 7) (z : Base),
          affineLift_41548 (affineVoltageGenerator_41548 s 3)
              (affineBaseGenerator_41548 3) (x, z) =
            (x + paritySign z, z)) ∧
        (∀ (x : ZMod 7) (z : Base),
          affineLift_41548 (affineVoltageGenerator_41548 s 4)
              (affineBaseGenerator_41548 4) (x, z) =
            (x + s (baseA z) - s z, baseA z)) ∧
        (∀ (x : ZMod 7) (z : Base),
          affineLift_41548 (affineVoltageGenerator_41548 s 5)
              (affineBaseGenerator_41548 5) (x, z) =
            (x + s (baseB2 z) - s z, baseB2 z))

end MathlibPlus.Open.GraphTheory.R1168

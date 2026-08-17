import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1508

noncomputable section

abbrev Fiber1508 := ZMod 5
abbrev Outer1508 := Fin 8
abbrev Carrier1508 := Fiber1508 × Outer1508
abbrev AffineProfile1508 :=
  (Outer1508 → Fiber1508ˣ) × (Outer1508 → Fiber1508)

/-- An affine permutation of one quinary block. -/
def affineLine1508 (a : Fiber1508ˣ) (b : Fiber1508) :
    Equiv.Perm Fiber1508 :=
  (Units.mulLeft a).trans (Equiv.addRight b)

/-- A blockwise affine chart on the eight outer blocks. -/
def blockwiseChart1508
    (h : Outer1508 → Fiber1508ˣ)
    (t : Outer1508 → Fiber1508) : Equiv.Perm Carrier1508 :=
  Equiv.prodCongrLeft (fun j => affineLine1508 (h j) (t j))

/-- The global fiber translation in the standard `E(C5,8)` action. -/
def fiberTranslation1508 : Equiv.Perm Carrier1508 :=
  Equiv.prodCongr (Equiv.addRight (1 : Fiber1508)) (Equiv.refl Outer1508)

/-- The order-eight outer generator, with inversion action on the fiber. -/
def outerGenerator1508 : Equiv.Perm Carrier1508 :=
  Equiv.prodCongr (Equiv.neg Fiber1508)
    (Equiv.addRight (1 : Outer1508))

/-- The regular order-forty `E(C5,8)` subgroup, not the independent
block-translation closure. -/
def standardRegularGroup1508 :
    Subgroup (Equiv.Perm Carrier1508) :=
  Subgroup.closure
    ({fiberTranslation1508, outerGenerator1508} :
      Set (Equiv.Perm Carrier1508))

def conjugatedSubgroup1508
    (F : Equiv.Perm Carrier1508)
    (R : Subgroup (Equiv.Perm Carrier1508)) :
    Subgroup (Equiv.Perm Carrier1508) :=
  Subgroup.map (MulAut.conj F.symm).toMonoidHom R

def profileChart1508 (p : AffineProfile1508) :
    Equiv.Perm Carrier1508 :=
  blockwiseChart1508 p.1 p.2

def globalAffineNormalizer1508
    (a : Fiber1508ˣ) (b : Fiber1508) : Equiv.Perm Carrier1508 :=
  blockwiseChart1508 (fun _ => a) (fun _ => b)

def globalNormalizerOfSource1508
    (a : Fiber1508ˣ) (b : Fiber1508) : Prop :=
  conjugatedSubgroup1508 (globalAffineNormalizer1508 a b)
      standardRegularGroup1508 = standardRegularGroup1508

def normalizedProfile1508 (p : AffineProfile1508) : Prop :=
  p.1 0 = 1 ∧ p.2 0 = 0

def sourceSideNormalization1508
    (raw normalized : AffineProfile1508) : Prop :=
  ∃ a : Fiber1508ˣ, ∃ b : Fiber1508,
    raw.1 0 = a ∧ raw.2 0 = b ∧
      normalizedProfile1508 normalized ∧
      globalNormalizerOfSource1508 a b ∧
      (∀ j : Outer1508,
        raw.1 j = a * normalized.1 j ∧
          raw.2 j = (a : Fiber1508) * normalized.2 j + b) ∧
      profileChart1508 raw =
        (profileChart1508 normalized).trans
          (globalAffineNormalizer1508 a b)

def orderedTwoClosure1508
    (G : Subgroup (Equiv.Perm Carrier1508)) :
    Set (Equiv.Perm Carrier1508) :=
  {q | ∀ x y : Carrier1508, ∃ g : G,
    q x = (g : Equiv.Perm Carrier1508) x ∧
      q y = (g : Equiv.Perm Carrier1508) y}

def generatedPair1508
    (T : Subgroup (Equiv.Perm Carrier1508)) :
    Subgroup (Equiv.Perm Carrier1508) :=
  Subgroup.closure
    ((standardRegularGroup1508 : Set (Equiv.Perm Carrier1508)) ∪
      (T : Set (Equiv.Perm Carrier1508)))

def alternatingTranslationProfile1508 (ε : Fiber1508ˣ) :
    AffineProfile1508 :=
  (fun _ => 1,
    fun j => (ε : Fiber1508) * ((j.val % 2 : ℕ) : Fiber1508))

def equalGroupProfile1508 (p : AffineProfile1508) : Prop :=
  normalizedProfile1508 p ∧
    ∃ ε : Fiber1508ˣ, p = alternatingTranslationProfile1508 ε

def pairTranslationRow1508
    (v : Outer1508 → Fiber1508) (j d : Outer1508) :
    Fiber1508 × Fiber1508 :=
  (v j, v (j + d))

def sourcePairRow1508 (j d : Outer1508) :
    Fiber1508 × Fiber1508 :=
  pairTranslationRow1508 (fun _ => 1) j d

def targetPairRow1508
    (h : Outer1508 → Fiber1508ˣ) (j d : Outer1508) :
    Fiber1508 × Fiber1508 :=
  pairTranslationRow1508
    (fun k => ((h k : Fiber1508)⁻¹)) j d

def fullPairTranslationPlane1508
    (u v : Fiber1508 × Fiber1508) : Prop :=
  LinearIndependent Fiber1508 ![u, v] ∧
    Submodule.span Fiber1508 ({u, v} : Set (Fiber1508 × Fiber1508)) = ⊤

/-- The normalized affine-chart count and source-side global normalization. -/
def claim37959 : Prop :=
  Nat.card AffineProfile1508 = 20 ^ 8 ∧
    Nat.card {p : AffineProfile1508 // normalizedProfile1508 p} = 20 ^ 7 ∧
    ∀ raw : AffineProfile1508,
      ∃ normalized : AffineProfile1508,
        sourceSideNormalization1508 raw normalized ∧
          conjugatedSubgroup1508 (profileChart1508 normalized)
              standardRegularGroup1508 =
            conjugatedSubgroup1508 (profileChart1508 raw)
              standardRegularGroup1508

/-- Every normalized affine chart is in the ordered binary two-closure,
except when the two regular copies are equal. -/
def claim37960 : Prop :=
  ∀ (H : Equiv.Perm Carrier1508)
    (T : Subgroup (Equiv.Perm Carrier1508)),
    (∃ p : AffineProfile1508,
      normalizedProfile1508 p ∧ H = profileChart1508 p) →
    T = conjugatedSubgroup1508 H standardRegularGroup1508 →
    let X := generatedPair1508 T
    H ∈ orderedTwoClosure1508 X ∨
      T = standardRegularGroup1508

/-- The four normalized equal-group profiles and the eighty raw profiles
obtained after restoring one global affine normalizer. -/
def claim37961 : Prop :=
  Nat.card {p : AffineProfile1508 // equalGroupProfile1508 p} = 4 ∧
    (∀ ε : Fiber1508ˣ,
      (alternatingTranslationProfile1508 ε).1 0 = 1 ∧
      (alternatingTranslationProfile1508 ε).2 0 = 0 ∧
      conjugatedSubgroup1508
          (profileChart1508 (alternatingTranslationProfile1508 ε))
          standardRegularGroup1508 = standardRegularGroup1508) ∧
    (∀ p : AffineProfile1508,
      normalizedProfile1508 p →
      conjugatedSubgroup1508 (profileChart1508 p)
          standardRegularGroup1508 = standardRegularGroup1508 ↔
        ∃ ε : Fiber1508ˣ,
          p = alternatingTranslationProfile1508 ε) ∧
    Nat.card {p : AffineProfile1508 //
      conjugatedSubgroup1508 (profileChart1508 p)
          standardRegularGroup1508 = standardRegularGroup1508} = 80

/-- Nonperiodicity of the normalized slope word supplies the full pair
translation plane. -/
def claim37962 : Prop :=
  ∀ (p : AffineProfile1508) (d : Outer1508),
    normalizedProfile1508 p →
    d ≠ 0 →
    (∀ j : Outer1508,
      p.1 (j + d) ≠ p.1 j →
      fullPairTranslationPlane1508
        (sourcePairRow1508 j d)
        (targetPairRow1508 p.1 j d)) ∧
    (¬ ∀ k : Outer1508, p.1 (k + d) = p.1 k) →
    ∃ j : Outer1508,
      p.1 (j + d) ≠ p.1 j ∧
      fullPairTranslationPlane1508
        (sourcePairRow1508 j d)
        (targetPairRow1508 p.1 j d)

end
end MathlibPlus.Open.ResearchFormalization.R1508

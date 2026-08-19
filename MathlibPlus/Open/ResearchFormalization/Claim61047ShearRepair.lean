import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Claim61047

noncomputable section

open Classical

/-- The span of the mixed second differences occurring in the shear repair. -/
def secondDifferenceSpan {s d : ℕ} {O : Type*} [AddGroup O]
    (F : ((Fin s → ZMod 2) × O) → (Fin d → ZMod 2))
    (b : (Fin s → ZMod 2) × O) :
    Submodule (ZMod 2) (Fin d → ZMod 2) :=
  Submodule.span (ZMod 2)
    (Set.range (fun xa :
        ((Fin s → ZMod 2) × O) × ((Fin s → ZMod 2) × O) =>
      let x := xa.1
      let a := xa.2
      F x + F (x + a) + F (x + b) + F (x + a + b)))

def shearFunction {s d : ℕ} {O : Type*} [AddGroup O]
    (F : ((Fin s → ZMod 2) × O) → (Fin d → ZMod 2))
    (p : (Fin d → ZMod 2) × ((Fin s → ZMod 2) × O)) :
    (Fin d → ZMod 2) × ((Fin s → ZMod 2) × O) :=
  (p.1 + F p.2, p.2)

def qFRealizes {s d : ℕ} {O : Type*} [AddGroup O]
    (F : ((Fin s → ZMod 2) × O) → (Fin d → ZMod 2))
    (q : Equiv.Perm ((Fin d → ZMod 2) × ((Fin s → ZMod 2) × O))) : Prop :=
  ∀ p, q p = shearFunction F p

def regularTranslationSet (Ω : Type*) [AddGroup Ω] :
    Set (Equiv.Perm Ω) :=
  Set.range (Equiv.addRight : Ω → Equiv.Perm Ω)

def conjugatedPermutationSet {Ω : Type*}
    (q : Equiv.Perm Ω) (R : Set (Equiv.Perm Ω)) :
    Set (Equiv.Perm Ω) :=
  Set.image (fun g => q⁻¹ * g * q) R

def orderedTwoClosure {Ω : Type*}
    (K : Set (Equiv.Perm Ω)) : Set (Equiv.Perm Ω) :=
  {q | ∀ x y, ∃ g, g ∈ K ∧ q x = g x ∧ q y = g y}

def unorderedOrbital {Ω : Type*}
    (K : Set (Equiv.Perm Ω)) (s : Finset Ω) : Set (Finset Ω) :=
  {t | t.card = 2 ∧ ∃ g, g ∈ K ∧ t = s.map g.toEmbedding}

def unorderedTwoClosure {Ω : Type*}
    (K : Set (Equiv.Perm Ω)) : Set (Equiv.Perm Ω) :=
  {q | ∀ s, s.card = 2 → ∀ t,
    t ∈ unorderedOrbital K s ↔
      t.map q.toEmbedding ∈ unorderedOrbital K s}

def claim61047 : Prop :=
  ∀ (s d : ℕ) (O : Type*) [Fintype O] [AddGroup O],
    (∃ n : ℕ, Fintype.card O = 2 * n + 1) →
    d + s ≤ 5 →
    ∀ F : ((Fin s → ZMod 2) × O) → (Fin d → ZMod 2),
      F (0 : (Fin s → ZMod 2) × O) =
        (0 : Fin d → ZMod 2) →
      ∃ L : ((Fin s → ZMod 2) × O) →+
          (Fin d → ZMod 2),
        (∀ b, F b + L b ∈ secondDifferenceSpan F b) ∧
        ∃ q : Equiv.Perm
            ((Fin d → ZMod 2) × ((Fin s → ZMod 2) × O)),
          qFRealizes F q ∧
          let R := regularTranslationSet
            ((Fin d → ZMod 2) × ((Fin s → ZMod 2) × O))
          let T := conjugatedPermutationSet q R
          let G := Subgroup.closure (R ∪ T)
          (∃ c,
            c ∈ orderedTwoClosure (G : Set (Equiv.Perm
              ((Fin d → ZMod 2) × ((Fin s → ZMod 2) × O)))) ∧
            conjugatedPermutationSet c R = T ∧
            c ∈ unorderedTwoClosure (G : Set (Equiv.Perm
              ((Fin d → ZMod 2) × ((Fin s → ZMod 2) × O)))))

end
end MathlibPlus.Open.ResearchFormalization.Claim61047

import Mathlib

namespace MathlibPlus.Open

namespace NormalizedVoltageShearAffine

def voltageTranslation {A V : Type*} [AddGroup A] [AddGroup V]
    (c : A) (r : V) : Equiv.Perm (A × V) :=
  Equiv.prodCongr (Equiv.addRight c) (Equiv.addRight r)

def voltageShearFiber {A V : Type*} [AddGroup A]
    (F : V → A) : (v : V) × A ≃ (v : V) × A :=
  Equiv.sigmaCongrRight (fun v => Equiv.addRight (F v))

def voltageShear {A V : Type*} [AddGroup A] [AddGroup V]
    (F : V → A) : Equiv.Perm (A × V) :=
  (((Equiv.prodComm A V).trans (Equiv.sigmaEquivProd V A).symm).trans
      (voltageShearFiber F)).trans
    ((Equiv.sigmaEquivProd V A).trans (Equiv.prodComm V A))

def voltageDelta {A V : Type*} [AddGroup A] [AddGroup V]
    (F : V → A) (r : V) : V → A :=
  fun v => F (v + r) - F v

def voltageTranslateFunction {A V : Type*} [AddGroup A] [AddGroup V]
    (w : V) (h : V → A) : V → A :=
  fun v => h (v + w)

def voltageConstantFunctions {A V : Type*} [AddGroup A] : Set (V → A) :=
  Set.range (fun a : A => fun _ : V => a)

def voltageTranslatedDifferences {A V : Type*} [AddGroup A] [AddGroup V]
    (F : V → A) : Set (V → A) :=
  Set.range (fun wr : V × V => voltageTranslateFunction wr.1 (voltageDelta F wr.2))

def voltageM {A V : Type*} [AddGroup A] [AddGroup V]
    (F : V → A) : AddSubgroup (V → A) :=
  AddSubgroup.closure (voltageConstantFunctions (A := A) (V := V) ∪
    voltageTranslatedDifferences F)

def voltageQ {A V : Type*} [AddGroup A] [AddGroup V]
    (F : V → A) : AddSubgroup (V → A) :=
  voltageM F ⊓
    AddSubgroup.comap (Pi.evalAddMonoidHom (fun _ : V => A) 0)
      (⊥ : AddSubgroup A)

def voltageH {A V : Type*} [AddGroup A] [AddGroup V]
    (F : V → A) (v : V) : AddSubgroup A :=
  AddSubgroup.map (Pi.evalAddMonoidHom (fun _ : V => A) v) (voltageQ F)

def voltageConjugateSet {G : Type*} [Group G]
    (S : Set G) (q : G) : Set G :=
  (fun g => q * g * q⁻¹) '' S

def voltageShearCandidate {A V : Type*} [AddGroup A] [AddGroup V]
    (u : A ≃+ A) (s : V → A) (B : Equiv.Perm V) : Equiv.Perm (A × V) :=
  (((Equiv.prodCongr u (Equiv.refl V)).trans (voltageShear s)).trans
    (Equiv.prodCongr (Equiv.refl A) B))

def voltageOrbitSet {A V : Type*} [AddGroup A] [AddGroup V]
    (P : Set (Equiv.Perm (A × V))) (x : A × V) : Set (A × V) :=
  {y | ∃ g ∈ P, g x = y}

def voltagePointStabilizer {A V : Type*} [AddGroup A] [AddGroup V]
    (Y : Subgroup (Equiv.Perm (A × V))) (x : A × V) : Set (Equiv.Perm (A × V)) :=
  {g | g ∈ Y ∧ g x = x}

def voltageQuotientMap {A : Type*} [AddGroup A]
    (H : AddSubgroup A) : A → A ⧸ H :=
  QuotientAddGroup.mk (s := H)

def voltageLeftCoset {A V : Type*} [AddGroup A] [AddGroup V]
    (R : Set (Equiv.Perm (A × V))) (x : Equiv.Perm (A × V)) :
    Set (Equiv.Perm (A × V)) :=
  (fun g => g * x) '' R

def normalizedVoltageShearAffineCandidatesReduceExactlyToShiftCongruences : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (A V : Type*)
    [Fintype A] [AddCommGroup A]
    [Fintype V] [AddCommGroup V]
    [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
    (F : V → A),
    F 0 = 0 →
      let Ω := A × V
      let ρ : A → V → Equiv.Perm Ω :=
        fun c r => voltageTranslation c r
      let q_F : Equiv.Perm Ω := voltageShear F
      let t : A → V → Equiv.Perm Ω :=
        fun c r => q_F * ρ c r * q_F⁻¹
      let R : Set (Equiv.Perm Ω) := Set.range (fun cr : A × V => ρ cr.1 cr.2)
      let T : Set (Equiv.Perm Ω) := Set.range (fun cr : A × V => t cr.1 cr.2)
      let Y_F : Subgroup (Equiv.Perm Ω) := Subgroup.closure (R ∪ T)
      let P : Set (Equiv.Perm Ω) := voltagePointStabilizer Y_F (0, 0)
      let H_F : V → AddSubgroup A := voltageH F
      (∀ c r a v, ρ c r (a, v) = (a + c, v + r)) ∧
      (∀ a v, q_F (a, v) = (a + F v, v)) ∧
      (∀ c r a v,
        t c r (a, v) = (a + c + F (v + r) - F v, v + r)) ∧
      T = voltageConjugateSet R q_F ∧
      (∀ a v,
        voltageOrbitSet P (a, v) =
          (fun h : A => (a + h, v)) '' (H_F v : Set A)) ∧
      (∀ a v,
        Set.image Prod.snd (voltageOrbitSet P (a, v)) = ({v} : Set V)) ∧
      (H_F 0 : Set A) = ({0} : Set A) ∧
      (∀ (u : A ≃+ A) (s : V → A) (B : Equiv.Perm V),
        (∀ a v,
          Set.image (voltageShearCandidate u s B)
            (voltageOrbitSet P (a, v)) = voltageOrbitSet P (a, v)) ↔
          (B = Equiv.refl V ∧ u = AddEquiv.refl A ∧
            ∀ v, s v ∈ H_F v)) ∧
      (∀ [Module (ZMod p) A] (L : V →ₗ[ZMod p] A),
        (∀ a v,
          Set.image
              (voltageShearCandidate (AddEquiv.refl A)
                (fun w => F w + L w) (Equiv.refl V))
              (voltageOrbitSet P (a, v)) = voltageOrbitSet P (a, v)) ↔
            (∀ v, F v + L v ∈ H_F v)) ∧
      (∀ [Module (ZMod p) A] (L : V →ₗ[ZMod p] A),
        (∀ v, F v + L v ∈ H_F v) ↔
          (∀ v,
            voltageQuotientMap (H_F v) (F v + L v) = 0)) ∧
      (∀ x y : Ω,
        ∃! g, g ∈ R ∧ g x = y) ∧
      (∀ x : Equiv.Perm Ω,
        (∃! y,
          y ∈ voltageLeftCoset R x ∧ y (0, 0) = (0, 0)) ∧
        (∀ y,
          y ∈ voltageLeftCoset R x → y (0, 0) = (0, 0) →
            voltageConjugateSet R y = voltageConjugateSet R x))

end NormalizedVoltageShearAffine

end MathlibPlus.Open

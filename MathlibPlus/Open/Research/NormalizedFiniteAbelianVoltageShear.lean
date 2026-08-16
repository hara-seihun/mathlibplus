import Mathlib

namespace MathlibPlus.Open

section NormalizedFiniteAbelianVoltageShear

variable {p : ℕ} [Fact p.Prime]
variable {A V : Type*}
variable [Fintype A] [AddCommGroup A]
variable [AddCommGroup V] [Module (ZMod p) V]
variable [FiniteDimensional (ZMod p) V]

def voltageShear (f : V → A) : Equiv.Perm (A × V) :=
  let swap : A × V ≃ V × A := Equiv.prodComm A V
  let sigma : (_v : V) × A ≃ V × A := Equiv.sigmaEquivProd V A
  let fibre : (_v : V) × A ≃ (_v : V) × A :=
    Equiv.sigmaCongrRight (fun v => Equiv.addRight (f v))
  swap.trans (sigma.symm.trans (fibre.trans (sigma.trans swap.symm)))

def voltageRho (c : A) (r : V) : Equiv.Perm (A × V) :=
  Equiv.addRight (c, r)

def voltageTau (w : V) (h : V → A) : V → A :=
  fun v => h (v + w)

def voltageDelta (f : V → A) (r : V) : V → A :=
  fun v => f (v + r) - f v

def voltageConstantFunctions : Set (V → A) :=
  {h | ∃ c : A, h = fun _ => c}

def voltageGenerators (f : V → A) : Set (V → A) :=
  voltageConstantFunctions ∪
    {h | ∃ (r w : V), h = voltageTau w (voltageDelta f r)}

def voltageM (f : V → A) : AddSubgroup (V → A) :=
  AddSubgroup.closure (voltageGenerators f)

def voltageQ (f : V → A) : AddSubgroup (V → A) :=
  AddSubgroup.comap (Pi.evalAddMonoidHom (fun _ : V => A) 0)
      (⊥ : AddSubgroup A) ⊓ voltageM f

def voltageH (f : V → A) (v : V) : AddSubgroup A :=
  AddSubgroup.map (Pi.evalAddMonoidHom (fun _ : V => A) v) (voltageQ f)

def voltageT (f : V → A) (c : A) (r : V) : Equiv.Perm (A × V) :=
  (voltageShear f).symm.trans ((voltageRho c r).trans (voltageShear f))

def voltageRSet : Set (Equiv.Perm (A × V)) :=
  Set.range (fun z : A × V => voltageRho z.1 z.2)

def voltageTSet (f : V → A) : Set (Equiv.Perm (A × V)) :=
  Set.range (fun z : A × V => voltageT f z.1 z.2)

def voltageYElement (m : V → A) (r : V) : Equiv.Perm (A × V) :=
  (voltageShear m).trans (voltageRho 0 r)

def voltageYGroup (f : V → A) : Subgroup (Equiv.Perm (A × V)) :=
  Subgroup.closure (voltageRSet ∪ voltageTSet f)

def voltageCandidateSet (f : V → A) : Set (Equiv.Perm (A × V)) :=
  {g | ∃ (m : V → A) (r : V), m ∈ voltageM f ∧ g = voltageYElement m r}

def voltagePointStabilizerSet (f : V → A) : Set (Equiv.Perm (A × V)) :=
  {g | g ∈ voltageYGroup f ∧ g (0, 0) = (0, 0)}

def voltagePointStabilizerCandidate (f : V → A) : Set (Equiv.Perm (A × V)) :=
  {g | ∃ (m : V → A), m ∈ voltageQ f ∧ g = voltageYElement m 0}

def voltagePointStabilizerOrbit (f : V → A) (a : A) (v : V) : Set (A × V) :=
  {x | ∃ g : Equiv.Perm (A × V),
    g ∈ voltageYGroup f ∧ g (0, 0) = (0, 0) ∧ x = g (a, v)}

def voltageEvaluationCoset (f : V → A) (a : A) (v : V) : Set (A × V) :=
  {x | ∃ h : A, h ∈ voltageH f v ∧ x = (a + h, v)}

def voltageVectorFibreSpan
    (moduleA : Module (ZMod p) A) (f : V → A) : Prop :=
  letI : Module (ZMod p) A := moduleA
  voltageM f = (Submodule.span (ZMod p) (voltageGenerators f)).toAddSubgroup

def normalizedFiniteAbelianVoltageShearImageExactStabilizerOrbits
    (f : V → A) (_hF0 : f 0 = 0) : Prop :=
  (∀ (c : A) (r : V) (a : A) (v : V),
      voltageRho c r (a, v) = (a + c, v + r)) ∧
  (∀ (a : A) (v : V),
      voltageShear f (a, v) = (a + f v, v)) ∧
  (∀ (c : A) (r : V) (a : A) (v : V),
      voltageT f c r (a, v) = (a + c + f (v + r) - f v, v + r)) ∧
  voltageTSet f =
    {g | ∃ h : Equiv.Perm (A × V), h ∈ voltageRSet ∧
      g = (voltageShear f).symm.trans (h.trans (voltageShear f))} ∧
  (∀ (x y : A × V), ∃! g : Equiv.Perm (A × V),
      g ∈ voltageRSet ∧ g x = y) ∧
  (∀ (m : V → A) (r : V) (a : A) (v : V),
      voltageYElement m r (a, v) = (a + m v, v + r)) ∧
  (voltageYGroup f : Set (Equiv.Perm (A × V))) = voltageCandidateSet f ∧
  (∀ (w : V) (m : V → A), m ∈ voltageM f → voltageTau w m ∈ voltageM f) ∧
  (∀ (m n : V → A) (r s : V), m ∈ voltageM f → n ∈ voltageM f →
      (voltageYElement m r).trans (voltageYElement n s) =
        voltageYElement (m + voltageTau r n) (r + s)) ∧
  (∀ (m n : V → A) (r s : V),
      voltageYElement m r = voltageYElement n s → m = n ∧ r = s) ∧
  voltagePointStabilizerSet f = voltagePointStabilizerCandidate f ∧
  (∀ (a : A) (v : V),
      voltagePointStabilizerOrbit f a v = voltageEvaluationCoset f a v) ∧
  (∀ (moduleA : Module (ZMod p) A), voltageVectorFibreSpan moduleA f)

end NormalizedFiniteAbelianVoltageShear

end MathlibPlus.Open

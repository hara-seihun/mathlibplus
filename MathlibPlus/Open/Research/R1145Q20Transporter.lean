-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is not built and MathlibPlus.lean does not import it. See unverified.txt.
import Mathlib

noncomputable section

namespace MathlibPlus.Open.Research.R1145Q20Transporter

abbrev Q20 := QuaternionGroup 5
abbrev Coordinate20 := ZMod 5 × Fin 4

def succFour (i : Fin 4) : Fin 4 :=
  ⟨(i.val + 1) % 4, Nat.mod_lt _ (by decide)⟩

def finitePerm (f : Coordinate20 → Coordinate20)
    (hf : Function.Bijective f) : Equiv.Perm Coordinate20 :=
  Equiv.ofBijective f hf

def q20X1Fun (z : Coordinate20) : Coordinate20 :=
  (z.1 + (if z.2.val % 2 = 0 then 1 else -1), z.2)

def q20Y1Fun (z : Coordinate20) : Coordinate20 :=
  (z.1, succFour z.2)

def q20X2Fun (z : Coordinate20) : Coordinate20 :=
  (z.1 + (match z.2.val with
    | 0 => 1
    | 1 => 2
    | 2 => 4
    | _ => 3), z.2)

def q20Y2Fun (z : Coordinate20) : Coordinate20 :=
  (3 * z.1, succFour z.2)

def q20X1 : Equiv.Perm Coordinate20 :=
  finitePerm q20X1Fun (by native_decide)

def q20Y1 : Equiv.Perm Coordinate20 :=
  finitePerm q20Y1Fun (by native_decide)

def q20X2 : Equiv.Perm Coordinate20 :=
  finitePerm q20X2Fun (by native_decide)

def q20Y2 : Equiv.Perm Coordinate20 :=
  finitePerm q20Y2Fun (by native_decide)

def ambient20Generator0Fun (z : Coordinate20) : Coordinate20 :=
  ((match z.2.val with
      | 0 => 1 - z.1
      | 1 => 2 - z.1
      | 2 => 2 - z.1
      | _ => 1 - z.1), succFour z.2)

def ambient20Generator1Fun (z : Coordinate20) : Coordinate20 :=
  ((match z.2.val with
      | 0 => 2 * z.1 + 1
      | 1 => 2 * z.1 + 1
      | 2 => 2 * z.1 + 3
      | _ => 2 * z.1), succFour z.2)

def ambient20Generator2Fun (z : Coordinate20) : Coordinate20 :=
  ((match z.2.val with
      | 0 => 3 - 2 * z.1
      | 1 => 3 - 2 * z.1
      | 2 => 4 - 2 * z.1
      | _ => -2 * z.1), succFour z.2)

def ambient20Generator0 : Equiv.Perm Coordinate20 :=
  finitePerm ambient20Generator0Fun (by native_decide)

def ambient20Generator1 : Equiv.Perm Coordinate20 :=
  finitePerm ambient20Generator1Fun (by native_decide)

def ambient20Generator2 : Equiv.Perm Coordinate20 :=
  finitePerm ambient20Generator2Fun (by native_decide)

def ambient20T102 : Subgroup (Equiv.Perm Coordinate20) :=
  Subgroup.closure
    ({ambient20Generator0, ambient20Generator1, ambient20Generator2} :
      Set (Equiv.Perm Coordinate20))

def regularOn (H : Subgroup (Equiv.Perm Coordinate20)) : Prop :=
  ∀ x y : Coordinate20, ∃! h : H, (h : Equiv.Perm Coordinate20) x = y

def isRegularQ20 (H : Subgroup (Equiv.Perm Coordinate20)) : Prop :=
  regularOn H ∧ Nonempty (H ≃* Q20)

def conjugates (u : Equiv.Perm Coordinate20)
    (H K : Subgroup (Equiv.Perm Coordinate20)) : Prop :=
  ∀ g : Equiv.Perm Coordinate20,
    g ∈ K ↔ ∃ h : H, g = u⁻¹ * (h : Equiv.Perm Coordinate20) * u

def ambientConjugate (H K : Subgroup (Equiv.Perm Coordinate20)) : Prop :=
  ∃ u : ambient20T102, conjugates (u : Equiv.Perm Coordinate20) H K

def regularActionConjugator (H K : Subgroup (Equiv.Perm Coordinate20))
    (u : Equiv.Perm Coordinate20) : Prop :=
  conjugates u H K

def orderedOrbital (x y : Coordinate20) : Set (Coordinate20 × Coordinate20) :=
  {p | ∃ g : ambient20T102,
    p = ((g : Equiv.Perm Coordinate20) x, (g : Equiv.Perm Coordinate20) y)}

def pairMap (u : Equiv.Perm Coordinate20)
    (p : Coordinate20 × Coordinate20) : Coordinate20 × Coordinate20 :=
  (u p.1, u p.2)

def ambientOrbitalSet : Set (Set (Coordinate20 × Coordinate20)) :=
  {O | ∃ x y : Coordinate20, O = orderedOrbital x y}

def preservesEveryAmbientOrbital (u : Equiv.Perm Coordinate20) : Prop :=
  ∀ O : Set (Coordinate20 × Coordinate20), O ∈ ambientOrbitalSet →
    Set.image (pairMap u) O = O

def normalizesAmbient (u : Equiv.Perm Coordinate20) : Prop :=
  ∀ g : Equiv.Perm Coordinate20,
    g ∈ ambient20T102 ↔ u⁻¹ * g * u ∈ ambient20T102

def q20ClassPair (H₁ H₂ : Subgroup (Equiv.Perm Coordinate20)) : Prop :=
  isRegularQ20 H₁ ∧
    isRegularQ20 H₂ ∧
    ¬ ambientConjugate H₁ H₂ ∧
    (∀ H : Subgroup (Equiv.Perm Coordinate20), isRegularQ20 H →
      ambientConjugate H H₁ ∨ ambientConjugate H H₂) ∧
    Nat.card {u : Equiv.Perm Coordinate20 //
      regularActionConjugator H₁ H₂ u} = 800 ∧
    Nat.card {u : Equiv.Perm Coordinate20 //
      regularActionConjugator H₁ H₂ u ∧ preservesEveryAmbientOrbital u} = 400

def claim41291 : Prop :=
  Fintype.card Coordinate20 = 20 ∧
    Nat.card ambient20T102 = 400 ∧
    Nat.card {H : Subgroup (Equiv.Perm Coordinate20) // isRegularQ20 H} = 10 ∧
    Nat.card {O : Set (Coordinate20 × Coordinate20) // O ∈ ambientOrbitalSet} = 5 ∧
    ∃ H₁ H₂ : Subgroup (Equiv.Perm Coordinate20), q20ClassPair H₁ H₂

def q20SigmaFun (z : Coordinate20) : Coordinate20 :=
  ((2 : ZMod 5) ^ z.2.val * z.1, z.2)

def q20Sigma : Equiv.Perm Coordinate20 :=
  finitePerm q20SigmaFun (by native_decide)

def q20LayerUnits : Prop :=
  (∀ y : ZMod 5, q20Sigma (y, (0 : Fin 4)) = (y, (0 : Fin 4))) ∧
    (∀ y : ZMod 5, q20Sigma (y, (1 : Fin 4)) = (2 * y, (1 : Fin 4))) ∧
      (∀ y : ZMod 5, q20Sigma (y, (2 : Fin 4)) = (4 * y, (2 : Fin 4))) ∧
        (∀ y : ZMod 5, q20Sigma (y, (3 : Fin 4)) = (3 * y, (3 : Fin 4)))

def q20Class1 : Subgroup (Equiv.Perm Coordinate20) :=
  Subgroup.closure ({q20X1, q20Y1} : Set (Equiv.Perm Coordinate20))

def q20Class2 : Subgroup (Equiv.Perm Coordinate20) :=
  Subgroup.closure ({q20X2, q20Y2} : Set (Equiv.Perm Coordinate20))

/-- Claim 41292: the displayed quotient switch is an orbital-preserving
binary-2-closure transporter for the two regular `Q₂₀` classes. -/
def claim41292 : Prop :=
  q20ClassPair q20Class2 q20Class1 ∧
    regularActionConjugator q20Class2 q20Class1 q20Sigma ∧
    preservesEveryAmbientOrbital q20Sigma ∧
    q20LayerUnits ∧
    ¬ q20Sigma ∈ ambient20T102 ∧
    ¬ normalizesAmbient q20Sigma

end MathlibPlus.Open.Research.R1145Q20Transporter

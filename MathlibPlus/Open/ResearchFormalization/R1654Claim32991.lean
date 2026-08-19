import MathlibPlus.Open.ProjectsResearch.CayleyCIClaims
import MathlibPlus.GroupTheory.TwoClosure

namespace MathlibPlus.Open.ResearchFormalization.R1654

open MathlibPlus.Open
open MathlibPlus.GroupTheory.TwoClosure

abbrev Local7 := Equiv.Perm (ZMod 7)
abbrev BasePoint := ZMod 7 × ZMod 8

/-- The regular seven-cycle used in every local derivative. -/
def localSevenCycle : Local7 := Equiv.addRight 1

def conjugateLocalPermutation (s g : Local7) : Local7 :=
  s⁻¹ * g * s

def localPrimeCycleDerivative (sigma : Local7) : Local7 :=
  localSevenCycle⁻¹ *
    conjugateLocalPermutation sigma localSevenCycle

def localSynchronousDerivative (sigma : Local7) (i : Fin 7) : Local7 :=
  conjugateLocalPermutation (localSevenCycle ^ (i : ℕ))
    (localPrimeCycleDerivative sigma)

def localDerivativeClosure (sigma : Local7) : Subgroup Local7 :=
  Subgroup.closure (Set.range (localSynchronousDerivative sigma))

def localCyclicSeven : Subgroup Local7 :=
  Subgroup.closure ({localSevenCycle} : Set Local7)

/-- The affine local charts in `AGL(1,7)`. -/
def affineLocal (f : Local7) : Prop :=
  ∃ a : (ZMod 7)ˣ, ∃ b : ZMod 7,
    ∀ x : ZMod 7, f x = (a : ZMod 7) * x + b

def nonzeroTranslation (f : Local7) : Prop :=
  ∃ b : ZMod 7, b ≠ 0 ∧ ∀ x : ZMod 7, f x = x + b

def nontrivialMultiplier (f : Local7) : Prop :=
  ∃ a : (ZMod 7)ˣ, a ≠ 1 ∧ ∃ b : ZMod 7,
    ∀ x : ZMod 7, f x = (a : ZMod 7) * x + b

/-- The exact two local derivative-closure alternatives for a nonidentity
affine chart. -/
def affineDerivativeClassification (f : Local7) : Prop :=
  (nonzeroTranslation f ∧ localDerivativeClosure f = ⊥) ∨
    (nontrivialMultiplier f ∧
      localDerivativeClosure f = localCyclicSeven)

/-- Seven points for the projective action of `GL(3,2)`, which is
`PSL₃(2)` in this characteristic. -/
abbrev BinaryThree := Fin 3 → ZMod 2

def projectivePoints : Fin 7 → BinaryThree :=
  ![
    ![1, 0, 0],
    ![0, 1, 0],
    ![0, 0, 1],
    ![1, 1, 0],
    ![1, 0, 1],
    ![0, 1, 1],
    ![1, 1, 1]
  ]

def projectiveLinearImage (g : Local7) : Prop :=
  ∃ L : BinaryThree ≃ₗ[ZMod 2] BinaryThree,
    ∀ i : Fin 7, projectivePoints (g i) = L (projectivePoints i)

/-- A local permutation is `PSL₃(2)`-type when its derivative closure is the
projective linear group on these seven marked points. -/
def psl32Type (sigma : Local7) : Prop :=
  ∀ g : Local7, g ∈ localDerivativeClosure sigma ↔ projectiveLinearImage g

/-- The analogous `A₇` local type. -/
def a7Type (tau : Local7) : Prop :=
  localDerivativeClosure tau = alternatingGroup (Fin 7)

/-- The synchronous derivative subgroup on the three local factors. -/
def synchronousDerivativeProduct
    (alpha sigma tau : Local7) :
    Subgroup (Local7 × Local7 × Local7) :=
  Subgroup.closure (Set.range (fun i : Fin 7 =>
    (localSynchronousDerivative alpha i,
      localSynchronousDerivative sigma i,
      localSynchronousDerivative tau i)))

/-- Full direct-product splitting of the three local derivative factors. -/
def fullDerivativeProduct
    (alpha sigma tau : Local7) : Prop :=
  ∀ z : Local7 × Local7 × Local7,
    z ∈ synchronousDerivativeProduct alpha sigma tau ↔
      z.1 ∈ localDerivativeClosure alpha ∧
        z.2.1 ∈ localDerivativeClosure sigma ∧
          z.2.2 ∈ localDerivativeClosure tau

/-- The literal blockwise chart on `E(C₇,8)`, with identity on the other
five outer blocks. -/
def threeBlockChart
    (alpha sigma tau : Local7) (i j k : ZMod 8) :
    Equiv.Perm BasePoint :=
  Equiv.prodCongrLeft (fun b =>
    if b = i then alpha else
      if b = j then sigma else
        if b = k then tau else Equiv.refl (ZMod 7))

/-- The standard regular copy, written directly from the displayed
`E(C₇,8)` multiplication. -/
def standardTranslationSet : Set (Equiv.Perm BasePoint) :=
  {f | ∃ g : BasePoint, ∀ x : BasePoint,
    f x = eMul 7 8 g x}

def standardRegularCopy : Subgroup (Equiv.Perm BasePoint) :=
  Subgroup.closure standardTranslationSet

/-- Conjugation of a permutation subgroup by a chart. -/
def conjugateCopy {Ω : Type*}
    (f : Equiv.Perm Ω) (R : Subgroup (Equiv.Perm Ω)) :
    Subgroup (Equiv.Perm Ω) :=
  Subgroup.map (MulAut.conj f.symm).toMonoidHom R

def generatedCopy {Ω : Type*}
    (R T : Subgroup (Equiv.Perm Ω)) : Subgroup (Equiv.Perm Ω) :=
  Subgroup.closure ((R : Set (Equiv.Perm Ω)) ∪ (T : Set (Equiv.Perm Ω)))

/-- The pointwise prime-layer carrier: the added prime coordinate is present
in the regular copy, while the lifted chart acts fibrewise on the `q=7`
component. -/
abbrev InflatedPoint (r : ℕ) := ZMod r × BasePoint

def inflatedHallCycle (r : ℕ) : Equiv.Perm (InflatedPoint r) :=
  Equiv.addRight ((1 : ZMod r), ((1 : ZMod 7), (0 : ZMod 8)))

def inflatedOuterInversion (r : ℕ) : Equiv.Perm (InflatedPoint r) :=
  (Equiv.prodCongr (Equiv.neg (ZMod r))
      (Equiv.prodCongr (Equiv.neg (ZMod 7)) (Equiv.refl (ZMod 8)))).trans
    (Equiv.addRight ((0 : ZMod r), ((0 : ZMod 7), (1 : ZMod 8))))

def inflatedRegularCopy (r : ℕ) :
    Subgroup (Equiv.Perm (InflatedPoint r)) :=
  Subgroup.closure
    ({inflatedHallCycle r, inflatedOuterInversion r} :
      Set (Equiv.Perm (InflatedPoint r)))

def inflatedChart (r : ℕ) (f : Equiv.Perm BasePoint) :
    Equiv.Perm (InflatedPoint r) :=
  Equiv.prodCongr (Equiv.refl (ZMod r)) f

def inflatedTargetCopy (r : ℕ) (f : Equiv.Perm BasePoint) :
    Subgroup (Equiv.Perm (InflatedPoint r)) :=
  conjugateCopy (inflatedChart r f) (inflatedRegularCopy r)

def inflatedGeneratedCopy (r : ℕ) (f : Equiv.Perm BasePoint) :
    Subgroup (Equiv.Perm (InflatedPoint r)) :=
  generatedCopy (inflatedRegularCopy r) (inflatedTargetCopy r f)

/-- Claim 32991: every exact affine/`PSL₃(2)`/`A₇` three-block chart has a
full local derivative product and lies in the generated ordered two-closure;
the same ordered-closure conclusion holds for every distinct odd-prime
pointwise inflation. -/
def claim32991 : Prop :=
  ∀ (alpha sigma tau : Local7) (i j k : ZMod 8),
    alpha ≠ 1 → affineLocal alpha →
      ¬ affineLocal sigma → psl32Type sigma →
        ¬ affineLocal tau → a7Type tau →
          i ≠ j → i ≠ k → j ≠ k →
            let F := threeBlockChart alpha sigma tau i j k
            let R := standardRegularCopy
            let T := conjugateCopy F R
            let X := generatedCopy R T
            affineDerivativeClassification alpha ∧
              fullDerivativeProduct alpha sigma tau ∧
                inTwoClosure X F ∧
                  ∀ r : ℕ, Nat.Prime r → Odd r → r ≠ 7 →
                    let F' := inflatedChart r F
                    let R' := inflatedRegularCopy r
                    let T' := inflatedTargetCopy r F
                    let X' := generatedCopy R' T'
                    inTwoClosure X' F'

end MathlibPlus.Open.ResearchFormalization.R1654

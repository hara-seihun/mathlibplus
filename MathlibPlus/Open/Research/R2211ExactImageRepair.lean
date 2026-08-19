import MathlibPlus.Open.Research.R2211

open scoped BigOperators

namespace MathlibPlus.Open.Research.R2211ExactImageRepair

open MathlibPlus.Open.Research.R2211

noncomputable section

abbrev Ω := F3 × H

def xMap : H → H := fun h =>
  let i := coordI h
  let j := coordJ h
  let a := coordA h
  let b := coordB h
  let c := coordC h
  (i, j, a + i, b + j, c)

def yMap : H → H := fun h =>
  let i := coordI h
  let j := coordJ h
  let a := coordA h
  let b := coordB h
  let c := coordC h
  (i, j, a, b + i, c + j)

def translationPerm (t : H) : Equiv.Perm H :=
  Equiv.addRight t

def generatedX (x y : Equiv.Perm H) : Subgroup (Equiv.Perm H) :=
  Subgroup.closure
    (((Subgroup.closure (Set.range translationPerm) :
        Subgroup (Equiv.Perm H)) : Set (Equiv.Perm H)) ∪ {x, y})

def modelData (x y g : Equiv.Perm H) : Prop :=
  (∀ h : H, x h = xMap h) ∧
    (∀ h : H, y h = yMap h) ∧
    (∀ h : H, g h = gMap h) ∧
    Set.ncard (generatedX x y : Set (Equiv.Perm H)) = 3 ^ 7 ∧
    Set.ncard (generatedX x y : Set (Equiv.Perm H)) = 2187

def affineCoordinateBasis (i : Fin 6) : FunctionSpace :=
  match i.val with
  | 0 => fun _ => 1
  | 1 => coordI
  | 2 => coordJ
  | 3 => coordA
  | 4 => coordB
  | _ => coordC

def affineCoordinateModule : Submodule F3 FunctionSpace :=
  Submodule.span F3 (Set.range affineCoordinateBasis)

def seedOrbitSpan (X : Subgroup (Equiv.Perm H)) :
    Submodule F3 FunctionSpace :=
  Submodule.span F3
    {f | ∃ u : X, f = aSquare ∘ (u : Equiv.Perm H)}

def xInvariant (X : Subgroup (Equiv.Perm H))
    (M : Submodule F3 FunctionSpace) : Prop :=
  ∀ u : X, ∀ f : FunctionSpace, f ∈ M →
    f ∘ (u : Equiv.Perm H) ∈ M

def affineSpanModule : Submodule F3 FunctionSpace :=
  K_NL ⊔ affineCoordinateModule

def actualImage (X : Subgroup (Equiv.Perm H))
    (K : Submodule F3 FunctionSpace) : Set (Equiv.Perm Ω) :=
  {a | ∃ k : K, ∃ u : X,
    ∀ z : F3, ∀ h : H,
      a (z, h) = (z + (k : FunctionSpace) h,
        (u : Equiv.Perm H) h)}

def isPermutationSubgroup (U : Set (Equiv.Perm Ω)) : Prop :=
  1 ∈ U ∧
    (∀ a ∈ U, ∀ b ∈ U, a * b ∈ U) ∧
    (∀ a ∈ U, a⁻¹ ∈ U)

def constantFunction (d : F3) : FunctionSpace := fun _ => d

def D : Submodule F3 FunctionSpace :=
  Submodule.span F3 (Set.range constantFunction)

def canonicalRegularCopy (g : Equiv.Perm H) (k : Fin 3) :
    Set (Equiv.Perm Ω) :=
  {a | ∃ d : D, ∃ t : H,
    ∀ z : F3, ∀ h : H,
      a (z, h) =
        (z + (d : FunctionSpace) h,
          ((g ^ k.val)⁻¹ * translationPerm t * (g ^ k.val)) h)}

def regularOn (U : Set (Equiv.Perm Ω)) : Prop :=
  ∀ u v : Ω, ∃! a, a ∈ U ∧ a u = v

def conjugacyEntry (A : Set (Equiv.Perm Ω))
    (g : Equiv.Perm H) (k l : Fin 3) : Prop :=
  ∃ c : Equiv.Perm Ω, c ∈ A ∧
    ∀ a : Equiv.Perm Ω,
      a ∈ canonicalRegularCopy g k ↔
        c * a * c⁻¹ ∈ canonicalRegularCopy g l

def conjugacyMatrixIsIdentity (A : Set (Equiv.Perm Ω))
    (g : Equiv.Perm H) : Prop :=
  (∀ k : Fin 3, conjugacyEntry A g k k) ∧
    (∀ ⦃k l : Fin 3⦄, k ≠ l → ¬ conjugacyEntry A g k l)

def pointStabilizerSuborbit (A : Set (Equiv.Perm Ω))
    (u v : Ω) : Set Ω :=
  {w | ∃ a : Equiv.Perm Ω,
    a ∈ A ∧ a u = u ∧ a v = w}

def pointStabilizerSuborbitFamily (A : Set (Equiv.Perm Ω))
    (u : Ω) : Set (Set Ω) :=
  {C | ∃ v : Ω, C = pointStabilizerSuborbit A u v}

def suborbitCount (A : Set (Equiv.Perm Ω)) (u : Ω) : ℕ :=
  Set.ncard (pointStabilizerSuborbitFamily A u)

def suborbitSizeCount (A : Set (Equiv.Perm Ω))
    (u : Ω) (n : ℕ) : ℕ :=
  Set.ncard {C : Set Ω |
    ∃ v : Ω,
      C = pointStabilizerSuborbit A u v ∧ Set.ncard C = n}

def omegaZero : Ω := (0, 0)

def transporterFormula (qg : Equiv.Perm Ω)
    (g : Equiv.Perm H) : Prop :=
  ∀ z : F3, ∀ h : H, qg (z, h) = (z, g h)

def transporterFixesSuborbits (A : Set (Equiv.Perm Ω))
    (qg : Equiv.Perm Ω) : Prop :=
  qg omegaZero = omegaZero ∧
    ∀ v : Ω,
      qg '' pointStabilizerSuborbit A omegaZero v =
        pointStabilizerSuborbit A omegaZero v

/-- The six-dimensional X-invariant nonlinear module, its exact semidirect
actual image, and the nine-dimensional affine span. -/
def nonlinearInvariantModuleAndImage_claim43431 : Prop :=
  ∃ x y g : Equiv.Perm H,
    modelData x y g ∧
      let X := generatedX x y
      let A := actualImage X K_NL
      xInvariant X K_NL ∧
        K_NL = seedOrbitSpan X ∧
        Module.finrank F3 K_NL = 6 ∧
        isPermutationSubgroup A ∧
        Set.ncard A = 3 ^ 13 ∧
        Set.ncard A = 1594323 ∧
        Module.finrank F3 affineSpanModule = 9 ∧
        ¬ K_NL = affineCoordinateModule

/-- The three constant-function-line lifts are anchored inside the exact
actual image before their order, regularity, and identity conjugacy matrix are
asserted. -/
def threeRegularCopiesNonconjugate_claim43434 : Prop :=
  ∃ x y g : Equiv.Perm H,
    modelData x y g ∧
      let X := generatedX x y
      let A := actualImage X K_NL
      (∀ k : Fin 3,
        canonicalRegularCopy g k ⊆ A) ∧
        Fintype.card Ω = 3 ^ 6 ∧
        Fintype.card Ω = 729 ∧
        (∀ k : Fin 3,
          isPermutationSubgroup (canonicalRegularCopy g k) ∧
            Set.ncard (canonicalRegularCopy g k) = 3 ^ 6 ∧
            Set.ncard (canonicalRegularCopy g k) = 729 ∧
            regularOn (canonicalRegularCopy g k)) ∧
        conjugacyMatrixIsIdentity A g

/-- The actual-image point-stabilizer census and the exact block transporter. -/
def pointStabilizerSuborbitData_claim43435 : Prop :=
  ∃ x y g : Equiv.Perm H, ∃ qg : Equiv.Perm Ω,
    modelData x y g ∧
      let X := generatedX x y
      let A := actualImage X K_NL
      transporterFormula qg g ∧
        suborbitCount A omegaZero = 73 ∧
        suborbitSizeCount A omegaZero 1 = 27 ∧
        suborbitSizeCount A omegaZero 3 = 18 ∧
        suborbitSizeCount A omegaZero 9 = 6 ∧
        suborbitSizeCount A omegaZero 27 = 22 ∧
        transporterFixesSuborbits A qg

end

end MathlibPlus.Open.Research.R2211ExactImageRepair

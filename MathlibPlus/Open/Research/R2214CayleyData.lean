-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is a root of the Unverified library rather than of MathlibPlus and no build here depends on it. See unverified.txt.
import Mathlib

namespace MathlibPlus.Open.Research.R2214

noncomputable section

abbrev V := Fin 3 → ZMod 3
abbrev G := ZMod 4 × V

def addTranslation {α : Type*} [AddGroup α] (t : α) : α ≃ α :=
  { toFun := fun x => x + t
    invFun := fun x => x - t
    left_inv := by intro x; simp
    right_inv := by intro x; simp }

def standardBasis (i : Fin 3) : V :=
  fun j => if j = i then 1 else 0

def p4 : Equiv.Perm (ZMod 4) := Equiv.swap 2 3

def c4 : Equiv.Perm (ZMod 4) := addTranslation 1

def cyclicSet (c : Equiv.Perm (ZMod 4)) : Set (Equiv.Perm (ZMod 4)) :=
  {e | ∃ n : Nat, e = c ^ n}

def outsideNormalizer (p c : Equiv.Perm (ZMod 4)) : Prop :=
  ¬ ∀ z, z ∈ cyclicSet c → p * z * p⁻¹ ∈ cyclicSet c

def pFiber (x : G) : G :=
  if x.2 = 0 then (p4 x.1, x.2) else x

def pFiberEquiv : Equiv.Perm G :=
  { toFun := pFiber
    invFun := pFiber
    left_inv := by native_decide
    right_inv := by native_decide }

def translation (t : G) : Equiv.Perm G := addTranslation t

def R : Set (Equiv.Perm G) :=
  {e | ∃ t : G, e = translation t}

def conjugateSet (f : Equiv.Perm G) (U : Set (Equiv.Perm G)) : Set (Equiv.Perm G) :=
  {e | f⁻¹ * e * f ∈ U}

def T : Set (Equiv.Perm G) := conjugateSet pFiberEquiv R

def cayleyAdj (S : Set G) (x y : G) : Prop :=
  x ≠ y ∧ y - x ∈ S

def graphPerm (S : Set G) (e : Equiv.Perm G) : Prop :=
  ∀ x y, cayleyAdj S x y ↔ cayleyAdj S (e x) (e y)

def connectedCayley (S : Set G) : Prop :=
  ∀ x y, Relation.ReflTransGen (fun a b => cayleyAdj S a b) x y

def IsPermutationSubgroup (U : Set (Equiv.Perm G)) : Prop :=
  1 ∈ U ∧
  (∀ a ∈ U, ∀ b ∈ U, a * b ∈ U) ∧
  (∀ a ∈ U, a⁻¹ ∈ U)

def IsRegularPermutationSet (U : Set (Equiv.Perm G)) : Prop :=
  IsPermutationSubgroup U ∧
  Nat.card {e : Equiv.Perm G // e ∈ U} = 108 ∧
  (∀ x y, ∃! e, e ∈ U ∧ e x = y)

def ConjugateInAutomorphismGroup
    (S : Set G) (U W : Set (Equiv.Perm G)) : Prop :=
  ∃ c : Equiv.Perm G,
    graphPerm S c ∧
    ∀ e, e ∈ U ↔ c * e * c⁻¹ ∈ W

def inverseClosed (S : Set G) : Prop :=
  ∀ x, x ∈ S ↔ -x ∈ S

def identityFree (S : Set G) : Prop :=
  (0 : G) ∉ S

def e1 : V := standardBasis 0
def e2 : V := standardBasis 1
def e3 : V := standardBasis 2

def nonzeroC4 : Set (ZMod 4) := {a | a ≠ 0}

def S1 : Set G :=
  Set.univ ×ˢ ({e1, -e1, e2, -e2, e3, -e3} : Set V)

def S2 : Set G :=
  S1 ∪ nonzeroC4 ×ˢ ({0} : Set V)

def S3 : Set G :=
  (Set.univ ×ˢ ({e2, -e2, e3, -e3} : Set V)) ∪
    (({0} : Set (ZMod 4)) ×ˢ ({e1, -e1} : Set V)) ∪
    (nonzeroC4 ×ˢ ({0} : Set V))

def connectionSet (i : Fin 3) : Set G :=
  match i.1 with
  | 0 => S1
  | 1 => S2
  | _ => S3

def SquareMismatch : Prop :=
  outsideNormalizer p4 c4 ∧ p4 ^ 2 ≠ c4 ^ 2

def ThreeConnectionSets : Prop :=
  inverseClosed S1 ∧ identityFree S1 ∧ Set.ncard S1 = 24 ∧
  inverseClosed S2 ∧ identityFree S2 ∧ Set.ncard S2 = 27 ∧
  inverseClosed S3 ∧ identityFree S3 ∧ Set.ncard S3 = 21

def ThreeGraphResult : Prop :=
  ∀ i : Fin 3,
    let S := connectionSet i
    connectedCayley S ∧
    IsRegularPermutationSet R ∧
    IsRegularPermutationSet T ∧
    (∀ e ∈ R, graphPerm S e) ∧
    (∀ e ∈ T, graphPerm S e) ∧
    ConjugateInAutomorphismGroup S R T

def graphAutomorphismSet (S : Set G) : Set (Equiv.Perm G) :=
  {e | graphPerm S e}

def graphTransporterSet (S : Set G) : Set (Equiv.Perm G) :=
  {e | graphPerm S e ∧ ∀ r, r ∈ R ↔ e * r * e⁻¹ ∈ T}

def tOrbit (g : G) : G :=
  (pFiberEquiv⁻¹ * translation g * pFiberEquiv) 0

def tLabeledConnectionSet (S : Set G) : Set G :=
  {g | cayleyAdj S 0 (tOrbit g)}

def additiveAutomorphismTransporters (S : Set G) : Set (G ≃+ G) :=
  {α | α '' S = tLabeledConnectionSet S}

def GroupAutomorphismOrbitData : Prop :=
  Nat.card (G ≃+ G) = 22464 ∧
  (∀ i : Fin 3,
    ∃ α : G ≃+ G,
      α '' connectionSet i = tLabeledConnectionSet (connectionSet i)) ∧
  Set.ncard (additiveAutomorphismTransporters S1) = 96 ∧
  Set.ncard (additiveAutomorphismTransporters S2) = 96 ∧
  Set.ncard (additiveAutomorphismTransporters S3) = 32

def ExactGraphTransporterData : Prop :=
  Set.ncard (graphAutomorphismSet S1) =
      23895082139415112746353796555647697813504 ∧
  Set.ncard (graphTransporterSet S1) = 10368 ∧
  Set.ncard (graphAutomorphismSet S2) =
      23895082139415112746353796555647697813504 ∧
  Set.ncard (graphTransporterSet S2) = 10368 ∧
  Set.ncard (graphAutomorphismSet S3) = 1141260857376768 ∧
  Set.ncard (graphTransporterSet S3) = 3456

end
end MathlibPlus.Open.Research.R2214

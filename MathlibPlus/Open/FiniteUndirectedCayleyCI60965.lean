import Mathlib

namespace MathlibPlus.Open.FormalizationBatch

abbrev E35 := ZMod 8 × ZMod 35

def e35One : E35 := (0, 0)
def e35Sign (j : ZMod 8) : ZMod 35 := (-1 : ZMod 35) ^ ZMod.val j

def e35Mul (u v : E35) : E35 :=
  (u.1 + v.1, u.2 + e35Sign u.1 * v.2)

def e35Inv (u : E35) : E35 :=
  (-u.1, -(e35Sign u.1 * u.2))

def e35Mod5 (x : ZMod 35) : ℕ := ZMod.val x % 5

def e35A (j : ZMod 8) : Prop :=
  ZMod.val j = 1 ∨ ZMod.val j = 6 ∨ ZMod.val j = 7

def e35B (j : ZMod 8) : Prop :=
  ZMod.val j = 2 ∨ ZMod.val j = 3 ∨ ZMod.val j = 5

def e35C0 : Set E35 :=
  {u | ZMod.val u.1 = 0 ∧ (e35Mod5 u.2 = 1 ∨ e35Mod5 u.2 = 4)}
def e35C1 : Set E35 :=
  {u | ZMod.val u.1 = 0 ∧ (e35Mod5 u.2 = 2 ∨ e35Mod5 u.2 = 3)}
def e35C2 : Set E35 :=
  {u | ZMod.val u.1 = 0 ∧ (u.2 = 5 ∨ u.2 = -5)}
def e35C3 : Set E35 :=
  {u | ZMod.val u.1 = 0 ∧ (u.2 = 10 ∨ u.2 = -10)}
def e35C4 : Set E35 :=
  {u | ZMod.val u.1 = 0 ∧ (u.2 = 15 ∨ u.2 = -15)}
def e35C5 : Set E35 :=
  {u | (e35A u.1 ∨ e35B u.1) ∧ e35Mod5 u.2 = 0}
def e35Cr (r : ℕ) : Set E35 :=
  {u | (e35A u.1 ∧ e35Mod5 u.2 = r) ∨
    (e35B u.1 ∧ e35Mod5 u.2 = (5 - r) % 5)}
def e35C10 : Set E35 :=
  {u | ZMod.val u.1 = 4 ∧ e35Mod5 u.2 = 0}
def e35C11 : Set E35 :=
  {u | ZMod.val u.1 = 4 ∧ (e35Mod5 u.2 = 1 ∨ e35Mod5 u.2 = 4)}
def e35C12 : Set E35 :=
  {u | ZMod.val u.1 = 4 ∧ (e35Mod5 u.2 = 2 ∨ e35Mod5 u.2 = 3)}

def e35C : Fin 13 → Set E35 :=
  ![e35C0, e35C1, e35C2, e35C3, e35C4, e35C5,
    e35Cr 1, e35Cr 2, e35Cr 3, e35Cr 4, e35C10, e35C11, e35C12]

def e35H (j : ZMod 8) : ZMod 8 :=
  match ZMod.val j with
  | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 6 | 4 => 4
  | 5 => 5 | 6 => 7 | 7 => 2 | _ => 0

def e35HInv (j : ZMod 8) : ZMod 8 :=
  match ZMod.val j with
  | 0 => 0 | 1 => 1 | 2 => 7 | 3 => 2 | 4 => 4
  | 5 => 5 | 6 => 3 | 7 => 6 | _ => 0

def e35Alpha (u : E35) : E35 := (-u.1, u.2)

def e35QFun (f : ZMod 35 → ZMod 35) (u : E35) : E35 :=
  if u.1 = (1 : ZMod 8) then (e35H u.1, f u.2) else (e35H u.1, u.2)

def e35QInvFun (fInv : ZMod 35 → ZMod 35) (u : E35) : E35 :=
  if u.1 = (1 : ZMod 8) then (e35HInv u.1, fInv u.2)
  else (e35HInv u.1, u.2)

def e35Congruent5 (f : ZMod 35 → ZMod 35) : Prop :=
  ∀ x, e35Mod5 (f x) = e35Mod5 x

def e35Connection (R : Set E35) : Prop :=
  e35One ∉ R ∧ ∀ ⦃u : E35⦄, u ∈ R → e35Inv u ∈ R

def e35Adj (R : Set E35) (u v : E35) : Prop :=
  u ≠ v ∧ e35Mul (e35Inv u) v ∈ R

def e35GraphIso (R T : Set E35) (q : E35 → E35) : Prop :=
  Function.Bijective q ∧ ∀ u v, e35Adj R u v ↔ e35Adj T (q u) (q v)

def e35SourceUnion (I : Set (Fin 13)) : Set E35 :=
  {u | ∃ i : Fin 13, i ∈ I ∧ u ∈ e35C i}

def e35Left (g : E35) : E35 → E35 := fun u => e35Mul g u

def e35R : Set (E35 → E35) := {f | ∃ g : E35, f = e35Left g}

def e35HConjugate (q qInv : E35 → E35) : Set (E35 → E35) :=
  {f | ∃ g : E35, f = fun u => qInv (e35Left g (q u))}

def e35XStep (q qInv : E35 → E35) (p r : E35 × E35) : Prop :=
  ∃ f : E35 → E35,
    f ∈ e35R ∪ e35HConjugate q qInv ∧ r = (f p.1, f p.2)

def e35XOrbit (q qInv : E35 → E35) (p r : E35 × E35) : Prop :=
  Relation.EqvGen (e35XStep q qInv) p r

def e35DirectedOrbital (q qInv : E35 → E35)
    (D : Set (E35 × E35)) : Prop :=
  ∃ p : E35 × E35, p.1 ≠ p.2 ∧ D = {r | e35XOrbit q qInv p r}

def e35Transpose (D : Set (E35 × E35)) : Set (E35 × E35) :=
  {p | (p.2, p.1) ∈ D}

/-- A directed orbital is paired with its transpose; this includes a union of
 two distinct transpose-paired directed orbitals. -/
def e35InversePairedOrbitalAtIdentity
    (q qInv : E35 → E35) (S : Set E35) : Prop :=
  ∃ D : Set (E35 × E35),
    e35DirectedOrbital q qInv D ∧
      S = {s | (e35One, s) ∈ D ∪ e35Transpose D}

def e35F0 (x : ZMod 35) : ZMod 35 :=
  x + (15 : ZMod 35) * (e35Mod5 x : ZMod 35) ^ 2

def e35F0Inv (x : ZMod 35) : ZMod 35 :=
  x - (15 : ZMod 35) * (e35Mod5 x : ZMod 35) ^ 2

def e35C35OrbitalBooleanAlgebra : Set (Set E35) :=
  {S | ∃ I : Set (Fin 13), S = e35SourceUnion I}

def E35_C35_8_uniform_mod5_terminal_transporter : Prop :=
  (Function.Bijective e35Alpha ∧ e35Alpha e35One = e35One ∧
    ∀ u v, e35Alpha (e35Mul u v) = e35Mul (e35Alpha u) (e35Alpha v)) ∧
  Set.iUnion e35C = {u | u ≠ e35One} ∧
  (∀ ⦃i j : Fin 13⦄, i ≠ j → Disjoint (e35C i) (e35C j)) ∧
  (∀ i : Fin 13, (e35C i).Nonempty) ∧
  (∀ i : Fin 13, ∀ u : E35, u ∈ e35C i → e35Inv u ∈ e35C i) ∧
  (∀ i : Fin 13, e35Connection (e35C i)) ∧
  (∀ f : ZMod 35 → ZMod 35, Function.Bijective f → e35Congruent5 f →
    Function.Bijective (e35QFun f) ∧ e35QFun f e35One = e35One ∧
    (∀ i : Fin 13,
      Set.image (e35QFun f) (e35C i) = Set.image e35Alpha (e35C i)) ∧
    (∀ I : Set (Fin 13),
      e35Connection (e35SourceUnion I) ∧
      e35Connection (Set.image (e35QFun f) (e35SourceUnion I)) ∧
      Set.image e35Alpha (e35SourceUnion I) =
        Set.image (e35QFun f) (e35SourceUnion I))) ∧
  (let q := e35QFun e35F0
   let qInv := e35QInvFun e35F0Inv
   Function.Bijective e35F0 ∧ e35Congruent5 e35F0 ∧
   (∀ x : ZMod 35,
      ZMod.val (e35F0 x) % 7 =
        (ZMod.val x % 7 + (e35Mod5 x) ^ 2) % 7) ∧
   Function.Bijective q ∧ q e35One = e35One ∧
   (∀ u, qInv (q u) = u ∧ q (qInv u) = u) ∧
   (∀ i : Fin 13, e35InversePairedOrbitalAtIdentity q qInv (e35C i)) ∧
   (∀ S : Set E35,
      e35InversePairedOrbitalAtIdentity q qInv S →
        ∃ i : Fin 13, S = e35C i) ∧
   Nat.card {S : Set E35 // S ∈ e35C35OrbitalBooleanAlgebra} = 8192 ∧
   (∀ I : Set (Fin 13),
      let S := e35SourceUnion I
      e35Connection S ∧ e35Connection (Set.image q S) ∧
      e35GraphIso S (Set.image q S) q ∧
      Set.image e35Alpha S = Set.image q S))

end MathlibPlus.Open.FormalizationBatch

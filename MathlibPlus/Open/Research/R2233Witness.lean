import Mathlib

namespace MathlibPlus.Open.Research

abbrev R2233F7 := ZMod 7
abbrev R2233W := Fin 4 → R2233F7
abbrev R2233G := R2233W × Fin 3

def r2233LayerAdd (i j : Fin 3) : Fin 3 :=
  ⟨(i.val + j.val) % 3, by omega⟩

def r2233LayerNeg (i : Fin 3) : Fin 3 :=
  ⟨(3 - i.val) % 3, by omega⟩

def r2233LayerScalar (i : Fin 3) : R2233F7 :=
  (2 : R2233F7) ^ i.val

def r2233Mul (g h : R2233G) : R2233G :=
  (fun k => g.1 k + r2233LayerScalar g.2 * h.1 k,
    r2233LayerAdd g.2 h.2)

def r2233One : R2233G :=
  (0, ⟨0, by omega⟩)

def r2233Inv (g : R2233G) : R2233G :=
  (fun k => -((2 : R2233F7) ^ ((3 - g.2.val) % 3)) * g.1 k,
    r2233LayerNeg g.2)

def r2233InverseClosed (S : Set R2233G) : Prop :=
  ∀ x, x ∈ S → r2233Inv x ∈ S

def r2233IdentityFree (S : Set R2233G) : Prop :=
  r2233One ∉ S

def r2233Cardinality500 (S : Set R2233G) : Prop :=
  S.ncard = 500

def r2233CayleyAdj (S : Set R2233G) (x y : R2233G) : Prop :=
  ∃ s, s ∈ S ∧ y = r2233Mul x s

def r2233Connected (S : Set R2233G) : Prop :=
  ∀ x y, Relation.ReflTransGen (r2233CayleyAdj S) x y

def r2233CayleyIsomorphic (S T : Set R2233G) : Prop :=
  ∃ f : R2233G → R2233G,
    Function.Bijective f ∧
      ∀ x y,
        r2233CayleyAdj S x y ↔ r2233CayleyAdj T (f x) (f y)

def r2233GroupAutomorphism (f : R2233G → R2233G) : Prop :=
  Function.Bijective f ∧
  f r2233One = r2233One ∧
  (∀ x y, f (r2233Mul x y) = r2233Mul (f x) (f y)) ∧
  (∀ x, f (r2233Inv x) = r2233Inv (f x))

def r2233OrdinaryUndirectedCI : Prop :=
  ∀ S T : Set R2233G,
    r2233InverseClosed S →
    r2233InverseClosed T →
    r2233IdentityFree S →
    r2233IdentityFree T →
    r2233CayleyIsomorphic S T →
    ∃ f : R2233G → R2233G,
      r2233GroupAutomorphism f ∧ f '' S = T

def r2233ExplicitOrdinaryNonCIWitness : Prop :=
  (∃ S T : Set R2233G,
    r2233Cardinality500 S ∧
    r2233Cardinality500 T ∧
    r2233Connected S ∧
    r2233Connected T ∧
    r2233InverseClosed S ∧
    r2233InverseClosed T ∧
    r2233IdentityFree S ∧
    r2233IdentityFree T ∧
    r2233CayleyIsomorphic S T ∧
    ¬ ∃ f : R2233G → R2233G,
      r2233GroupAutomorphism f ∧ f '' S = T) ∧
  ¬ r2233OrdinaryUndirectedCI

end MathlibPlus.Open.Research

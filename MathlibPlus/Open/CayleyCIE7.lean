import Mathlib

namespace MathlibPlus.Open
namespace CayleyCIE7

abbrev E_C7_3 := ZMod 7 × ZMod 3

def actionTwoPower (k : ZMod 3) : ZMod 7 :=
  (2 : ZMod 7) ^ k.val

def eC73Mul (a b : E_C7_3) : E_C7_3 :=
  (a.1 + actionTwoPower a.2 * b.1, a.2 + b.2)

def eC73One : E_C7_3 := (0, 0)

def eC73Inv (a : E_C7_3) : E_C7_3 :=
  (-(actionTwoPower (-a.2) * a.1), -a.2)

def eC73IdentityFree (S : Set E_C7_3) : Prop :=
  eC73One ∉ S

def eC73InverseClosed (S : Set E_C7_3) : Prop :=
  ∀ x, x ∈ S ↔ eC73Inv x ∈ S

def eC73CayleyAdjacent (S : Set E_C7_3) (x y : E_C7_3) : Prop :=
  eC73Mul (eC73Inv x) y ∈ S

def eC73GraphIsomorphic (S T : Set E_C7_3) : Prop :=
  ∃ e : E_C7_3 ≃ E_C7_3, ∀ x y,
    eC73CayleyAdjacent S x y ↔ eC73CayleyAdjacent T (e x) (e y)

def eC73GroupAutomorphism (α : E_C7_3 ≃ E_C7_3) : Prop :=
  α eC73One = eC73One ∧
    ∀ x y, α (eC73Mul x y) = eC73Mul (α x) (α y)

def eC73UndirectedCI : Prop :=
  ∀ S T : Set E_C7_3,
    eC73IdentityFree S → eC73InverseClosed S →
    eC73IdentityFree T → eC73InverseClosed T →
    eC73GraphIsomorphic S T →
    ∃ α : E_C7_3 ≃ E_C7_3,
      eC73GroupAutomorphism α ∧ α '' S = T

end CayleyCIE7
end MathlibPlus.Open

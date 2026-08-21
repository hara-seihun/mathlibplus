-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is not built and MathlibPlus.lean does not import it. See unverified.txt.
import Mathlib

namespace MathlibPlus

namespace EC13C3

/-- The residue-coordinate carrier for `E(C₁₃, 3)`. -/
structure Carrier where
  v : ZMod 13
  k : Fin 3
  deriving DecidableEq, Fintype

/-- The action of the second coordinate on the first coordinate. -/
def actionPow (k : Fin 3) : ZMod 13 := (3 : ZMod 13) ^ k.val

/-- The inverse action, using `3^3 = 1` in `ZMod 13`. -/
def inverseActionPow (k : Fin 3) : ZMod 13 :=
  (3 : ZMod 13) ^ ((3 - k.val) % 3)

/-- `(v,k)(u,l) = (v + 3^k u, k+l)`. -/
def mul (x y : Carrier) : Carrier :=
  ⟨x.v + actionPow x.k * y.v, x.k + y.k⟩

def one : Carrier := ⟨0, 0⟩

def inv (x : Carrier) : Carrier :=
  ⟨-(inverseActionPow x.k * x.v), -x.k⟩

instance : Mul Carrier := ⟨mul⟩
instance : One Carrier := ⟨one⟩
instance : Inv Carrier := ⟨inv⟩

instance : Group Carrier where
  mul_assoc := by native_decide
  one_mul := by native_decide
  mul_one := by native_decide
  inv_mul_cancel := by native_decide

end EC13C3

namespace Open

/-- The ordinary undirected Cayley graph of a concrete connection set. -/
def EC13C3.cayleyGraph (S : Set EC13C3.Carrier) : SimpleGraph EC13C3.Carrier :=
  SimpleGraph.fromRel (fun x y => ∃ s ∈ S, y = x * s)

/-- `E(C₁₃,3)` is an ordinary undirected CI-group, with no connectivity assumption. -/
def EC13C3.ordinaryUndirectedCI : Prop :=
  ∀ (S T : Set EC13C3.Carrier),
    1 ∉ S →
    1 ∉ T →
    S⁻¹ = S →
    T⁻¹ = T →
    Nonempty (SimpleGraph.Iso (EC13C3.cayleyGraph S) (EC13C3.cayleyGraph T)) →
    ∃ α : EC13C3.Carrier ≃* EC13C3.Carrier, α '' S = T

end Open
end MathlibPlus

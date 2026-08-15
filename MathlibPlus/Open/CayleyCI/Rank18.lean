import Mathlib

namespace MathlibPlus.Open

abbrev C2PowTimesC9 (r : ℕ) := (Fin r → ZMod 2) × ZMod 9

def inverseClosed {G : Type*} [Neg G] (S : Set G) : Prop :=
  ∀ ⦃x : G⦄, x ∈ S → -x ∈ S

def cayleyGraph {G : Type*} [AddGroup G] (S : Set G) : SimpleGraph G :=
  SimpleGraph.fromRel (fun x y => y - x ∈ S)

def cayleyCI {G : Type*} [AddGroup G] (S : Set G) : Prop :=
  inverseClosed S ∧
    S ⊆ ({0} : Set G)ᶜ ∧
      ∀ T : Set G,
        inverseClosed T →
          T ⊆ ({0} : Set G)ᶜ →
            Nonempty (cayleyGraph S ≃g cayleyGraph T) →
              ∃ α : G ≃+ G, α '' S = T

def fourValent {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ v : V, Nat.card {w : V // G.Adj v w} = 4

def rank18FourStepConnection {r : ℕ} (e : Fin r → ZMod 2) (z : ZMod 9) :
    Set (C2PowTimesC9 r) :=
  let a : C2PowTimesC9 r := (e, z)
  {a, -a, 3 • a, -(3 • a)}

def ciBinaryTimesC9Rank18 : Prop :=
  ∀ r : ℕ,
    1 ≤ r →
      ∀ e : Fin r → ZMod 2,
        e ≠ 0 →
          ∀ z : ZMod 9,
            addOrderOf z = 9 →
              let S := rank18FourStepConnection e z
              cayleyCI S ∧
                (r ∈ ({3, 4, 5} : Set ℕ) → fourValent (cayleyGraph S))

end MathlibPlus.Open

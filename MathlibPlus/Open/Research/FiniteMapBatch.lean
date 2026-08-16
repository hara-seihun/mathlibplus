import Mathlib

namespace MathlibPlus.Open.Research.FiniteMapBatch

/-
The packet's F₅³ is represented by functions from `Fin 3` to `ZMod 5`.
The direct-sum coordinates are represented by pairs, so `V` is `X × Z`.
-/
abbrev F5 := ZMod 5
abbrev Vec := Fin 3 → F5
abbrev X := Vec
abbrev Z := Vec
abbrev V := X × Z

/-- The coordinate vector with entries `a`, `b`, and `c`. -/
def vec (a b c : F5) : Vec := ![a, b, c]

/-- The map `F(z₁,z₂,z₃)=(z₁²+z₁z₂z₃,z₂²,z₃²)`. -/
def F (z : Vec) : Vec :=
  ![z 0 ^ 2 + z 0 * z 1 * z 2, z 1 ^ 2, z 2 ^ 2]

/-- The map `q(x,z)=(z,x+F(z))`. -/
def q : V → V
  | (x, z) => (z, x + F z)

/-- The map `A(x,z)=(z,x+z)`. -/
def A : V → V
  | (x, z) => (z, x + z)

/-- The exact definition claim in packet item 60665. -/
def claim60665 : Prop :=
  (∀ z : Vec,
      F z = ![z 0 ^ 2 + z 0 * z 1 * z 2, z 1 ^ 2, z 2 ^ 2]) ∧
    (∀ x : X, ∀ z : Z, q (x, z) = (z, x + F z)) ∧
    (∀ x : X, ∀ z : Z, A (x, z) = (z, x + z))

/-- The seven representatives in `F₅³`. -/
def D : Set Vec :=
  {d |
    d = vec 1 0 0 ∨
    d = vec 0 1 0 ∨
    d = vec 0 0 1 ∨
    d = vec 0 1 1 ∨
    d = vec 1 1 0 ∨
    d = vec 1 0 1 ∨
    d = vec 1 1 1}

/-- The first signed mixed-difference set for a representative `d`. -/
def mixedPlus (d : Vec) : Set Vec :=
  Set.range (fun a : Vec => F (a + d) - F a - F d)

/-- The second signed mixed-difference set for a representative `d`. -/
def mixedMinus (d : Vec) : Set Vec :=
  Set.range (fun a : Vec => F (a - d) - F a - F (-d))

/-- The span of the two signed mixed-difference sets, for `d ∈ D`. -/
abbrev DRep := {d : Vec // d ∈ D}

def W (d : DRep) : Submodule F5 Vec :=
  Submodule.span F5 (mixedPlus d.1 ∪ mixedMinus d.1)

/-- Translate a set by adding a vector on the right. -/
def translatePlus (s : Set Vec) (d : Vec) : Set Vec :=
  {x | ∃ w ∈ s, x = w + d}

/-- Translate a set by subtracting a vector on the right. -/
def translateMinus (s : Set Vec) (d : Vec) : Set Vec :=
  {x | ∃ w ∈ s, x = w - d}

/-- The set `S_I` for a mask `I ⊆ D`. -/
def S (I : Set Vec) (hI : I ⊆ D) : Set Vec :=
  ⋃ (d : Vec) (hd : d ∈ I),
    (translatePlus (W ⟨d, hI hd⟩) d ∪ translateMinus (W ⟨d, hI hd⟩) d)

/-- The exact representative, span, and masked-union definition claim in packet item 60666. -/
def claim60666 : Prop :=
  (D =
      {d |
        d = vec 1 0 0 ∨
        d = vec 0 1 0 ∨
        d = vec 0 0 1 ∨
        d = vec 0 1 1 ∨
        d = vec 1 1 0 ∨
        d = vec 1 0 1 ∨
        d = vec 1 1 1}) ∧
    (∀ d : DRep,
      W d = Submodule.span F5 (mixedPlus d.1 ∪ mixedMinus d.1)) ∧
    (∀ I : Set Vec, ∀ hI : I ⊆ D,
      S I hI =
        ⋃ (d : Vec) (hd : d ∈ I),
          (translatePlus (W ⟨d, hI hd⟩) d ∪
            translateMinus (W ⟨d, hI hd⟩) d))

end MathlibPlus.Open.Research.FiniteMapBatch

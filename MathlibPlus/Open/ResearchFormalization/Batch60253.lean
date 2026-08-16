import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Batch60250_60251_60252_60253

abbrev vectorSpace60253 : Type := Fin 3 → ZMod 3
abbrev ambientGroup60253 : Type := ZMod 4 × vectorSpace60253

def addCayleyGraph60253 (R : Set ambientGroup60253) :
    SimpleGraph ambientGroup60253 :=
  SimpleGraph.fromRel (fun x y => y - x ∈ R)

def identityFreeInverseClosed60253 (R : Set ambientGroup60253) : Prop :=
  R ⊆ {x | x ≠ 0} ∧ ∀ x, x ∈ R → -x ∈ R

def subgroup60253 (W : Submodule (ZMod 3) vectorSpace60253) :
    AddSubgroup ambientGroup60253 :=
  AddSubgroup.prod (⊤ : AddSubgroup (ZMod 4)) W.toAddSubgroup

def twoDimensional60253 (W : Submodule (ZMod 3) vectorSpace60253) : Prop :=
  Module.finrank (ZMod 3) W = 2

def supportedGenerating60253
    (W : Submodule (ZMod 3) vectorSpace60253)
    (S : Set ambientGroup60253) : Prop :=
  identityFreeInverseClosed60253 S ∧
    S ⊆ subgroup60253 W ∧
    AddSubgroup.closure S = subgroup60253 W

def ambientComplement60253 (S : Set ambientGroup60253) : Set ambientGroup60253 :=
  (Set.univ \ {0}) \ S

def ordinaryUndirectedCI60253 (R : Set ambientGroup60253) : Prop :=
  identityFreeInverseClosed60253 R ∧
    ∀ T : Set ambientGroup60253,
      identityFreeInverseClosed60253 T →
      (addCayleyGraph60253 R ≃g addCayleyGraph60253 T) →
      ∃ α : AddEquiv ambientGroup60253 ambientGroup60253, α '' R = T

def supportedCollection60253 : Set (Set ambientGroup60253) :=
  {S | ∃ W : Submodule (ZMod 3) vectorSpace60253,
    twoDimensional60253 W ∧ supportedGenerating60253 W S}

def complementCollection60253 : Set (Set ambientGroup60253) :=
  {R | ∃ S ∈ supportedCollection60253, R = ambientComplement60253 S}

def Claim60253 : Prop :=
  (∀ W : Submodule (ZMod 3) vectorSpace60253,
      twoDimensional60253 W →
      Set.ncard {S : Set ambientGroup60253 | supportedGenerating60253 W S} = 261414 ∧
      ∀ S : Set ambientGroup60253,
        supportedGenerating60253 W S →
        ordinaryUndirectedCI60253 S ∧
          ordinaryUndirectedCI60253 (ambientComplement60253 S)) ∧
    Set.ncard {W : Submodule (ZMod 3) vectorSpace60253 | twoDimensional60253 W} = 13 ∧
    Set.ncard supportedCollection60253 = 3398382 ∧
    Set.ncard complementCollection60253 = 3398382 ∧
    Set.ncard (supportedCollection60253 ∪ complementCollection60253) = 6796764

end MathlibPlus.Open.ResearchFormalization.Batch60250_60251_60252_60253

import Mathlib

namespace MathlibPlus.Open.ResearchBatch

abbrev NetA := Fin 4 → ZMod 7
abbrev NetQ := Fin 3
abbrev NetG := NetA × NetQ

def netOmega : ZMod 7 := 2

def netQNeg (i : NetQ) : NetQ :=
  ⟨(3 - i.1) % 3, by omega⟩

def netSemidirectInv (g : NetG) : NetG :=
  (-((netOmega ^ (netQNeg g.2).1) • g.1), netQNeg g.2)

def IsNetConnectionSet (U : Finset NetG) : Prop :=
  (0, 0) ∉ U ∧ ∀ g ∈ U, netSemidirectInv g ∈ U

def NetConnectionSet := {U : Finset NetG // IsNetConnectionSet U}

noncomputable def netSection (U : NetConnectionSet) (i : NetQ) : Finset NetA :=
  (U.1.filter (fun g => g.2 = i)).image Prod.fst

noncomputable def orderedSectionProduct
    (U : NetConnectionSet) (i j : NetQ) (a : NetA) : ℕ :=
  ((netSection U i).product (netSection U j)).filter
    (fun xy => xy.1 + (netOmega ^ i.1) • xy.2 = a) |>.card

noncomputable def orderedProductArray (U : NetConnectionSet) : NetQ → NetQ → NetA → ℕ :=
  fun i j a => orderedSectionProduct U i j a

end MathlibPlus.Open.ResearchBatch

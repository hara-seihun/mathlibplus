import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1379MorrisCounterexample

abbrev F := ZMod 3
abbrev H := F × F
abbrev D := F × F
abbrev Profile := H → D

def table (v : Fin 9 → D) (h : H) : D :=
  if h = (0, 0) then v 0 else
  if h = (0, 1) then v 1 else
  if h = (0, 2) then v 2 else
  if h = (1, 0) then v 3 else
  if h = (1, 1) then v 4 else
  if h = (1, 2) then v 5 else
  if h = (2, 0) then v 6 else
  if h = (2, 1) then v 7 else
  v 8

def row1 : Profile := table ![(1, 0), (0, 1), (0, 1), (0, 0), (2, 1), (2, 1),
  (0, 0), (1, 2), (0, 0)]
def row2 : Profile := table ![(0, 1), (0, 1), (0, 1), (0, 0), (1, 2), (2, 1),
  (0, 2), (2, 0), (1, 1)]
def row3 : Profile := table ![(0, 0), (1, 2), (0, 0), (0, 0), (0, 0), (1, 2),
  (0, 1), (1, 0), (0, 1)]
def row4 : Profile := table ![(0, 0), (0, 0), (1, 2), (0, 0), (2, 1), (2, 1),
  (0, 1), (0, 1), (1, 0)]
def row5 : Profile := table ![(0, 0), (0, 0), (0, 0), (1, 0), (0, 1), (2, 2),
  (0, 2), (1, 1), (2, 0)]
def row6 : Profile := table ![(0, 0), (0, 0), (0, 0), (0, 1), (2, 2), (1, 0),
  (0, 2), (1, 1), (2, 0)]
def row7 : Profile := table ![(0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0),
  (1, 2), (1, 2), (1, 2)]
def codeRow : Fin 7 → Profile := ![row1, row2, row3, row4, row5, row6, row7]
def code : Submodule F Profile := Submodule.span F (Set.range codeRow)

def baseTranslate (a : H) (s : Profile) : Profile :=
  fun h => s (h - a)

def pairwiseClosure (C : Submodule F Profile) : Set Profile :=
  {s | ∀ x y : H, ∃ k : C, k.1 x = s x ∧ k.1 y = s y}

def witnessProfile : Profile := row5

def separatingFunctional (s : Profile) : F :=
  (s (1, 0)).1 + (s (1, 0)).2

def vectorMorrisPatchCounterexample : Prop :=
  Module.finrank F code = 7 ∧
    (∀ a : H, ∀ s : Profile, s ∈ code → baseTranslate a s ∈ code) ∧
    (∀ d : D, (fun _ : H => d : Profile) ∈ code) ∧
    witnessProfile ∈ code ∧
    witnessProfile (0, 0) = (0, 0) ∧
    witnessProfile + baseTranslate (0, 1) witnessProfile +
        baseTranslate (0, 1) (baseTranslate (0, 1) witnessProfile) = 0 ∧
    (∀ s : Profile, s ∈ pairwiseClosure code →
      separatingFunctional
        (baseTranslate (0, 1) s - s) = 0) ∧
    separatingFunctional witnessProfile = 1 ∧
    ¬ ∃ s : Profile,
      s ∈ pairwiseClosure code ∧
        baseTranslate (0, 1) s - s = witnessProfile

end MathlibPlus.Open.ResearchFormalization.R1379MorrisCounterexample

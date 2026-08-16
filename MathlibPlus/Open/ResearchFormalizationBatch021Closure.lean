import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch021Closure

abbrev CrossEdge := Fin 4 × Fin 5

def component₁ : Finset CrossEdge :=
  {(0, 0), (0, 1), (0, 2), (0, 4), (2, 1), (2, 2), (2, 3), (2, 4)}

def component₂ : Finset CrossEdge :=
  {(0, 3), (2, 0)}

def component₃ : Finset CrossEdge :=
  {(1, 0), (1, 1), (1, 3), (1, 4), (3, 0), (3, 2), (3, 3), (3, 4)}

def component₄ : Finset CrossEdge :=
  {(1, 2), (3, 1)}

def sameClosureComponent (e f : CrossEdge) : Prop :=
  (e ∈ component₁ ∧ f ∈ component₁) ∨
  (e ∈ component₂ ∧ f ∈ component₂) ∨
  (e ∈ component₃ ∧ f ∈ component₃) ∨
  (e ∈ component₄ ∧ f ∈ component₄)

def swapFin5 (a b x : Fin 5) : Fin 5 :=
  if x = a then b else if x = b then a else x

def tau₀ (z : Fin 5) : Fin 5 := swapFin5 1 2 (swapFin5 3 4 z)
def tau₁ (z : Fin 5) : Fin 5 := swapFin5 0 3 (swapFin5 2 4 z)
def tau₂ (z : Fin 5) : Fin 5 := swapFin5 0 4 (swapFin5 1 2 z)
def tau₃ (z : Fin 5) : Fin 5 := swapFin5 0 3 (swapFin5 1 4 z)

def tauForRow (u : Fin 4) (z : Fin 5) : Fin 5 :=
  if u = 0 then tau₀ z else if u = 1 then tau₁ z else if u = 2 then tau₂ z else tau₃ z

def omittedOutside (u : Fin 4) : Fin 5 :=
  if u = 0 then 3 else if u = 1 then 2 else if u = 2 then 0 else 1

def omittedEdge (u : Fin 4) : CrossEdge := (u, omittedOutside u)

def omittedRowImage (e : CrossEdge) : CrossEdge := (e.1, tauForRow e.1 e.2)

def edge07 : CrossEdge := (0, 3)
def edge08 : CrossEdge := (0, 4)
def edge16 : CrossEdge := (1, 2)
def edge18 : CrossEdge := (1, 4)
def edge24 : CrossEdge := (2, 0)
def edge28 : CrossEdge := (2, 4)
def edge35 : CrossEdge := (3, 1)
def edge38 : CrossEdge := (3, 4)

def claim_12652 : Prop :=
  omittedRowImage edge07 = edge08 ∧
  omittedRowImage edge16 = edge18 ∧
  omittedRowImage edge24 = edge28 ∧
  omittedRowImage edge35 = edge38 ∧
  (∀ u : Fin 4, ¬ sameClosureComponent (omittedEdge u) (omittedRowImage (omittedEdge u)))

end MathlibPlus.Open.ResearchFormalizationBatch021Closure

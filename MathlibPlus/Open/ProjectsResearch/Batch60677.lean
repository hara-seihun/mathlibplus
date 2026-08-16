import Mathlib

namespace MathlibPlus.Open.ProjectsResearch

abbrev TopVertex := Fin 3 → ℚ
abbrev SourceEdge := Fin 2 → ℚ
abbrev LowerCell := Fin 3 → ℚ
abbrev Response := Fin 2 → ℚ

def topT : TopVertex := ![1, 0, 0]
def topV : TopVertex := ![0, 1, 0]
def topU : TopVertex := ![0, 0, 1]

def sourceE₁ : SourceEdge := ![1, 0]
def sourceE₂ : SourceEdge := ![0, 1]

def lowerA : LowerCell := ![1, 0, 0]
def lowerB : LowerCell := ![0, 1, 0]
def lowerC : LowerCell := ![0, 0, 1]

def incidenceD : Matrix (Fin 3) (Fin 2) ℚ := !![1, 0; -1, 1; 0, -1]
def sigma : Matrix (Fin 3) (Fin 3) ℚ := !![1, 0, 0; 1, 1, 0; 0, 1, 2]
def responseMatrix : Matrix (Fin 2) (Fin 3) ℚ := !![1, 1, 1; 1, -1, 0]

def lowerBoundary : Matrix (Fin 3) (Fin 2) ℚ := sigma * incidenceD
def unitPath : SourceEdge := sourceE₁ + sourceE₂
def topBoundary : TopVertex := incidenceD.mulVec unitPath
def lowerPath : LowerCell := sigma.mulVec topBoundary

def filtration : Fin 3 → ℚ := ![2, 1, 0]

def responseA : Response := ![1, 1]
def responseB : Response := ![1, -1]
def responseC : Response := ![1, 0]

def responseMap : LowerCell →ₗ[ℚ] Response := Matrix.toLin' responseMatrix

def twoColumnMinor (u v : Response) : ℚ := u 0 * v 1 - u 1 * v 0

def claim60677 : Prop :=
  incidenceD = !![1, 0; -1, 1; 0, -1] ∧
  sigma = !![1, 0, 0; 1, 1, 0; 0, 1, 2] ∧
  sigma.mulVec topT = lowerA + lowerB ∧
  sigma.mulVec topV = lowerB + lowerC ∧
  sigma.mulVec topU = 2 • lowerC ∧
  lowerBoundary = !![1, 0; 0, 1; -1, -1] ∧
  lowerBoundary.mulVec sourceE₁ = lowerA - lowerC ∧
  lowerBoundary.mulVec sourceE₂ = lowerB - lowerC ∧
  filtration 0 = 2 ∧
  filtration 1 = 1 ∧
  filtration 2 = 0 ∧
  unitPath = sourceE₁ + sourceE₂ ∧
  incidenceD.mulVec unitPath = topT - topU ∧
  lowerPath = lowerA + lowerB - 2 • lowerC ∧
  responseMap lowerA = responseA ∧
  responseMap lowerB = responseB ∧
  responseMap lowerC = responseC ∧
  responseMap lowerPath = 0 ∧
  twoColumnMinor responseA responseB = -2 ∧
  twoColumnMinor responseA responseC = -1 ∧
  twoColumnMinor responseB responseC = 1 ∧
  Module.finrank ℚ (LinearMap.range responseMap) = 2 ∧
  LinearMap.ker responseMap = Submodule.span ℚ {lowerPath} ∧
  Module.finrank ℚ (LinearMap.ker responseMap) = 1 ∧
  ∀ x : LowerCell, responseMap x = 0 → x ≠ 0 →
    x 0 ≠ 0 ∧ x 1 ≠ 0 ∧ x 2 ≠ 0

end MathlibPlus.Open.ProjectsResearch

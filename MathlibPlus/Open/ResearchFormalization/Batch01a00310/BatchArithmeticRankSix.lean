import Mathlib

noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter

namespace MathlibPlus.Open.ResearchFormalization.Batch01a00310.BatchArithmeticRankSix

def arithmeticQ : Fin 6 → ℝ :=
  ![(67.8956844869100299 : ℝ), (79.7789175269571401 : ℝ),
    (130.672766383356478 : ℝ), (199.190988026814018 : ℝ),
    (221.575712203671201 : ℝ), (261.258032828055981 : ℝ)]

def arithmeticEll : Fin 6 → ℝ :=
  ![(1.00000013539932446 : ℝ), (1.00000056646214238 : ℝ),
    (1.00000118323819103 : ℝ), (1.00000142748418075 : ℝ),
    (1.01456019100249629 : ℝ), (1.01456811020225134 : ℝ)]

def claim12007 : Prop :=
  arithmeticEll 0 > 1 ∧ arithmeticEll 0 < arithmeticEll 1 ∧
    arithmeticEll 1 < arithmeticEll 2 ∧ arithmeticEll 2 < arithmeticEll 3 ∧
    arithmeticEll 3 < arithmeticEll 4 ∧ arithmeticEll 4 < arithmeticEll 5 ∧
    (Real.pi * (4 : ℝ)^2 < arithmeticQ 0 ∧ arithmeticQ 0 < Real.pi * (5 : ℝ)^2) ∧
    (Real.pi * (5 : ℝ)^2 < arithmeticQ 1 ∧ arithmeticQ 1 < Real.pi * (6 : ℝ)^2) ∧
    (Real.pi * (6 : ℝ)^2 < arithmeticQ 2 ∧ arithmeticQ 2 < Real.pi * (7 : ℝ)^2) ∧
    (Real.pi * (7 : ℝ)^2 < arithmeticQ 3 ∧ arithmeticQ 3 < Real.pi * (8 : ℝ)^2) ∧
    (Real.pi * (8 : ℝ)^2 < arithmeticQ 4 ∧ arithmeticQ 4 < Real.pi * (9 : ℝ)^2) ∧
    (Real.pi * (9 : ℝ)^2 < arithmeticQ 5 ∧ arithmeticQ 5 < Real.pi * (10 : ℝ)^2)

end MathlibPlus.Open.ResearchFormalization.Batch01a00310.BatchArithmeticRankSix

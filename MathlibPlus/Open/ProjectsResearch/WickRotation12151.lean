import Mathlib

noncomputable section

namespace MathlibPlus.Open.ProjectsResearch.WickRotation12151

abbrev Index2 := Fin 2

def rootMatrix (u v a b : ℝ) : Matrix Index2 Index2 ℂ :=
  !![ ((Real.sqrt 2 : ℂ) * ((u : ℂ) + (v : ℂ)) + ((u : ℂ) - (v : ℂ))),
      Complex.I * ((a : ℂ) - (b : ℂ));
      Complex.I * ((a : ℂ) - (b : ℂ)),
      ((Real.sqrt 2 : ℂ) * ((u : ℂ) + (v : ℂ)) - ((u : ℂ) - (v : ℂ))) ]

def realCounterpart (u v a b : ℝ) : Matrix Index2 Index2 ℝ :=
  !![ Real.sqrt 2 * (u + v) + (u - v), a - b;
      a - b, -Real.sqrt 2 * (u + v) + (u - v) ]

def complexRealCounterpart (u v a b : ℝ) : Matrix Index2 Index2 ℂ :=
  fun i j => (realCounterpart u v a b i j : ℂ)

def oddCoordinateRotation : Matrix Index2 Index2 ℂ :=
  !![ (1 : ℂ), 0;
      0, Complex.I ]

/-- Q is independently displayed and obtained from L by the complex odd rotation. -/
def complexOddCoordinateWickRotation (u v a b : ℝ) : Prop :=
  (rootMatrix u v a b =
      oddCoordinateRotation * complexRealCounterpart u v a b * oddCoordinateRotation) ∧
    Matrix.det (rootMatrix u v a b) =
      -Matrix.det (complexRealCounterpart u v a b)

end MathlibPlus.Open.ProjectsResearch.WickRotation12151

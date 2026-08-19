import MathlibPlus.Open.Research.R2211

namespace MathlibPlus.Open.Research.R2211

/-- Translation of a function on the displayed `H = F₃^5` model by a vector. -/
def translateFunction (p : H) (f : FunctionSpace) : FunctionSpace :=
  fun h => f (h + p)

/-- The common periods of the six-dimensional nonlinear function module. -/
def commonPeriodK_NL : Set H :=
  {p | ∀ f : FunctionSpace, f ∈ K_NL → translateFunction p f = f}

/-- The displayed set of vectors with free `j`, `b`, and `c` coordinates. -/
def displayedCommonPeriod : Set H :=
  {p | ∃ j b c : F3, p = (0, j, 0, b, c)}

/-- Claim 43433: the common period of the displayed model is the displayed
set, and that set has cardinality 27. -/
def commonPeriod_claim43433 : Prop :=
  commonPeriodK_NL = displayedCommonPeriod ∧
    Set.ncard displayedCommonPeriod = 27

end MathlibPlus.Open.Research.R2211

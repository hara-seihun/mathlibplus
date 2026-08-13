import MathlibPlus.GraphTheory.CayleyCIHierarchy

namespace MathlibPlus.Open.GraphTheory

/-- The alternating group on four letters is a directed Cayley CI-group.
Together with the explicit two-relation simultaneous defect, this makes the
implication from binary-relational `CI^(2)` to directed CI strict. -/
def alternatingFourDirectedCayleyCI : Prop :=
  MathlibPlus.GraphTheory.IsCayleyDCI (alternatingGroup (Fin 4))

end MathlibPlus.Open.GraphTheory

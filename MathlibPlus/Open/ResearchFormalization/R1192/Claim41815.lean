import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1192.Claim41815

abbrev C2Cube := Fin 3 → ZMod 2
abbrev C3Square := Fin 2 → ZMod 3

/-- The displacement subgroup attached to the row indexed by `u` is the
additive subgroup spanned by `t - q_u(t) + q_u(0)` over `C₃²`. -/
def activeDisplacementSubgroup_claim41815
    (q : C2Cube → Equiv.Perm C3Square) (u : C2Cube) :
    AddSubgroup C3Square :=
  AddSubgroup.closure (Set.range (fun t : C3Square =>
    t - q u t + q u 0))

end MathlibPlus.Open.ResearchFormalization.R1192.Claim41815

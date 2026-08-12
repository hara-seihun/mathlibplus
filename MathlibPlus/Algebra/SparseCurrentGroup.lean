import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Group.Finsupp

namespace MathlibPlus.Algebra.SparseCurrentGroup

/-- Claim 5672: the sparse current group is the additive group of finitely
supported maps from an equality-comparable code set to a field. -/
def sparseCurrentGroup (K F : Type*) [DecidableEq K] [Field F] : Type _ := K →₀ F

noncomputable instance sparseCurrentGroup.addCommGroup
    (K F : Type*) [DecidableEq K] [Field F] :
    AddCommGroup (sparseCurrentGroup K F) := by
  change AddCommGroup (K →₀ F)
  infer_instance

end MathlibPlus.Algebra.SparseCurrentGroup

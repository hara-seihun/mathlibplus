import Mathlib.Combinatorics.SimpleGraph.Copy

namespace MathlibPlus.GraphTheory.LabelledCopyCount

 theorem labelledCopyCount_iso
    {P S T : Type*} [Fintype P] [Fintype S] [Fintype T]
    (pattern : SimpleGraph P) (source : SimpleGraph S) (target : SimpleGraph T)
    (e : source ≃g target) :
    source.labelledCopyCount pattern = target.labelledCopyCount pattern := by
  classical
  letI : Fintype {f : pattern →g source // Function.Injective f} := Subtype.fintype _
  letI : Fintype {f : pattern →g target // Function.Injective f} := Subtype.fintype _
  let f : pattern.Copy source ≃ pattern.Copy target :=
    { toFun := fun c => e.toCopy.comp c
      invFun := fun c => e.symm.toCopy.comp c
      left_inv := by
        intro c
        apply SimpleGraph.Copy.ext
        intro v
        simp [SimpleGraph.Copy.comp_apply]
      right_inv := by
        intro c
        apply SimpleGraph.Copy.ext
        intro v
        simp [SimpleGraph.Copy.comp_apply] }
  have hcard : Fintype.card (pattern.Copy source) = Fintype.card (pattern.Copy target) :=
    Fintype.card_congr f
  simpa [SimpleGraph.labelledCopyCount] using hcard

end MathlibPlus.GraphTheory.LabelledCopyCount

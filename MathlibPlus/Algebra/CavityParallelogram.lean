import MathlibPlus.Basic

namespace MathlibPlus.Algebra.Claim24926

/-- Four pairwise distinct values in one unrooted closure class form the
additive cavity parallelogram exactly when the two displayed pair sums agree.
The class map is explicit because the source claim does not fix a concrete
cavity-value type or closure-class representation. -/
def isAdditiveCavityParallelogram
    {α ι : Type*} [Add α]
    (closureClass : α → ι) (A D B E : α) : Prop :=
  A ≠ D ∧ A ≠ B ∧ A ≠ E ∧ D ≠ B ∧ D ≠ E ∧ B ≠ E ∧
    closureClass A = closureClass D ∧
    closureClass A = closureClass B ∧
    closureClass A = closureClass E ∧
    A + D = B + E

end MathlibPlus.Algebra.Claim24926

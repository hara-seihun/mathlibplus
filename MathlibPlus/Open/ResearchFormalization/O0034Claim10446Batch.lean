import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.O0034Claim10446

noncomputable section
open Classical
open scoped BigOperators

/-- Claim 10446: the explicit binary `[I₄ | J₄ - I₄]` code has the
self-orthogonality, rank-four, and code/dual equality asserted in the source. -/
def binaryC8CodeSelfDual_claim10446_batch : Prop :=
  let G : Matrix (Fin 4) (Fin 8) (ZMod 2) := fun i j =>
    if j.val < 4 then
      if i.val = j.val then 1 else 0
    else if i.val = j.val - 4 then 0 else 1
  let codeword : (Fin 4 → ZMod 2) → (Fin 8 → ZMod 2) :=
    fun u j => ∑ i : Fin 4, u i * G i j
  let dot : (Fin 8 → ZMod 2) → (Fin 8 → ZMod 2) → ZMod 2 :=
    fun v w => ∑ i : Fin 8, v i * w i
  let C : Finset (Fin 8 → ZMod 2) :=
    Finset.univ.filter (fun v => ∃ u : Fin 4 → ZMod 2, codeword u = v)
  let Cperp : Finset (Fin 8 → ZMod 2) :=
    Finset.univ.filter (fun w => ∀ v ∈ C, dot v w = 0)
  G * G.transpose = 0 ∧
    Function.Injective codeword ∧
    C.card = 16 ∧
    C = Cperp

end
end MathlibPlus.Open.ResearchFormalization.O0034Claim10446

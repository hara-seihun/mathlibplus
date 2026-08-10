import Mathlib

/-!
# Open-problem registry

Every open problem in the system is a formally stated `Prop` in the
`MathlibPlus.Open` namespace, declared as a `def ... : Prop`.

Rules (enforced by admission, see `docs/ADMISSION.md`):

* **No proofs in this namespace.** A node is resolved by proving `Node` or `¬ Node`
  as an ordinary theorem in the appropriate area file, after which the registry
  declaration is retired by the coordinator.
* **Equivalences never create nodes.** A statement provably equivalent to an existing
  node is attached to that node in the ledger as an alternate statement, with the
  kernel-checked `↔` theorem living in the area files.
* Reduction moves (split / merge / specialization discharge) are kernel-checked
  implications in the area files, registered as ledger reduction records. They never
  delete obligations, only restructure the frontier.
* Nothing outside `MathlibPlus.Open` may import or depend on this namespace's
  declarations except `Iff`/implication theorems used by registered moves.

Naming: `MathlibPlus.Open.<Area>.<shortName>`. Statement fidelity review happens at
node admission and is the load-bearing human/coordinator gate: the kernel cannot check
that a `Prop` means what the informal problem meant.
-/

namespace MathlibPlus.Open

/-- Example node shape (retired immediately; kept as documentation of form):
a registry node is a `def : Prop`, never a theorem, never an axiom. -/
def exampleNodeShape : Prop := ∀ n : ℕ, n + 0 = n

end MathlibPlus.Open

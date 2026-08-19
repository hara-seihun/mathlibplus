import Mathlib

namespace MathlibPlus.Combinatorics.Claim52499

noncomputable section

/-- A directed edge list is a source-to-sink path when each edge starts at
where the preceding edge ends.  The empty list is the degenerate path. -/
def path52499 {V E : Type*}
    (tail head : E → V) (source sink : V) : List E → Prop
  | [] => source = sink
  | e :: rest => tail e = source ∧ path52499 tail head (head e) sink rest

def edgeResponse52499 {V E : Type*}
    (tail head : E → V) (Φ : V → ℝ) (e : E) : ℝ :=
  Φ (tail e) - Φ (head e)

def pathAggregate52499 {V E : Type*}
    (tail head : E → V) (Φ : V → ℝ) (p : List E) : ℝ :=
  (p.map (edgeResponse52499 tail head Φ)).sum

def endpointCounterexampleTail52499 : Fin 2 → Fin 3
  | 0 => 0
  | 1 => 1

def endpointCounterexampleHead52499 : Fin 2 → Fin 3
  | 0 => 1
  | 1 => 2

def endpointCounterexamplePotential52499 (v : Fin 3) : ℝ :=
  if v = 1 then 1 else 0

def endpointCounterexamplePath52499 : List (Fin 2) := [0, 1]

/-- Claim 52499: exact tail-minus-head responses telescope on every finite
source-to-sink path.  The concrete two-edge witness records why equal scalar
endpoints do not force each edge response to vanish. -/
def claim52499_path_responses_telescope : Prop :=
  (∀ {V E : Type*} (tail head : E → V) (Φ : V → ℝ)
      (source sink : V) (p : List E),
    path52499 tail head source sink p →
      pathAggregate52499 tail head Φ p = Φ source - Φ sink) ∧
  path52499 endpointCounterexampleTail52499
      endpointCounterexampleHead52499 0 2 endpointCounterexamplePath52499 ∧
    endpointCounterexamplePotential52499 0 =
      endpointCounterexamplePotential52499 2 ∧
    pathAggregate52499 endpointCounterexampleTail52499
      endpointCounterexampleHead52499 endpointCounterexamplePotential52499
      endpointCounterexamplePath52499 = 0 ∧
    (∀ e : Fin 2, e ∈ endpointCounterexamplePath52499 →
      edgeResponse52499 endpointCounterexampleTail52499
        endpointCounterexampleHead52499 endpointCounterexamplePotential52499 e ≠ 0)

end

end MathlibPlus.Combinatorics.Claim52499

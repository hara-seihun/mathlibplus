import Mathlib

namespace MathlibPlus.Open.Research.RankTwoVoltageCode

noncomputable section

abbrev Fp (p : ℕ) := ZMod p
abbrev B (p : ℕ) := Fin 2 → Fp p
abbrev D (p : ℕ) := Fin 2 → Fp p
abbrev FunctionSpace (p : ℕ) := B p → D p

def basisVector (p : ℕ) (i : Fin 2) : B p :=
  fun j => if i = j then 1 else 0

def e1 (p : ℕ) : B p := basisVector p 0

def e2 (p : ℕ) : B p := basisVector p 1

def translate {p : ℕ} (w : FunctionSpace p) (a : B p) :
    FunctionSpace p :=
  fun x => w (x + a)

def difference {p : ℕ} (s : FunctionSpace p) (d : B p) :
    FunctionSpace p :=
  fun x => s (x + d) - s x

def c (p : ℕ) (s : FunctionSpace p) (i : Fin 2) :
    FunctionSpace p :=
  difference s (basisVector p i)

def constantFunction {p : ℕ} (d : D p) : FunctionSpace p :=
  fun _ => d

def codeGenerators {p : ℕ} (s : FunctionSpace p) :
    Set (FunctionSpace p) :=
  Set.range constantFunction ∪
    ⋃ i : Fin 2, Set.range (translate (c p s i))

def generatedCode {p : ℕ} (s : FunctionSpace p) :
    Submodule (Fp p) (FunctionSpace p) :=
  Submodule.span (Fp p) (codeGenerators s)

def normalized (p : ℕ) (s : FunctionSpace p) : Prop :=
  s 0 = 0 ∧ s (e1 p) = 0 ∧ s (e2 p) = 0

def translationInvariant {p : ℕ}
    (K : Submodule (Fp p) (FunctionSpace p)) : Prop :=
  ∀ w ∈ K, ∀ a : B p, translate w a ∈ K

/-- The exact hypotheses package includes the prime condition, normalization,
and translation invariance of the generated code. -/
def normalizedRankTwoVoltageCodeData (p : ℕ) (s : FunctionSpace p) : Prop :=
  Nat.Prime p ∧ normalized p s ∧ translationInvariant (generatedCode s)

/-- Pairwise binary closure: the codeword witnessing the two coordinates may
depend on the ordered pair of coordinates. -/
def InBinaryClosure {p : ℕ}
    (K : Submodule (Fp p) (FunctionSpace p))
    (w : FunctionSpace p) : Prop :=
  ∀ x y : B p, ∃ k : FunctionSpace p,
    k ∈ K ∧ k x = w x ∧ k y = w y

end
end MathlibPlus.Open.Research.RankTwoVoltageCode

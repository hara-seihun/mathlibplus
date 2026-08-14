import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Septenary

noncomputable section

abbrev V7 := Fin 2 → ZMod 7
abbrev Color7 := Fin 7

def Pair7 : Type := {s : Finset V7 // s.card = 2}

deriving instance Fintype for Pair7
noncomputable instance : DecidableEq Pair7 := Classical.decEq _

abbrev Vertex7 := Sum V7 Pair7

def VertexColor7 (c : Pair7 → Color7) : Vertex7 → Option Color7
  | Sum.inl _ => none
  | Sum.inr p => some (c p)

def IncidenceAdjacent7 : Vertex7 → Vertex7 → Prop
  | Sum.inl _, Sum.inl _ => False
  | Sum.inr _, Sum.inr _ => False
  | Sum.inl x, Sum.inr p => x ∈ p.1
  | Sum.inr p, Sum.inl x => x ∈ p.1

def ColoredIncidenceIso7 (c d : Pair7 → Color7) : Prop :=
  ∃ e : Equiv.Perm Vertex7,
    (∀ v, VertexColor7 c v = VertexColor7 d (e v)) ∧
    (∀ v w, IncidenceAdjacent7 v w ↔ IncidenceAdjacent7 (e v) (e w))

def GraphSetoid7 : Setoid (Pair7 → Color7) := by
  classical
  refine { r := ColoredIncidenceIso7, iseqv := ?_ }
  refine ⟨?_, ?_, ?_⟩
  · intro c
    refine ⟨Equiv.refl _, ?_, ?_⟩
    · intro v
      rfl
    · intro v w
      rfl
  · intro c d h
    rcases h with ⟨e, hc, ha⟩
    refine ⟨e.symm, ?_, ?_⟩
    · intro v
      have hv := hc (e.symm v)
      simpa using hv.symm
    · intro v w
      simpa using (ha (e.symm v) (e.symm w)).symm
  · intro c d e hcd hde
    rcases hcd with ⟨f, hf, af⟩
    rcases hde with ⟨g, hg, ag⟩
    refine ⟨f.trans g, ?_, ?_⟩
    · intro v
      simpa only [Equiv.trans_apply] using (hf v).trans (hg (f v))
    · intro v w
      simpa only [Equiv.trans_apply] using (af v w).trans (ag (f v) (f w))

def ExactCanonicalLabel7 (c : Pair7 → Color7) : Quotient GraphSetoid7 :=
  Quotient.mk _ c

def claim32711 : Prop :=
  Fintype.card V7 = 49 ∧
    Fintype.card Pair7 = 1176 ∧
    Fintype.card Vertex7 = 1225 ∧
    (∀ c d : Pair7 → Color7,
      ExactCanonicalLabel7 c = ExactCanonicalLabel7 d ↔
        ColoredIncidenceIso7 c d)

end
end MathlibPlus.Open.ResearchFormalization.Septenary

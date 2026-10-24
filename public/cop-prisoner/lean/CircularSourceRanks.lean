import CircleConstruction

/-! A finite source-rank certificate at recipient zero proves every rotation
of an explicit circulant base/envelope pair. All optional subsets are covered. -/
namespace Delivery.CircularSourceRanks
open CyclicArithmetic CirclePropagation CircleEnvelope RobustLayers RobustTwoMove
open FiniteGame Extremal DenseCombinatorics

def arc {n : Nat} (offsets : List Nat) (s t : Fin n) : Prop :=
  s≠t ∧ offsets.any (fun d => decide (t=shift s d))=true

instance {n : Nat} (offsets : List Nat) (s t : Fin n) : Decidable (arc offsets s t) :=
  inferInstanceAs (Decidable (_∧_))

theorem arc_eq {n : Nat} (offsets : List Nat) :
    arc (n:=n) offsets=Envelope (fun d => d∈offsets) := by
  funext s t
  apply propext
  simp only [arc,Envelope,List.any_eq_true,decide_eq_true_eq]

theorem shift_comm {n : Nat} (s : Fin n) (a b : Nat) :
    shift (shift s a) b=shift (shift s b) a := by
  simp only [shift_add,Nat.add_comm a b]

theorem arc_shift {n : Nat} (offsets : List Nat) (s t : Fin n) (d : Nat) :
    arc offsets (shift s d) (shift t d) ↔ arc offsets s t := by
  simp only [arc_eq,Envelope]
  constructor
  · rintro ⟨ne,e,he,equal⟩
    refine ⟨fun same => ne (congrArg (fun x => shift x d) same),e,he,?_⟩
    apply shift_injective (d:=d)
    exact equal.trans (shift_comm s d e)
  · rintro ⟨ne,e,he,equal⟩
    refine ⟨fun same => ne (shift_injective same),e,he,?_⟩
    rw [equal,shift_comm]

theorem legal_shift {n : Nat} (offsets : List Nat) (s t : Fin n) (d : Nat) :
    Legal (arc offsets) (shift s d) (shift t d) ↔ Legal (arc offsets) s t := by
  constructor
  · rintro (same | edge)
    · exact Or.inl (shift_injective same)
    · exact Or.inr ((arc_shift offsets s t d).mp edge)
  · rintro (same | edge)
    · exact Or.inl (congrArg (fun x => shift x d) same)
    · exact Or.inr ((arc_shift offsets s t d).mpr edge)

theorem retreat_shift {n : Nat} (s : Fin n) {d : Nat} (small : d≤n) :
    retreat (shift s d) d=s := by
  rw [retreat,shift_add,show d+(n-d)=n by omega,shift_period]

/-- The finite checker only tries the listed base offsets as successors. -/
def Checked {n : Nat} (positive : 0<n) (C A : List Nat) (rank : Fin n → Nat) : Prop :=
  ∀ s, s≠⟨0,positive⟩ →
    (arc C s ⟨0,positive⟩ ∧ 1≤rank s) ∨
    ∀ c, c≠s → C.any (fun d => decide
      (arc C s (shift s d) ∧ c≠shift s d ∧ ¬arc A c (shift s d) ∧
        rank (shift s d)<rank s))=true

theorem checked_ranks {n : Nat} (positive : 0<n) (C A : List Nat) (rank : Fin n → Nat)
    (checked : Checked positive C A rank) : SourceRanks (arc C) (arc A) ⟨0,positive⟩ rank := by
  intro s different
  rcases checked s different with direct | branch
  · exact Or.inl direct
  · right
    intro c initial
    obtain ⟨d,_,good⟩ := List.any_eq_true.mp (branch c initial)
    have h := of_decide_eq_true good
    exact ⟨shift s d,h.1,fun reachable => reachable.elim h.2.1 h.2.2.1,h.2.2.2⟩

theorem rotate_ranks {n : Nat} (positive : 0<n) (C A : List Nat) (rank : Fin n → Nat)
    (ranks : SourceRanks (arc C) (arc A) ⟨0,positive⟩ rank) (t : Fin n) :
    SourceRanks (arc C) (arc A) t (fun s => rank (retreat s t.val)) := by
  intro s different
  let s0 := retreat s t.val
  have ts : t.val≤n := Nat.le_of_lt t.isLt
  have target : shift (⟨0,positive⟩ : Fin n) t.val=t := by
    apply Fin.ext
    simp only [shift,Nat.zero_add,Nat.mod_eq_of_lt t.isLt]
  have ne : s0≠⟨0,positive⟩ := by
    intro same
    have h := congrArg (fun x => shift x t.val) same
    apply different
    simpa only [s0,retreat_cancel s ts,target] using h
  rcases ranks s0 ne with direct | branch
  · left
    refine ⟨?_,direct.2⟩
    have h := (arc_shift C s0 ⟨0,positive⟩ t.val).mpr direct.1
    simpa only [s0,retreat_cancel s ts,target] using h
  · right
    intro c initial
    let c0 := retreat c t.val
    have initial0 : c0≠s0 := by
      intro same
      have h := congrArg (fun x => shift x t.val) same
      apply initial
      simpa only [c0,s0,retreat_cancel _ ts] using h
    obtain ⟨z,move,safe,smaller⟩ := branch c0 initial0
    refine ⟨shift z t.val,?_,?_,?_⟩
    · have h := (arc_shift C s0 z t.val).mpr move
      simpa only [s0,retreat_cancel s ts] using h
    · intro reply
      apply safe
      apply (legal_shift A c0 z t.val).mp
      simpa only [c0,retreat_cancel c ts] using reply
    · simpa only [retreat_shift _ ts] using smaller

theorem maximum {n m : Nat} (positive : 0<n) (C A : List Nat) (rank : Fin n → Nat)
    (subset : ∀ d∈C, d∈A)
    (ranks : SourceRanks (arc C) (arc A) ⟨0,positive⟩ rank)
    (low : arcCount (arc (n:=n) C)≤m) (high : m≤arcCount (arc (n:=n) A)) :
    IsMaximum n m (n*(n-1)-m) := by
  have sub : Subgraph (arc (n:=n) C) (arc A) := by
    intro s t edge
    rw [arc_eq] at edge ⊢
    exact ⟨edge.1,edge.2.choose,subset _ edge.2.choose_spec.1,edge.2.choose_spec.2⟩
  apply GuaranteedPrefix.maximum (arc C) (arc A) sub (fun _ e => e.1 rfl)
  · intro G lower upper s t
    exact universal_guaranteed
      (ranked_envelope_universal lower upper (rotate_ranks positive C A rank ranks t) s)
  · exact low
  · exact high

#print axioms rotate_ranks
#print axioms maximum
end Delivery.CircularSourceRanks

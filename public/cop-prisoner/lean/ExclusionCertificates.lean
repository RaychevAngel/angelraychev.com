import Extremal
import CampingObstruction

/-! A finite upper-exclusion interface with an explicit completeness premise,
and a kernel-checked pilot covering all 64 loopless three-vertex graphs.
The pilot is not evidence for the larger external enumerations. -/
namespace Delivery.ExclusionCertificates
open FiniteGame Extremal

structure FiniteCover (n : Nat) (admissible : Graph (Fin n) → Prop) where
  Index : Type
  cases : List Index
  graph : Index → Graph (Fin n)
  complete : ∀ E, admissible E → ∃ i, i ∈ cases ∧ E = graph i

theorem upper_from_cover {n bound : Nat} {admissible : Graph (Fin n) → Prop}
    (cover : FiniteCover n admissible)
    (leaves : ∀ i, i ∈ cover.cases → score (cover.graph i) ≤ bound) :
    ∀ E, admissible E → score E ≤ bound := by
  intro E allowed
  obtain ⟨i, listed, same⟩ := cover.complete E allowed
  rw [same]
  exact leaves i listed

theorem camping_not_guaranteed {V : Type} {E : Graph V} {s t c : V}
    (distinct : s ≠ t) (missing : ¬ E s t) (initial : c ≠ s)
    (covers : ∀ z, E z t → Legal E c z) : ¬ Guaranteed E s t := by
  intro guaranteed
  obtain ⟨k, win⟩ := guaranteed c initial
  exact camping_predecessor_obstruction distinct missing covers win

structure Bits3 where
  b01 : Bool
  b02 : Bool
  b10 : Bool
  b12 : Bool
  b20 : Bool
  b21 : Bool
  deriving DecidableEq

def allBits3 : List Bits3 :=
  [false,true].flatMap fun a => [false,true].flatMap fun b =>
  [false,true].flatMap fun c => [false,true].flatMap fun d =>
  [false,true].flatMap fun e => [false,true].map fun f => ⟨a,b,c,d,e,f⟩

def bit3 (b : Bits3) (s t : Fin 3) : Bool :=
  match s.val, t.val with
  | 0, 1 => b.b01
  | 0, 2 => b.b02
  | 1, 0 => b.b10
  | 1, 2 => b.b12
  | 2, 0 => b.b20
  | 2, 1 => b.b21
  | _, _ => false

def graph3 (b : Bits3) (s t : Fin 3) : Prop := bit3 b s t = true
instance (b : Bits3) (s t : Fin 3) : Decidable (graph3 b s t) :=
  inferInstanceAs (Decidable (_ = _))

theorem allBits3_complete (b : Bits3) : b ∈ allBits3 := by
  rcases b with ⟨a,b,c,d,e,f⟩
  revert a b c d e f
  decide +kernel

theorem allBits3_count : allBits3.length = 64 := by decide +kernel

/-- Every loopless graph, including all opposite-arrow choices, is represented.
This is the coverage proof missing from mere checks of listed examples. -/
theorem graph3_complete (E : Graph (Fin 3)) (loopless : Loopless E) :
    ∃ b, b ∈ allBits3 ∧ E = graph3 b := by
  classical
  let b : Bits3 := ⟨decide (E 0 1), decide (E 0 2), decide (E 1 0),
    decide (E 1 2), decide (E 2 0), decide (E 2 1)⟩
  refine ⟨b, allBits3_complete b, ?_⟩
  funext s t
  apply propext
  rcases s with ⟨s,hs⟩
  rcases t with ⟨t,ht⟩
  have scases : s = 0 ∨ s = 1 ∨ s = 2 := by omega
  have tcases : t = 0 ∨ t = 1 ∨ t = 2 := by omega
  rcases scases with rfl | rfl | rfl <;>
    rcases tcases with rfl | rfl | rfl <;>
    simp [graph3, bit3, b, loopless 0, loopless 1, loopless 2]

def threeVertexCover : FiniteCover 3 Loopless where
  Index := Bits3
  cases := allBits3
  graph := graph3
  complete := graph3_complete

/-- Full 64-graph kernel calculation; a legal camping start is supplied for
every missing pair. No external solver or sampled traversal is trusted. -/
theorem graph3_camping (b : Bits3) :
    ∀ s t : Fin 3, s ≠ t → ¬ graph3 b s t →
      ∃ c : Fin 3, c ≠ s ∧ ∀ z, graph3 b z t → Legal (graph3 b) c z := by
  rcases b with ⟨a,b,c,d,e,f⟩
  revert a b c d e f
  unfold Legal
  decide +kernel

theorem graph3_score_zero (b : Bits3) : score (graph3 b) = 0 := by
  apply score_eq_zero
  intro s t distinct missing
  obtain ⟨c, initial, covers⟩ := graph3_camping b s t distinct missing
  exact camping_not_guaranteed distinct missing initial covers

theorem three_vertex_upper (E : Graph (Fin 3)) (loopless : Loopless E) :
    score E ≤ 0 :=
  upper_from_cover threeVertexCover
    (fun b _ => Nat.le_of_eq (graph3_score_zero b)) E loopless

theorem three_vertex_score_zero (E : Graph (Fin 3)) (loopless : Loopless E) :
    score E = 0 := Nat.eq_zero_of_le_zero (three_vertex_upper E loopless)

#print axioms upper_from_cover
#print axioms graph3_complete
#print axioms graph3_camping
#print axioms three_vertex_upper
end Delivery.ExclusionCertificates

import GroupedGraphRanks
import EnvelopeRowSymmetry
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.FiveFinite70Base
open FiniteGame Extremal GroupedArena
/- Literal five-type recipe; local window geometry is not assumed here. -/
def lowerRow (x : Nat) : List (Fin 70) := (if x < 35 then (if x < 17 then (if x < 8 then (if x < 4 then (if x < 2 then (if x < 1 then [1,5] else [2,67]) else (if x < 3 then [3,69] else [4,68])) else (if x < 6 then (if x < 5 then [5,66] else [6,10]) else (if x < 7 then [2,7] else [4,8]))) else (if x < 12 then (if x < 10 then (if x < 9 then [3,9] else [1,10]) else (if x < 11 then [11,15] else [7,12])) else (if x < 14 then (if x < 13 then [9,13] else [8,14]) else (if x < 15 then [6,15] else (if x < 16 then [16,20] else [12,17]))))) else (if x < 26 then (if x < 21 then (if x < 19 then (if x < 18 then [14,18] else [13,19]) else (if x < 20 then [11,20] else [21,25])) else (if x < 23 then (if x < 22 then [17,22] else [19,23]) else (if x < 24 then [18,24] else (if x < 25 then [16,25] else [26,30])))) else (if x < 30 then (if x < 28 then (if x < 27 then [22,27] else [24,28]) else (if x < 29 then [23,29] else [21,30])) else (if x < 32 then (if x < 31 then [31,35] else [27,32]) else (if x < 33 then [29,33] else (if x < 34 then [28,34] else [26,35])))))) else (if x < 52 then (if x < 43 then (if x < 39 then (if x < 37 then (if x < 36 then [36,40] else [32,37]) else (if x < 38 then [34,38] else [33,39])) else (if x < 41 then (if x < 40 then [31,40] else [41,45]) else (if x < 42 then [37,42] else [39,43]))) else (if x < 47 then (if x < 45 then (if x < 44 then [38,44] else [36,45]) else (if x < 46 then [46,50] else [42,47])) else (if x < 49 then (if x < 48 then [44,48] else [43,49]) else (if x < 50 then [41,50] else (if x < 51 then [51,55] else [47,52]))))) else (if x < 61 then (if x < 56 then (if x < 54 then (if x < 53 then [49,53] else [48,54]) else (if x < 55 then [46,55] else [56,60])) else (if x < 58 then (if x < 57 then [52,57] else [54,58]) else (if x < 59 then [53,59] else (if x < 60 then [51,60] else [61,65])))) else (if x < 65 then (if x < 63 then (if x < 62 then [57,62] else [59,63]) else (if x < 64 then [58,64] else [56,65])) else (if x < 67 then (if x < 66 then [0,66] else [62,67]) else (if x < 68 then [64,68] else (if x < 69 then [63,69] else [0,61])))))))
def upperRow (x : Nat) : List (Fin 70) := (if x < 35 then (if x < 17 then (if x < 8 then (if x < 4 then (if x < 2 then (if x < 1 then [1,5,15] else [2,15,67]) else (if x < 3 then [3,15,69] else [4,15,68])) else (if x < 6 then (if x < 5 then [5,15,66] else [6,10,20]) else (if x < 7 then [2,7,20] else [4,8,20]))) else (if x < 12 then (if x < 10 then (if x < 9 then [3,9,20] else [1,10,20]) else (if x < 11 then [11,15,25] else [7,12,25])) else (if x < 14 then (if x < 13 then [9,13,25] else [8,14,25]) else (if x < 15 then [6,15,25] else (if x < 16 then [16,20,30] else [12,17,30]))))) else (if x < 26 then (if x < 21 then (if x < 19 then (if x < 18 then [14,18,30] else [13,19,30]) else (if x < 20 then [11,20,30] else [21,25,35])) else (if x < 23 then (if x < 22 then [17,22,35] else [19,23,35]) else (if x < 24 then [18,24,35] else (if x < 25 then [16,25,35] else [26,30,40])))) else (if x < 30 then (if x < 28 then (if x < 27 then [22,27,40] else [24,28,40]) else (if x < 29 then [23,29,40] else [21,30,40])) else (if x < 32 then (if x < 31 then [31,35,45] else [27,32,45]) else (if x < 33 then [29,33,45] else (if x < 34 then [28,34,45] else [26,35,45])))))) else (if x < 52 then (if x < 43 then (if x < 39 then (if x < 37 then (if x < 36 then [36,40,50] else [32,37,50]) else (if x < 38 then [34,38,50] else [33,39,50])) else (if x < 41 then (if x < 40 then [31,40,50] else [41,45,55]) else (if x < 42 then [37,42,55] else [39,43,55]))) else (if x < 47 then (if x < 45 then (if x < 44 then [38,44,55] else [36,45,55]) else (if x < 46 then [46,50,60] else [42,47,60])) else (if x < 49 then (if x < 48 then [44,48,60] else [43,49,60]) else (if x < 50 then [41,50,60] else (if x < 51 then [51,55,65] else [47,52,65]))))) else (if x < 61 then (if x < 56 then (if x < 54 then (if x < 53 then [49,53,65] else [48,54,65]) else (if x < 55 then [46,55,65] else [0,56,60])) else (if x < 58 then (if x < 57 then [0,52,57] else [0,54,58]) else (if x < 59 then [0,53,59] else (if x < 60 then [0,51,60] else [5,61,65])))) else (if x < 65 then (if x < 63 then (if x < 62 then [5,57,62] else [5,59,63]) else (if x < 64 then [5,58,64] else [5,56,65])) else (if x < 67 then (if x < 66 then [0,10,66] else [10,62,67]) else (if x < 68 then [10,64,68] else (if x < 69 then [10,63,69] else [0,10,61])))))))
def lowerRows (s : Fin 70) := lowerRow s.val
def upperRows (s : Fin 70) := upperRow s.val
def lower := EnvelopeRowSymmetry.edge lowerRows
def upper := EnvelopeRowSymmetry.edge upperRows
instance (s t : Fin 70) : Decidable (lower s t) := inferInstanceAs (Decidable (t∈lowerRows s))
instance (s t : Fin 70) : Decidable (upper s t) := inferInstanceAs (Decidable (t∈upperRows s))
def replyMasks (c : Fin 70) : Nat := maskOf (c::upperRows c)
theorem reply_coverage : ∀ c d, Legal upper c d → Has (replyMasks c) d := by
  intro c d legal
  apply (has_maskOf _ _).mpr
  rcases legal with same|edge
  · exact List.mem_cons.mpr (Or.inl same.symm)
  · exact List.mem_cons.mpr (Or.inr edge)
theorem inclusion : RobustTwoMove.Subgraph lower upper := by
  unfold RobustTwoMove.Subgraph; decide +kernel
theorem loopless : Loopless upper := by unfold Loopless; decide +kernel
theorem counts : arcCount lower=140 ∧ arcCount upper=210 := by
  constructor <;> rw [arcCount_eq] <;> decide +kernel

def rotate (t x : Fin 70) : Fin 70 := ⟨(x.val+5*(t.val/5))%70,Nat.mod_lt _ (by decide)⟩
def unrotate (t x : Fin 70) : Fin 70 := ⟨(x.val+70-5*(t.val/5))%70,Nat.mod_lt _ (by decide)⟩
theorem inverses : ∀t x, unrotate t (rotate t x)=x ∧ rotate t (unrotate t x)=x := by decide +kernel
theorem lower_forward : ∀t s, (lowerRows s).all (fun d => decide (rotate t d∈lowerRows (rotate t s)))=true := by decide +kernel
theorem lower_backward : ∀t s, (lowerRows (rotate t s)).all (fun d => decide (unrotate t d∈lowerRows s))=true := by decide +kernel
theorem upper_forward : ∀t s, (upperRows s).all (fun d => decide (rotate t d∈upperRows (rotate t s)))=true := by decide +kernel
theorem upper_backward : ∀t s, (upperRows (rotate t s)).all (fun d => decide (unrotate t d∈upperRows s))=true := by decide +kernel
noncomputable def rotation (t : Fin 70) : GraphRelabeling.Iso lower lower :=
  EnvelopeRowSymmetry.iso_of_rows lowerRows (rotate t) (unrotate t)
    (fun x => (inverses t x).1) (fun x => (inverses t x).2)
    (fun s d member => of_decide_eq_true ((List.all_eq_true.mp (lower_forward t s)) d member))
    (fun s d member => of_decide_eq_true ((List.all_eq_true.mp (lower_backward t s)) d member))
theorem upper_invariant (t : Fin 70) : ∀s d,upper s d ↔ upper ((rotation t).toFun s) ((rotation t).toFun d) := by
  exact EnvelopeRowSymmetry.invariant_of_rows upperRows (rotate t) (unrotate t)
    (fun x => (inverses t x).1)
    (fun s d member => of_decide_eq_true ((List.all_eq_true.mp (upper_forward t s)) d member))
    (fun s d member => of_decide_eq_true ((List.all_eq_true.mp (upper_backward t s)) d member))
def representative (t : Fin 70) : Fin 70 := ⟨t.val%5,by omega⟩
theorem representative_small (t : Fin 70) : (representative t).val<5 := Nat.mod_lt _ (by decide)
theorem target_cover : ∀t,rotate t (representative t)=t := by decide +kernel
#print axioms counts
#print axioms upper_invariant
end Delivery.FiveFinite70Base

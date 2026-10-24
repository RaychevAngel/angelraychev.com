import GroupedGraphRanks
import EnvelopeRowSymmetry
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.FiveFinite75Base
open FiniteGame Extremal GroupedArena
/- Literal five-type recipe; local window geometry is not assumed here. -/
def lowerRow (x : Nat) : List (Fin 75) := (if x < 37 then (if x < 18 then (if x < 9 then (if x < 4 then (if x < 2 then (if x < 1 then [1,5] else [2,72]) else (if x < 3 then [3,74] else [4,73])) else (if x < 6 then (if x < 5 then [5,71] else [6,10]) else (if x < 7 then [2,7] else (if x < 8 then [4,8] else [3,9])))) else (if x < 13 then (if x < 11 then (if x < 10 then [1,10] else [11,15]) else (if x < 12 then [7,12] else [9,13])) else (if x < 15 then (if x < 14 then [8,14] else [6,15]) else (if x < 16 then [16,20] else (if x < 17 then [12,17] else [14,18]))))) else (if x < 27 then (if x < 22 then (if x < 20 then (if x < 19 then [13,19] else [11,20]) else (if x < 21 then [21,25] else [17,22])) else (if x < 24 then (if x < 23 then [19,23] else [18,24]) else (if x < 25 then [16,25] else (if x < 26 then [26,30] else [22,27])))) else (if x < 32 then (if x < 29 then (if x < 28 then [24,28] else [23,29]) else (if x < 30 then [21,30] else (if x < 31 then [31,35] else [27,32]))) else (if x < 34 then (if x < 33 then [29,33] else [28,34]) else (if x < 35 then [26,35] else (if x < 36 then [36,40] else [32,37])))))) else (if x < 56 then (if x < 46 then (if x < 41 then (if x < 39 then (if x < 38 then [34,38] else [33,39]) else (if x < 40 then [31,40] else [41,45])) else (if x < 43 then (if x < 42 then [37,42] else [39,43]) else (if x < 44 then [38,44] else (if x < 45 then [36,45] else [46,50])))) else (if x < 51 then (if x < 48 then (if x < 47 then [42,47] else [44,48]) else (if x < 49 then [43,49] else (if x < 50 then [41,50] else [51,55]))) else (if x < 53 then (if x < 52 then [47,52] else [49,53]) else (if x < 54 then [48,54] else (if x < 55 then [46,55] else [56,60]))))) else (if x < 65 then (if x < 60 then (if x < 58 then (if x < 57 then [52,57] else [54,58]) else (if x < 59 then [53,59] else [51,60])) else (if x < 62 then (if x < 61 then [61,65] else [57,62]) else (if x < 63 then [59,63] else (if x < 64 then [58,64] else [56,65])))) else (if x < 70 then (if x < 67 then (if x < 66 then [66,70] else [62,67]) else (if x < 68 then [64,68] else (if x < 69 then [63,69] else [61,70]))) else (if x < 72 then (if x < 71 then [0,71] else [67,72]) else (if x < 73 then [69,73] else (if x < 74 then [68,74] else [0,66])))))))
def upperRow (x : Nat) : List (Fin 75) := (if x < 37 then (if x < 18 then (if x < 9 then (if x < 4 then (if x < 2 then (if x < 1 then [1,5,15] else [2,15,72]) else (if x < 3 then [3,15,74] else [4,15,73])) else (if x < 6 then (if x < 5 then [5,15,71] else [6,10,20]) else (if x < 7 then [2,7,20] else (if x < 8 then [4,8,20] else [3,9,20])))) else (if x < 13 then (if x < 11 then (if x < 10 then [1,10,20] else [11,15,25]) else (if x < 12 then [7,12,25] else [9,13,25])) else (if x < 15 then (if x < 14 then [8,14,25] else [6,15,25]) else (if x < 16 then [16,20,30] else (if x < 17 then [12,17,30] else [14,18,30]))))) else (if x < 27 then (if x < 22 then (if x < 20 then (if x < 19 then [13,19,30] else [11,20,30]) else (if x < 21 then [21,25,35] else [17,22,35])) else (if x < 24 then (if x < 23 then [19,23,35] else [18,24,35]) else (if x < 25 then [16,25,35] else (if x < 26 then [26,30,40] else [22,27,40])))) else (if x < 32 then (if x < 29 then (if x < 28 then [24,28,40] else [23,29,40]) else (if x < 30 then [21,30,40] else (if x < 31 then [31,35,45] else [27,32,45]))) else (if x < 34 then (if x < 33 then [29,33,45] else [28,34,45]) else (if x < 35 then [26,35,45] else (if x < 36 then [36,40,50] else [32,37,50])))))) else (if x < 56 then (if x < 46 then (if x < 41 then (if x < 39 then (if x < 38 then [34,38,50] else [33,39,50]) else (if x < 40 then [31,40,50] else [41,45,55])) else (if x < 43 then (if x < 42 then [37,42,55] else [39,43,55]) else (if x < 44 then [38,44,55] else (if x < 45 then [36,45,55] else [46,50,60])))) else (if x < 51 then (if x < 48 then (if x < 47 then [42,47,60] else [44,48,60]) else (if x < 49 then [43,49,60] else (if x < 50 then [41,50,60] else [51,55,65]))) else (if x < 53 then (if x < 52 then [47,52,65] else [49,53,65]) else (if x < 54 then [48,54,65] else (if x < 55 then [46,55,65] else [56,60,70]))))) else (if x < 65 then (if x < 60 then (if x < 58 then (if x < 57 then [52,57,70] else [54,58,70]) else (if x < 59 then [53,59,70] else [51,60,70])) else (if x < 62 then (if x < 61 then [0,61,65] else [0,57,62]) else (if x < 63 then [0,59,63] else (if x < 64 then [0,58,64] else [0,56,65])))) else (if x < 70 then (if x < 67 then (if x < 66 then [5,66,70] else [5,62,67]) else (if x < 68 then [5,64,68] else (if x < 69 then [5,63,69] else [5,61,70]))) else (if x < 72 then (if x < 71 then [0,10,71] else [10,67,72]) else (if x < 73 then [10,69,73] else (if x < 74 then [10,68,74] else [0,10,66])))))))
def lowerRows (s : Fin 75) := lowerRow s.val
def upperRows (s : Fin 75) := upperRow s.val
def lower := EnvelopeRowSymmetry.edge lowerRows
def upper := EnvelopeRowSymmetry.edge upperRows
instance (s t : Fin 75) : Decidable (lower s t) := inferInstanceAs (Decidable (t∈lowerRows s))
instance (s t : Fin 75) : Decidable (upper s t) := inferInstanceAs (Decidable (t∈upperRows s))
def replyMasks (c : Fin 75) : Nat := maskOf (c::upperRows c)
theorem reply_coverage : ∀ c d, Legal upper c d → Has (replyMasks c) d := by
  intro c d legal
  apply (has_maskOf _ _).mpr
  rcases legal with same|edge
  · exact List.mem_cons.mpr (Or.inl same.symm)
  · exact List.mem_cons.mpr (Or.inr edge)
theorem inclusion : RobustTwoMove.Subgraph lower upper := by
  unfold RobustTwoMove.Subgraph; decide +kernel
theorem loopless : Loopless upper := by unfold Loopless; decide +kernel
theorem counts : arcCount lower=150 ∧ arcCount upper=225 := by
  constructor <;> rw [arcCount_eq] <;> decide +kernel

def rotate (t x : Fin 75) : Fin 75 := ⟨(x.val+5*(t.val/5))%75,Nat.mod_lt _ (by decide)⟩
def unrotate (t x : Fin 75) : Fin 75 := ⟨(x.val+75-5*(t.val/5))%75,Nat.mod_lt _ (by decide)⟩
theorem inverses : ∀t x, unrotate t (rotate t x)=x ∧ rotate t (unrotate t x)=x := by decide +kernel
theorem lower_forward : ∀t s, (lowerRows s).all (fun d => decide (rotate t d∈lowerRows (rotate t s)))=true := by decide +kernel
theorem lower_backward : ∀t s, (lowerRows (rotate t s)).all (fun d => decide (unrotate t d∈lowerRows s))=true := by decide +kernel
theorem upper_forward : ∀t s, (upperRows s).all (fun d => decide (rotate t d∈upperRows (rotate t s)))=true := by decide +kernel
theorem upper_backward : ∀t s, (upperRows (rotate t s)).all (fun d => decide (unrotate t d∈upperRows s))=true := by decide +kernel
noncomputable def rotation (t : Fin 75) : GraphRelabeling.Iso lower lower :=
  EnvelopeRowSymmetry.iso_of_rows lowerRows (rotate t) (unrotate t)
    (fun x => (inverses t x).1) (fun x => (inverses t x).2)
    (fun s d member => of_decide_eq_true ((List.all_eq_true.mp (lower_forward t s)) d member))
    (fun s d member => of_decide_eq_true ((List.all_eq_true.mp (lower_backward t s)) d member))
theorem upper_invariant (t : Fin 75) : ∀s d,upper s d ↔ upper ((rotation t).toFun s) ((rotation t).toFun d) := by
  exact EnvelopeRowSymmetry.invariant_of_rows upperRows (rotate t) (unrotate t)
    (fun x => (inverses t x).1)
    (fun s d member => of_decide_eq_true ((List.all_eq_true.mp (upper_forward t s)) d member))
    (fun s d member => of_decide_eq_true ((List.all_eq_true.mp (upper_backward t s)) d member))
def representative (t : Fin 75) : Fin 75 := ⟨t.val%5,by omega⟩
theorem representative_small (t : Fin 75) : (representative t).val<5 := Nat.mod_lt _ (by decide)
theorem target_cover : ∀t,rotate t (representative t)=t := by decide +kernel
#print axioms counts
#print axioms upper_invariant
end Delivery.FiveFinite75Base

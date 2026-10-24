import GroupedGraphRanks
import EnvelopeRowSymmetry
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.FiveFinite65Base
open FiniteGame Extremal GroupedArena
/- Literal five-type recipe; local window geometry is not assumed here. -/
def lowerRow (x : Nat) : List (Fin 65) := (if x < 32 then (if x < 16 then (if x < 8 then (if x < 4 then (if x < 2 then (if x < 1 then [1,5] else [2,62]) else (if x < 3 then [3,64] else [4,63])) else (if x < 6 then (if x < 5 then [5,61] else [6,10]) else (if x < 7 then [2,7] else [4,8]))) else (if x < 12 then (if x < 10 then (if x < 9 then [3,9] else [1,10]) else (if x < 11 then [11,15] else [7,12])) else (if x < 14 then (if x < 13 then [9,13] else [8,14]) else (if x < 15 then [6,15] else [16,20])))) else (if x < 24 then (if x < 20 then (if x < 18 then (if x < 17 then [12,17] else [14,18]) else (if x < 19 then [13,19] else [11,20])) else (if x < 22 then (if x < 21 then [21,25] else [17,22]) else (if x < 23 then [19,23] else [18,24]))) else (if x < 28 then (if x < 26 then (if x < 25 then [16,25] else [26,30]) else (if x < 27 then [22,27] else [24,28])) else (if x < 30 then (if x < 29 then [23,29] else [21,30]) else (if x < 31 then [31,35] else [27,32]))))) else (if x < 48 then (if x < 40 then (if x < 36 then (if x < 34 then (if x < 33 then [29,33] else [28,34]) else (if x < 35 then [26,35] else [36,40])) else (if x < 38 then (if x < 37 then [32,37] else [34,38]) else (if x < 39 then [33,39] else [31,40]))) else (if x < 44 then (if x < 42 then (if x < 41 then [41,45] else [37,42]) else (if x < 43 then [39,43] else [38,44])) else (if x < 46 then (if x < 45 then [36,45] else [46,50]) else (if x < 47 then [42,47] else [44,48])))) else (if x < 56 then (if x < 52 then (if x < 50 then (if x < 49 then [43,49] else [41,50]) else (if x < 51 then [51,55] else [47,52])) else (if x < 54 then (if x < 53 then [49,53] else [48,54]) else (if x < 55 then [46,55] else [56,60]))) else (if x < 60 then (if x < 58 then (if x < 57 then [52,57] else [54,58]) else (if x < 59 then [53,59] else [51,60])) else (if x < 62 then (if x < 61 then [0,61] else [57,62]) else (if x < 63 then [59,63] else (if x < 64 then [58,64] else [0,56])))))))
def upperRow (x : Nat) : List (Fin 65) := (if x < 32 then (if x < 16 then (if x < 8 then (if x < 4 then (if x < 2 then (if x < 1 then [1,5,15] else [2,15,62]) else (if x < 3 then [3,15,64] else [4,15,63])) else (if x < 6 then (if x < 5 then [5,15,61] else [6,10,20]) else (if x < 7 then [2,7,20] else [4,8,20]))) else (if x < 12 then (if x < 10 then (if x < 9 then [3,9,20] else [1,10,20]) else (if x < 11 then [11,15,25] else [7,12,25])) else (if x < 14 then (if x < 13 then [9,13,25] else [8,14,25]) else (if x < 15 then [6,15,25] else [16,20,30])))) else (if x < 24 then (if x < 20 then (if x < 18 then (if x < 17 then [12,17,30] else [14,18,30]) else (if x < 19 then [13,19,30] else [11,20,30])) else (if x < 22 then (if x < 21 then [21,25,35] else [17,22,35]) else (if x < 23 then [19,23,35] else [18,24,35]))) else (if x < 28 then (if x < 26 then (if x < 25 then [16,25,35] else [26,30,40]) else (if x < 27 then [22,27,40] else [24,28,40])) else (if x < 30 then (if x < 29 then [23,29,40] else [21,30,40]) else (if x < 31 then [31,35,45] else [27,32,45]))))) else (if x < 48 then (if x < 40 then (if x < 36 then (if x < 34 then (if x < 33 then [29,33,45] else [28,34,45]) else (if x < 35 then [26,35,45] else [36,40,50])) else (if x < 38 then (if x < 37 then [32,37,50] else [34,38,50]) else (if x < 39 then [33,39,50] else [31,40,50]))) else (if x < 44 then (if x < 42 then (if x < 41 then [41,45,55] else [37,42,55]) else (if x < 43 then [39,43,55] else [38,44,55])) else (if x < 46 then (if x < 45 then [36,45,55] else [46,50,60]) else (if x < 47 then [42,47,60] else [44,48,60])))) else (if x < 56 then (if x < 52 then (if x < 50 then (if x < 49 then [43,49,60] else [41,50,60]) else (if x < 51 then [0,51,55] else [0,47,52])) else (if x < 54 then (if x < 53 then [0,49,53] else [0,48,54]) else (if x < 55 then [0,46,55] else [5,56,60]))) else (if x < 60 then (if x < 58 then (if x < 57 then [5,52,57] else [5,54,58]) else (if x < 59 then [5,53,59] else [5,51,60])) else (if x < 62 then (if x < 61 then [0,10,61] else [10,57,62]) else (if x < 63 then [10,59,63] else (if x < 64 then [10,58,64] else [0,10,56])))))))
def lowerRows (s : Fin 65) := lowerRow s.val
def upperRows (s : Fin 65) := upperRow s.val
def lower := EnvelopeRowSymmetry.edge lowerRows
def upper := EnvelopeRowSymmetry.edge upperRows
instance (s t : Fin 65) : Decidable (lower s t) := inferInstanceAs (Decidable (t∈lowerRows s))
instance (s t : Fin 65) : Decidable (upper s t) := inferInstanceAs (Decidable (t∈upperRows s))
def replyMasks (c : Fin 65) : Nat := maskOf (c::upperRows c)
theorem reply_coverage : ∀ c d, Legal upper c d → Has (replyMasks c) d := by
  intro c d legal
  apply (has_maskOf _ _).mpr
  rcases legal with same|edge
  · exact List.mem_cons.mpr (Or.inl same.symm)
  · exact List.mem_cons.mpr (Or.inr edge)
theorem inclusion : RobustTwoMove.Subgraph lower upper := by
  unfold RobustTwoMove.Subgraph; decide +kernel
theorem loopless : Loopless upper := by unfold Loopless; decide +kernel
theorem counts : arcCount lower=130 ∧ arcCount upper=195 := by
  constructor <;> rw [arcCount_eq] <;> decide +kernel

def rotate (t x : Fin 65) : Fin 65 := ⟨(x.val+5*(t.val/5))%65,Nat.mod_lt _ (by decide)⟩
def unrotate (t x : Fin 65) : Fin 65 := ⟨(x.val+65-5*(t.val/5))%65,Nat.mod_lt _ (by decide)⟩
theorem inverses : ∀t x, unrotate t (rotate t x)=x ∧ rotate t (unrotate t x)=x := by decide +kernel
theorem lower_forward : ∀t s, (lowerRows s).all (fun d => decide (rotate t d∈lowerRows (rotate t s)))=true := by decide +kernel
theorem lower_backward : ∀t s, (lowerRows (rotate t s)).all (fun d => decide (unrotate t d∈lowerRows s))=true := by decide +kernel
theorem upper_forward : ∀t s, (upperRows s).all (fun d => decide (rotate t d∈upperRows (rotate t s)))=true := by decide +kernel
theorem upper_backward : ∀t s, (upperRows (rotate t s)).all (fun d => decide (unrotate t d∈upperRows s))=true := by decide +kernel
noncomputable def rotation (t : Fin 65) : GraphRelabeling.Iso lower lower :=
  EnvelopeRowSymmetry.iso_of_rows lowerRows (rotate t) (unrotate t)
    (fun x => (inverses t x).1) (fun x => (inverses t x).2)
    (fun s d member => of_decide_eq_true ((List.all_eq_true.mp (lower_forward t s)) d member))
    (fun s d member => of_decide_eq_true ((List.all_eq_true.mp (lower_backward t s)) d member))
theorem upper_invariant (t : Fin 65) : ∀s d,upper s d ↔ upper ((rotation t).toFun s) ((rotation t).toFun d) := by
  exact EnvelopeRowSymmetry.invariant_of_rows upperRows (rotate t) (unrotate t)
    (fun x => (inverses t x).1)
    (fun s d member => of_decide_eq_true ((List.all_eq_true.mp (upper_forward t s)) d member))
    (fun s d member => of_decide_eq_true ((List.all_eq_true.mp (upper_backward t s)) d member))
def representative (t : Fin 65) : Fin 65 := ⟨t.val%5,by omega⟩
theorem representative_small (t : Fin 65) : (representative t).val<5 := Nat.mod_lt _ (by decide)
theorem target_cover : ∀t,rotate t (representative t)=t := by decide +kernel
#print axioms counts
#print axioms upper_invariant
end Delivery.FiveFinite65Base

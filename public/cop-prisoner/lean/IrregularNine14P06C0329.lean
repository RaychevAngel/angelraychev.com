import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0098

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b19740 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 66, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 67 140 56 21 288 70 198 326), lower := (rows 35 67 140 56 21 288 64 128 256), losses := [{ target := 5, region := (rows 1 18 12 8 16 0 88 152 280), good := (rows 3 67 460 478 471 256 64 128 256) }] }

theorem u19740 : Upper (D 6) (R 6) [34,65,136,48,5,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19740 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19741 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 67 140 56 22 33 324 452 324), lower := (rows 35 67 140 56 22 33 64 128 256), losses := [] }

theorem u19741 : Upper (D 6) (R 6) [34,65,136,48,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19741 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19742 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 322, targets := 36 },{ cop := 4, region := 40, targets := 1 }], pairs := [(1,2),(1,5),(3,0)], upper := (rows 35 67 140 56 22 36 321 449 321), lower := (rows 35 67 140 56 22 36 64 128 256), losses := [] }

theorem u19742 : Upper (D 6) (R 6) [34,65,136,48,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19742 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19743 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 140 56 22 96 325 389 261), lower := (rows 35 67 140 56 22 96 64 128 256), losses := [] }

theorem u19743 : Upper (D 6) (R 6) [34,65,136,48,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19743 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19744 : Route 9 := (fun mask => (mask,id))

def c19744 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19744 : Upper (D 6) (R 6) [34,65,136,48,6,256] 13 := by
  apply FastRouting.sound _ _ [34,65,136,48,6,256] 13 (by decide) (choices 1) [1,4] r19744 c19744
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5914
  · exact u5915

def b19745 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 140 56 84 33 326 390 262), lower := (rows 35 67 140 56 84 33 64 128 256), losses := [] }

theorem u19745 : Upper (D 6) (R 6) [34,65,136,48,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19745 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19746 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 140 56 84 34 325 389 261), lower := (rows 35 67 140 56 84 34 64 128 256), losses := [] }

theorem u19746 : Upper (D 6) (R 6) [34,65,136,48,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19746 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19747 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 67 140 56 84 36 323 387 259), lower := (rows 35 67 140 56 84 36 64 128 256), losses := [] }

theorem u19747 : Upper (D 6) (R 6) [34,65,136,48,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19747 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19748 : Route 9 := (fun mask => (mask,id))

def c19748 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19748 : Upper (D 6) (R 6) [34,65,136,48,68,256] 13 := by
  apply FastRouting.sound _ _ [34,65,136,48,68,256] 13 (by decide) (choices 1) [1,2,4] r19748 c19748
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5916
  · exact u5917
  · exact u5918

def b19749 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 140 56 273 34 68 196 324), lower := (rows 35 67 140 56 273 34 64 128 256), losses := [] }

theorem u19749 : Upper (D 6) (R 6) [34,65,136,48,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19749 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19750 : Route 9 := (fun mask => (mask,id))

def c19750 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19750 : Upper (D 6) (R 6) [34,65,136,48,257,4] 13 := by
  apply FastRouting.sound _ _ [34,65,136,48,257,4] 13 (by decide) (choices 1) [2,4] r19750 c19750
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5919
  · exact u5920

def b19751 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 140 56 273 96 70 134 262), lower := (rows 35 67 140 56 273 96 64 128 256), losses := [] }

theorem u19751 : Upper (D 6) (R 6) [34,65,136,48,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19751 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19752 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 67 140 56 274 33 68 196 324), lower := (rows 35 67 140 56 274 33 64 128 256), losses := [] }

theorem u19752 : Upper (D 6) (R 6) [34,65,136,48,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19752 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19753 : Route 9 := (fun mask => (mask,id))

def c19753 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19753 : Upper (D 6) (R 6) [34,65,136,48,258,4] 13 := by
  apply FastRouting.sound _ _ [34,65,136,48,258,4] 13 (by decide) (choices 1) [1,4] r19753 c19753
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5921
  · exact u5922

def b19754 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 140 56 274 96 69 133 261), lower := (rows 35 67 140 56 274 96 64 128 256), losses := [] }

theorem u19754 : Upper (D 6) (R 6) [34,65,136,48,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19754 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19755 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 140 56 276 33 70 198 326), lower := (rows 35 67 140 56 276 33 64 128 256), losses := [] }

theorem u19755 : Upper (D 6) (R 6) [34,65,136,48,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19755 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19756 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 140 56 276 34 69 197 325), lower := (rows 35 67 140 56 276 34 64 128 256), losses := [] }

theorem u19756 : Upper (D 6) (R 6) [34,65,136,48,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19756 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19757 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 67 140 56 276 36 67 195 323), lower := (rows 35 67 140 56 276 36 64 128 256), losses := [] }

theorem u19757 : Upper (D 6) (R 6) [34,65,136,48,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19757 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19758 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 140 56 276 96 71 135 263), lower := (rows 35 67 140 56 276 96 64 128 256), losses := [] }

theorem u19758 : Upper (D 6) (R 6) [34,65,136,48,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19758 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19759 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 140 56 336 33 70 134 262), lower := (rows 35 67 140 56 336 33 64 128 256), losses := [] }

theorem u19759 : Upper (D 6) (R 6) [34,65,136,48,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19759 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19760 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 140 56 336 34 69 133 261), lower := (rows 35 67 140 56 336 34 64 128 256), losses := [] }

theorem u19760 : Upper (D 6) (R 6) [34,65,136,48,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19760 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19761 : Route 9 := (fun mask => (mask,id))

def c19761 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19761 : Upper (D 6) (R 6) [34,65,136,48,320,4] 13 := by
  apply FastRouting.sound _ _ [34,65,136,48,320,4] 13 (by decide) (choices 1) [1,2,4] r19761 c19761
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5923
  · exact u5924
  · exact u5925

def b19762 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 140 104 273 34 84 148 276), lower := (rows 35 67 140 104 273 34 64 128 256), losses := [] }

theorem u19762 : Upper (D 6) (R 6) [34,65,136,96,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19762 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19763 : Route 9 := (fun mask => (mask,id))

def c19763 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19763 : Upper (D 6) (R 6) [34,65,136,96,257,4] 13 := by
  apply FastRouting.sound _ _ [34,65,136,96,257,4] 13 (by decide) (choices 1) [2,4,16] r19763 c19763
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5926
  · exact u5927
  · exact u5928

def b19764 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 204, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 67 140 104 273 48 70 134 262), lower := (rows 35 67 140 104 273 48 64 128 256), losses := [] }

theorem u19764 : Upper (D 6) (R 6) [34,65,136,96,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19764 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19765 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 140 104 276 33 86 150 278), lower := (rows 35 67 140 104 276 33 64 128 256), losses := [] }

theorem u19765 : Upper (D 6) (R 6) [34,65,136,96,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19765 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19766 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 140 104 276 34 85 149 277), lower := (rows 35 67 140 104 276 34 64 128 256), losses := [] }

theorem u19766 : Upper (D 6) (R 6) [34,65,136,96,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19766 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m19767_1 : Upper (D 6) (R 6) [34,65,136,96,260,4,1] 13 :=
  permutation_upper _ _ _ [34,65,136,96,260,2,4] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5930

theorem m19767_2 : Upper (D 6) (R 6) [34,65,136,96,260,4,2] 13 :=
  permutation_upper _ _ _ [34,65,136,96,260,1,4] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5929

def r19767 : Route 9 := (fun mask => (mask,id))

def c19767 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19767 : Upper (D 6) (R 6) [34,65,136,96,260,4] 13 := by
  apply FastRouting.sound _ _ [34,65,136,96,260,4] 13 (by decide) (choices 1) [1,2,16] r19767 c19767
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m19767_1
  · exact m19767_2
  · exact u5931

def b19768 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 3, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 67 140 104 276 48 71 135 263), lower := (rows 35 67 140 104 276 48 64 128 256), losses := [] }

theorem u19768 : Upper (D 6) (R 6) [34,65,136,96,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19768 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19769 : Route 9 := (fun mask => (mask,id))

def c19769 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19769 : Upper (D 6) (R 6) [34,65,136,257,6,4] 13 := by
  apply FastRouting.sound _ _ [34,65,136,257,6,4] 13 (by decide) (choices 1) [16,32] r19769 c19769
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5932
  · exact u5933

def b19770 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 67 140 265 22 48 100 228 356), lower := (rows 35 67 140 265 22 48 64 128 256), losses := [] }

theorem u19770 : Upper (D 6) (R 6) [34,65,136,257,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19770 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19771 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 140 265 22 96 116 180 308), lower := (rows 35 67 140 265 22 96 64 128 256), losses := [] }

theorem u19771 : Upper (D 6) (R 6) [34,65,136,257,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19771 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19772 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 140 265 52 34 84 212 340), lower := (rows 35 67 140 265 52 34 64 128 256), losses := [] }

theorem u19772 : Upper (D 6) (R 6) [34,65,136,257,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19772 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19773 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 67 140 265 52 36 82 210 338), lower := (rows 35 67 140 265 52 36 64 128 256), losses := [] }

theorem u19773 : Upper (D 6) (R 6) [34,65,136,257,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19773 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19774 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 67 140 265 52 48 70 198 326), lower := (rows 35 67 140 265 52 48 64 128 256), losses := [] }

theorem u19774 : Upper (D 6) (R 6) [34,65,136,257,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19774 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19775 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 140 265 52 96 86 150 278), lower := (rows 35 67 140 265 52 96 64 128 256), losses := [] }

theorem u19775 : Upper (D 6) (R 6) [34,65,136,257,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19775 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19776 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 140 265 84 34 116 180 308), lower := (rows 35 67 140 265 84 34 64 128 256), losses := [] }

theorem u19776 : Upper (D 6) (R 6) [34,65,136,257,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19776 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19777 : Route 9 := (fun mask => (mask,id))

def c19777 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19777 : Upper (D 6) (R 6) [34,65,136,257,68,4] 13 := by
  apply FastRouting.sound _ _ [34,65,136,257,68,4] 13 (by decide) (choices 1) [2,16,32] r19777 c19777
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5934
  · exact u5935
  · exact u5936

def b19778 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 67 140 265 84 48 102 166 294), lower := (rows 35 67 140 265 84 48 64 128 256), losses := [] }

theorem u19778 : Upper (D 6) (R 6) [34,65,136,257,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19778 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19779 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 140 265 112 34 84 148 276), lower := (rows 35 67 140 265 112 34 64 128 256), losses := [] }

theorem u19779 : Upper (D 6) (R 6) [34,65,136,257,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19779 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19780 : Route 9 := (fun mask => (mask,id))

def c19780 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19780 : Upper (D 6) (R 6) [34,65,136,257,96,4] 13 := by
  apply FastRouting.sound _ _ [34,65,136,257,96,4] 13 (by decide) (choices 1) [2,4,16] r19780 c19780
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5937
  · exact u5938
  · exact u5939

def b19781 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 67 140 265 112 48 70 134 262), lower := (rows 35 67 140 265 112 48 64 128 256), losses := [] }

theorem u19781 : Upper (D 6) (R 6) [34,65,136,257,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19781 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19782 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 140 268 21 34 112 240 368), lower := (rows 35 67 140 268 21 34 64 128 256), losses := [] }

theorem u19782 : Upper (D 6) (R 6) [34,65,136,260,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19782 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19783 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 460, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 67 140 268 21 48 98 226 354), lower := (rows 35 67 140 268 21 48 64 128 256), losses := [] }

theorem u19783 : Upper (D 6) (R 6) [34,65,136,260,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19783 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19784 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 140 268 21 96 114 178 306), lower := (rows 35 67 140 268 21 96 64 128 256), losses := [] }

theorem u19784 : Upper (D 6) (R 6) [34,65,136,260,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19784 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19785 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 140 268 52 33 82 210 338), lower := (rows 35 67 140 268 52 33 64 128 256), losses := [] }

theorem u19785 : Upper (D 6) (R 6) [34,65,136,260,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19785 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19786 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 140 268 52 34 81 209 337), lower := (rows 35 67 140 268 52 34 64 128 256), losses := [] }

theorem u19786 : Upper (D 6) (R 6) [34,65,136,260,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19786 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19787 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 67 140 268 52 48 67 195 323), lower := (rows 35 67 140 268 52 48 64 128 256), losses := [] }

theorem u19787 : Upper (D 6) (R 6) [34,65,136,260,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19787 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19788 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 140 268 52 96 83 147 275), lower := (rows 35 67 140 268 52 96 64 128 256), losses := [] }

theorem u19788 : Upper (D 6) (R 6) [34,65,136,260,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19788 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19789 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 140 268 112 33 86 150 278), lower := (rows 35 67 140 268 112 33 64 128 256), losses := [] }

theorem u19789 : Upper (D 6) (R 6) [34,65,136,260,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19789 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19790 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 140 268 112 34 85 149 277), lower := (rows 35 67 140 268 112 34 64 128 256), losses := [] }

theorem u19790 : Upper (D 6) (R 6) [34,65,136,260,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19790 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19791 : PairBound 9 := { available := 19, camps := [{ cop := 5, region := 83, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 67 140 268 112 36 83 147 275), lower := (rows 35 67 140 268 112 36 64 128 256), losses := [] }

theorem u19791 : Upper (D 6) (R 6) [34,65,136,260,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19791 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19792 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 67 140 268 112 48 71 135 263), lower := (rows 35 67 140 268 112 48 64 128 256), losses := [] }

theorem u19792 : Upper (D 6) (R 6) [34,65,136,260,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19792 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19793 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 140 280 21 34 100 228 356), lower := (rows 35 67 140 280 21 34 64 128 256), losses := [] }

theorem u19793 : Upper (D 6) (R 6) [34,65,136,272,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19793 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19794 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 67, targets := 4 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 35 67 140 280 21 36 98 226 354), lower := (rows 35 67 140 280 21 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 60 65 129 257), good := (rows 482 450 172 316 508 36 64 128 256) }] }

theorem u19794 : Upper (D 6) (R 6) [34,65,136,272,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19794 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19795 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 140 280 21 96 102 166 294), lower := (rows 35 67 140 280 21 96 64 128 256), losses := [] }

theorem u19795 : Upper (D 6) (R 6) [34,65,136,272,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19795 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19796 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 140 280 52 33 70 198 326), lower := (rows 35 67 140 280 52 33 64 128 256), losses := [] }

theorem u19796 : Upper (D 6) (R 6) [34,65,136,272,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19796 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19797 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 140 280 52 34 69 197 325), lower := (rows 35 67 140 280 52 34 64 128 256), losses := [] }

theorem u19797 : Upper (D 6) (R 6) [34,65,136,272,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19797 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19798 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 67 140 280 52 36 67 195 323), lower := (rows 35 67 140 280 52 36 64 128 256), losses := [] }

theorem u19798 : Upper (D 6) (R 6) [34,65,136,272,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19798 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19799 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 140 280 52 96 71 135 263), lower := (rows 35 67 140 280 52 96 64 128 256), losses := [] }

theorem u19799 : Upper (D 6) (R 6) [34,65,136,272,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19799 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u19799
end Delivery.IrregularNine14.P06

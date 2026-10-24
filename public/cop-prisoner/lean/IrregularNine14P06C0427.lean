import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0131
import IrregularNine14P06C0132

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b25620 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 338, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 82 133 14 304 36 67 195 323), lower := (rows 41 82 133 14 304 36 64 128 256), losses := [] }

theorem u25620 : Upper (D 6) (R 6) [40,80,129,6,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25620 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25621 : Route 9 := (fun mask => (mask,id))

def c25621 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25621 : Upper (D 6) (R 6) [40,80,129,6,288,64] 13 := by
  apply FastRouting.sound _ _ [40,80,129,6,288,64] 13 (by decide) (choices 1) [1,2,4] r25621 c25621
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7917
  · exact u7918
  · exact u7919

def b25622 : PairBound 9 := { available := 292, camps := [{ cop := 5, region := 461, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 41 82 133 73 22 34 356 420 292), lower := (rows 41 82 133 73 22 34 64 128 256), losses := [] }

theorem u25622 : Upper (D 6) (R 6) [40,80,129,65,6,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25622 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25623 : PairBound 9 := { available := 290, camps := [{ cop := 2, region := 370, targets := 1 }], pairs := [(0,1),(1,0),(4,0)], upper := (rows 41 82 133 73 22 36 354 418 290), lower := (rows 41 82 133 73 22 36 64 128 256), losses := [{ target := 1, region := (rows 19 0 4 10 16 52 64 128 256), good := (rows 41 121 165 73 61 36 64 128 256) }] }

theorem u25623 : Upper (D 6) (R 6) [40,80,129,65,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25623 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25624 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 370, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 41 82 133 73 22 288 102 166 294), lower := (rows 41 82 133 73 22 288 64 128 256), losses := [] }

theorem u25624 : Upper (D 6) (R 6) [40,80,129,65,6,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25624 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25625 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 205, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 41 82 133 73 274 34 100 164 292), lower := (rows 41 82 133 73 274 34 64 128 256), losses := [] }

theorem u25625 : Upper (D 6) (R 6) [40,80,129,65,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25625 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25626 : Route 9 := (fun mask => (mask,id))

def c25626 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25626 : Upper (D 6) (R 6) [40,80,129,65,258,4] 13 := by
  apply FastRouting.sound _ _ [40,80,129,65,258,4] 13 (by decide) (choices 1) [2,4,32] r25626 c25626
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7920
  · exact u7921
  · exact u7922

def b25627 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 41, targets := 4 },{ cop := 2, region := 370, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 41 82 133 73 276 34 102 166 294), lower := (rows 41 82 133 73 276 34 64 128 256), losses := [] }

theorem u25627 : Upper (D 6) (R 6) [40,80,129,65,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25627 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25628 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 370, targets := 1 }], pairs := [(0,1),(1,0),(4,0)], upper := (rows 41 82 133 73 276 36 98 162 290), lower := (rows 41 82 133 73 276 36 64 128 256), losses := [{ target := 1, region := (rows 3 0 4 10 16 52 64 128 256), good := (rows 41 121 165 73 308 36 64 128 256) }] }

theorem u25628 : Upper (D 6) (R 6) [40,80,129,65,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25628 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25629 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 41, targets := 4 },{ cop := 2, region := 370, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 41 82 133 73 304 34 70 134 262), lower := (rows 41 82 133 73 304 34 64 128 256), losses := [] }

theorem u25629 : Upper (D 6) (R 6) [40,80,129,65,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25629 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25630 : Route 9 := (fun mask => (mask,id))

def c25630 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25630 : Upper (D 6) (R 6) [40,80,129,65,288,4] 13 := by
  apply FastRouting.sound _ _ [40,80,129,65,288,4] 13 (by decide) (choices 1) [2,4] r25630 c25630
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7923
  · exact u7924

def b25631 : PairBound 9 := { available := 292, camps := [{ cop := 3, region := 51, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 41 82 133 76 19 34 356 420 292), lower := (rows 41 82 133 76 19 34 64 128 256), losses := [] }

theorem u25631 : Upper (D 6) (R 6) [40,80,129,68,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25631 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25632 : PairBound 9 := { available := 290, camps := [{ cop := 0, region := 338, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 82 133 76 19 36 354 418 290), lower := (rows 41 82 133 76 19 36 64 128 256), losses := [] }

theorem u25632 : Upper (D 6) (R 6) [40,80,129,68,3,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25632 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25633 : Route 9 := (fun mask => (mask,id))

def c25633 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25633 : Upper (D 6) (R 6) [40,80,129,68,3,256] 13 := by
  apply FastRouting.sound _ _ [40,80,129,68,3,256] 13 (by decide) (choices 1) [2,4,32] r25633 c25633
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7925
  · exact u7926
  · exact u7927

def b25634 : PairBound 9 := { available := 262, camps := [{ cop := 3, region := 51, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 41 82 133 76 50 33 326 390 262), lower := (rows 41 82 133 76 50 33 64 128 256), losses := [] }

theorem u25634 : Upper (D 6) (R 6) [40,80,129,68,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25634 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25635 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 41 82 133 76 50 34 325 389 261), lower := (rows 41 82 133 76 50 34 64 128 256), losses := [] }

theorem u25635 : Upper (D 6) (R 6) [40,80,129,68,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25635 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25636 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 338, targets := 4 },{ cop := 3, region := 50, targets := 1 }], pairs := [(1,0),(1,2),(4,2)], upper := (rows 41 82 133 76 50 36 323 387 259), lower := (rows 41 82 133 76 50 36 64 128 256), losses := [] }

theorem u25636 : Upper (D 6) (R 6) [40,80,129,68,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25636 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25637 : Route 9 := (fun mask => (mask,id))

def c25637 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25637 : Upper (D 6) (R 6) [40,80,129,68,34,256] 13 := by
  apply FastRouting.sound _ _ [40,80,129,68,34,256] 13 (by decide) (choices 1) [1,2,4] r25637 c25637
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7928
  · exact u7929
  · exact u7930

def b25638 : PairBound 9 := { available := 258, camps := [{ cop := 3, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 41 82 133 76 52 33 322 386 258), lower := (rows 41 82 133 76 52 33 64 128 256), losses := [] }

theorem u25638 : Upper (D 6) (R 6) [40,80,129,68,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25638 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25639 : Route 9 := (fun mask => (mask,id))

def c25639 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u25639 : Upper (D 6) (R 6) [40,80,129,68,36,2] 13 := by
  apply FastRouting.sound _ _ [40,80,129,68,36,2] 13 (by decide) (choices 1) [1,2,256] r25639 c25639
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7931
  · exact u7932
  · exact u7933

def r25640 : Route 9 := (fun mask => (mask,id))

def c25640 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25640 : Upper (D 6) (R 6) [40,80,129,68,36,256] 13 := by
  apply FastRouting.sound _ _ [40,80,129,68,36,256] 13 (by decide) (choices 1) [1,2] r25640 c25640
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7934
  · exact u7935

def r25641 : Route 9 := (fun mask => (mask,id))

def c25641 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25641 : Upper (D 6) (R 6) [40,80,129,68,257,2] 13 := by
  apply FastRouting.sound _ _ [40,80,129,68,257,2] 13 (by decide) (choices 1) [2,4,32] r25641 c25641
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7936
  · exact u7937
  · exact u7938

def b25642 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 338, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 82 133 76 273 36 98 162 290), lower := (rows 41 82 133 76 273 36 64 128 256), losses := [] }

theorem u25642 : Upper (D 6) (R 6) [40,80,129,68,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25642 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25643 : PairBound 9 := { available := 38, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 82 133 76 274 33 102 166 294), lower := (rows 41 82 133 76 274 33 64 128 256), losses := [] }

theorem u25643 : Upper (D 6) (R 6) [40,80,129,68,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25643 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25644 : PairBound 9 := { available := 37, camps := [{ cop := 5, region := 205, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 41 82 133 76 274 34 101 165 293), lower := (rows 41 82 133 76 274 34 64 128 256), losses := [] }

theorem u25644 : Upper (D 6) (R 6) [40,80,129,68,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25644 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25645 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 338, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 82 133 76 274 36 99 163 291), lower := (rows 41 82 133 76 274 36 64 128 256), losses := [] }

theorem u25645 : Upper (D 6) (R 6) [40,80,129,68,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25645 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25646 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 82 133 76 276 33 98 162 290), lower := (rows 41 82 133 76 276 33 64 128 256), losses := [] }

theorem u25646 : Upper (D 6) (R 6) [40,80,129,68,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25646 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25647 : Route 9 := (fun mask => (mask,id))

def c25647 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25647 : Upper (D 6) (R 6) [40,80,129,68,260,2] 13 := by
  apply FastRouting.sound _ _ [40,80,129,68,260,2] 13 (by decide) (choices 1) [1,2,32] r25647 c25647
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7939
  · exact u7940
  · exact u7941

def b25648 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 82 133 76 304 33 70 134 262), lower := (rows 41 82 133 76 304 33 64 128 256), losses := [] }

theorem u25648 : Upper (D 6) (R 6) [40,80,129,68,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25648 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25649 : Route 9 := (fun mask => (mask,id))

def c25649 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25649 : Upper (D 6) (R 6) [40,80,129,68,288,2] 13 := by
  apply FastRouting.sound _ _ [40,80,129,68,288,2] 13 (by decide) (choices 1) [1,2,4] r25649 c25649
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7942
  · exact u7943
  · exact u7944

def b25650 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 338, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 82 133 76 304 36 67 131 259), lower := (rows 41 82 133 76 304 36 64 128 256), losses := [] }

theorem u25650 : Upper (D 6) (R 6) [40,80,129,68,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25650 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25651 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 461, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 41 82 133 265 22 34 100 228 356), lower := (rows 41 82 133 265 22 34 64 128 256), losses := [] }

theorem u25651 : Upper (D 6) (R 6) [40,80,129,257,6,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25651 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25652 : Route 9 := (fun mask => (mask,id))

def c25652 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25652 : Upper (D 6) (R 6) [40,80,129,257,6,4] 13 := by
  apply FastRouting.sound _ _ [40,80,129,257,6,4] 13 (by decide) (choices 1) [2,32] r25652 c25652
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7945
  · exact u7946

def r25653 : Route 9 := (fun mask => (mask,id))

def c25653 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25653 : Upper (D 6) (R 6) [40,80,129,257,6,64] 13 := by
  apply FastRouting.sound _ _ [40,80,129,257,6,64] 13 (by decide) (choices 1) [2,4,32] r25653 c25653
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7947
  · exact u7948
  · exact u7949

def b25654 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 41 82 133 265 50 34 68 196 324), lower := (rows 41 82 133 265 50 34 64 128 256), losses := [] }

theorem u25654 : Upper (D 6) (R 6) [40,80,129,257,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25654 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25655 : Route 9 := (fun mask => (mask,id))

def c25655 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25655 : Upper (D 6) (R 6) [40,80,129,257,34,4] 13 := by
  apply FastRouting.sound _ _ [40,80,129,257,34,4] 13 (by decide) (choices 1) [2,4] r25655 c25655
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7950
  · exact u7951

def b25656 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 18, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 41 82 133 265 50 96 70 134 262), lower := (rows 41 82 133 265 50 96 64 128 256), losses := [] }

theorem u25656 : Upper (D 6) (R 6) [40,80,129,257,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25656 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25657 : Route 9 := (fun mask => (mask,id))

def c25657 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25657 : Upper (D 6) (R 6) [40,80,129,258,3,4] 13 := by
  apply FastRouting.sound _ _ [40,80,129,258,3,4] 13 (by decide) (choices 1) [4,32] r25657 c25657
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7952
  · exact u7953

def b25658 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 229, targets := 2 },{ cop := 0, region := 132, targets := 64 }], pairs := [(0,1),(2,1),(2,6)], upper := (rows 41 82 133 266 19 96 100 164 292), lower := (rows 41 82 133 266 19 96 64 128 256), losses := [] }

theorem u25658 : Upper (D 6) (R 6) [40,80,129,258,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25658 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25659 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 229, targets := 2 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,1),(0,2),(2,1)], upper := (rows 41 82 133 266 22 33 100 228 356), lower := (rows 41 82 133 266 22 33 64 128 256), losses := [] }

theorem u25659 : Upper (D 6) (R 6) [40,80,129,258,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25659 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25660 : Route 9 := (fun mask => (mask,id))

def c25660 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25660 : Upper (D 6) (R 6) [40,80,129,258,6,4] 13 := by
  apply FastRouting.sound _ _ [40,80,129,258,6,4] 13 (by decide) (choices 1) [1,32] r25660 c25660
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7954
  · exact u7955

def b25661 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 229, targets := 2 },{ cop := 0, region := 132, targets := 64 }], pairs := [(0,1),(2,1),(2,6)], upper := (rows 41 82 133 266 22 96 101 165 293), lower := (rows 41 82 133 266 22 96 64 128 256), losses := [] }

theorem u25661 : Upper (D 6) (R 6) [40,80,129,258,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25661 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25662 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 330, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 41 82 133 266 52 33 70 198 326), lower := (rows 41 82 133 266 52 33 64 128 256), losses := [] }

theorem u25662 : Upper (D 6) (R 6) [40,80,129,258,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25662 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25663 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 212, targets := 2 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 41 82 133 266 52 34 69 197 325), lower := (rows 41 82 133 266 52 34 64 128 256), losses := [] }

theorem u25663 : Upper (D 6) (R 6) [40,80,129,258,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25663 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25664 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 41 82 133 266 52 36 67 195 323), lower := (rows 41 82 133 266 52 36 64 128 256), losses := [] }

theorem u25664 : Upper (D 6) (R 6) [40,80,129,258,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25664 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25665 : Route 9 := (fun mask => (mask,id))

def c25665 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25665 : Upper (D 6) (R 6) [40,80,129,258,36,64] 13 := by
  apply FastRouting.sound _ _ [40,80,129,258,36,64] 13 (by decide) (choices 1) [1,2,4] r25665 c25665
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7956
  · exact u7957
  · exact u7958

def b25666 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 461, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 41 82 133 268 19 34 100 228 356), lower := (rows 41 82 133 268 19 34 64 128 256), losses := [] }

theorem u25666 : Upper (D 6) (R 6) [40,80,129,260,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25666 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25667 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 82, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 82 133 268 19 36 98 226 354), lower := (rows 41 82 133 268 19 36 64 128 256), losses := [] }

theorem u25667 : Upper (D 6) (R 6) [40,80,129,260,3,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25667 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25668 : Route 9 := (fun mask => (mask,id))

def c25668 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25668 : Upper (D 6) (R 6) [40,80,129,260,3,64] 13 := by
  apply FastRouting.sound _ _ [40,80,129,260,3,64] 13 (by decide) (choices 1) [2,4,32] r25668 c25668
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7959
  · exact u7960
  · exact u7961

def b25669 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 82 133 268 22 33 98 226 354), lower := (rows 41 82 133 268 22 33 64 128 256), losses := [] }

theorem u25669 : Upper (D 6) (R 6) [40,80,129,260,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25669 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25670 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 461, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 41 82 133 268 22 34 97 225 353), lower := (rows 41 82 133 268 22 34 64 128 256), losses := [] }

theorem u25670 : Upper (D 6) (R 6) [40,80,129,260,6,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25670 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25671 : Route 9 := (fun mask => (mask,id))

def c25671 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25671 : Upper (D 6) (R 6) [40,80,129,260,6,64] 13 := by
  apply FastRouting.sound _ _ [40,80,129,260,6,64] 13 (by decide) (choices 1) [1,2,32] r25671 c25671
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7962
  · exact u7963
  · exact u7964

def b25672 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 82 133 268 50 33 70 198 326), lower := (rows 41 82 133 268 50 33 64 128 256), losses := [] }

theorem u25672 : Upper (D 6) (R 6) [40,80,129,260,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25672 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25673 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 41 82 133 268 50 34 69 197 325), lower := (rows 41 82 133 268 50 34 64 128 256), losses := [] }

theorem u25673 : Upper (D 6) (R 6) [40,80,129,260,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25673 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25674 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 82, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 82 133 268 50 36 67 195 323), lower := (rows 41 82 133 268 50 36 64 128 256), losses := [] }

theorem u25674 : Upper (D 6) (R 6) [40,80,129,260,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25674 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25675 : PairBound 9 := { available := 7, camps := [{ cop := 5, region := 18, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 41 82 133 268 50 96 71 135 263), lower := (rows 41 82 133 268 50 96 64 128 256), losses := [] }

theorem u25675 : Upper (D 6) (R 6) [40,80,129,260,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25675 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25676 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 41 82 133 268 52 33 66 194 322), lower := (rows 41 82 133 268 52 33 64 128 256), losses := [] }

theorem u25676 : Upper (D 6) (R 6) [40,80,129,260,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25676 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25677 : Route 9 := (fun mask => (mask,id))

def c25677 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25677 : Upper (D 6) (R 6) [40,80,129,260,36,2] 13 := by
  apply FastRouting.sound _ _ [40,80,129,260,36,2] 13 (by decide) (choices 1) [1,2] r25677 c25677
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7965
  · exact u7966

def r25678 : Route 9 := (fun mask => (mask,id))

def c25678 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25678 : Upper (D 6) (R 6) [40,80,129,260,36,64] 13 := by
  apply FastRouting.sound _ _ [40,80,129,260,36,64] 13 (by decide) (choices 1) [1,2] r25678 c25678
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7967
  · exact u7968

def b25679 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 51, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 41 82 133 328 19 34 100 164 292), lower := (rows 41 82 133 328 19 34 64 128 256), losses := [] }

theorem u25679 : Upper (D 6) (R 6) [40,80,129,320,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25679 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u25679
end Delivery.IrregularNine14.P06

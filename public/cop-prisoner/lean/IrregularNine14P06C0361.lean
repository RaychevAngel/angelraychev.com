import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0106

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b21660 : PairBound 9 := { available := 68, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 44 28 274 33 68 196 324), lower := (rows 35 131 44 28 274 33 64 128 256), losses := [] }

theorem u21660 : Upper (D 6) (R 6) [34,129,40,20,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21660 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21661 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 466, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 131 44 28 274 36 65 193 321), lower := (rows 35 131 44 28 274 36 64 128 256), losses := [] }

theorem u21661 : Upper (D 6) (R 6) [34,129,40,20,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21661 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21662 : Route 9 := (fun mask => (mask,id))

def c21662 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21662 : Upper (D 6) (R 6) [34,129,40,20,258,64] 13 := by
  apply FastRouting.sound _ _ [34,129,40,20,258,64] 13 (by decide) (choices 1) [1,4] r21662 c21662
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6363
  · exact u6364

def b21663 : PairBound 9 := { available := 70, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 44 28 336 33 70 198 326), lower := (rows 35 131 44 28 336 33 64 128 256), losses := [] }

theorem u21663 : Upper (D 6) (R 6) [34,129,40,20,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21663 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21664 : PairBound 9 := { available := 69, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 44 28 336 34 69 197 325), lower := (rows 35 131 44 28 336 34 64 128 256), losses := [] }

theorem u21664 : Upper (D 6) (R 6) [34,129,40,20,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21664 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21665 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 44, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 131 44 28 336 36 67 195 323), lower := (rows 35 131 44 28 336 36 64 128 256), losses := [] }

theorem u21665 : Upper (D 6) (R 6) [34,129,40,20,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21665 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21666 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 44 28 336 96 71 135 263), lower := (rows 35 131 44 28 336 96 64 128 256), losses := [] }

theorem u21666 : Upper (D 6) (R 6) [34,129,40,20,320,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21666 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21667 : PairBound 9 := { available := 336, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 131 44 73 22 36 336 464 336), lower := (rows 35 131 44 73 22 36 64 128 256), losses := [] }

theorem u21667 : Upper (D 6) (R 6) [34,129,40,65,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21667 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21668 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 131 44 73 22 48 324 452 324), lower := (rows 35 131 44 73 22 48 64 128 256), losses := [] }

theorem u21668 : Upper (D 6) (R 6) [34,129,40,65,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21668 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21669 : PairBound 9 := { available := 276, camps := [{ cop := 2, region := 403, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 131 44 73 22 96 340 404 276), lower := (rows 35 131 44 73 22 96 64 128 256), losses := [] }

theorem u21669 : Upper (D 6) (R 6) [34,129,40,65,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21669 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21670 : Route 9 := (fun mask => (mask,id))

def c21670 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21670 : Upper (D 6) (R 6) [34,129,40,65,6,256] 13 := by
  apply FastRouting.sound _ _ [34,129,40,65,6,256] 13 (by decide) (choices 1) [4,16] r21670 c21670
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6365
  · exact u6366

def b21671 : PairBound 9 := { available := 276, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 131 44 73 82 36 340 404 276), lower := (rows 35 131 44 73 82 36 64 128 256), losses := [] }

theorem u21671 : Upper (D 6) (R 6) [34,129,40,65,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21671 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21672 : PairBound 9 := { available := 260, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 131 44 73 82 48 324 388 260), lower := (rows 35 131 44 73 82 48 64 128 256), losses := [] }

theorem u21672 : Upper (D 6) (R 6) [34,129,40,65,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21672 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21673 : Route 9 := (fun mask => (mask,id))

def c21673 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21673 : Upper (D 6) (R 6) [34,129,40,65,66,256] 13 := by
  apply FastRouting.sound _ _ [34,129,40,65,66,256] 13 (by decide) (choices 1) [4,16] r21673 c21673
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6367
  · exact u6368

def b21674 : PairBound 9 := { available := 276, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 44 73 84 34 340 404 276), lower := (rows 35 131 44 73 84 34 64 128 256), losses := [] }

theorem u21674 : Upper (D 6) (R 6) [34,129,40,65,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21674 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21675 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 52, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 131 44 73 84 36 338 402 274), lower := (rows 35 131 44 73 84 36 64 128 256), losses := [] }

theorem u21675 : Upper (D 6) (R 6) [34,129,40,65,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21675 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21676 : PairBound 9 := { available := 262, camps := [{ cop := 3, region := 52, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 131 44 73 84 48 326 390 262), lower := (rows 35 131 44 73 84 48 64 128 256), losses := [] }

theorem u21676 : Upper (D 6) (R 6) [34,129,40,65,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21676 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21677 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 419, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 44 73 84 288 86 150 278), lower := (rows 35 131 44 73 84 288 64 128 256), losses := [] }

theorem u21677 : Upper (D 6) (R 6) [34,129,40,65,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21677 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21678 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 131 44 73 274 36 84 212 340), lower := (rows 35 131 44 73 274 36 64 128 256), losses := [] }

theorem u21678 : Upper (D 6) (R 6) [34,129,40,65,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21678 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21679 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 76, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 131 44 73 274 48 68 196 324), lower := (rows 35 131 44 73 274 48 64 128 256), losses := [] }

theorem u21679 : Upper (D 6) (R 6) [34,129,40,65,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21679 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21680 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 403, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 131 44 73 274 96 84 148 276), lower := (rows 35 131 44 73 274 96 64 128 256), losses := [] }

theorem u21680 : Upper (D 6) (R 6) [34,129,40,65,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21680 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21681 : PairBound 9 := { available := 84, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 44 73 276 34 84 212 340), lower := (rows 35 131 44 73 276 34 64 128 256), losses := [] }

theorem u21681 : Upper (D 6) (R 6) [34,129,40,65,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21681 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21682 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 131 44 73 276 36 82 210 338), lower := (rows 35 131 44 73 276 36 64 128 256), losses := [] }

theorem u21682 : Upper (D 6) (R 6) [34,129,40,65,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21682 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21683 : Route 9 := (fun mask => (mask,id))

def c21683 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21683 : Upper (D 6) (R 6) [34,129,40,65,260,16] 13 := by
  apply FastRouting.sound _ _ [34,129,40,65,260,16] 13 (by decide) (choices 1) [2,4] r21683 c21683
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6369
  · exact u6370

def b21684 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 403, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 131 44 73 276 96 86 150 278), lower := (rows 35 131 44 73 276 96 64 128 256), losses := [] }

theorem u21684 : Upper (D 6) (R 6) [34,129,40,65,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21684 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21685 : PairBound 9 := { available := 20, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 44 73 336 34 84 148 276), lower := (rows 35 131 44 73 336 34 64 128 256), losses := [] }

theorem u21685 : Upper (D 6) (R 6) [34,129,40,65,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21685 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21686 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 131 44 73 336 36 86 150 278), lower := (rows 35 131 44 73 336 36 64 128 256), losses := [] }

theorem u21686 : Upper (D 6) (R 6) [34,129,40,65,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21686 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21687 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 131, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 44 73 336 48 70 134 262), lower := (rows 35 131 44 73 336 48 64 128 256), losses := [] }

theorem u21687 : Upper (D 6) (R 6) [34,129,40,65,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21687 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21688 : PairBound 9 := { available := 336, camps := [{ cop := 4, region := 458, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 35 131 44 74 21 36 336 464 336), lower := (rows 35 131 44 74 21 36 64 128 256), losses := [] }

theorem u21688 : Upper (D 6) (R 6) [34,129,40,66,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21688 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21689 : PairBound 9 := { available := 324, camps := [{ cop := 3, region := 53, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 131 44 74 21 48 324 452 324), lower := (rows 35 131 44 74 21 48 64 128 256), losses := [] }

theorem u21689 : Upper (D 6) (R 6) [34,129,40,66,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21689 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21690 : PairBound 9 := { available := 276, camps := [{ cop := 2, region := 403, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 131 44 74 21 96 340 404 276), lower := (rows 35 131 44 74 21 96 64 128 256), losses := [] }

theorem u21690 : Upper (D 6) (R 6) [34,129,40,66,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21690 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21691 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 202, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 35 131 44 74 21 288 84 212 340), lower := (rows 35 131 44 74 21 288 64 128 256), losses := [] }

theorem u21691 : Upper (D 6) (R 6) [34,129,40,66,5,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21691 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21692 : PairBound 9 := { available := 276, camps := [{ cop := 3, region := 36, targets := 3 },{ cop := 3, region := 37, targets := 64 }], pairs := [(0,6),(2,0),(2,1)], upper := (rows 35 131 44 74 81 36 340 404 276), lower := (rows 35 131 44 74 81 36 64 128 256), losses := [] }

theorem u21692 : Upper (D 6) (R 6) [34,129,40,66,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21692 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21693 : PairBound 9 := { available := 260, camps := [{ cop := 0, region := 332, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 131 44 74 81 48 324 388 260), lower := (rows 35 131 44 74 81 48 64 128 256), losses := [] }

theorem u21693 : Upper (D 6) (R 6) [34,129,40,66,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21693 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21694 : Route 9 := (fun mask => (mask,id))

def c21694 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21694 : Upper (D 6) (R 6) [34,129,40,66,65,256] 13 := by
  apply FastRouting.sound _ _ [34,129,40,66,65,256] 13 (by decide) (choices 1) [4,16] r21694 c21694
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6371
  · exact u6372

def b21695 : PairBound 9 := { available := 276, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 44 74 84 33 340 404 276), lower := (rows 35 131 44 74 84 33 64 128 256), losses := [] }

theorem u21695 : Upper (D 6) (R 6) [34,129,40,66,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21695 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21696 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 52, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 131 44 74 84 36 337 401 273), lower := (rows 35 131 44 74 84 36 64 128 256), losses := [] }

theorem u21696 : Upper (D 6) (R 6) [34,129,40,66,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21696 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21697 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 52, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 131 44 74 84 48 325 389 261), lower := (rows 35 131 44 74 84 48 64 128 256), losses := [] }

theorem u21697 : Upper (D 6) (R 6) [34,129,40,66,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21697 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21698 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 419, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 44 74 84 288 85 149 277), lower := (rows 35 131 44 74 84 288 64 128 256), losses := [] }

theorem u21698 : Upper (D 6) (R 6) [34,129,40,66,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21698 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21699 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 36, targets := 3 },{ cop := 3, region := 37, targets := 64 }], pairs := [(0,6),(2,0),(2,1)], upper := (rows 35 131 44 74 273 36 84 212 340), lower := (rows 35 131 44 74 273 36 64 128 256), losses := [] }

theorem u21699 : Upper (D 6) (R 6) [34,129,40,66,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21699 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21700 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 76, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 131 44 74 273 48 68 196 324), lower := (rows 35 131 44 74 273 48 64 128 256), losses := [] }

theorem u21700 : Upper (D 6) (R 6) [34,129,40,66,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21700 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21701 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 403, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 131 44 74 273 96 84 148 276), lower := (rows 35 131 44 74 273 96 64 128 256), losses := [] }

theorem u21701 : Upper (D 6) (R 6) [34,129,40,66,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21701 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21702 : PairBound 9 := { available := 84, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 44 74 276 33 84 212 340), lower := (rows 35 131 44 74 276 33 64 128 256), losses := [] }

theorem u21702 : Upper (D 6) (R 6) [34,129,40,66,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21702 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21703 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 36, targets := 3 },{ cop := 3, region := 37, targets := 64 }], pairs := [(0,6),(2,0),(2,1)], upper := (rows 35 131 44 74 276 36 81 209 337), lower := (rows 35 131 44 74 276 36 64 128 256), losses := [] }

theorem u21703 : Upper (D 6) (R 6) [34,129,40,66,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21703 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21704 : Route 9 := (fun mask => (mask,id))

def c21704 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21704 : Upper (D 6) (R 6) [34,129,40,66,260,16] 13 := by
  apply FastRouting.sound _ _ [34,129,40,66,260,16] 13 (by decide) (choices 1) [1,4] r21704 c21704
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6373
  · exact u6374

def b21705 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 403, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 131 44 74 276 96 85 149 277), lower := (rows 35 131 44 74 276 96 64 128 256), losses := [] }

theorem u21705 : Upper (D 6) (R 6) [34,129,40,66,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21705 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21706 : PairBound 9 := { available := 20, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 44 74 336 33 84 148 276), lower := (rows 35 131 44 74 336 33 64 128 256), losses := [] }

theorem u21706 : Upper (D 6) (R 6) [34,129,40,66,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21706 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21707 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 36, targets := 3 },{ cop := 3, region := 37, targets := 64 }], pairs := [(0,6),(2,0),(2,1)], upper := (rows 35 131 44 74 336 36 85 149 277), lower := (rows 35 131 44 74 336 36 64 128 256), losses := [] }

theorem u21707 : Upper (D 6) (R 6) [34,129,40,66,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21707 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21708 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 131, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 44 74 336 48 69 133 261), lower := (rows 35 131 44 74 336 48 64 128 256), losses := [] }

theorem u21708 : Upper (D 6) (R 6) [34,129,40,66,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21708 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21709 : PairBound 9 := { available := 336, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 44 76 22 33 336 464 336), lower := (rows 35 131 44 76 22 33 64 128 256), losses := [] }

theorem u21709 : Upper (D 6) (R 6) [34,129,40,68,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21709 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21710 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 131 44 76 22 48 321 449 321), lower := (rows 35 131 44 76 22 48 64 128 256), losses := [] }

theorem u21710 : Upper (D 6) (R 6) [34,129,40,68,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21710 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21711 : PairBound 9 := { available := 273, camps := [{ cop := 5, region := 12, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 44 76 22 96 337 401 273), lower := (rows 35 131 44 76 22 96 64 128 256), losses := [] }

theorem u21711 : Upper (D 6) (R 6) [34,129,40,68,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21711 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21712 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 483, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 131 44 76 22 288 81 209 337), lower := (rows 35 131 44 76 22 288 64 128 256), losses := [] }

theorem u21712 : Upper (D 6) (R 6) [34,129,40,68,6,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21712 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21713 : PairBound 9 := { available := 276, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 44 76 81 34 340 404 276), lower := (rows 35 131 44 76 81 34 64 128 256), losses := [] }

theorem u21713 : Upper (D 6) (R 6) [34,129,40,68,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21713 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21714 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 466, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 131 44 76 81 36 338 402 274), lower := (rows 35 131 44 76 81 36 64 128 256), losses := [] }

theorem u21714 : Upper (D 6) (R 6) [34,129,40,68,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21714 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21715 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 131 44 76 81 48 326 390 262), lower := (rows 35 131 44 76 81 48 64 128 256), losses := [] }

theorem u21715 : Upper (D 6) (R 6) [34,129,40,68,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21715 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21716 : Route 9 := (fun mask => (mask,id))

def c21716 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21716 : Upper (D 6) (R 6) [34,129,40,68,65,256] 13 := by
  apply FastRouting.sound _ _ [34,129,40,68,65,256] 13 (by decide) (choices 1) [2,4,16] r21716 c21716
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6375
  · exact u6376
  · exact u6377

def b21717 : PairBound 9 := { available := 276, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 44 76 82 33 340 404 276), lower := (rows 35 131 44 76 82 33 64 128 256), losses := [] }

theorem u21717 : Upper (D 6) (R 6) [34,129,40,68,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21717 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21718 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 466, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 131 44 76 82 36 337 401 273), lower := (rows 35 131 44 76 82 36 64 128 256), losses := [] }

theorem u21718 : Upper (D 6) (R 6) [34,129,40,68,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21718 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21719 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 131 44 76 82 48 325 389 261), lower := (rows 35 131 44 76 82 48 64 128 256), losses := [] }

theorem u21719 : Upper (D 6) (R 6) [34,129,40,68,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21719 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u21719
end Delivery.IrregularNine14.P06

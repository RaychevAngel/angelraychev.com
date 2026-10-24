import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0131

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b25560 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 43, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 41 50 388 74 84 33 71 135 263), lower := (rows 41 50 388 74 84 33 64 128 256), losses := [] }

theorem u25560 : Upper (D 6) (R 6) [40,48,384,66,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25560 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25561 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 41 50 388 74 84 34 69 133 261), lower := (rows 41 50 388 74 84 34 64 128 256), losses := [] }

theorem u25561 : Upper (D 6) (R 6) [40,48,384,66,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25561 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25562 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 73, targets := 4 },{ cop := 3, region := 421, targets := 64 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 50 388 74 84 36 67 131 259), lower := (rows 41 50 388 74 84 36 64 128 256), losses := [] }

theorem u25562 : Upper (D 6) (R 6) [40,48,384,66,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25562 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25563 : PairBound 9 := { available := 260, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 82 100 11 145 34 324 388 260), lower := (rows 41 82 100 11 145 34 64 128 256), losses := [] }

theorem u25563 : Upper (D 6) (R 6) [40,80,96,3,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25563 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25564 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 358, targets := 1 },{ cop := 1, region := 36, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 41 82 100 11 145 36 326 390 262), lower := (rows 41 82 100 11 145 36 64 128 256), losses := [] }

theorem u25564 : Upper (D 6) (R 6) [40,80,96,3,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25564 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25565 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 358, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 41 82 100 11 145 288 70 134 262), lower := (rows 41 82 100 11 145 288 64 128 256), losses := [] }

theorem u25565 : Upper (D 6) (R 6) [40,80,96,3,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25565 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25566 : PairBound 9 := { available := 260, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 82 100 11 146 33 324 388 260), lower := (rows 41 82 100 11 146 33 64 128 256), losses := [] }

theorem u25566 : Upper (D 6) (R 6) [40,80,96,3,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25566 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25567 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 357, targets := 2 },{ cop := 1, region := 36, targets := 1 }], pairs := [(0,1),(2,0),(2,1)], upper := (rows 41 82 100 11 146 36 325 389 261), lower := (rows 41 82 100 11 146 36 64 128 256), losses := [] }

theorem u25567 : Upper (D 6) (R 6) [40,80,96,3,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25567 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25568 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 357, targets := 2 }], pairs := [(0,1),(2,1)], upper := (rows 41 82 100 11 146 288 69 133 261), lower := (rows 41 82 100 11 146 288 64 128 256), losses := [] }

theorem u25568 : Upper (D 6) (R 6) [40,80,96,3,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25568 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25569 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 82 100 11 148 33 326 390 262), lower := (rows 41 82 100 11 148 33 64 128 256), losses := [] }

theorem u25569 : Upper (D 6) (R 6) [40,80,96,3,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25569 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25570 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 82 100 11 148 34 325 389 261), lower := (rows 41 82 100 11 148 34 64 128 256), losses := [] }

theorem u25570 : Upper (D 6) (R 6) [40,80,96,3,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25570 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25571 : PairBound 9 := { available := 259, camps := [{ cop := 6, region := 36, targets := 3 }], pairs := [(0,1),(2,0),(2,1)], upper := (rows 41 82 100 11 148 36 323 387 259), lower := (rows 41 82 100 11 148 36 64 128 256), losses := [{ target := 1, region := (rows 9 0 70 8 16 126 64 128 256), good := (rows 41 116 100 45 180 36 100 128 256) }] }

theorem u25571 : Upper (D 6) (R 6) [40,80,96,3,132,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25571 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25572 : Route 9 := (fun mask => (mask,id))

def c25572 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25572 : Upper (D 6) (R 6) [40,80,96,3,132,256] 13 := by
  apply FastRouting.sound _ _ [40,80,96,3,132,256] 13 (by decide) (choices 1) [1,2,4] r25572 c25572
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7896
  · exact u7897
  · exact u7898

def b25573 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 82 100 11 400 33 70 134 262), lower := (rows 41 82 100 11 400 33 64 128 256), losses := [] }

theorem u25573 : Upper (D 6) (R 6) [40,80,96,3,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25573 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25574 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 82 100 11 400 34 69 133 261), lower := (rows 41 82 100 11 400 34 64 128 256), losses := [] }

theorem u25574 : Upper (D 6) (R 6) [40,80,96,3,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25574 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25575 : PairBound 9 := { available := 7, camps := [{ cop := 6, region := 36, targets := 3 }], pairs := [(0,1),(2,0),(2,1)], upper := (rows 41 82 100 11 400 36 71 135 263), lower := (rows 41 82 100 11 400 36 64 128 256), losses := [{ target := 1, region := (rows 9 0 70 8 16 110 64 128 256), good := (rows 41 116 100 45 400 36 100 128 256) }] }

theorem u25575 : Upper (D 6) (R 6) [40,80,96,3,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25575 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25576 : PairBound 9 := { available := 262, camps := [{ cop := 3, region := 33, targets := 6 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 82 100 14 145 33 326 390 262), lower := (rows 41 82 100 14 145 33 64 128 256), losses := [] }

theorem u25576 : Upper (D 6) (R 6) [40,80,96,6,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25576 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25577 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 1, region := 36, targets := 1 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 41 82 100 14 145 34 325 389 261), lower := (rows 41 82 100 14 145 34 64 128 256), losses := [] }

theorem u25577 : Upper (D 6) (R 6) [40,80,96,6,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25577 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25578 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 466, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 41 82 100 14 145 36 323 387 259), lower := (rows 41 82 100 14 145 36 64 128 256), losses := [] }

theorem u25578 : Upper (D 6) (R 6) [40,80,96,6,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25578 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25579 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 433, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 41 82 100 14 145 288 71 135 263), lower := (rows 41 82 100 14 145 288 64 128 256), losses := [] }

theorem u25579 : Upper (D 6) (R 6) [40,80,96,6,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25579 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25580 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 33, targets := 6 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 82 100 14 400 33 71 135 263), lower := (rows 41 82 100 14 400 33 64 128 256), losses := [] }

theorem u25580 : Upper (D 6) (R 6) [40,80,96,6,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25580 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25581 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 1, region := 36, targets := 1 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 41 82 100 14 400 34 69 133 261), lower := (rows 41 82 100 14 400 34 64 128 256), losses := [] }

theorem u25581 : Upper (D 6) (R 6) [40,80,96,6,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25581 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25582 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 466, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 41 82 100 14 400 36 67 131 259), lower := (rows 41 82 100 14 400 36 64 128 256), losses := [] }

theorem u25582 : Upper (D 6) (R 6) [40,80,96,6,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25582 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25583 : Route 9 := (fun mask => (mask,id))

def c25583 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25583 : Upper (D 6) (R 6) [40,80,96,129,257,2] 13 := by
  apply FastRouting.sound _ _ [40,80,96,129,257,2] 13 (by decide) (choices 1) [2,4] r25583 c25583
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7899
  · exact u7900

def b25584 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 102, targets := 1 },{ cop := 1, region := 36, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 41 82 100 137 273 36 70 134 262), lower := (rows 41 82 100 137 273 36 64 128 256), losses := [] }

theorem u25584 : Upper (D 6) (R 6) [40,80,96,129,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25584 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25585 : PairBound 9 := { available := 6, camps := [{ cop := 7, region := 41, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 82 100 137 274 33 70 134 262), lower := (rows 41 82 100 137 274 33 64 128 256), losses := [] }

theorem u25585 : Upper (D 6) (R 6) [40,80,96,129,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25585 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25586 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 205, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 41 82 100 137 274 34 69 133 261), lower := (rows 41 82 100 137 274 34 64 128 256), losses := [] }

theorem u25586 : Upper (D 6) (R 6) [40,80,96,129,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25586 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m25587_1 : Upper (D 6) (R 6) [40,80,96,129,258,4,1] 13 :=
  permutation_upper _ _ _ [40,80,96,129,258,2,4] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7902

theorem m25587_2 : Upper (D 6) (R 6) [40,80,96,129,258,4,2] 13 :=
  permutation_upper _ _ _ [40,80,96,129,258,1,4] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7901

def r25587 : Route 9 := (fun mask => (mask,id))

def c25587 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25587 : Upper (D 6) (R 6) [40,80,96,129,258,4] 13 := by
  apply FastRouting.sound _ _ [40,80,96,129,258,4] 13 (by decide) (choices 1) [1,2,4] r25587 c25587
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m25587_1
  · exact m25587_2
  · exact u7903

def b25588 : PairBound 9 := { available := 6, camps := [{ cop := 7, region := 41, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 82 100 137 276 33 70 134 262), lower := (rows 41 82 100 137 276 33 64 128 256), losses := [] }

theorem u25588 : Upper (D 6) (R 6) [40,80,96,129,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25588 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25589 : Route 9 := (fun mask => (mask,id))

def c25589 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25589 : Upper (D 6) (R 6) [40,80,96,129,260,2] 13 := by
  apply FastRouting.sound _ _ [40,80,96,129,260,2] 13 (by decide) (choices 1) [1,2,4] r25589 c25589
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7904
  · exact u7905
  · exact u7906

def b25590 : PairBound 9 := { available := 3, camps := [{ cop := 6, region := 36, targets := 3 }], pairs := [(0,6),(2,0),(2,1)], upper := (rows 41 82 100 137 276 36 67 131 259), lower := (rows 41 82 100 137 276 36 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 10 16 52 0 130 258), good := (rows 41 443 36 137 308 36 0 128 256) }] }

theorem u25590 : Upper (D 6) (R 6) [40,80,96,129,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25590 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25591 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 82 100 138 273 33 70 134 262), lower := (rows 41 82 100 138 273 33 64 128 256), losses := [] }

theorem u25591 : Upper (D 6) (R 6) [40,80,96,130,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25591 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25592 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 41 82 100 138 273 34 69 133 261), lower := (rows 41 82 100 138 273 34 64 128 256), losses := [] }

theorem u25592 : Upper (D 6) (R 6) [40,80,96,130,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25592 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25593 : PairBound 9 := { available := 7, camps := [{ cop := 6, region := 36, targets := 3 }], pairs := [(0,1),(2,0),(2,1)], upper := (rows 41 82 100 138 273 36 71 135 263), lower := (rows 41 82 100 138 273 36 64 128 256), losses := [{ target := 1, region := (rows 9 0 70 8 16 110 64 128 256), good := (rows 41 116 100 173 273 36 100 128 256) }] }

theorem u25593 : Upper (D 6) (R 6) [40,80,96,130,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25593 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25594 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 82 100 138 276 33 71 135 263), lower := (rows 41 82 100 138 276 33 64 128 256), losses := [] }

theorem u25594 : Upper (D 6) (R 6) [40,80,96,130,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25594 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25595 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 41 82 100 138 276 34 69 133 261), lower := (rows 41 82 100 138 276 34 64 128 256), losses := [] }

theorem u25595 : Upper (D 6) (R 6) [40,80,96,130,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25595 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25596 : PairBound 9 := { available := 3, camps := [{ cop := 6, region := 36, targets := 3 }], pairs := [(0,1),(2,0),(2,1)], upper := (rows 41 82 100 138 276 36 67 131 259), lower := (rows 41 82 100 138 276 36 64 128 256), losses := [{ target := 1, region := (rows 9 0 70 8 16 126 64 128 256), good := (rows 41 116 100 173 308 36 100 128 256) }] }

theorem u25596 : Upper (D 6) (R 6) [40,80,96,130,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25596 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25597 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 82 100 140 276 33 67 131 259), lower := (rows 41 82 100 140 276 33 64 128 256), losses := [] }

theorem u25597 : Upper (D 6) (R 6) [40,80,96,132,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25597 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m25598_2 : Upper (D 6) (R 6) [40,80,96,132,260,2,2] 13 :=
  permutation_upper _ _ _ [40,80,96,132,260,1,1] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7907

def r25598 : Route 9 := (fun mask => (mask,id))

def c25598 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25598 : Upper (D 6) (R 6) [40,80,96,132,260,2] 13 := by
  apply FastRouting.sound _ _ [40,80,96,132,260,2] 13 (by decide) (choices 1) [1,2] r25598 c25598
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7908
  · exact m25598_2

def b25599 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 82 133 11 276 34 100 228 356), lower := (rows 41 82 133 11 276 34 64 128 256), losses := [] }

theorem u25599 : Upper (D 6) (R 6) [40,80,129,3,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25599 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25600 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 370, targets := 1 }], pairs := [(0,6),(1,0),(4,0)], upper := (rows 41 82 133 11 276 36 98 226 354), lower := (rows 41 82 133 11 276 36 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 10 16 52 0 128 256), good := (rows 41 59 165 11 308 36 0 128 256) }] }

theorem u25600 : Upper (D 6) (R 6) [40,80,129,3,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25600 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25601 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 41, targets := 4 },{ cop := 2, region := 370, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 41 82 133 11 276 96 102 166 294), lower := (rows 41 82 133 11 276 96 64 128 256), losses := [] }

theorem u25601 : Upper (D 6) (R 6) [40,80,129,3,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25601 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25602 : PairBound 9 := { available := 352, camps := [{ cop := 0, region := 338, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 82 133 14 19 36 352 480 352), lower := (rows 41 82 133 14 19 36 64 128 256), losses := [] }

theorem u25602 : Upper (D 6) (R 6) [40,80,129,6,3,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25602 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25603 : PairBound 9 := { available := 292, camps := [{ cop := 3, region := 485, targets := 2 },{ cop := 0, region := 388, targets := 64 }], pairs := [(0,1),(2,1),(2,6)], upper := (rows 41 82 133 14 19 96 356 420 292), lower := (rows 41 82 133 14 19 96 64 128 256), losses := [] }

theorem u25603 : Upper (D 6) (R 6) [40,80,129,6,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25603 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25604 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 485, targets := 2 }], pairs := [(0,1),(2,1)], upper := (rows 41 82 133 14 19 288 100 228 356), lower := (rows 41 82 133 14 19 288 64 128 256), losses := [] }

theorem u25604 : Upper (D 6) (R 6) [40,80,129,6,3,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25604 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25605 : PairBound 9 := { available := 322, camps := [{ cop := 3, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 41 82 133 14 52 33 322 450 322), lower := (rows 41 82 133 14 52 33 64 128 256), losses := [] }

theorem u25605 : Upper (D 6) (R 6) [40,80,129,6,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25605 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25606 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(4,1)], upper := (rows 41 82 133 14 52 34 321 449 321), lower := (rows 41 82 133 14 52 34 64 128 256), losses := [] }

theorem u25606 : Upper (D 6) (R 6) [40,80,129,6,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25606 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25607 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 353, targets := 4 }], pairs := [(0,1),(0,2),(4,0)], upper := (rows 41 82 133 14 52 96 323 387 259), lower := (rows 41 82 133 14 52 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 24 98 64 128 256), good := (rows 56 114 132 62 52 96 96 128 256) },{ target := 1, region := (rows 9 0 4 8 24 98 64 128 256), good := (rows 57 112 133 61 52 96 96 128 256) }] }

theorem u25607 : Upper (D 6) (R 6) [40,80,129,6,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25607 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25608 : Route 9 := (fun mask => (mask,id))

def c25608 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25608 : Upper (D 6) (R 6) [40,80,129,6,36,256] 13 := by
  apply FastRouting.sound _ _ [40,80,129,6,36,256] 13 (by decide) (choices 1) [1,2] r25608 c25608
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7909
  · exact u7910

def b25609 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 41 82 133 14 273 34 100 228 356), lower := (rows 41 82 133 14 273 34 64 128 256), losses := [] }

theorem u25609 : Upper (D 6) (R 6) [40,80,129,6,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25609 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25610 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 338, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 82 133 14 273 36 98 226 354), lower := (rows 41 82 133 14 273 36 64 128 256), losses := [] }

theorem u25610 : Upper (D 6) (R 6) [40,80,129,6,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25610 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25611 : Route 9 := (fun mask => (mask,id))

def c25611 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25611 : Upper (D 6) (R 6) [40,80,129,6,257,64] 13 := by
  apply FastRouting.sound _ _ [40,80,129,6,257,64] 13 (by decide) (choices 1) [2,4,32] r25611 c25611
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7911
  · exact u7912
  · exact u7913

def b25612 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 229, targets := 2 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,1),(0,2),(2,1)], upper := (rows 41 82 133 14 274 33 100 228 356), lower := (rows 41 82 133 14 274 33 64 128 256), losses := [] }

theorem u25612 : Upper (D 6) (R 6) [40,80,129,6,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25612 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25613 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 338, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 82 133 14 274 36 97 225 353), lower := (rows 41 82 133 14 274 36 64 128 256), losses := [] }

theorem u25613 : Upper (D 6) (R 6) [40,80,129,6,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25613 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25614 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 229, targets := 2 },{ cop := 0, region := 132, targets := 64 }], pairs := [(0,1),(2,1),(2,6)], upper := (rows 41 82 133 14 274 96 101 165 293), lower := (rows 41 82 133 14 274 96 64 128 256), losses := [] }

theorem u25614 : Upper (D 6) (R 6) [40,80,129,6,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25614 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25615 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 33, targets := 66 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 82 133 14 276 33 98 226 354), lower := (rows 41 82 133 14 276 33 64 128 256), losses := [] }

theorem u25615 : Upper (D 6) (R 6) [40,80,129,6,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25615 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25616 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 41 82 133 14 276 34 97 225 353), lower := (rows 41 82 133 14 276 34 64 128 256), losses := [] }

theorem u25616 : Upper (D 6) (R 6) [40,80,129,6,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25616 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25617 : Route 9 := (fun mask => (mask,id))

def c25617 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25617 : Upper (D 6) (R 6) [40,80,129,6,260,64] 13 := by
  apply FastRouting.sound _ _ [40,80,129,6,260,64] 13 (by decide) (choices 1) [1,2,32] r25617 c25617
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7914
  · exact u7915
  · exact u7916

def b25618 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 82 133 14 304 33 70 198 326), lower := (rows 41 82 133 14 304 33 64 128 256), losses := [] }

theorem u25618 : Upper (D 6) (R 6) [40,80,129,6,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25618 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25619 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 41 82 133 14 304 34 69 197 325), lower := (rows 41 82 133 14 304 34 64 128 256), losses := [] }

theorem u25619 : Upper (D 6) (R 6) [40,80,129,6,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25619 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u25619
end Delivery.IrregularNine14.P06

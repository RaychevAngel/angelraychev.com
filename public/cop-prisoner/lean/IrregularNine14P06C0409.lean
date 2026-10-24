import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0126

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b24540 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 293, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 194 44 26 81 288 69 133 261), lower := (rows 35 194 44 26 81 288 64 128 256), losses := [] }

theorem u24540 : Upper (D 6) (R 6) [34,192,40,18,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24540 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24541 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 37, targets := 64 }], pairs := [(0,2),(0,6),(2,6)], upper := (rows 35 194 44 26 84 33 325 389 261), lower := (rows 35 194 44 26 84 33 64 128 256), losses := [] }

theorem u24541 : Upper (D 6) (R 6) [34,192,40,18,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24541 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24542 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 60, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 194 44 26 84 36 321 385 257), lower := (rows 35 194 44 26 84 36 64 128 256), losses := [] }

theorem u24542 : Upper (D 6) (R 6) [34,192,40,18,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24542 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24543 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 293, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 194 44 26 84 288 69 133 261), lower := (rows 35 194 44 26 84 288 64 128 256), losses := [] }

theorem u24543 : Upper (D 6) (R 6) [34,192,40,18,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24543 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24544 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 2, region := 194, targets := 1 }], pairs := [(0,2),(0,6),(1,0)], upper := (rows 35 194 44 26 273 33 68 196 324), lower := (rows 35 194 44 26 273 33 64 128 256), losses := [] }

theorem u24544 : Upper (D 6) (R 6) [34,192,40,18,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24544 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24545 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 36, targets := 3 },{ cop := 3, region := 37, targets := 64 }], pairs := [(0,6),(2,0),(2,1)], upper := (rows 35 194 44 26 273 36 69 197 325), lower := (rows 35 194 44 26 273 36 64 128 256), losses := [] }

theorem u24545 : Upper (D 6) (R 6) [34,192,40,18,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24545 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24546 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 284, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 194 44 26 273 96 69 133 261), lower := (rows 35 194 44 26 273 96 64 128 256), losses := [] }

theorem u24546 : Upper (D 6) (R 6) [34,192,40,18,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24546 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24547 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 37, targets := 64 }], pairs := [(0,2),(0,6),(2,6)], upper := (rows 35 194 44 26 276 33 69 197 325), lower := (rows 35 194 44 26 276 33 64 128 256), losses := [] }

theorem u24547 : Upper (D 6) (R 6) [34,192,40,18,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24547 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24548 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 194, targets := 36 },{ cop := 3, region := 36, targets := 1 }], pairs := [(1,2),(1,5),(2,0)], upper := (rows 35 194 44 26 276 36 65 193 321), lower := (rows 35 194 44 26 276 36 64 128 256), losses := [] }

theorem u24548 : Upper (D 6) (R 6) [34,192,40,18,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24548 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24549 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 284, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 194 44 26 276 96 69 133 261), lower := (rows 35 194 44 26 276 96 64 128 256), losses := [] }

theorem u24549 : Upper (D 6) (R 6) [34,192,40,18,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24549 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24550 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 37, targets := 64 }], pairs := [(0,2),(0,6),(2,6)], upper := (rows 35 194 44 26 336 33 69 133 261), lower := (rows 35 194 44 26 336 33 64 128 256), losses := [] }

theorem u24550 : Upper (D 6) (R 6) [34,192,40,18,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24550 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24551 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 36, targets := 3 },{ cop := 3, region := 37, targets := 64 }], pairs := [(0,6),(2,0),(2,1)], upper := (rows 35 194 44 26 336 36 69 133 261), lower := (rows 35 194 44 26 336 36 64 128 256), losses := [] }

theorem u24551 : Upper (D 6) (R 6) [34,192,40,18,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24551 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24552 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 44, targets := 66 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 35 194 44 28 81 33 326 390 262), lower := (rows 35 194 44 28 81 33 64 128 256), losses := [] }

theorem u24552 : Upper (D 6) (R 6) [34,192,40,20,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24552 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24553 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 44 28 81 34 325 389 261), lower := (rows 35 194 44 28 81 34 64 128 256), losses := [] }

theorem u24553 : Upper (D 6) (R 6) [34,192,40,20,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24553 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24554 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 44, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 194 44 28 81 36 323 387 259), lower := (rows 35 194 44 28 81 36 64 128 256), losses := [] }

theorem u24554 : Upper (D 6) (R 6) [34,192,40,20,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24554 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24555 : Route 9 := (fun mask => (mask,id))

def c24555 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24555 : Upper (D 6) (R 6) [34,192,40,20,65,256] 13 := by
  apply FastRouting.sound _ _ [34,192,40,20,65,256] 13 (by decide) (choices 1) [1,2,4] r24555 c24555
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7561
  · exact u7562
  · exact u7563

def b24556 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 44, targets := 66 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 35 194 44 28 273 33 70 198 326), lower := (rows 35 194 44 28 273 33 64 128 256), losses := [] }

theorem u24556 : Upper (D 6) (R 6) [34,192,40,20,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24556 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24557 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 44 28 273 34 69 197 325), lower := (rows 35 194 44 28 273 34 64 128 256), losses := [] }

theorem u24557 : Upper (D 6) (R 6) [34,192,40,20,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24557 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24558 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 44, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 194 44 28 273 36 67 195 323), lower := (rows 35 194 44 28 273 36 64 128 256), losses := [] }

theorem u24558 : Upper (D 6) (R 6) [34,192,40,20,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24558 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24559 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 284, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 194 44 28 273 96 71 135 263), lower := (rows 35 194 44 28 273 96 64 128 256), losses := [] }

theorem u24559 : Upper (D 6) (R 6) [34,192,40,20,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24559 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24560 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 45, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 194 44 28 274 33 69 197 325), lower := (rows 35 194 44 28 274 33 64 128 256), losses := [] }

theorem u24560 : Upper (D 6) (R 6) [34,192,40,20,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24560 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24561 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 466, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 194 44 28 274 36 65 193 321), lower := (rows 35 194 44 28 274 36 64 128 256), losses := [] }

theorem u24561 : Upper (D 6) (R 6) [34,192,40,20,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24561 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24562 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 284, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 194 44 28 274 96 69 133 261), lower := (rows 35 194 44 28 274 96 64 128 256), losses := [] }

theorem u24562 : Upper (D 6) (R 6) [34,192,40,20,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24562 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24563 : Route 9 := (fun mask => (mask,id))

def c24563 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24563 : Upper (D 6) (R 6) [34,192,40,20,320,1] 13 := by
  apply FastRouting.sound _ _ [34,192,40,20,320,1] 13 (by decide) (choices 1) [1,2,4] r24563 c24563
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7564
  · exact u7565
  · exact u7566

def b24564 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 44 28 336 34 69 133 261), lower := (rows 35 194 44 28 336 34 64 128 256), losses := [] }

theorem u24564 : Upper (D 6) (R 6) [34,192,40,20,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24564 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24565 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 44, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 194 44 28 336 36 67 131 259), lower := (rows 35 194 44 28 336 36 64 128 256), losses := [] }

theorem u24565 : Upper (D 6) (R 6) [34,192,40,20,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24565 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24566 : PairBound 9 := { available := 276, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 194 44 73 22 33 340 404 276), lower := (rows 35 194 44 73 22 33 64 128 256), losses := [] }

theorem u24566 : Upper (D 6) (R 6) [34,192,40,65,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24566 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24567 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 194 44 73 22 36 337 401 273), lower := (rows 35 194 44 73 22 36 64 128 256), losses := [] }

theorem u24567 : Upper (D 6) (R 6) [34,192,40,65,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24567 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24568 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 194 44 73 22 48 325 389 261), lower := (rows 35 194 44 73 22 48 64 128 256), losses := [] }

theorem u24568 : Upper (D 6) (R 6) [34,192,40,65,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24568 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24569 : Route 9 := (fun mask => (mask,id))

def c24569 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24569 : Upper (D 6) (R 6) [34,192,40,65,6,256] 13 := by
  apply FastRouting.sound _ _ [34,192,40,65,6,256] 13 (by decide) (choices 1) [1,4,16] r24569 c24569
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7567
  · exact u7568
  · exact u7569

def b24570 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 44 73 273 34 84 148 276), lower := (rows 35 194 44 73 273 34 64 128 256), losses := [] }

theorem u24570 : Upper (D 6) (R 6) [34,192,40,65,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24570 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24571 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 194 44 73 273 36 86 150 278), lower := (rows 35 194 44 73 273 36 64 128 256), losses := [] }

theorem u24571 : Upper (D 6) (R 6) [34,192,40,65,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24571 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24572 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 194, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 194 44 73 273 48 70 134 262), lower := (rows 35 194 44 73 273 48 64 128 256), losses := [] }

theorem u24572 : Upper (D 6) (R 6) [34,192,40,65,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24572 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24573 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 194 44 73 274 33 84 148 276), lower := (rows 35 194 44 73 274 33 64 128 256), losses := [] }

theorem u24573 : Upper (D 6) (R 6) [34,192,40,65,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24573 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24574 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 194 44 73 274 36 85 149 277), lower := (rows 35 194 44 73 274 36 64 128 256), losses := [] }

theorem u24574 : Upper (D 6) (R 6) [34,192,40,65,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24574 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24575 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 76, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 194 44 73 274 48 69 133 261), lower := (rows 35 194 44 73 274 48 64 128 256), losses := [] }

theorem u24575 : Upper (D 6) (R 6) [34,192,40,65,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24575 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24576 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 194 44 73 276 33 86 150 278), lower := (rows 35 194 44 73 276 33 64 128 256), losses := [] }

theorem u24576 : Upper (D 6) (R 6) [34,192,40,65,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24576 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24577 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 44 73 276 34 85 149 277), lower := (rows 35 194 44 73 276 34 64 128 256), losses := [] }

theorem u24577 : Upper (D 6) (R 6) [34,192,40,65,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24577 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24578 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 194 44 73 276 36 83 147 275), lower := (rows 35 194 44 73 276 36 64 128 256), losses := [] }

theorem u24578 : Upper (D 6) (R 6) [34,192,40,65,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24578 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24579 : Route 9 := (fun mask => (mask,id))

def c24579 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24579 : Upper (D 6) (R 6) [34,192,40,65,260,16] 13 := by
  apply FastRouting.sound _ _ [34,192,40,65,260,16] 13 (by decide) (choices 1) [1,2,4] r24579 c24579
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7570
  · exact u7571
  · exact u7572

def r24580 : Route 9 := (fun mask => (mask,id))

def c24580 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24580 : Upper (D 6) (R 6) [34,192,40,68,257,1] 13 := by
  apply FastRouting.sound _ _ [34,192,40,68,257,1] 13 (by decide) (choices 1) [2,4,16] r24580 c24580
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7573
  · exact u7574
  · exact u7575

def b24581 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 44 76 273 34 85 149 277), lower := (rows 35 194 44 76 273 34 64 128 256), losses := [] }

theorem u24581 : Upper (D 6) (R 6) [34,192,40,68,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24581 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24582 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 466, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 194 44 76 273 36 83 147 275), lower := (rows 35 194 44 76 273 36 64 128 256), losses := [] }

theorem u24582 : Upper (D 6) (R 6) [34,192,40,68,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24582 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24583 : Route 9 := (fun mask => (mask,id))

def c24583 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24583 : Upper (D 6) (R 6) [34,192,40,68,257,16] 13 := by
  apply FastRouting.sound _ _ [34,192,40,68,257,16] 13 (by decide) (choices 1) [1,2,4] r24583 c24583
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7576
  · exact u7577
  · exact u7578

def r24584 : Route 9 := (fun mask => (mask,id))

def c24584 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24584 : Upper (D 6) (R 6) [34,192,40,68,258,1] 13 := by
  apply FastRouting.sound _ _ [34,192,40,68,258,1] 13 (by decide) (choices 1) [1,4,16] r24584 c24584
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7579
  · exact u7580
  · exact u7581

def b24585 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 466, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 194 44 76 274 36 81 145 273), lower := (rows 35 194 44 76 274 36 64 128 256), losses := [] }

theorem u24585 : Upper (D 6) (R 6) [34,192,40,68,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24585 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24586 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 76, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 194 44 76 274 48 69 133 261), lower := (rows 35 194 44 76 274 48 64 128 256), losses := [] }

theorem u24586 : Upper (D 6) (R 6) [34,192,40,68,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24586 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24587 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 4, region := 227, targets := 4 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 194 44 76 276 33 83 147 275), lower := (rows 35 194 44 76 276 33 64 128 256), losses := [] }

theorem u24587 : Upper (D 6) (R 6) [34,192,40,68,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24587 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24588 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 44 76 276 34 81 145 273), lower := (rows 35 194 44 76 276 34 64 128 256), losses := [] }

theorem u24588 : Upper (D 6) (R 6) [34,192,40,68,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24588 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24589 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 194, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 35 194 44 76 276 48 67 131 259), lower := (rows 35 194 44 76 276 48 64 128 256), losses := [] }

theorem u24589 : Upper (D 6) (R 6) [34,192,40,68,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24589 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24590 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 458, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 194 44 88 21 33 326 390 262), lower := (rows 35 194 44 88 21 33 64 128 256), losses := [] }

theorem u24590 : Upper (D 6) (R 6) [34,192,40,80,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24590 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24591 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 44 88 21 34 325 389 261), lower := (rows 35 194 44 88 21 34 64 128 256), losses := [] }

theorem u24591 : Upper (D 6) (R 6) [34,192,40,80,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24591 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24592 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 458, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 35 194 44 88 21 36 323 387 259), lower := (rows 35 194 44 88 21 36 64 128 256), losses := [] }

theorem u24592 : Upper (D 6) (R 6) [34,192,40,80,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24592 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24593 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 202, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 35 194 44 88 21 288 71 135 263), lower := (rows 35 194 44 88 21 288 64 128 256), losses := [] }

theorem u24593 : Upper (D 6) (R 6) [34,192,40,80,5,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24593 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24594 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(2,6)], upper := (rows 35 194 44 88 22 33 325 389 261), lower := (rows 35 194 44 88 22 33 64 128 256), losses := [{ target := 6, region := (rows 19 2 12 8 16 59 0 152 280), good := (rows 35 163 428 445 439 33 0 128 256) }] }

theorem u24594 : Upper (D 6) (R 6) [34,192,40,80,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24594 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24595 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 60, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 194 44 88 22 36 321 385 257), lower := (rows 35 194 44 88 22 36 64 128 256), losses := [] }

theorem u24595 : Upper (D 6) (R 6) [34,192,40,80,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24595 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24596 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 289, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 194 44 88 22 288 69 133 261), lower := (rows 35 194 44 88 22 288 64 128 256), losses := [{ target := 6, region := (rows 17 2 12 8 16 316 0 152 280), good := (rows 35 130 428 445 439 288 0 128 288) }] }

theorem u24596 : Upper (D 6) (R 6) [34,192,40,80,6,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24596 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24597 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 2, region := 194, targets := 1 }], pairs := [(0,2),(0,6),(1,0)], upper := (rows 35 194 44 88 273 33 70 134 262), lower := (rows 35 194 44 88 273 33 64 128 256), losses := [] }

theorem u24597 : Upper (D 6) (R 6) [34,192,40,80,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24597 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24598 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 44 88 273 34 69 133 261), lower := (rows 35 194 44 88 273 34 64 128 256), losses := [] }

theorem u24598 : Upper (D 6) (R 6) [34,192,40,80,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24598 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24599 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 194 44 88 273 36 71 135 263), lower := (rows 35 194 44 88 273 36 64 128 256), losses := [] }

theorem u24599 : Upper (D 6) (R 6) [34,192,40,80,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24599 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u24599
end Delivery.IrregularNine14.P06

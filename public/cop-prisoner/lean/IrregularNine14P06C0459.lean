import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0145

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b27540 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 194, targets := 33 },{ cop := 4, region := 324, targets := 1 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 97 138 276 13 50 33 70 198 326), lower := (rows 97 138 276 13 50 33 64 128 256), losses := [] }

theorem u27540 : Upper (D 6) (R 6) [96,136,272,5,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27540 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27541 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 48, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 97 138 276 13 50 34 69 197 325), lower := (rows 97 138 276 13 50 34 64 128 256), losses := [] }

theorem u27541 : Upper (D 6) (R 6) [96,136,272,5,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27541 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27542 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 194, targets := 36 },{ cop := 4, region := 65, targets := 4 }], pairs := [(0,2),(1,2),(1,5)], upper := (rows 97 138 276 13 50 36 67 195 323), lower := (rows 97 138 276 13 50 36 64 128 256), losses := [] }

theorem u27542 : Upper (D 6) (R 6) [96,136,272,5,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27542 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27543 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 138 276 13 50 96 71 135 263), lower := (rows 97 138 276 13 50 96 64 128 256), losses := [] }

theorem u27543 : Upper (D 6) (R 6) [96,136,272,5,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27543 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27544 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 325, targets := 2 },{ cop := 6, region := 33, targets := 4 }], pairs := [(0,1),(0,2),(2,1)], upper := (rows 97 138 276 14 50 33 69 197 325), lower := (rows 97 138 276 14 50 33 64 128 256), losses := [] }

theorem u27544 : Upper (D 6) (R 6) [96,136,272,6,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27544 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27545 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 48, targets := 65 },{ cop := 4, region := 65, targets := 2 }], pairs := [(0,1),(4,0),(4,6)], upper := (rows 97 138 276 14 50 36 65 193 321), lower := (rows 97 138 276 14 50 36 64 128 256), losses := [] }

theorem u27545 : Upper (D 6) (R 6) [96,136,272,6,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27545 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27546 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 138 276 14 50 96 69 133 261), lower := (rows 97 138 276 14 50 96 64 128 256), losses := [] }

theorem u27546 : Upper (D 6) (R 6) [96,136,272,6,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27546 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27547 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 227, targets := 4 },{ cop := 6, region := 33, targets := 2 }], pairs := [(0,1),(0,2),(1,2)], upper := (rows 97 138 276 14 52 33 67 195 323), lower := (rows 97 138 276 14 52 33 64 128 256), losses := [] }

theorem u27547 : Upper (D 6) (R 6) [96,136,272,6,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27547 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27548 : PairBound 9 := { available := 65, camps := [{ cop := 5, region := 341, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 97 138 276 14 52 34 65 193 321), lower := (rows 97 138 276 14 52 34 64 128 256), losses := [] }

theorem u27548 : Upper (D 6) (R 6) [96,136,272,6,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27548 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27549 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 138 276 14 52 96 67 131 259), lower := (rows 97 138 276 14 52 96 64 128 256), losses := [] }

theorem u27549 : Upper (D 6) (R 6) [96,136,272,6,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27549 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27550 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 293, targets := 2 },{ cop := 4, region := 33, targets := 4 }], pairs := [(0,1),(0,2),(2,1)], upper := (rows 97 138 276 42 82 33 69 133 261), lower := (rows 97 138 276 42 82 33 64 128 256), losses := [] }

theorem u27550 : Upper (D 6) (R 6) [96,136,272,34,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27550 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27551 : Route 9 := (fun mask => (mask,id))

def c27551 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27551 : Upper (D 6) (R 6) [96,136,272,34,66,4] 13 := by
  apply FastRouting.sound _ _ [96,136,272,34,66,4] 13 (by decide) (choices 1) [1,4] r27551 c27551
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8723
  · exact u8724

def r27552 : Route 9 := (fun mask => (mask,id))

def c27552 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27552 : Upper (D 6) (R 6) [96,136,272,34,68,1] 13 := by
  apply FastRouting.sound _ _ [96,136,272,34,68,1] 13 (by decide) (choices 1) [1,2,4] r27552 c27552
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8725
  · exact u8726
  · exact u8727

def b27553 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 42, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 97 138 276 42 84 34 69 133 261), lower := (rows 97 138 276 42 84 34 64 128 256), losses := [] }

theorem u27553 : Upper (D 6) (R 6) [96,136,272,34,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27553 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27554 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 203, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 97 138 276 42 84 36 67 131 259), lower := (rows 97 138 276 42 84 36 64 128 256), losses := [] }

theorem u27554 : Upper (D 6) (R 6) [96,136,272,34,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27554 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27555 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 33, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 97 138 276 44 82 33 71 135 263), lower := (rows 97 138 276 44 82 33 64 128 256), losses := [{ target := 1, region := (rows 81 0 4 12 16 117 64 128 256), good := (rows 97 136 317 44 113 33 97 128 256) }] }

theorem u27555 : Upper (D 6) (R 6) [96,136,272,36,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27555 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27556 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 65, targets := 2 },{ cop := 4, region := 33, targets := 4 }], pairs := [(0,1),(0,2),(3,0)], upper := (rows 97 138 276 44 82 34 69 133 261), lower := (rows 97 138 276 44 82 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 16 50 64 128 256), good := (rows 96 170 316 44 114 34 64 128 256) }] }

theorem u27556 : Upper (D 6) (R 6) [96,136,272,36,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27556 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27557 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 97 138 276 44 82 36 67 131 259), lower := (rows 97 138 276 44 82 36 64 128 256), losses := [] }

theorem u27557 : Upper (D 6) (R 6) [96,136,272,36,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27557 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27558 : PairBound 9 := { available := 84, camps := [{ cop := 5, region := 341, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 97 138 292 11 21 34 84 212 340), lower := (rows 97 138 292 11 21 34 64 128 256), losses := [] }

theorem u27558 : Upper (D 6) (R 6) [96,136,288,3,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27558 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27559 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 202, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 97 138 292 11 21 36 82 210 338), lower := (rows 97 138 292 11 21 36 64 128 256), losses := [] }

theorem u27559 : Upper (D 6) (R 6) [96,136,288,3,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27559 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27560 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 202, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 97 138 292 11 21 48 70 198 326), lower := (rows 97 138 292 11 21 48 64 128 256), losses := [] }

theorem u27560 : Upper (D 6) (R 6) [96,136,288,3,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27560 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27561 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 138 292 11 21 96 86 150 278), lower := (rows 97 138 292 11 21 96 64 128 256), losses := [] }

theorem u27561 : Upper (D 6) (R 6) [96,136,288,3,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27561 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27562 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 357, targets := 2 },{ cop := 6, region := 33, targets := 4 }], pairs := [(0,1),(0,2),(2,1)], upper := (rows 97 138 292 11 22 33 84 212 340), lower := (rows 97 138 292 11 22 33 64 128 256), losses := [] }

theorem u27562 : Upper (D 6) (R 6) [96,136,288,3,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27562 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27563 : PairBound 9 := { available := 81, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 97 138 292 11 22 36 81 209 337), lower := (rows 97 138 292 11 22 36 64 128 256), losses := [] }

theorem u27563 : Upper (D 6) (R 6) [96,136,288,3,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27563 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27564 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 357, targets := 2 }], pairs := [(0,1),(2,1)], upper := (rows 97 138 292 11 22 48 69 197 325), lower := (rows 97 138 292 11 22 48 64 128 256), losses := [] }

theorem u27564 : Upper (D 6) (R 6) [96,136,288,3,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27564 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27565 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 138 292 11 22 96 85 149 277), lower := (rows 97 138 292 11 22 96 64 128 256), losses := [] }

theorem u27565 : Upper (D 6) (R 6) [96,136,288,3,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27565 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27566 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 293, targets := 2 },{ cop := 4, region := 33, targets := 4 }], pairs := [(0,1),(0,2),(2,1)], upper := (rows 97 138 292 11 82 33 84 148 276), lower := (rows 97 138 292 11 82 33 64 128 256), losses := [] }

theorem u27566 : Upper (D 6) (R 6) [96,136,288,3,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27566 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27567 : PairBound 9 := { available := 21, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 97 138 292 11 82 36 85 149 277), lower := (rows 97 138 292 11 82 36 64 128 256), losses := [] }

theorem u27567 : Upper (D 6) (R 6) [96,136,288,3,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27567 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27568 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 138 292 11 82 48 69 133 261), lower := (rows 97 138 292 11 82 48 64 128 256), losses := [] }

theorem u27568 : Upper (D 6) (R 6) [96,136,288,3,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27568 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27569 : Route 9 := (fun mask => (mask,id))

def c27569 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27569 : Upper (D 6) (R 6) [96,136,288,3,68,1] 13 := by
  apply FastRouting.sound _ _ [96,136,288,3,68,1] 13 (by decide) (choices 1) [2,4,16] r27569 c27569
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8728
  · exact u8729
  · exact u8730

def b27570 : PairBound 9 := { available := 21, camps := [{ cop := 5, region := 341, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 97 138 292 11 84 34 85 149 277), lower := (rows 97 138 292 11 84 34 64 128 256), losses := [] }

theorem u27570 : Upper (D 6) (R 6) [96,136,288,3,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27570 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27571 : PairBound 9 := { available := 19, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 97 138 292 11 84 36 83 147 275), lower := (rows 97 138 292 11 84 36 64 128 256), losses := [] }

theorem u27571 : Upper (D 6) (R 6) [96,136,288,3,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27571 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27572 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 138 292 11 84 48 71 135 263), lower := (rows 97 138 292 11 84 48 64 128 256), losses := [] }

theorem u27572 : Upper (D 6) (R 6) [96,136,288,3,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27572 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27573 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 210, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 97 138 292 13 82 33 86 150 278), lower := (rows 97 138 292 13 82 33 64 128 256), losses := [] }

theorem u27573 : Upper (D 6) (R 6) [96,136,288,5,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27573 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27574 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 210, targets := 32 },{ cop := 4, region := 33, targets := 4 }], pairs := [(0,2),(1,5),(4,5)], upper := (rows 97 138 292 13 82 34 85 149 277), lower := (rows 97 138 292 13 82 34 64 128 256), losses := [] }

theorem u27574 : Upper (D 6) (R 6) [96,136,288,5,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27574 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27575 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 210, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 97 138 292 13 82 36 83 147 275), lower := (rows 97 138 292 13 82 36 64 128 256), losses := [] }

theorem u27575 : Upper (D 6) (R 6) [96,136,288,5,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27575 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27576 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 138 292 13 82 48 71 135 263), lower := (rows 97 138 292 13 82 48 64 128 256), losses := [] }

theorem u27576 : Upper (D 6) (R 6) [96,136,288,5,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27576 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27577 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 210, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 97 138 292 13 84 33 82 146 274), lower := (rows 97 138 292 13 84 33 64 128 256), losses := [] }

theorem u27577 : Upper (D 6) (R 6) [96,136,288,5,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27577 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27578 : Route 9 := (fun mask => (mask,id))

def c27578 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27578 : Upper (D 6) (R 6) [96,136,288,5,68,2] 13 := by
  apply FastRouting.sound _ _ [96,136,288,5,68,2] 13 (by decide) (choices 1) [1,2,16] r27578 c27578
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8731
  · exact u8732
  · exact u8733

def b27579 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 138 292 13 84 48 67 131 259), lower := (rows 97 138 292 13 84 48 64 128 256), losses := [] }

theorem u27579 : Upper (D 6) (R 6) [96,136,288,5,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27579 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27580 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 357, targets := 2 },{ cop := 6, region := 33, targets := 4 }], pairs := [(0,1),(0,2),(2,1)], upper := (rows 97 138 292 14 19 33 84 212 340), lower := (rows 97 138 292 14 19 33 64 128 256), losses := [] }

theorem u27580 : Upper (D 6) (R 6) [96,136,288,6,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27580 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27581 : PairBound 9 := { available := 81, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 97 138 292 14 19 36 81 209 337), lower := (rows 97 138 292 14 19 36 64 128 256), losses := [] }

theorem u27581 : Upper (D 6) (R 6) [96,136,288,6,3,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27581 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27582 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 357, targets := 2 }], pairs := [(0,1),(2,1)], upper := (rows 97 138 292 14 19 48 69 197 325), lower := (rows 97 138 292 14 19 48 64 128 256), losses := [] }

theorem u27582 : Upper (D 6) (R 6) [96,136,288,6,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27582 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27583 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 138 292 14 19 96 85 149 277), lower := (rows 97 138 292 14 19 96 64 128 256), losses := [] }

theorem u27583 : Upper (D 6) (R 6) [96,136,288,6,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27583 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27584 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 202, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 97 138 292 14 21 33 82 210 338), lower := (rows 97 138 292 14 21 33 64 128 256), losses := [] }

theorem u27584 : Upper (D 6) (R 6) [96,136,288,6,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27584 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27585 : PairBound 9 := { available := 81, camps := [{ cop := 5, region := 341, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 97 138 292 14 21 34 81 209 337), lower := (rows 97 138 292 14 21 34 64 128 256), losses := [] }

theorem u27585 : Upper (D 6) (R 6) [96,136,288,6,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27585 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27586 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 202, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 97 138 292 14 21 48 67 195 323), lower := (rows 97 138 292 14 21 48 64 128 256), losses := [] }

theorem u27586 : Upper (D 6) (R 6) [96,136,288,6,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27586 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27587 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 138 292 14 21 96 83 147 275), lower := (rows 97 138 292 14 21 96 64 128 256), losses := [] }

theorem u27587 : Upper (D 6) (R 6) [96,136,288,6,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27587 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27588 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 293, targets := 2 },{ cop := 4, region := 33, targets := 4 }], pairs := [(0,1),(0,2),(2,1)], upper := (rows 97 138 292 14 82 33 85 149 277), lower := (rows 97 138 292 14 82 33 64 128 256), losses := [] }

theorem u27588 : Upper (D 6) (R 6) [96,136,288,6,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27588 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27589 : PairBound 9 := { available := 17, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 97 138 292 14 82 36 81 145 273), lower := (rows 97 138 292 14 82 36 64 128 256), losses := [] }

theorem u27589 : Upper (D 6) (R 6) [96,136,288,6,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27589 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27590 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 138 292 14 82 48 69 133 261), lower := (rows 97 138 292 14 82 48 64 128 256), losses := [] }

theorem u27590 : Upper (D 6) (R 6) [96,136,288,6,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27590 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27591 : Route 9 := (fun mask => (mask,id))

def c27591 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27591 : Upper (D 6) (R 6) [96,136,288,6,68,1] 13 := by
  apply FastRouting.sound _ _ [96,136,288,6,68,1] 13 (by decide) (choices 1) [1,2,16] r27591 c27591
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8734
  · exact u8735
  · exact u8736

def b27592 : PairBound 9 := { available := 17, camps := [{ cop := 5, region := 341, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 97 138 292 14 84 34 81 145 273), lower := (rows 97 138 292 14 84 34 64 128 256), losses := [] }

theorem u27592 : Upper (D 6) (R 6) [96,136,288,6,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27592 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27593 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 138 292 14 84 48 67 131 259), lower := (rows 97 138 292 14 84 48 64 128 256), losses := [] }

theorem u27593 : Upper (D 6) (R 6) [96,136,288,6,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27593 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27594 : PairBound 9 := { available := 70, camps := [{ cop := 6, region := 33, targets := 6 }], pairs := [(0,1),(0,2),(1,0)], upper := (rows 97 138 292 25 22 33 70 198 326), lower := (rows 97 138 292 25 22 33 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 32 80 144 272), good := (rows 96 138 292 474 470 32 64 128 256) }] }

theorem u27594 : Upper (D 6) (R 6) [96,136,288,17,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27594 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27595 : PairBound 9 := { available := 69, camps := [{ cop := 5, region := 325, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 97 138 292 25 22 34 69 197 325), lower := (rows 97 138 292 25 22 34 64 128 256), losses := [{ target := 1, region := (rows 37 0 37 24 16 32 125 189 317), good := (rows 485 456 485 477 477 485 64 128 256) }] }

theorem u27595 : Upper (D 6) (R 6) [96,136,288,17,6,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27595 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27596 : PairBound 9 := { available := 67, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 97 138 292 25 22 36 67 195 323), lower := (rows 97 138 292 25 22 36 64 128 256), losses := [] }

theorem u27596 : Upper (D 6) (R 6) [96,136,288,17,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27596 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27597 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 138 292 25 22 96 71 135 263), lower := (rows 97 138 292 25 22 96 64 128 256), losses := [] }

theorem u27597 : Upper (D 6) (R 6) [96,136,288,17,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27597 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27598 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 41, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 97 138 292 25 82 33 70 134 262), lower := (rows 97 138 292 25 82 33 64 128 256), losses := [] }

theorem u27598 : Upper (D 6) (R 6) [96,136,288,17,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27598 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27599 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 422, targets := 64 },{ cop := 4, region := 33, targets := 4 }], pairs := [(0,2),(1,6),(2,6)], upper := (rows 97 138 292 25 82 34 69 133 261), lower := (rows 97 138 292 25 82 34 64 128 256), losses := [] }

theorem u27599 : Upper (D 6) (R 6) [96,136,288,17,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27599 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u27599
end Delivery.IrregularNine14.P06

import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0061
import IrregularNine14P06C0062

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b15600 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 451, targets := 36 }], pairs := [(0,2),(0,5),(1,2)], upper := (rows 11 131 100 56 22 36 321 449 321), lower := (rows 11 131 100 56 22 36 64 128 256), losses := [] }

theorem u15600 : Upper (D 6) (R 6) [10,129,96,48,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15600 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15601 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 131 100 56 22 96 325 389 261), lower := (rows 11 131 100 56 22 96 64 128 256), losses := [] }

theorem u15601 : Upper (D 6) (R 6) [10,129,96,48,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15601 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15602 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 356, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 11 131 100 56 22 288 69 197 325), lower := (rows 11 131 100 56 22 288 64 128 256), losses := [{ target := 1, region := (rows 1 0 23 24 16 307 67 131 259), good := (rows 493 485 100 60 508 288 64 128 288) }] }

theorem u15602 : Upper (D 6) (R 6) [10,129,96,48,6,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15602 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15603 : PairBound 9 := { available := 260, camps := [{ cop := 3, region := 324, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 100 56 81 34 324 388 260), lower := (rows 11 131 100 56 81 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 63 24 16 35 127 191 319), good := (rows 494 486 484 508 508 486 64 128 256) }] }

theorem u15603 : Upper (D 6) (R 6) [10,129,96,48,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15603 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15604 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 100 56 81 36 326 390 262), lower := (rows 11 131 100 56 81 36 64 128 256), losses := [] }

theorem u15604 : Upper (D 6) (R 6) [10,129,96,48,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15604 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15605 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 356, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 11 131 100 56 81 288 70 134 262), lower := (rows 11 131 100 56 81 288 64 128 256), losses := [{ target := 0, region := (rows 0 2 23 24 16 307 67 131 259), good := (rows 494 486 100 60 508 288 64 128 288) }] }

theorem u15605 : Upper (D 6) (R 6) [10,129,96,48,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15605 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15606 : PairBound 9 := { available := 260, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 131 100 56 82 33 324 388 260), lower := (rows 11 131 100 56 82 33 64 128 256), losses := [] }

theorem u15606 : Upper (D 6) (R 6) [10,129,96,48,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15606 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15607 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 100 56 82 36 325 389 261), lower := (rows 11 131 100 56 82 36 64 128 256), losses := [] }

theorem u15607 : Upper (D 6) (R 6) [10,129,96,48,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15607 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15608 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 356, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 11 131 100 56 82 288 69 133 261), lower := (rows 11 131 100 56 82 288 64 128 256), losses := [{ target := 1, region := (rows 1 0 23 24 16 307 67 131 259), good := (rows 493 485 100 60 508 288 64 128 288) }] }

theorem u15608 : Upper (D 6) (R 6) [10,129,96,48,66,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15608 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15609 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 68, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 100 56 273 34 68 196 324), lower := (rows 11 131 100 56 273 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 63 24 16 35 127 191 319), good := (rows 494 486 484 508 508 486 64 128 256) }] }

theorem u15609 : Upper (D 6) (R 6) [10,129,96,48,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15609 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15610 : PairBound 9 := { available := 70, camps := [{ cop := 6, region := 36, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 100 56 273 36 70 198 326), lower := (rows 11 131 100 56 273 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 87 24 16 127 67 131 259), good := (rows 494 486 100 60 508 36 100 128 256) }] }

theorem u15610 : Upper (D 6) (R 6) [10,129,96,48,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15610 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15611 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 131 100 56 273 96 70 134 262), lower := (rows 11 131 100 56 273 96 64 128 256), losses := [] }

theorem u15611 : Upper (D 6) (R 6) [10,129,96,48,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15611 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15612 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 131 100 56 274 33 68 196 324), lower := (rows 11 131 100 56 274 33 64 128 256), losses := [] }

theorem u15612 : Upper (D 6) (R 6) [10,129,96,48,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15612 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15613 : PairBound 9 := { available := 69, camps := [{ cop := 6, region := 36, targets := 3 }], pairs := [(2,0),(2,1),(3,1)], upper := (rows 11 131 100 56 274 36 69 197 325), lower := (rows 11 131 100 56 274 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 87 24 16 127 67 131 259), good := (rows 493 485 100 60 508 36 100 128 256) }] }

theorem u15613 : Upper (D 6) (R 6) [10,129,96,48,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15613 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15614 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 131 100 56 274 96 69 133 261), lower := (rows 11 131 100 56 274 96 64 128 256), losses := [] }

theorem u15614 : Upper (D 6) (R 6) [10,129,96,48,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15614 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15615 : Route 9 := (fun mask => (mask,id))

def c15615 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15615 : Upper (D 6) (R 6) [10,129,96,48,260,1] 13 := by
  apply FastRouting.sound _ _ [10,129,96,48,260,1] 13 (by decide) (choices 1) [2,4] r15615 c15615
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3699
  · exact u3700

def r15616 : Route 9 := (fun mask => (mask,id))

def c15616 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15616 : Upper (D 6) (R 6) [10,129,96,48,260,2] 13 := by
  apply FastRouting.sound _ _ [10,129,96,48,260,2] 13 (by decide) (choices 1) [1,4] r15616 c15616
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3701
  · exact u3702

def b15617 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 195, targets := 36 }], pairs := [(0,2),(0,5),(1,2)], upper := (rows 11 131 100 56 276 36 67 195 323), lower := (rows 11 131 100 56 276 36 64 128 256), losses := [] }

theorem u15617 : Upper (D 6) (R 6) [10,129,96,48,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15617 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15618 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 131 100 56 276 96 71 135 263), lower := (rows 11 131 100 56 276 96 64 128 256), losses := [] }

theorem u15618 : Upper (D 6) (R 6) [10,129,96,48,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15618 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15619 : Route 9 := (fun mask => (mask,id))

def c15619 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15619 : Upper (D 6) (R 6) [10,129,96,48,320,1] 13 := by
  apply FastRouting.sound _ _ [10,129,96,48,320,1] 13 (by decide) (choices 1) [2,4] r15619 c15619
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3703
  · exact u3704

def r15620 : Route 9 := (fun mask => (mask,id))

def c15620 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15620 : Upper (D 6) (R 6) [10,129,96,48,320,2] 13 := by
  apply FastRouting.sound _ _ [10,129,96,48,320,2] 13 (by decide) (choices 1) [1,4] r15620 c15620
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3705
  · exact u3706

def b15621 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 100 56 336 36 71 135 263), lower := (rows 11 131 100 56 336 36 64 128 256), losses := [] }

theorem u15621 : Upper (D 6) (R 6) [10,129,96,48,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15621 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15622 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 226, targets := 4 }], pairs := [(1,2),(2,0),(3,0)], upper := (rows 11 131 100 268 21 34 112 240 368), lower := (rows 11 131 100 268 21 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 35 80 144 272), good := (rows 42 162 100 268 508 34 64 128 256) }] }

theorem u15622 : Upper (D 6) (R 6) [10,129,96,260,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15622 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m15623_2 : Upper (D 6) (R 6) [10,129,96,260,5,16,2] 13 :=
  permutation_upper _ _ _ [10,129,96,260,5,2,16] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3707

def r15623 : Route 9 := (fun mask => (mask,id))

def c15623 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15623 : Upper (D 6) (R 6) [10,129,96,260,5,16] 13 := by
  apply FastRouting.sound _ _ [10,129,96,260,5,16] 13 (by decide) (choices 1) [2,32] r15623 c15623
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m15623_2
  · exact u3708

def b15624 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 131 100 268 21 96 114 178 306), lower := (rows 11 131 100 268 21 96 64 128 256), losses := [] }

theorem u15624 : Upper (D 6) (R 6) [10,129,96,260,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15624 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15625 : Route 9 := (fun mask => (mask,id))

def c15625 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15625 : Upper (D 6) (R 6) [10,129,96,260,6,1] 13 := by
  apply FastRouting.sound _ _ [10,129,96,260,6,1] 13 (by decide) (choices 1) [16,32] r15625 c15625
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3709
  · exact u3710

theorem m15626_1 : Upper (D 6) (R 6) [10,129,96,260,6,16,1] 13 :=
  permutation_upper _ _ _ [10,129,96,260,6,1,16] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3709

def r15626 : Route 9 := (fun mask => (mask,id))

def c15626 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15626 : Upper (D 6) (R 6) [10,129,96,260,6,16] 13 := by
  apply FastRouting.sound _ _ [10,129,96,260,6,16] 13 (by decide) (choices 1) [1,32] r15626 c15626
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m15626_1
  · exact u3711

def b15627 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 131 100 268 22 96 113 177 305), lower := (rows 11 131 100 268 22 96 64 128 256), losses := [] }

theorem u15627 : Upper (D 6) (R 6) [10,129,96,260,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15627 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15628 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 332, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 100 268 49 34 84 212 340), lower := (rows 11 131 100 268 49 34 64 128 256), losses := [] }

theorem u15628 : Upper (D 6) (R 6) [10,129,96,260,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15628 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15629 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 194, targets := 36 },{ cop := 6, region := 36, targets := 1 }], pairs := [(1,2),(1,5),(2,0)], upper := (rows 11 131 100 268 49 36 82 210 338), lower := (rows 11 131 100 268 49 36 64 128 256), losses := [] }

theorem u15629 : Upper (D 6) (R 6) [10,129,96,260,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15629 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15630 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 48, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 131 100 268 49 48 70 198 326), lower := (rows 11 131 100 268 49 48 64 128 256), losses := [] }

theorem u15630 : Upper (D 6) (R 6) [10,129,96,260,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15630 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15631 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 131 100 268 49 96 86 150 278), lower := (rows 11 131 100 268 49 96 64 128 256), losses := [] }

theorem u15631 : Upper (D 6) (R 6) [10,129,96,260,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15631 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15632 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 332, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 100 268 50 33 84 212 340), lower := (rows 11 131 100 268 50 33 64 128 256), losses := [] }

theorem u15632 : Upper (D 6) (R 6) [10,129,96,260,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15632 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15633 : PairBound 9 := { available := 81, camps := [{ cop := 6, region := 36, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 100 268 50 36 81 209 337), lower := (rows 11 131 100 268 50 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 68 8 17 108 64 128 256), good := (rows 58 146 100 300 50 36 100 128 256) }] }

theorem u15633 : Upper (D 6) (R 6) [10,129,96,260,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15633 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15634 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 48, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 11 131 100 268 50 48 69 197 325), lower := (rows 11 131 100 268 50 48 64 128 256), losses := [] }

theorem u15634 : Upper (D 6) (R 6) [10,129,96,260,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15634 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15635 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 131 100 268 50 96 85 149 277), lower := (rows 11 131 100 268 50 96 64 128 256), losses := [] }

theorem u15635 : Upper (D 6) (R 6) [10,129,96,260,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15635 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15636 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 68, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 100 280 21 34 100 228 356), lower := (rows 11 131 100 280 21 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 55 24 16 35 119 183 311), good := (rows 494 486 484 476 508 486 64 128 256) }] }

theorem u15636 : Upper (D 6) (R 6) [10,129,96,272,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15636 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15637 : PairBound 9 := { available := 98, camps := [{ cop := 6, region := 36, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 100 280 21 36 98 226 354), lower := (rows 11 131 100 280 21 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 87 24 16 127 67 131 259), good := (rows 494 486 100 316 508 36 100 128 256) }] }

theorem u15637 : Upper (D 6) (R 6) [10,129,96,272,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15637 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15638 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 131 100 280 21 96 102 166 294), lower := (rows 11 131 100 280 21 96 64 128 256), losses := [] }

theorem u15638 : Upper (D 6) (R 6) [10,129,96,272,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15638 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15639 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 68, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 100 280 22 33 100 228 356), lower := (rows 11 131 100 280 22 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 36 24 16 32 100 164 292), good := (rows 10 130 484 280 478 484 64 128 256) }] }

theorem u15639 : Upper (D 6) (R 6) [10,129,96,272,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15639 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15640 : PairBound 9 := { available := 97, camps := [{ cop := 6, region := 36, targets := 3 }], pairs := [(2,0),(2,1),(3,1)], upper := (rows 11 131 100 280 22 36 97 225 353), lower := (rows 11 131 100 280 22 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 87 24 16 127 67 131 259), good := (rows 493 485 100 316 508 36 100 128 256) }] }

theorem u15640 : Upper (D 6) (R 6) [10,129,96,272,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15640 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15641 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 131 100 280 22 96 101 165 293), lower := (rows 11 131 100 280 22 96 64 128 256), losses := [] }

theorem u15641 : Upper (D 6) (R 6) [10,129,96,272,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15641 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15642 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 332, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 100 280 49 34 68 196 324), lower := (rows 11 131 100 280 49 34 64 128 256), losses := [] }

theorem u15642 : Upper (D 6) (R 6) [10,129,96,272,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15642 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15643 : PairBound 9 := { available := 70, camps := [{ cop := 6, region := 36, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 100 280 49 36 70 198 326), lower := (rows 11 131 100 280 49 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 87 24 16 127 67 131 259), good := (rows 494 486 100 316 508 36 100 128 256) }] }

theorem u15643 : Upper (D 6) (R 6) [10,129,96,272,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15643 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15644 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 131 100 280 49 96 70 134 262), lower := (rows 11 131 100 280 49 96 64 128 256), losses := [] }

theorem u15644 : Upper (D 6) (R 6) [10,129,96,272,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15644 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15645 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 332, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 100 280 50 33 68 196 324), lower := (rows 11 131 100 280 50 33 64 128 256), losses := [] }

theorem u15645 : Upper (D 6) (R 6) [10,129,96,272,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15645 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15646 : PairBound 9 := { available := 69, camps := [{ cop := 6, region := 36, targets := 3 }], pairs := [(2,0),(2,1),(3,1)], upper := (rows 11 131 100 280 50 36 69 197 325), lower := (rows 11 131 100 280 50 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 87 24 16 127 67 131 259), good := (rows 493 485 100 316 508 36 100 128 256) }] }

theorem u15646 : Upper (D 6) (R 6) [10,129,96,272,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15646 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15647 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 131 100 280 50 96 69 133 261), lower := (rows 11 131 100 280 50 96 64 128 256), losses := [] }

theorem u15647 : Upper (D 6) (R 6) [10,129,96,272,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15647 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15648 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 194, targets := 32 }], pairs := [(1,5),(2,0),(3,0)], upper := (rows 11 131 100 296 21 34 84 212 340), lower := (rows 11 131 100 296 21 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 35 80 144 272), good := (rows 42 162 100 296 508 34 64 128 256) }] }

theorem u15648 : Upper (D 6) (R 6) [10,129,96,288,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15648 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15649 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 194, targets := 36 },{ cop := 6, region := 36, targets := 1 }], pairs := [(1,2),(1,5),(2,0)], upper := (rows 11 131 100 296 21 36 82 210 338), lower := (rows 11 131 100 296 21 36 64 128 256), losses := [] }

theorem u15649 : Upper (D 6) (R 6) [10,129,96,288,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15649 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15650 : Route 9 := (fun mask => (mask,id))

def c15650 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15650 : Upper (D 6) (R 6) [10,129,96,288,5,16] 13 := by
  apply FastRouting.sound _ _ [10,129,96,288,5,16] 13 (by decide) (choices 1) [2,4] r15650 c15650
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3712
  · exact u3713

def b15651 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 131 100 296 21 96 86 150 278), lower := (rows 11 131 100 296 21 96 64 128 256), losses := [] }

theorem u15651 : Upper (D 6) (R 6) [10,129,96,288,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15651 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15652 : PairBound 9 := { available := 84, camps := [], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 131 100 296 22 33 84 212 340), lower := (rows 11 131 100 296 22 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 44 44 17 32 113 177 305), good := (rows 478 466 492 492 478 508 64 128 256) }] }

theorem u15652 : Upper (D 6) (R 6) [10,129,96,288,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15652 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15653 : Route 9 := (fun mask => (mask,id))

def c15653 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15653 : Upper (D 6) (R 6) [10,129,96,288,6,4] 13 := by
  apply FastRouting.sound _ _ [10,129,96,288,6,4] 13 (by decide) (choices 1) [1,16] r15653 c15653
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3714
  · exact u3715

def r15654 : Route 9 := (fun mask => (mask,id))

def c15654 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15654 : Upper (D 6) (R 6) [10,129,96,288,6,16] 13 := by
  apply FastRouting.sound _ _ [10,129,96,288,6,16] 13 (by decide) (choices 1) [1,4] r15654 c15654
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3716
  · exact u3717

def b15655 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 131 100 296 22 96 85 149 277), lower := (rows 11 131 100 296 22 96 64 128 256), losses := [] }

theorem u15655 : Upper (D 6) (R 6) [10,129,96,288,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15655 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15656 : PairBound 9 := { available := 20, camps := [], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 100 296 81 34 84 148 276), lower := (rows 11 131 100 296 81 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 35 80 144 272), good := (rows 42 162 100 296 508 34 64 128 256) },{ target := 1, region := (rows 1 0 44 44 19 32 97 161 289), good := (rows 477 465 492 492 465 508 64 128 256) }] }

theorem u15656 : Upper (D 6) (R 6) [10,129,96,288,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15656 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15657 : Route 9 := (fun mask => (mask,id))

def c15657 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15657 : Upper (D 6) (R 6) [10,129,96,288,65,4] 13 := by
  apply FastRouting.sound _ _ [10,129,96,288,65,4] 13 (by decide) (choices 1) [2,4,16] r15657 c15657
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3718
  · exact u3719
  · exact u3720

def b15658 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 131 100 296 81 48 70 134 262), lower := (rows 11 131 100 296 81 48 64 128 256), losses := [] }

theorem u15658 : Upper (D 6) (R 6) [10,129,96,288,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15658 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15659 : PairBound 9 := { available := 20, camps := [], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 131 100 296 82 33 84 148 276), lower := (rows 11 131 100 296 82 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 44 44 19 32 97 161 289), good := (rows 478 466 492 492 82 508 64 128 256) }] }

theorem u15659 : Upper (D 6) (R 6) [10,129,96,288,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15659 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u15659
end Delivery.IrregularNine14.P06

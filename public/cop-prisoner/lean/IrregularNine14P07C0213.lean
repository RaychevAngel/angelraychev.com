import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0024

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r12780 : Route 9 := (fun mask => (mask,id))

def c12780 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12780 : Upper (D 7) (R 7) [6,33,320,96,129,128] 13 := by
  apply FastRouting.sound _ _ [6,33,320,96,129,128] 13 (by decide) (choices 1) [2,8,16] r12780 c12780
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1459
  · exact u1460
  · exact u1461

def b12781 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 7 35 324 104 146 33 216 152 408), lower := (rows 7 35 324 104 146 33 64 128 256), losses := [] }

theorem u12781 : Upper (D 7) (R 7) [6,33,320,96,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12781 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12782 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 35 324 104 146 40 209 145 401), lower := (rows 7 35 324 104 146 40 64 128 256), losses := [] }

theorem u12782 : Upper (D 7) (R 7) [6,33,320,96,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12782 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12783 : Route 9 := (fun mask => (mask,id))

def c12783 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12783 : Upper (D 7) (R 7) [6,33,320,96,130,16] 13 := by
  apply FastRouting.sound _ _ [6,33,320,96,130,16] 13 (by decide) (choices 1) [1,8,128] r12783 c12783
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1462
  · exact u1463
  · exact u1464

def r12784 : Route 9 := (fun mask => (mask,id))

def c12784 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12784 : Upper (D 7) (R 7) [6,33,320,96,130,128] 13 := by
  apply FastRouting.sound _ _ [6,33,320,96,130,128] 13 (by decide) (choices 1) [1,8,16] r12784 c12784
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1465
  · exact u1466
  · exact u1467

def b12785 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 7 35 324 104 152 33 210 146 402), lower := (rows 7 35 324 104 152 33 64 128 256), losses := [] }

theorem u12785 : Upper (D 7) (R 7) [6,33,320,96,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12785 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12786 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 476, targets := 2 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 7 35 324 104 152 34 209 145 401), lower := (rows 7 35 324 104 152 34 64 128 256), losses := [] }

theorem u12786 : Upper (D 7) (R 7) [6,33,320,96,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12786 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12787 : Route 9 := (fun mask => (mask,id))

def c12787 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12787 : Upper (D 7) (R 7) [6,33,320,96,136,16] 13 := by
  apply FastRouting.sound _ _ [6,33,320,96,136,16] 13 (by decide) (choices 1) [1,2,128] r12787 c12787
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1468
  · exact u1469
  · exact u1470

def r12788 : Route 9 := (fun mask => (mask,id))

def c12788 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12788 : Upper (D 7) (R 7) [6,33,320,96,136,128] 13 := by
  apply FastRouting.sound _ _ [6,33,320,96,136,128] 13 (by decide) (choices 1) [1,2,16] r12788 c12788
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1471
  · exact u1472
  · exact u1473

def b12789 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 3, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(4,0)], upper := (rows 7 35 324 137 146 40 112 240 368), lower := (rows 7 35 324 137 146 40 64 128 256), losses := [] }

theorem u12789 : Upper (D 7) (R 7) [6,33,320,129,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12789 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12790 : PairBound 9 := { available := 104, camps := [{ cop := 1, region := 460, targets := 2 },{ cop := 3, region := 50, targets := 64 }], pairs := [(1,6),(2,1),(3,1)], upper := (rows 7 35 324 137 146 48 104 232 360), lower := (rows 7 35 324 137 146 48 64 128 256), losses := [] }

theorem u12790 : Upper (D 7) (R 7) [6,33,320,129,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12790 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12791 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 152, targets := 64 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(3,6),(4,6)], upper := (rows 7 35 324 137 146 96 120 184 312), lower := (rows 7 35 324 137 146 96 64 128 256), losses := [] }

theorem u12791 : Upper (D 7) (R 7) [6,33,320,129,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12791 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12792 : PairBound 9 := { available := 88, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 324 137 176 34 88 216 344), lower := (rows 7 35 324 137 176 34 64 128 256), losses := [] }

theorem u12792 : Upper (D 7) (R 7) [6,33,320,129,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12792 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12793 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 324 137 176 40 82 210 338), lower := (rows 7 35 324 137 176 40 64 128 256), losses := [] }

theorem u12793 : Upper (D 7) (R 7) [6,33,320,129,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12793 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12794 : PairBound 9 := { available := 74, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 35 324 137 176 48 74 202 330), lower := (rows 7 35 324 137 176 48 64 128 256), losses := [] }

theorem u12794 : Upper (D 7) (R 7) [6,33,320,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12794 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12795 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 152, targets := 64 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(3,6),(4,6)], upper := (rows 7 35 324 137 176 96 90 154 282), lower := (rows 7 35 324 137 176 96 64 128 256), losses := [] }

theorem u12795 : Upper (D 7) (R 7) [6,33,320,129,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12795 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12796 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 324 137 208 34 120 184 312), lower := (rows 7 35 324 137 208 34 64 128 256), losses := [] }

theorem u12796 : Upper (D 7) (R 7) [6,33,320,129,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12796 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12797 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 3, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(4,0)], upper := (rows 7 35 324 137 208 40 114 178 306), lower := (rows 7 35 324 137 208 40 64 128 256), losses := [] }

theorem u12797 : Upper (D 7) (R 7) [6,33,320,129,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12797 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12798 : Route 9 := (fun mask => (mask,id))

def c12798 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12798 : Upper (D 7) (R 7) [6,33,320,129,192,16] 13 := by
  apply FastRouting.sound _ _ [6,33,320,129,192,16] 13 (by decide) (choices 1) [2,8,32] r12798 c12798
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1474
  · exact u1475
  · exact u1476

def b12799 : PairBound 9 := { available := 88, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 324 138 176 33 88 216 344), lower := (rows 7 35 324 138 176 33 64 128 256), losses := [] }

theorem u12799 : Upper (D 7) (R 7) [6,33,320,130,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12799 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12800 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 7 35 324 138 176 40 81 209 337), lower := (rows 7 35 324 138 176 40 64 128 256), losses := [] }

theorem u12800 : Upper (D 7) (R 7) [6,33,320,130,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12800 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12801 : PairBound 9 := { available := 73, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 35 324 138 176 48 73 201 329), lower := (rows 7 35 324 138 176 48 64 128 256), losses := [] }

theorem u12801 : Upper (D 7) (R 7) [6,33,320,130,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12801 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12802 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 152, targets := 64 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(3,6),(4,6)], upper := (rows 7 35 324 138 176 96 89 153 281), lower := (rows 7 35 324 138 176 96 64 128 256), losses := [] }

theorem u12802 : Upper (D 7) (R 7) [6,33,320,130,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12802 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12803 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 324 138 208 33 120 184 312), lower := (rows 7 35 324 138 208 33 64 128 256), losses := [] }

theorem u12803 : Upper (D 7) (R 7) [6,33,320,130,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12803 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12804 : Route 9 := (fun mask => (mask,id))

def c12804 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12804 : Upper (D 7) (R 7) [6,33,320,130,192,8] 13 := by
  apply FastRouting.sound _ _ [6,33,320,130,192,8] 13 (by decide) (choices 1) [1,16,32] r12804 c12804
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1477
  · exact u1478
  · exact u1479

def r12805 : Route 9 := (fun mask => (mask,id))

def c12805 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12805 : Upper (D 7) (R 7) [6,33,320,130,192,16] 13 := by
  apply FastRouting.sound _ _ [6,33,320,130,192,16] 13 (by decide) (choices 1) [1,8,32] r12805 c12805
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1480
  · exact u1481
  · exact u1482

def b12806 : PairBound 9 := { available := 26, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 324 168 208 33 90 154 282), lower := (rows 7 35 324 168 208 33 64 128 256), losses := [] }

theorem u12806 : Upper (D 7) (R 7) [6,33,320,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12806 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12807 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 324 168 208 34 89 153 281), lower := (rows 7 35 324 168 208 34 64 128 256), losses := [] }

theorem u12807 : Upper (D 7) (R 7) [6,33,320,160,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12807 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12808 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 35 324 168 208 40 83 147 275), lower := (rows 7 35 324 168 208 40 64 128 256), losses := [] }

theorem u12808 : Upper (D 7) (R 7) [6,33,320,160,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12808 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12809 : PairBound 9 := { available := 11, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 324 168 208 48 75 139 267), lower := (rows 7 35 324 168 208 48 64 128 256), losses := [] }

theorem u12809 : Upper (D 7) (R 7) [6,33,320,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12809 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12810 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 456, targets := 34 },{ cop := 3, region := 434, targets := 1 }], pairs := [(1,0),(3,1),(3,5),(4,0)], upper := (rows 7 42 21 73 176 34 448 448 448), lower := (rows 7 42 21 73 176 34 64 128 256), losses := [] }

theorem u12810 : Upper (D 7) (R 7) [6,40,17,65,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12810 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12811 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 405, targets := 64 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,6)], upper := (rows 7 42 21 73 176 96 450 386 386), lower := (rows 7 42 21 73 176 96 64 128 256), losses := [] }

theorem u12811 : Upper (D 7) (R 7) [6,40,17,65,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12811 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12812 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 42 21 73 176 160 322 450 322), lower := (rows 7 42 21 73 176 160 64 128 256), losses := [] }

theorem u12812 : Upper (D 7) (R 7) [6,40,17,65,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12812 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12813 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 434, targets := 1 },{ cop := 0, region := 200, targets := 32 }], pairs := [(1,0),(3,5),(4,0)], upper := (rows 7 42 21 73 176 288 194 194 450), lower := (rows 7 42 21 73 176 288 64 128 256), losses := [] }

theorem u12813 : Upper (D 7) (R 7) [6,40,17,65,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12813 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12814 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 42 21 73 208 34 480 416 416), lower := (rows 7 42 21 73 208 34 64 128 256), losses := [] }

theorem u12814 : Upper (D 7) (R 7) [6,40,17,65,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12814 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12815 : PairBound 9 := { available := 290, camps := [{ cop := 3, region := 434, targets := 1 },{ cop := 3, region := 418, targets := 64 }], pairs := [(1,0),(1,6),(3,7),(4,0)], upper := (rows 7 42 21 73 208 160 354 418 290), lower := (rows 7 42 21 73 208 160 64 128 256), losses := [{ target := 7, region := (rows 1 2 4 9 16 32 66 0 258), good := (rows 335 362 29 73 80 32 64 0 256) }] }

theorem u12815 : Upper (D 7) (R 7) [6,40,17,65,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12815 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12816 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 434, targets := 1 },{ cop := 3, region := 418, targets := 64 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 7 42 21 73 208 288 226 162 418), lower := (rows 7 42 21 73 208 288 64 128 256), losses := [] }

theorem u12816 : Upper (D 7) (R 7) [6,40,17,65,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12816 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12817 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 200, targets := 34 },{ cop := 3, region := 434, targets := 1 }], pairs := [(1,0),(3,1),(3,5),(4,0)], upper := (rows 7 42 21 73 304 34 192 192 448), lower := (rows 7 42 21 73 304 34 64 128 256), losses := [] }

theorem u12817 : Upper (D 7) (R 7) [6,40,17,65,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12817 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12818 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 405, targets := 64 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,6)], upper := (rows 7 42 21 73 304 96 194 130 386), lower := (rows 7 42 21 73 304 96 64 128 256), losses := [] }

theorem u12818 : Upper (D 7) (R 7) [6,40,17,65,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12818 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12819 : Route 9 := (fun mask => (mask,id))

def c12819 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12819 : Upper (D 7) (R 7) [6,40,17,65,288,128] 13 := by
  apply FastRouting.sound _ _ [6,40,17,65,288,128] 13 (by decide) (choices 1) [2,128] r12819 c12819
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1483
  · exact u1484

def b12820 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 42 21 73 336 34 224 160 416), lower := (rows 7 42 21 73 336 34 64 128 256), losses := [] }

theorem u12820 : Upper (D 7) (R 7) [6,40,17,65,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12820 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12821 : Route 9 := (fun mask => (mask,id))

def c12821 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u12821 : Upper (D 7) (R 7) [6,40,17,65,320,128] 13 := by
  apply FastRouting.sound _ _ [6,40,17,65,320,128] 13 (by decide) (choices 1) [2,32,128] r12821 c12821
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1485
  · exact u1486
  · exact u1487

def b12822 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 434, targets := 1 },{ cop := 3, region := 34, targets := 192 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 7 42 21 73 400 34 224 224 480), lower := (rows 7 42 21 73 400 34 64 128 256), losses := [] }

theorem u12822 : Upper (D 7) (R 7) [6,40,17,65,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12822 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12823 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 405, targets := 64 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,6)], upper := (rows 7 42 21 73 400 96 226 162 418), lower := (rows 7 42 21 73 400 96 64 128 256), losses := [] }

theorem u12823 : Upper (D 7) (R 7) [6,40,17,65,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12823 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12824 : Route 9 := (fun mask => (mask,id))

def c12824 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12824 : Upper (D 7) (R 7) [6,40,17,65,384,128] 13 := by
  apply FastRouting.sound _ _ [6,40,17,65,384,128] 13 (by decide) (choices 1) [2,32] r12824 c12824
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1488
  · exact u1489

def b12825 : PairBound 9 := { available := 448, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 0, region := 500, targets := 2 }], pairs := [(1,0),(2,1),(3,0),(4,0)], upper := (rows 7 42 21 74 176 33 448 448 448), lower := (rows 7 42 21 74 176 33 64 128 256), losses := [] }

theorem u12825 : Upper (D 7) (R 7) [6,40,17,66,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12825 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12826 : PairBound 9 := { available := 385, camps := [{ cop := 5, region := 10, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 7 42 21 74 176 96 449 385 385), lower := (rows 7 42 21 74 176 96 64 128 256), losses := [] }

theorem u12826 : Upper (D 7) (R 7) [6,40,17,66,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12826 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12827 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 42 21 74 176 160 321 449 321), lower := (rows 7 42 21 74 176 160 64 128 256), losses := [] }

theorem u12827 : Upper (D 7) (R 7) [6,40,17,66,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12827 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12828 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 200, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 7 42 21 74 176 288 193 193 449), lower := (rows 7 42 21 74 176 288 64 128 256), losses := [] }

theorem u12828 : Upper (D 7) (R 7) [6,40,17,66,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12828 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12829 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 42 21 74 208 33 480 416 416), lower := (rows 7 42 21 74 208 33 64 128 256), losses := [] }

theorem u12829 : Upper (D 7) (R 7) [6,40,17,66,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12829 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12830 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 4, region := 42, targets := 1 }], pairs := [(1,0),(2,1),(3,0),(4,1)], upper := (rows 7 42 21 74 208 160 353 417 289), lower := (rows 7 42 21 74 208 160 64 128 256), losses := [] }

theorem u12830 : Upper (D 7) (R 7) [6,40,17,66,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12830 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12831 : Route 9 := (fun mask => (mask,id))

def c12831 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u12831 : Upper (D 7) (R 7) [6,40,17,66,192,256] 13 := by
  apply FastRouting.sound _ _ [6,40,17,66,192,256] 13 (by decide) (choices 1) [1,32,128] r12831 c12831
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1490
  · exact u1491
  · exact u1492

def b12832 : PairBound 9 := { available := 192, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 0, region := 500, targets := 2 }], pairs := [(1,0),(2,1),(3,0),(4,0)], upper := (rows 7 42 21 74 304 33 192 192 448), lower := (rows 7 42 21 74 304 33 64 128 256), losses := [] }

theorem u12832 : Upper (D 7) (R 7) [6,40,17,66,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12832 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12833 : PairBound 9 := { available := 129, camps := [{ cop := 5, region := 10, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 7 42 21 74 304 96 193 129 385), lower := (rows 7 42 21 74 304 96 64 128 256), losses := [] }

theorem u12833 : Upper (D 7) (R 7) [6,40,17,66,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12833 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12834 : Route 9 := (fun mask => (mask,id))

def c12834 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12834 : Upper (D 7) (R 7) [6,40,17,66,288,128] 13 := by
  apply FastRouting.sound _ _ [6,40,17,66,288,128] 13 (by decide) (choices 1) [1,128] r12834 c12834
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1493
  · exact u1494

def b12835 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 42 21 74 336 33 224 160 416), lower := (rows 7 42 21 74 336 33 64 128 256), losses := [] }

theorem u12835 : Upper (D 7) (R 7) [6,40,17,66,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12835 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12836 : Route 9 := (fun mask => (mask,id))

def c12836 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u12836 : Upper (D 7) (R 7) [6,40,17,66,320,128] 13 := by
  apply FastRouting.sound _ _ [6,40,17,66,320,128] 13 (by decide) (choices 1) [1,32,128] r12836 c12836
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1495
  · exact u1496
  · exact u1497

def b12837 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 0, region := 500, targets := 2 }], pairs := [(1,0),(2,1),(3,0),(4,0)], upper := (rows 7 42 21 74 400 33 224 224 480), lower := (rows 7 42 21 74 400 33 64 128 256), losses := [] }

theorem u12837 : Upper (D 7) (R 7) [6,40,17,66,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12837 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12838 : PairBound 9 := { available := 161, camps := [{ cop := 5, region := 10, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 7 42 21 74 400 96 225 161 417), lower := (rows 7 42 21 74 400 96 64 128 256), losses := [] }

theorem u12838 : Upper (D 7) (R 7) [6,40,17,66,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12838 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12839 : Route 9 := (fun mask => (mask,id))

def c12839 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12839 : Upper (D 7) (R 7) [6,40,17,66,384,128] 13 := by
  apply FastRouting.sound _ _ [6,40,17,66,384,128] 13 (by decide) (choices 1) [1,32] r12839 c12839
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1498
  · exact u1499

#print axioms u12839
end Delivery.IrregularNine14.P07

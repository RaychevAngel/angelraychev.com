import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0023
import IrregularNine14P07C0024

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r12720 : Route 9 := (fun mask => (mask,id))

def c12720 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u12720 : Upper (D 7) (R 7) [6,33,320,18,192,8] 13 := by
  apply FastRouting.sound _ _ [6,33,320,18,192,8] 13 (by decide) (choices 1) [1,32,128] r12720 c12720
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1426
  · exact u1427
  · exact u1428

def r12721 : Route 9 := (fun mask => (mask,id))

def c12721 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12721 : Upper (D 7) (R 7) [6,33,320,18,192,128] 13 := by
  apply FastRouting.sound _ _ [6,33,320,18,192,128] 13 (by decide) (choices 1) [1,8,32] r12721 c12721
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1429
  · exact u1430
  · exact u1431

def b12722 : PairBound 9 := { available := 136, camps := [{ cop := 2, region := 59, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 35 324 56 81 34 200 136 392), lower := (rows 7 35 324 56 81 34 64 128 256), losses := [] }

theorem u12722 : Upper (D 7) (R 7) [6,33,320,48,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12722 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12723 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 59, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 35 324 56 81 40 194 130 386), lower := (rows 7 35 324 56 81 40 64 128 256), losses := [] }

theorem u12723 : Upper (D 7) (R 7) [6,33,320,48,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12723 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12724 : Route 9 := (fun mask => (mask,id))

def c12724 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12724 : Upper (D 7) (R 7) [6,33,320,48,65,128] 13 := by
  apply FastRouting.sound _ _ [6,33,320,48,65,128] 13 (by decide) (choices 1) [2,8,128] r12724 c12724
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1432
  · exact u1433
  · exact u1434

def b12725 : PairBound 9 := { available := 136, camps := [{ cop := 2, region := 59, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 35 324 56 82 33 200 136 392), lower := (rows 7 35 324 56 82 33 64 128 256), losses := [] }

theorem u12725 : Upper (D 7) (R 7) [6,33,320,48,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12725 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12726 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 59, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 35 324 56 82 40 193 129 385), lower := (rows 7 35 324 56 82 40 64 128 256), losses := [] }

theorem u12726 : Upper (D 7) (R 7) [6,33,320,48,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12726 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12727 : Route 9 := (fun mask => (mask,id))

def c12727 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12727 : Upper (D 7) (R 7) [6,33,320,48,66,128] 13 := by
  apply FastRouting.sound _ _ [6,33,320,48,66,128] 13 (by decide) (choices 1) [1,8,128] r12727 c12727
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1435
  · exact u1436
  · exact u1437

def b12728 : PairBound 9 := { available := 200, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 324 56 145 34 200 200 456), lower := (rows 7 35 324 56 145 34 64 128 256), losses := [] }

theorem u12728 : Upper (D 7) (R 7) [6,33,320,48,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12728 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12729 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 42, targets := 192 }], pairs := [(1,6),(1,7),(3,6)], upper := (rows 7 35 324 56 145 40 194 194 450), lower := (rows 7 35 324 56 145 40 64 128 256), losses := [] }

theorem u12729 : Upper (D 7) (R 7) [6,33,320,48,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12729 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12730 : PairBound 9 := { available := 138, camps := [{ cop := 1, region := 152, targets := 64 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(3,6),(4,6)], upper := (rows 7 35 324 56 145 96 202 138 394), lower := (rows 7 35 324 56 145 96 64 128 256), losses := [] }

theorem u12730 : Upper (D 7) (R 7) [6,33,320,48,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12730 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12731 : PairBound 9 := { available := 74, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 35 324 56 145 160 74 202 330), lower := (rows 7 35 324 56 145 160 64 128 256), losses := [] }

theorem u12731 : Upper (D 7) (R 7) [6,33,320,48,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12731 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12732 : PairBound 9 := { available := 200, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 324 56 146 33 200 200 456), lower := (rows 7 35 324 56 146 33 64 128 256), losses := [] }

theorem u12732 : Upper (D 7) (R 7) [6,33,320,48,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12732 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12733 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 7 35 324 56 146 40 193 193 449), lower := (rows 7 35 324 56 146 40 64 128 256), losses := [] }

theorem u12733 : Upper (D 7) (R 7) [6,33,320,48,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12733 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12734 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 152, targets := 64 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(3,6),(4,6)], upper := (rows 7 35 324 56 146 96 201 137 393), lower := (rows 7 35 324 56 146 96 64 128 256), losses := [] }

theorem u12734 : Upper (D 7) (R 7) [6,33,320,48,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12734 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12735 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 35 324 56 146 160 73 201 329), lower := (rows 7 35 324 56 146 160 64 128 256), losses := [] }

theorem u12735 : Upper (D 7) (R 7) [6,33,320,48,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12735 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12736 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 324 56 152 33 194 194 450), lower := (rows 7 35 324 56 152 33 64 128 256), losses := [] }

theorem u12736 : Upper (D 7) (R 7) [6,33,320,48,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12736 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12737 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 324 56 152 34 193 193 449), lower := (rows 7 35 324 56 152 34 64 128 256), losses := [] }

theorem u12737 : Upper (D 7) (R 7) [6,33,320,48,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12737 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12738 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 453, targets := 32 },{ cop := 1, region := 152, targets := 64 }], pairs := [(0,5),(2,5),(3,6),(4,6)], upper := (rows 7 35 324 56 152 96 195 131 387), lower := (rows 7 35 324 56 152 96 64 128 256), losses := [] }

theorem u12738 : Upper (D 7) (R 7) [6,33,320,48,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12738 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12739 : PairBound 9 := { available := 67, camps := [{ cop := 5, region := 24, targets := 67 }], pairs := [(3,0),(3,1),(3,6),(4,0)], upper := (rows 7 35 324 56 152 160 67 195 323), lower := (rows 7 35 324 56 152 160 64 128 256), losses := [] }

theorem u12739 : Upper (D 7) (R 7) [6,33,320,48,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12739 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12740 : PairBound 9 := { available := 138, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 324 56 208 33 202 138 394), lower := (rows 7 35 324 56 208 33 64 128 256), losses := [] }

theorem u12740 : Upper (D 7) (R 7) [6,33,320,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12740 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12741 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 324 56 208 34 201 137 393), lower := (rows 7 35 324 56 208 34 64 128 256), losses := [] }

theorem u12741 : Upper (D 7) (R 7) [6,33,320,48,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12741 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12742 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 7 35 324 56 208 40 195 131 387), lower := (rows 7 35 324 56 208 40 64 128 256), losses := [] }

theorem u12742 : Upper (D 7) (R 7) [6,33,320,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12742 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12743 : PairBound 9 := { available := 11, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 35 324 56 208 160 75 139 267), lower := (rows 7 35 324 56 208 160 64 128 256), losses := [] }

theorem u12743 : Upper (D 7) (R 7) [6,33,320,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12743 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12744 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 43, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 35 324 73 146 40 240 176 432), lower := (rows 7 35 324 73 146 40 64 128 256), losses := [] }

theorem u12744 : Upper (D 7) (R 7) [6,33,320,65,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12744 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12745 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 460, targets := 2 },{ cop := 3, region := 178, targets := 64 }], pairs := [(1,6),(2,1),(3,1)], upper := (rows 7 35 324 73 146 48 232 168 424), lower := (rows 7 35 324 73 146 48 64 128 256), losses := [] }

theorem u12745 : Upper (D 7) (R 7) [6,33,320,65,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12745 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12746 : Route 9 := (fun mask => (mask,id))

def c12746 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12746 : Upper (D 7) (R 7) [6,33,320,65,130,128] 13 := by
  apply FastRouting.sound _ _ [6,33,320,65,130,128] 13 (by decide) (choices 1) [8,16,32] r12746 c12746
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1438
  · exact u1439
  · exact u1440

def b12747 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 476, targets := 2 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 7 35 324 73 152 34 240 176 432), lower := (rows 7 35 324 73 152 34 64 128 256), losses := [] }

theorem u12747 : Upper (D 7) (R 7) [6,33,320,65,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12747 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12748 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 178, targets := 64 },{ cop := 1, region := 452, targets := 1 }], pairs := [(1,6),(2,0),(4,6)], upper := (rows 7 35 324 73 152 48 226 162 418), lower := (rows 7 35 324 73 152 48 64 128 256), losses := [] }

theorem u12748 : Upper (D 7) (R 7) [6,33,320,65,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12748 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12749 : Route 9 := (fun mask => (mask,id))

def c12749 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12749 : Upper (D 7) (R 7) [6,33,320,65,136,128] 13 := by
  apply FastRouting.sound _ _ [6,33,320,65,136,128] 13 (by decide) (choices 1) [2,16,32] r12749 c12749
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1441
  · exact u1442
  · exact u1443

def b12750 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 476, targets := 2 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 7 35 324 73 176 34 216 152 408), lower := (rows 7 35 324 73 176 34 64 128 256), losses := [] }

theorem u12750 : Upper (D 7) (R 7) [6,33,320,65,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12750 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12751 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 43, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 35 324 73 176 40 210 146 402), lower := (rows 7 35 324 73 176 40 64 128 256), losses := [] }

theorem u12751 : Upper (D 7) (R 7) [6,33,320,65,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12751 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12752 : PairBound 9 := { available := 138, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 35 324 73 176 48 202 138 394), lower := (rows 7 35 324 73 176 48 64 128 256), losses := [] }

theorem u12752 : Upper (D 7) (R 7) [6,33,320,65,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12752 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12753 : PairBound 9 := { available := 26, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 35 324 73 176 160 90 154 282), lower := (rows 7 35 324 73 176 160 64 128 256), losses := [] }

theorem u12753 : Upper (D 7) (R 7) [6,33,320,65,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12753 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12754 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 43, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 35 324 74 145 40 240 176 432), lower := (rows 7 35 324 74 145 40 64 128 256), losses := [] }

theorem u12754 : Upper (D 7) (R 7) [6,33,320,66,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12754 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12755 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 460, targets := 1 },{ cop := 4, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0)], upper := (rows 7 35 324 74 145 48 232 168 424), lower := (rows 7 35 324 74 145 48 64 128 256), losses := [] }

theorem u12755 : Upper (D 7) (R 7) [6,33,320,66,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12755 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12756 : Route 9 := (fun mask => (mask,id))

def c12756 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12756 : Upper (D 7) (R 7) [6,33,320,66,129,128] 13 := by
  apply FastRouting.sound _ _ [6,33,320,66,129,128] 13 (by decide) (choices 1) [8,16,32] r12756 c12756
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1444
  · exact u1445
  · exact u1446

def b12757 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 7 35 324 74 152 33 240 176 432), lower := (rows 7 35 324 74 152 33 64 128 256), losses := [] }

theorem u12757 : Upper (D 7) (R 7) [6,33,320,66,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12757 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12758 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 452, targets := 2 }], pairs := [(2,1),(4,1),(4,6)], upper := (rows 7 35 324 74 152 48 225 161 417), lower := (rows 7 35 324 74 152 48 64 128 256), losses := [{ target := 1, region := (rows 1 0 15 8 24 56 66 130 258), good := (rows 453 485 324 508 188 48 64 128 256) },{ target := 6, region := (rows 1 2 4 8 24 56 0 130 258), good := (rows 391 419 260 442 184 48 0 128 256) }] }

theorem u12758 : Upper (D 7) (R 7) [6,33,320,66,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12758 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12759 : Route 9 := (fun mask => (mask,id))

def c12759 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12759 : Upper (D 7) (R 7) [6,33,320,66,136,128] 13 := by
  apply FastRouting.sound _ _ [6,33,320,66,136,128] 13 (by decide) (choices 1) [1,16,32] r12759 c12759
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1447
  · exact u1448
  · exact u1449

def b12760 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 7 35 324 74 176 33 216 152 408), lower := (rows 7 35 324 74 176 33 64 128 256), losses := [] }

theorem u12760 : Upper (D 7) (R 7) [6,33,320,66,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12760 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12761 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 43, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 35 324 74 176 40 209 145 401), lower := (rows 7 35 324 74 176 40 64 128 256), losses := [] }

theorem u12761 : Upper (D 7) (R 7) [6,33,320,66,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12761 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12762 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 35 324 74 176 48 201 137 393), lower := (rows 7 35 324 74 176 48 64 128 256), losses := [] }

theorem u12762 : Upper (D 7) (R 7) [6,33,320,66,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12762 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12763 : PairBound 9 := { available := 25, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 35 324 74 176 160 89 153 281), lower := (rows 7 35 324 74 176 160 64 128 256), losses := [] }

theorem u12763 : Upper (D 7) (R 7) [6,33,320,66,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12763 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12764 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 324 88 145 34 232 168 424), lower := (rows 7 35 324 88 145 34 64 128 256), losses := [] }

theorem u12764 : Upper (D 7) (R 7) [6,33,320,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12764 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12765 : Route 9 := (fun mask => (mask,id))

def c12765 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u12765 : Upper (D 7) (R 7) [6,33,320,80,129,8] 13 := by
  apply FastRouting.sound _ _ [6,33,320,80,129,8] 13 (by decide) (choices 1) [2,32,128] r12765 c12765
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1450
  · exact u1451
  · exact u1452

def r12766 : Route 9 := (fun mask => (mask,id))

def c12766 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12766 : Upper (D 7) (R 7) [6,33,320,80,129,128] 13 := by
  apply FastRouting.sound _ _ [6,33,320,80,129,128] 13 (by decide) (choices 1) [2,8,32] r12766 c12766
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1453
  · exact u1454
  · exact u1455

def b12767 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 324 88 146 33 232 168 424), lower := (rows 7 35 324 88 146 33 64 128 256), losses := [] }

theorem u12767 : Upper (D 7) (R 7) [6,33,320,80,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12767 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12768 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 452, targets := 2 },{ cop := 1, region := 144, targets := 64 }], pairs := [(2,1),(3,1),(4,6)], upper := (rows 7 35 324 88 146 40 225 161 417), lower := (rows 7 35 324 88 146 40 64 128 256), losses := [{ target := 1, region := (rows 1 0 23 24 16 56 66 130 258), good := (rows 453 485 324 124 508 40 64 128 256) }] }

theorem u12768 : Upper (D 7) (R 7) [6,33,320,80,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12768 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12769 : Route 9 := (fun mask => (mask,id))

def c12769 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12769 : Upper (D 7) (R 7) [6,33,320,80,130,128] 13 := by
  apply FastRouting.sound _ _ [6,33,320,80,130,128] 13 (by decide) (choices 1) [1,8,32] r12769 c12769
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1456
  · exact u1457
  · exact u1458

def b12770 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(2,0),(3,0),(4,0)], upper := (rows 7 35 324 88 152 33 226 162 418), lower := (rows 7 35 324 88 152 33 64 128 256), losses := [] }

theorem u12770 : Upper (D 7) (R 7) [6,33,320,80,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12770 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12771 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 476, targets := 2 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 7 35 324 88 152 34 225 161 417), lower := (rows 7 35 324 88 152 34 64 128 256), losses := [] }

theorem u12771 : Upper (D 7) (R 7) [6,33,320,80,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12771 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12772 : PairBound 9 := { available := 35, camps := [{ cop := 5, region := 327, targets := 128 },{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,7)], upper := (rows 7 35 324 88 152 160 99 163 291), lower := (rows 7 35 324 88 152 160 64 128 256), losses := [] }

theorem u12772 : Upper (D 7) (R 7) [6,33,320,80,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12772 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12773 : PairBound 9 := { available := 138, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 324 88 176 33 202 138 394), lower := (rows 7 35 324 88 176 33 64 128 256), losses := [] }

theorem u12773 : Upper (D 7) (R 7) [6,33,320,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12773 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12774 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 324 88 176 34 201 137 393), lower := (rows 7 35 324 88 176 34 64 128 256), losses := [] }

theorem u12774 : Upper (D 7) (R 7) [6,33,320,80,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12774 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12775 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 453, targets := 32 },{ cop := 1, region := 144, targets := 64 }], pairs := [(0,5),(2,5),(4,6)], upper := (rows 7 35 324 88 176 40 195 131 387), lower := (rows 7 35 324 88 176 40 64 128 256), losses := [] }

theorem u12775 : Upper (D 7) (R 7) [6,33,320,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12775 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12776 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 35 324 88 176 160 75 139 267), lower := (rows 7 35 324 88 176 160 64 128 256), losses := [] }

theorem u12776 : Upper (D 7) (R 7) [6,33,320,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12776 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12777 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 476, targets := 2 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 7 35 324 104 145 34 216 152 408), lower := (rows 7 35 324 104 145 34 64 128 256), losses := [] }

theorem u12777 : Upper (D 7) (R 7) [6,33,320,96,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12777 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12778 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 35 324 104 145 40 210 146 402), lower := (rows 7 35 324 104 145 40 64 128 256), losses := [] }

theorem u12778 : Upper (D 7) (R 7) [6,33,320,96,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12778 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12779 : PairBound 9 := { available := 138, camps := [{ cop := 1, region := 460, targets := 1 },{ cop := 4, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0)], upper := (rows 7 35 324 104 145 48 202 138 394), lower := (rows 7 35 324 104 145 48 64 128 256), losses := [] }

theorem u12779 : Upper (D 7) (R 7) [6,33,320,96,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12779 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u12779
end Delivery.IrregularNine14.P07

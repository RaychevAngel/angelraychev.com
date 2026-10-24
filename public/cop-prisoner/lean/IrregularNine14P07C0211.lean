import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0023

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b12660 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 268 104 81 34 208 144 400), lower := (rows 7 35 268 104 81 34 64 128 256), losses := [] }

theorem u12660 : Upper (D 7) (R 7) [6,33,264,96,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12660 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12661 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 35 268 104 81 48 194 130 386), lower := (rows 7 35 268 104 81 48 64 128 256), losses := [] }

theorem u12661 : Upper (D 7) (R 7) [6,33,264,96,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12661 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12662 : Route 9 := (fun mask => (mask,id))

def c12662 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12662 : Upper (D 7) (R 7) [6,33,264,96,65,128] 13 := by
  apply FastRouting.sound _ _ [6,33,264,96,65,128] 13 (by decide) (choices 1) [2,16,128] r12662 c12662
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1390
  · exact u1391
  · exact u1392

def b12663 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 268 104 82 33 208 144 400), lower := (rows 7 35 268 104 82 33 64 128 256), losses := [] }

theorem u12663 : Upper (D 7) (R 7) [6,33,264,96,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12663 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12664 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 35 268 104 82 48 193 129 385), lower := (rows 7 35 268 104 82 48 64 128 256), losses := [] }

theorem u12664 : Upper (D 7) (R 7) [6,33,264,96,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12664 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12665 : Route 9 := (fun mask => (mask,id))

def c12665 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12665 : Upper (D 7) (R 7) [6,33,264,96,66,128] 13 := by
  apply FastRouting.sound _ _ [6,33,264,96,66,128] 13 (by decide) (choices 1) [1,16,128] r12665 c12665
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1393
  · exact u1394
  · exact u1395

def b12666 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 268 104 145 34 208 208 464), lower := (rows 7 35 268 104 145 34 64 128 256), losses := [] }

theorem u12666 : Upper (D 7) (R 7) [6,33,264,96,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12666 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12667 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 460, targets := 1 },{ cop := 4, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0)], upper := (rows 7 35 268 104 145 48 194 194 450), lower := (rows 7 35 268 104 145 48 64 128 256), losses := [] }

theorem u12667 : Upper (D 7) (R 7) [6,33,264,96,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12667 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12668 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 7 35 268 104 145 96 210 146 402), lower := (rows 7 35 268 104 145 96 64 128 256), losses := [] }

theorem u12668 : Upper (D 7) (R 7) [6,33,264,96,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12668 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12669 : Route 9 := (fun mask => (mask,id))

def c12669 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12669 : Upper (D 7) (R 7) [6,33,264,96,129,128] 13 := by
  apply FastRouting.sound _ _ [6,33,264,96,129,128] 13 (by decide) (choices 1) [2,16] r12669 c12669
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1396
  · exact u1397

def b12670 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 268 104 146 33 208 208 464), lower := (rows 7 35 268 104 146 33 64 128 256), losses := [] }

theorem u12670 : Upper (D 7) (R 7) [6,33,264,96,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12670 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12671 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 460, targets := 2 },{ cop := 0, region := 208, targets := 32 }], pairs := [(2,1),(3,1),(4,5)], upper := (rows 7 35 268 104 146 48 193 193 449), lower := (rows 7 35 268 104 146 48 64 128 256), losses := [] }

theorem u12671 : Upper (D 7) (R 7) [6,33,264,96,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12671 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12672 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 7 35 268 104 146 96 209 145 401), lower := (rows 7 35 268 104 146 96 64 128 256), losses := [] }

theorem u12672 : Upper (D 7) (R 7) [6,33,264,96,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12672 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12673 : Route 9 := (fun mask => (mask,id))

def c12673 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12673 : Upper (D 7) (R 7) [6,33,264,96,130,128] 13 := by
  apply FastRouting.sound _ _ [6,33,264,96,130,128] 13 (by decide) (choices 1) [1,16] r12673 c12673
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1398
  · exact u1399

def b12674 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 268 104 208 33 210 146 402), lower := (rows 7 35 268 104 208 33 64 128 256), losses := [] }

theorem u12674 : Upper (D 7) (R 7) [6,33,264,96,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12674 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12675 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 268 104 208 34 209 145 401), lower := (rows 7 35 268 104 208 34 64 128 256), losses := [] }

theorem u12675 : Upper (D 7) (R 7) [6,33,264,96,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12675 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12676 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 35 268 104 208 48 195 131 387), lower := (rows 7 35 268 104 208 48 64 128 256), losses := [] }

theorem u12676 : Upper (D 7) (R 7) [6,33,264,96,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12676 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12677 : Route 9 := (fun mask => (mask,id))

def c12677 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12677 : Upper (D 7) (R 7) [6,33,264,96,192,128] 13 := by
  apply FastRouting.sound _ _ [6,33,264,96,192,128] 13 (by decide) (choices 1) [1,2,16] r12677 c12677
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1400
  · exact u1401
  · exact u1402

def b12678 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 268 200 81 34 240 176 432), lower := (rows 7 35 268 200 81 34 64 128 256), losses := [] }

theorem u12678 : Upper (D 7) (R 7) [6,33,264,192,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12678 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12679 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 460, targets := 1 },{ cop := 4, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0)], upper := (rows 7 35 268 200 81 48 226 162 418), lower := (rows 7 35 268 200 81 48 64 128 256), losses := [] }

theorem u12679 : Upper (D 7) (R 7) [6,33,264,192,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12679 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12680 : Route 9 := (fun mask => (mask,id))

def c12680 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12680 : Upper (D 7) (R 7) [6,33,264,192,65,128] 13 := by
  apply FastRouting.sound _ _ [6,33,264,192,65,128] 13 (by decide) (choices 1) [2,16,32] r12680 c12680
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1403
  · exact u1404
  · exact u1405

def b12681 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 268 200 82 33 240 176 432), lower := (rows 7 35 268 200 82 33 64 128 256), losses := [] }

theorem u12681 : Upper (D 7) (R 7) [6,33,264,192,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12681 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12682 : Route 9 := (fun mask => (mask,id))

def c12682 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u12682 : Upper (D 7) (R 7) [6,33,264,192,66,16] 13 := by
  apply FastRouting.sound _ _ [6,33,264,192,66,16] 13 (by decide) (choices 1) [1,32,128] r12682 c12682
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1406
  · exact u1407
  · exact u1408

def r12683 : Route 9 := (fun mask => (mask,id))

def c12683 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12683 : Upper (D 7) (R 7) [6,33,264,192,66,128] 13 := by
  apply FastRouting.sound _ _ [6,33,264,192,66,128] 13 (by decide) (choices 1) [1,16,32] r12683 c12683
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1409
  · exact u1410
  · exact u1411

def b12684 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 268 200 112 33 210 146 402), lower := (rows 7 35 268 200 112 33 64 128 256), losses := [] }

theorem u12684 : Upper (D 7) (R 7) [6,33,264,192,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12684 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12685 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 268 200 112 34 209 145 401), lower := (rows 7 35 268 200 112 34 64 128 256), losses := [] }

theorem u12685 : Upper (D 7) (R 7) [6,33,264,192,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12685 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12686 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 35 268 200 112 48 195 131 387), lower := (rows 7 35 268 200 112 48 64 128 256), losses := [] }

theorem u12686 : Upper (D 7) (R 7) [6,33,264,192,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12686 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12687 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 48, targets := 3 },{ cop := 1, region := 80, targets := 128 }], pairs := [(0,6),(4,0),(4,1),(4,7)], upper := (rows 7 35 268 200 112 160 83 147 275), lower := (rows 7 35 268 200 112 160 64 128 256), losses := [{ target := 6, region := (rows 5 6 4 8 16 168 0 128 256), good := (rows 7 35 303 168 48 160 0 160 256) }] }

theorem u12687 : Upper (D 7) (R 7) [6,33,264,192,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12687 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12688 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 59, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 35 324 25 82 40 224 160 416), lower := (rows 7 35 324 25 82 40 64 128 256), losses := [] }

theorem u12688 : Upper (D 7) (R 7) [6,33,320,17,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12688 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12689 : Route 9 := (fun mask => (mask,id))

def c12689 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u12689 : Upper (D 7) (R 7) [6,33,320,17,66,128] 13 := by
  apply FastRouting.sound _ _ [6,33,320,17,66,128] 13 (by decide) (choices 1) [8,32,128] r12689 c12689
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1412
  · exact u1413
  · exact u1414

def b12690 : PairBound 9 := { available := 136, camps := [{ cop := 2, region := 59, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 35 324 25 112 34 200 136 392), lower := (rows 7 35 324 25 112 34 64 128 256), losses := [] }

theorem u12690 : Upper (D 7) (R 7) [6,33,320,17,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12690 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12691 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 59, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 35 324 25 112 40 194 130 386), lower := (rows 7 35 324 25 112 40 64 128 256), losses := [] }

theorem u12691 : Upper (D 7) (R 7) [6,33,320,17,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12691 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12692 : Route 9 := (fun mask => (mask,id))

def c12692 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12692 : Upper (D 7) (R 7) [6,33,320,17,96,128] 13 := by
  apply FastRouting.sound _ _ [6,33,320,17,96,128] 13 (by decide) (choices 1) [2,8,128] r12692 c12692
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1415
  · exact u1416
  · exact u1417

def b12693 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 3, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(4,0)], upper := (rows 7 35 324 25 146 40 224 224 480), lower := (rows 7 35 324 25 146 40 64 128 256), losses := [] }

theorem u12693 : Upper (D 7) (R 7) [6,33,320,17,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12693 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12694 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 152, targets := 64 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(3,6),(4,6)], upper := (rows 7 35 324 25 146 96 232 168 424), lower := (rows 7 35 324 25 146 96 64 128 256), losses := [] }

theorem u12694 : Upper (D 7) (R 7) [6,33,320,17,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12694 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12695 : Route 9 := (fun mask => (mask,id))

def c12695 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12695 : Upper (D 7) (R 7) [6,33,320,17,130,128] 13 := by
  apply FastRouting.sound _ _ [6,33,320,17,130,128] 13 (by decide) (choices 1) [8,32] r12695 c12695
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1418
  · exact u1419

def b12696 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 324 25 152 34 224 224 480), lower := (rows 7 35 324 25 152 34 64 128 256), losses := [] }

theorem u12696 : Upper (D 7) (R 7) [6,33,320,17,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12696 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12697 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 152, targets := 64 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(3,6),(4,6)], upper := (rows 7 35 324 25 152 96 226 162 418), lower := (rows 7 35 324 25 152 96 64 128 256), losses := [] }

theorem u12697 : Upper (D 7) (R 7) [6,33,320,17,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12697 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12698 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 327, targets := 128 },{ cop := 0, region := 484, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(2,7)], upper := (rows 7 35 324 25 152 160 98 226 354), lower := (rows 7 35 324 25 152 160 64 128 256), losses := [] }

theorem u12698 : Upper (D 7) (R 7) [6,33,320,17,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12698 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12699 : PairBound 9 := { available := 200, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 324 25 176 34 200 200 456), lower := (rows 7 35 324 25 176 34 64 128 256), losses := [] }

theorem u12699 : Upper (D 7) (R 7) [6,33,320,17,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12699 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12700 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(2,0),(4,0)], upper := (rows 7 35 324 25 176 40 194 194 450), lower := (rows 7 35 324 25 176 40 64 128 256), losses := [] }

theorem u12700 : Upper (D 7) (R 7) [6,33,320,17,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12700 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12701 : PairBound 9 := { available := 138, camps := [{ cop := 1, region := 152, targets := 64 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(3,6),(4,6)], upper := (rows 7 35 324 25 176 96 202 138 394), lower := (rows 7 35 324 25 176 96 64 128 256), losses := [] }

theorem u12701 : Upper (D 7) (R 7) [6,33,320,17,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12701 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12702 : PairBound 9 := { available := 74, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 35 324 25 176 160 74 202 330), lower := (rows 7 35 324 25 176 160 64 128 256), losses := [] }

theorem u12702 : Upper (D 7) (R 7) [6,33,320,17,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12702 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12703 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 324 25 208 34 232 168 424), lower := (rows 7 35 324 25 208 34 64 128 256), losses := [] }

theorem u12703 : Upper (D 7) (R 7) [6,33,320,17,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12703 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12704 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 3, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(4,0)], upper := (rows 7 35 324 25 208 40 226 162 418), lower := (rows 7 35 324 25 208 40 64 128 256), losses := [] }

theorem u12704 : Upper (D 7) (R 7) [6,33,320,17,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12704 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12705 : Route 9 := (fun mask => (mask,id))

def c12705 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12705 : Upper (D 7) (R 7) [6,33,320,17,192,128] 13 := by
  apply FastRouting.sound _ _ [6,33,320,17,192,128] 13 (by decide) (choices 1) [2,8,32] r12705 c12705
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1420
  · exact u1421
  · exact u1422

def b12706 : PairBound 9 := { available := 136, camps := [{ cop := 2, region := 59, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 35 324 26 112 33 200 136 392), lower := (rows 7 35 324 26 112 33 64 128 256), losses := [] }

theorem u12706 : Upper (D 7) (R 7) [6,33,320,18,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12706 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12707 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 59, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 35 324 26 112 40 193 129 385), lower := (rows 7 35 324 26 112 40 64 128 256), losses := [] }

theorem u12707 : Upper (D 7) (R 7) [6,33,320,18,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12707 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12708 : Route 9 := (fun mask => (mask,id))

def c12708 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12708 : Upper (D 7) (R 7) [6,33,320,18,96,128] 13 := by
  apply FastRouting.sound _ _ [6,33,320,18,96,128] 13 (by decide) (choices 1) [1,8,128] r12708 c12708
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1423
  · exact u1424
  · exact u1425

def b12709 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 42, targets := 192 }], pairs := [(1,6),(1,7),(3,6)], upper := (rows 7 35 324 26 145 40 224 224 480), lower := (rows 7 35 324 26 145 40 64 128 256), losses := [] }

theorem u12709 : Upper (D 7) (R 7) [6,33,320,18,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12709 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12710 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 152, targets := 64 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(3,6),(4,6)], upper := (rows 7 35 324 26 145 96 232 168 424), lower := (rows 7 35 324 26 145 96 64 128 256), losses := [] }

theorem u12710 : Upper (D 7) (R 7) [6,33,320,18,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12710 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12711 : PairBound 9 := { available := 104, camps := [{ cop := 3, region := 484, targets := 3 },{ cop := 4, region := 42, targets := 64 }], pairs := [(1,6),(2,0),(2,1),(3,6)], upper := (rows 7 35 324 26 145 160 104 232 360), lower := (rows 7 35 324 26 145 160 64 128 256), losses := [] }

theorem u12711 : Upper (D 7) (R 7) [6,33,320,18,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12711 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12712 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 324 26 152 33 224 224 480), lower := (rows 7 35 324 26 152 33 64 128 256), losses := [] }

theorem u12712 : Upper (D 7) (R 7) [6,33,320,18,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12712 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12713 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 152, targets := 64 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(3,6),(4,6)], upper := (rows 7 35 324 26 152 96 225 161 417), lower := (rows 7 35 324 26 152 96 64 128 256), losses := [] }

theorem u12713 : Upper (D 7) (R 7) [6,33,320,18,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12713 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12714 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 327, targets := 128 },{ cop := 0, region := 484, targets := 2 }], pairs := [(0,7),(1,7),(2,1),(2,7)], upper := (rows 7 35 324 26 152 160 97 225 353), lower := (rows 7 35 324 26 152 160 64 128 256), losses := [] }

theorem u12714 : Upper (D 7) (R 7) [6,33,320,18,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12714 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12715 : PairBound 9 := { available := 200, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 324 26 176 33 200 200 456), lower := (rows 7 35 324 26 176 33 64 128 256), losses := [] }

theorem u12715 : Upper (D 7) (R 7) [6,33,320,18,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12715 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12716 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 452, targets := 34 },{ cop := 1, region := 208, targets := 2 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 7 35 324 26 176 40 193 193 449), lower := (rows 7 35 324 26 176 40 64 128 256), losses := [] }

theorem u12716 : Upper (D 7) (R 7) [6,33,320,18,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12716 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12717 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 152, targets := 64 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(3,6),(4,6)], upper := (rows 7 35 324 26 176 96 201 137 393), lower := (rows 7 35 324 26 176 96 64 128 256), losses := [] }

theorem u12717 : Upper (D 7) (R 7) [6,33,320,18,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12717 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12718 : PairBound 9 := { available := 73, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 35 324 26 176 160 73 201 329), lower := (rows 7 35 324 26 176 160 64 128 256), losses := [] }

theorem u12718 : Upper (D 7) (R 7) [6,33,320,18,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12718 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12719 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 324 26 208 33 232 168 424), lower := (rows 7 35 324 26 208 33 64 128 256), losses := [] }

theorem u12719 : Upper (D 7) (R 7) [6,33,320,18,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12719 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u12719
end Delivery.IrregularNine14.P07

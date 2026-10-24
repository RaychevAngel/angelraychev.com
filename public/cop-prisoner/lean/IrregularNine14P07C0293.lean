import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0072
import IrregularNine14P07C0073
import IrregularNine14P07C0074

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b17580 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 2, region := 208, targets := 32 }], pairs := [(1,0),(3,0),(4,5)], upper := (rows 13 290 7 104 145 48 194 194 450), lower := (rows 13 290 7 104 145 48 64 128 256), losses := [] }

theorem u17580 : Upper (D 7) (R 7) [12,288,3,96,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17580 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17581 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 13 290 7 104 145 96 210 146 402), lower := (rows 13 290 7 104 145 96 64 128 256), losses := [] }

theorem u17581 : Upper (D 7) (R 7) [12,288,3,96,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17581 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17582 : Route 9 := (fun mask => (mask,id))

def c17582 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17582 : Upper (D 7) (R 7) [12,288,3,96,129,128] 13 := by
  apply FastRouting.sound _ _ [12,288,3,96,129,128] 13 (by decide) (choices 1) [2,16] r17582 c17582
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4379
  · exact u4380

def b17583 : PairBound 9 := { available := 208, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 1, region := 208, targets := 32 }], pairs := [(1,0),(3,0),(4,0),(4,5)], upper := (rows 13 290 7 104 146 33 208 208 464), lower := (rows 13 290 7 104 146 33 64 128 256), losses := [] }

theorem u17583 : Upper (D 7) (R 7) [12,288,3,96,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17583 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17584 : Route 9 := (fun mask => (mask,id))

def c17584 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17584 : Upper (D 7) (R 7) [12,288,3,96,130,16] 13 := by
  apply FastRouting.sound _ _ [12,288,3,96,130,16] 13 (by decide) (choices 1) [1,128] r17584 c17584
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4381
  · exact u4382

def b17585 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 13 290 7 104 146 96 209 145 401), lower := (rows 13 290 7 104 146 96 64 128 256), losses := [] }

theorem u17585 : Upper (D 7) (R 7) [12,288,3,96,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17585 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17586 : Route 9 := (fun mask => (mask,id))

def c17586 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17586 : Upper (D 7) (R 7) [12,288,3,96,130,128] 13 := by
  apply FastRouting.sound _ _ [12,288,3,96,130,128] 13 (by decide) (choices 1) [1,16] r17586 c17586
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4383
  · exact u4384

def b17587 : PairBound 9 := { available := 146, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 1, region := 208, targets := 32 }], pairs := [(1,0),(3,0),(4,0),(4,5)], upper := (rows 13 290 7 104 208 33 210 146 402), lower := (rows 13 290 7 104 208 33 64 128 256), losses := [] }

theorem u17587 : Upper (D 7) (R 7) [12,288,3,96,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17587 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17588 : PairBound 9 := { available := 145, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 0, region := 208, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(4,1)], upper := (rows 13 290 7 104 208 34 209 145 401), lower := (rows 13 290 7 104 208 34 64 128 256), losses := [] }

theorem u17588 : Upper (D 7) (R 7) [12,288,3,96,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17588 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17589 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 13 290 7 104 208 48 195 131 387), lower := (rows 13 290 7 104 208 48 64 128 256), losses := [] }

theorem u17589 : Upper (D 7) (R 7) [12,288,3,96,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17589 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17590 : Route 9 := (fun mask => (mask,id))

def c17590 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17590 : Upper (D 7) (R 7) [12,288,3,96,192,128] 13 := by
  apply FastRouting.sound _ _ [12,288,3,96,192,128] 13 (by decide) (choices 1) [1,2,16] r17590 c17590
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4385
  · exact u4386
  · exact u4387

def b17591 : PairBound 9 := { available := 208, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 2, region := 48, targets := 64 }], pairs := [(1,0),(1,6),(1,7),(4,6)], upper := (rows 13 290 7 200 49 34 208 208 464), lower := (rows 13 290 7 200 49 34 64 128 256), losses := [] }

theorem u17591 : Upper (D 7) (R 7) [12,288,3,192,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17591 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17592 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 48, targets := 194 }], pairs := [(4,1),(4,6),(4,7)], upper := (rows 13 290 7 200 49 48 194 194 450), lower := (rows 13 290 7 200 49 48 64 128 256), losses := [] }

theorem u17592 : Upper (D 7) (R 7) [12,288,3,192,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17592 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17593 : PairBound 9 := { available := 146, camps := [{ cop := 4, region := 458, targets := 1 },{ cop := 4, region := 390, targets := 64 }], pairs := [(1,0),(1,6),(2,6),(3,0)], upper := (rows 13 290 7 200 49 96 210 146 402), lower := (rows 13 290 7 200 49 96 64 128 256), losses := [] }

theorem u17593 : Upper (D 7) (R 7) [12,288,3,192,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17593 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17594 : Route 9 := (fun mask => (mask,id))

def c17594 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u17594 : Upper (D 7) (R 7) [12,288,3,192,66,1] 13 := by
  apply FastRouting.sound _ _ [12,288,3,192,66,1] 13 (by decide) (choices 1) [16,32,128] r17594 c17594
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4388
  · exact u4389
  · exact u4390

def r17595 : Route 9 := (fun mask => (mask,id))

def c17595 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17595 : Upper (D 7) (R 7) [12,288,3,192,66,16] 13 := by
  apply FastRouting.sound _ _ [12,288,3,192,66,16] 13 (by decide) (choices 1) [1,32,128] r17595 c17595
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4391
  · exact u4392
  · exact u4393

def r17596 : Route 9 := (fun mask => (mask,id))

def c17596 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17596 : Upper (D 7) (R 7) [12,288,3,192,66,128] 13 := by
  apply FastRouting.sound _ _ [12,288,3,192,66,128] 13 (by decide) (choices 1) [1,16,32] r17596 c17596
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4394
  · exact u4395
  · exact u4396

def b17597 : PairBound 9 := { available := 146, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 4, region := 386, targets := 64 }], pairs := [(1,0),(1,6),(3,0),(4,0)], upper := (rows 13 290 7 200 112 33 210 146 402), lower := (rows 13 290 7 200 112 33 64 128 256), losses := [] }

theorem u17597 : Upper (D 7) (R 7) [12,288,3,192,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17597 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17598 : Route 9 := (fun mask => (mask,id))

def c17598 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17598 : Upper (D 7) (R 7) [12,288,3,192,96,2] 13 := by
  apply FastRouting.sound _ _ [12,288,3,192,96,2] 13 (by decide) (choices 1) [1,16,128] r17598 c17598
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4397
  · exact u4398
  · exact u4399

def b17599 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 205, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 13 290 7 200 112 48 195 131 387), lower := (rows 13 290 7 200 112 48 64 128 256), losses := [] }

theorem u17599 : Upper (D 7) (R 7) [12,288,3,192,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17599 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17600 : Route 9 := (fun mask => (mask,id))

def c17600 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17600 : Upper (D 7) (R 7) [12,288,3,192,96,128] 13 := by
  apply FastRouting.sound _ _ [12,288,3,192,96,128] 13 (by decide) (choices 1) [1,2,16] r17600 c17600
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4400
  · exact u4401
  · exact u4402

def b17601 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 45, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 13 290 21 41 82 34 192 192 448), lower := (rows 13 290 21 41 82 34 64 128 256), losses := [] }

theorem u17601 : Upper (D 7) (R 7) [12,288,17,33,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17601 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17602 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 45, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 290 21 41 82 96 194 130 386), lower := (rows 13 290 21 41 82 96 64 128 256), losses := [] }

theorem u17602 : Upper (D 7) (R 7) [12,288,17,33,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17602 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17603 : Route 9 := (fun mask => (mask,id))

def c17603 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17603 : Upper (D 7) (R 7) [12,288,17,33,66,128] 13 := by
  apply FastRouting.sound _ _ [12,288,17,33,66,128] 13 (by decide) (choices 1) [2,128] r17603 c17603
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4403
  · exact u4404

def b17604 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 8, region := 34, targets := 192 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 13 290 21 41 208 34 194 194 450), lower := (rows 13 290 21 41 208 34 64 128 256), losses := [] }

theorem u17604 : Upper (D 7) (R 7) [12,288,17,33,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17604 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17605 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 45, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 290 21 41 208 96 194 130 386), lower := (rows 13 290 21 41 208 96 64 128 256), losses := [] }

theorem u17605 : Upper (D 7) (R 7) [12,288,17,33,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17605 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17606 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 8, region := 34, targets := 192 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 13 290 21 73 146 34 224 224 480), lower := (rows 13 290 21 73 146 34 64 128 256), losses := [] }

theorem u17606 : Upper (D 7) (R 7) [12,288,17,65,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17606 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17607 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 5, region := 402, targets := 64 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 13 290 21 73 146 96 226 162 418), lower := (rows 13 290 21 73 146 96 64 128 256), losses := [] }

theorem u17607 : Upper (D 7) (R 7) [12,288,17,65,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17607 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17608 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 5, region := 322, targets := 128 }], pairs := [(0,7),(1,0),(1,7),(4,0)], upper := (rows 13 290 21 73 146 160 98 226 354), lower := (rows 13 290 21 73 146 160 64 128 256), losses := [{ target := 7, region := (rows 21 34 20 24 16 32 98 0 290), good := (rows 13 354 29 73 351 354 64 0 256) }] }

theorem u17608 : Upper (D 7) (R 7) [12,288,17,65,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17608 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17609 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 8, region := 34, targets := 192 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 13 290 21 73 176 34 194 194 450), lower := (rows 13 290 21 73 176 34 64 128 256), losses := [] }

theorem u17609 : Upper (D 7) (R 7) [12,288,17,65,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17609 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17610 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 5, region := 402, targets := 64 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 13 290 21 73 176 96 194 130 386), lower := (rows 13 290 21 73 176 96 64 128 256), losses := [] }

theorem u17610 : Upper (D 7) (R 7) [12,288,17,65,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17610 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17611 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 290 21 73 176 160 66 194 322), lower := (rows 13 290 21 73 176 160 64 128 256), losses := [] }

theorem u17611 : Upper (D 7) (R 7) [12,288,17,65,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17611 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17612 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 53, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 290 21 74 112 33 194 130 386), lower := (rows 13 290 21 74 112 33 64 128 256), losses := [] }

theorem u17612 : Upper (D 7) (R 7) [12,288,17,66,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17612 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17613 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 53, targets := 128 },{ cop := 8, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 13 290 21 74 112 34 193 129 385), lower := (rows 13 290 21 74 112 34 64 128 256), losses := [] }

theorem u17613 : Upper (D 7) (R 7) [12,288,17,66,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17613 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17614 : Route 9 := (fun mask => (mask,id))

def c17614 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17614 : Upper (D 7) (R 7) [12,288,17,66,96,128] 13 := by
  apply FastRouting.sound _ _ [12,288,17,66,96,128] 13 (by decide) (choices 1) [1,2,128] r17614 c17614
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4405
  · exact u4406
  · exact u4407

def r17615 : Route 9 := (fun mask => (mask,id))

def c17615 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17615 : Upper (D 7) (R 7) [12,288,17,66,130,1] 13 := by
  apply FastRouting.sound _ _ [12,288,17,66,130,1] 13 (by decide) (choices 1) [32,128] r17615 c17615
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4408
  · exact u4409

def r17616 : Route 9 := (fun mask => (mask,id))

def c17616 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17616 : Upper (D 7) (R 7) [12,288,17,66,130,64] 13 := by
  apply FastRouting.sound _ _ [12,288,17,66,130,64] 13 (by decide) (choices 1) [1,32,128] r17616 c17616
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4410
  · exact u4411
  · exact u4412

def r17617 : Route 9 := (fun mask => (mask,id))

def c17617 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17617 : Upper (D 7) (R 7) [12,288,17,66,130,128] 13 := by
  apply FastRouting.sound _ _ [12,288,17,66,130,128] 13 (by decide) (choices 1) [1,32] r17617 c17617
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4413
  · exact u4414

def b17618 : PairBound 9 := { available := 194, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 1, region := 200, targets := 32 }], pairs := [(1,0),(3,0),(3,5),(4,0)], upper := (rows 13 290 21 74 176 33 194 194 450), lower := (rows 13 290 21 74 176 33 64 128 256), losses := [] }

theorem u17618 : Upper (D 7) (R 7) [12,288,17,66,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17618 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17619 : Route 9 := (fun mask => (mask,id))

def c17619 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17619 : Upper (D 7) (R 7) [12,288,17,66,160,2] 13 := by
  apply FastRouting.sound _ _ [12,288,17,66,160,2] 13 (by decide) (choices 1) [1,128] r17619 c17619
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4415
  · exact u4416

def r17620 : Route 9 := (fun mask => (mask,id))

def c17620 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17620 : Upper (D 7) (R 7) [12,288,17,66,160,64] 13 := by
  apply FastRouting.sound _ _ [12,288,17,66,160,64] 13 (by decide) (choices 1) [1,2,128] r17620 c17620
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4417
  · exact u4418
  · exact u4419

def b17621 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 290 21 74 176 160 67 195 323), lower := (rows 13 290 21 74 176 160 64 128 256), losses := [] }

theorem u17621 : Upper (D 7) (R 7) [12,288,17,66,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17621 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17622 : PairBound 9 := { available := 162, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 0, region := 418, targets := 64 }], pairs := [(1,0),(1,6),(3,0),(4,0)], upper := (rows 13 290 21 74 208 33 226 162 418), lower := (rows 13 290 21 74 208 33 64 128 256), losses := [] }

theorem u17622 : Upper (D 7) (R 7) [12,288,17,66,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17622 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17623 : Route 9 := (fun mask => (mask,id))

def c17623 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17623 : Upper (D 7) (R 7) [12,288,17,66,192,2] 13 := by
  apply FastRouting.sound _ _ [12,288,17,66,192,2] 13 (by decide) (choices 1) [1,32,128] r17623 c17623
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4420
  · exact u4421
  · exact u4422

def r17624 : Route 9 := (fun mask => (mask,id))

def c17624 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17624 : Upper (D 7) (R 7) [12,288,17,66,192,128] 13 := by
  apply FastRouting.sound _ _ [12,288,17,66,192,128] 13 (by decide) (choices 1) [1,2,32] r17624 c17624
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4423
  · exact u4424
  · exact u4425

def b17625 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 45, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 290 21 104 82 33 194 130 386), lower := (rows 13 290 21 104 82 33 64 128 256), losses := [] }

theorem u17625 : Upper (D 7) (R 7) [12,288,17,96,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17625 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17626 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 45, targets := 128 },{ cop := 8, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 13 290 21 104 82 34 193 129 385), lower := (rows 13 290 21 104 82 34 64 128 256), losses := [] }

theorem u17626 : Upper (D 7) (R 7) [12,288,17,96,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17626 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17627 : Route 9 := (fun mask => (mask,id))

def c17627 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17627 : Upper (D 7) (R 7) [12,288,17,96,66,128] 13 := by
  apply FastRouting.sound _ _ [12,288,17,96,66,128] 13 (by decide) (choices 1) [1,2,128] r17627 c17627
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4426
  · exact u4427
  · exact u4428

def b17628 : PairBound 9 := { available := 194, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 1, region := 208, targets := 32 }], pairs := [(1,0),(3,0),(4,0),(4,5)], upper := (rows 13 290 21 104 146 33 194 194 450), lower := (rows 13 290 21 104 146 33 64 128 256), losses := [] }

theorem u17628 : Upper (D 7) (R 7) [12,288,17,96,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17628 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17629 : Route 9 := (fun mask => (mask,id))

def c17629 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17629 : Upper (D 7) (R 7) [12,288,17,96,130,2] 13 := by
  apply FastRouting.sound _ _ [12,288,17,96,130,2] 13 (by decide) (choices 1) [1,128] r17629 c17629
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4429
  · exact u4430

def b17630 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 13 290 21 104 146 96 195 131 387), lower := (rows 13 290 21 104 146 96 64 128 256), losses := [] }

theorem u17630 : Upper (D 7) (R 7) [12,288,17,96,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17630 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17631 : Route 9 := (fun mask => (mask,id))

def c17631 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17631 : Upper (D 7) (R 7) [12,288,17,96,130,128] 13 := by
  apply FastRouting.sound _ _ [12,288,17,96,130,128] 13 (by decide) (choices 1) [1,2] r17631 c17631
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4431
  · exact u4432

def b17632 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 45, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 290 21 104 208 33 194 130 386), lower := (rows 13 290 21 104 208 33 64 128 256), losses := [] }

theorem u17632 : Upper (D 7) (R 7) [12,288,17,96,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17632 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17633 : Route 9 := (fun mask => (mask,id))

def c17633 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17633 : Upper (D 7) (R 7) [12,288,17,96,192,2] 13 := by
  apply FastRouting.sound _ _ [12,288,17,96,192,2] 13 (by decide) (choices 1) [1,2,128] r17633 c17633
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4433
  · exact u4434
  · exact u4435

def b17634 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 45, targets := 2 },{ cop := 0, region := 418, targets := 64 }], pairs := [(0,1),(1,6),(2,1),(3,1)], upper := (rows 13 290 21 104 208 160 67 131 259), lower := (rows 13 290 21 104 208 160 64 128 256), losses := [] }

theorem u17634 : Upper (D 7) (R 7) [12,288,17,96,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17634 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17635 : PairBound 9 := { available := 162, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 0, region := 418, targets := 64 }], pairs := [(1,0),(1,6),(3,0),(4,0)], upper := (rows 13 290 21 200 82 33 226 162 418), lower := (rows 13 290 21 200 82 33 64 128 256), losses := [] }

theorem u17635 : Upper (D 7) (R 7) [12,288,17,192,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17635 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17636 : Route 9 := (fun mask => (mask,id))

def c17636 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17636 : Upper (D 7) (R 7) [12,288,17,192,66,2] 13 := by
  apply FastRouting.sound _ _ [12,288,17,192,66,2] 13 (by decide) (choices 1) [1,32,128] r17636 c17636
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4436
  · exact u4437
  · exact u4438

def r17637 : Route 9 := (fun mask => (mask,id))

def c17637 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17637 : Upper (D 7) (R 7) [12,288,17,192,66,128] 13 := by
  apply FastRouting.sound _ _ [12,288,17,192,66,128] 13 (by decide) (choices 1) [1,2,32] r17637 c17637
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4439
  · exact u4440
  · exact u4441

def b17638 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 53, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 290 21 200 112 33 194 130 386), lower := (rows 13 290 21 200 112 33 64 128 256), losses := [] }

theorem u17638 : Upper (D 7) (R 7) [12,288,17,192,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17638 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17639 : Route 9 := (fun mask => (mask,id))

def c17639 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17639 : Upper (D 7) (R 7) [12,288,17,192,96,2] 13 := by
  apply FastRouting.sound _ _ [12,288,17,192,96,2] 13 (by decide) (choices 1) [1,2,128] r17639 c17639
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4442
  · exact u4443
  · exact u4444

#print axioms u17639
end Delivery.IrregularNine14.P07

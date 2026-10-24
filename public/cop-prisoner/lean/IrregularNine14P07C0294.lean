import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0074

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b17640 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 53, targets := 2 },{ cop := 0, region := 418, targets := 64 }], pairs := [(0,1),(1,6),(2,1),(4,1)], upper := (rows 13 290 21 200 112 160 67 131 259), lower := (rows 13 290 21 200 112 160 64 128 256), losses := [] }

theorem u17640 : Upper (D 7) (R 7) [12,288,17,192,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17640 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17641 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 13 290 22 41 81 34 192 192 448), lower := (rows 13 290 22 41 81 34 64 128 256), losses := [] }

theorem u17641 : Upper (D 7) (R 7) [12,288,18,33,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17641 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17642 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 422, targets := 1 },{ cop := 4, region := 40, targets := 130 }], pairs := [(1,0),(2,0),(3,1),(3,7)], upper := (rows 13 290 22 41 81 96 194 130 386), lower := (rows 13 290 22 41 81 96 64 128 256), losses := [] }

theorem u17642 : Upper (D 7) (R 7) [12,288,18,33,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17642 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17643 : Route 9 := (fun mask => (mask,id))

def c17643 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17643 : Upper (D 7) (R 7) [12,288,18,33,65,128] 13 := by
  apply FastRouting.sound _ _ [12,288,18,33,65,128] 13 (by decide) (choices 1) [2,128] r17643 c17643
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4445
  · exact u4446

def b17644 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 41, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(3,1)], upper := (rows 13 290 22 41 208 33 194 194 450), lower := (rows 13 290 22 41 208 33 64 128 256), losses := [] }

theorem u17644 : Upper (D 7) (R 7) [12,288,18,33,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17644 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17645 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 13 290 22 41 208 34 193 193 449), lower := (rows 13 290 22 41 208 34 64 128 256), losses := [] }

theorem u17645 : Upper (D 7) (R 7) [12,288,18,33,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17645 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17646 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 386, targets := 64 }], pairs := [(0,1),(0,7),(1,6),(3,1)], upper := (rows 13 290 22 41 208 96 195 131 387), lower := (rows 13 290 22 41 208 96 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 12 16 112 64 128 256), good := (rows 13 288 61 41 240 96 96 128 256) },{ target := 7, region := (rows 5 2 4 12 16 112 64 0 256), good := (rows 13 290 63 41 112 96 96 0 256) }] }

theorem u17646 : Upper (D 7) (R 7) [12,288,18,33,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17646 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17647 : PairBound 9 := { available := 130, camps := [{ cop := 5, region := 470, targets := 1 },{ cop := 2, region := 201, targets := 32 }], pairs := [(0,5),(1,0),(2,0),(4,0)], upper := (rows 13 290 22 73 112 33 194 130 386), lower := (rows 13 290 22 73 112 33 64 128 256), losses := [] }

theorem u17647 : Upper (D 7) (R 7) [12,288,18,65,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17647 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17648 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 201, targets := 34 }], pairs := [(0,1),(0,5),(3,1),(3,5)], upper := (rows 13 290 22 73 112 34 193 129 385), lower := (rows 13 290 22 73 112 34 64 128 256), losses := [] }

theorem u17648 : Upper (D 7) (R 7) [12,288,18,65,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17648 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17649 : Route 9 := (fun mask => (mask,id))

def c17649 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17649 : Upper (D 7) (R 7) [12,288,18,65,96,128] 13 := by
  apply FastRouting.sound _ _ [12,288,18,65,96,128] 13 (by decide) (choices 1) [1,2,128] r17649 c17649
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4447
  · exact u4448
  · exact u4449

def b17650 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 358, targets := 1 },{ cop := 8, region := 34, targets := 192 }], pairs := [(1,0),(1,6),(1,7),(2,0)], upper := (rows 13 290 22 73 145 34 224 224 480), lower := (rows 13 290 22 73 145 34 64 128 256), losses := [] }

theorem u17650 : Upper (D 7) (R 7) [12,288,18,65,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17650 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17651 : Route 9 := (fun mask => (mask,id))

def c17651 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17651 : Upper (D 7) (R 7) [12,288,18,65,129,64] 13 := by
  apply FastRouting.sound _ _ [12,288,18,65,129,64] 13 (by decide) (choices 1) [2,32,128] r17651 c17651
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4450
  · exact u4451
  · exact u4452

def b17652 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 358, targets := 1 },{ cop := 5, region := 322, targets := 128 }], pairs := [(0,7),(1,0),(1,7),(2,0)], upper := (rows 13 290 22 73 145 160 98 226 354), lower := (rows 13 290 22 73 145 160 64 128 256), losses := [{ target := 7, region := (rows 5 34 4 12 16 32 98 0 290), good := (rows 13 354 351 73 17 354 64 0 256) }] }

theorem u17652 : Upper (D 7) (R 7) [12,288,18,65,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17652 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17653 : PairBound 9 := { available := 194, camps := [{ cop := 5, region := 470, targets := 1 },{ cop := 2, region := 201, targets := 32 }], pairs := [(0,5),(1,0),(2,0),(4,0)], upper := (rows 13 290 22 73 176 33 194 194 450), lower := (rows 13 290 22 73 176 33 64 128 256), losses := [] }

theorem u17653 : Upper (D 7) (R 7) [12,288,18,65,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17653 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17654 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 201, targets := 34 }], pairs := [(0,1),(0,5),(3,1),(3,5)], upper := (rows 13 290 22 73 176 34 193 193 449), lower := (rows 13 290 22 73 176 34 64 128 256), losses := [] }

theorem u17654 : Upper (D 7) (R 7) [12,288,18,65,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17654 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17655 : Route 9 := (fun mask => (mask,id))

def c17655 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17655 : Upper (D 7) (R 7) [12,288,18,65,160,64] 13 := by
  apply FastRouting.sound _ _ [12,288,18,65,160,64] 13 (by decide) (choices 1) [1,2,128] r17655 c17655
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4453
  · exact u4454
  · exact u4455

def b17656 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 290 22 73 176 160 67 195 323), lower := (rows 13 290 22 73 176 160 64 128 256), losses := [] }

theorem u17656 : Upper (D 7) (R 7) [12,288,18,65,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17656 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17657 : PairBound 9 := { available := 162, camps := [{ cop := 5, region := 470, targets := 1 },{ cop := 0, region := 418, targets := 64 }], pairs := [(1,0),(1,6),(2,0),(4,0)], upper := (rows 13 290 22 73 208 33 226 162 418), lower := (rows 13 290 22 73 208 33 64 128 256), losses := [] }

theorem u17657 : Upper (D 7) (R 7) [12,288,18,65,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17657 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17658 : Route 9 := (fun mask => (mask,id))

def c17658 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17658 : Upper (D 7) (R 7) [12,288,18,65,192,2] 13 := by
  apply FastRouting.sound _ _ [12,288,18,65,192,2] 13 (by decide) (choices 1) [1,32,128] r17658 c17658
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4456
  · exact u4457
  · exact u4458

def r17659 : Route 9 := (fun mask => (mask,id))

def c17659 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17659 : Upper (D 7) (R 7) [12,288,18,65,192,128] 13 := by
  apply FastRouting.sound _ _ [12,288,18,65,192,128] 13 (by decide) (choices 1) [1,2,32] r17659 c17659
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4459
  · exact u4460
  · exact u4461

def b17660 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 53, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 13 290 22 74 49 33 192 192 448), lower := (rows 13 290 22 74 49 33 64 128 256), losses := [] }

theorem u17660 : Upper (D 7) (R 7) [12,288,18,66,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17660 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17661 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 53, targets := 128 },{ cop := 2, region := 201, targets := 32 }], pairs := [(0,5),(0,7),(2,7),(4,7)], upper := (rows 13 290 22 74 49 96 193 129 385), lower := (rows 13 290 22 74 49 96 64 128 256), losses := [] }

theorem u17661 : Upper (D 7) (R 7) [12,288,18,66,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17661 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17662 : Route 9 := (fun mask => (mask,id))

def c17662 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17662 : Upper (D 7) (R 7) [12,288,18,66,33,128] 13 := by
  apply FastRouting.sound _ _ [12,288,18,66,33,128] 13 (by decide) (choices 1) [1,128] r17662 c17662
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4462
  · exact u4463

def r17663 : Route 9 := (fun mask => (mask,id))

def c17663 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17663 : Upper (D 7) (R 7) [12,288,18,66,129,1] 13 := by
  apply FastRouting.sound _ _ [12,288,18,66,129,1] 13 (by decide) (choices 1) [32,128] r17663 c17663
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4464
  · exact u4465

def r17664 : Route 9 := (fun mask => (mask,id))

def c17664 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17664 : Upper (D 7) (R 7) [12,288,18,66,129,64] 13 := by
  apply FastRouting.sound _ _ [12,288,18,66,129,64] 13 (by decide) (choices 1) [1,32,128] r17664 c17664
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4466
  · exact u4467
  · exact u4468

def r17665 : Route 9 := (fun mask => (mask,id))

def c17665 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17665 : Upper (D 7) (R 7) [12,288,18,66,129,128] 13 := by
  apply FastRouting.sound _ _ [12,288,18,66,129,128] 13 (by decide) (choices 1) [1,32] r17665 c17665
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4469
  · exact u4470

def r17666 : Route 9 := (fun mask => (mask,id))

def c17666 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17666 : Upper (D 7) (R 7) [12,288,18,66,160,1] 13 := by
  apply FastRouting.sound _ _ [12,288,18,66,160,1] 13 (by decide) (choices 1) [1,128] r17666 c17666
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4471
  · exact u4472

def r17667 : Route 9 := (fun mask => (mask,id))

def c17667 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17667 : Upper (D 7) (R 7) [12,288,18,66,160,64] 13 := by
  apply FastRouting.sound _ _ [12,288,18,66,160,64] 13 (by decide) (choices 1) [1,128] r17667 c17667
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4473
  · exact u4474

def b17668 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 290 22 74 176 160 65 193 321), lower := (rows 13 290 22 74 176 160 64 128 256), losses := [] }

theorem u17668 : Upper (D 7) (R 7) [12,288,18,66,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17668 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17669 : Route 9 := (fun mask => (mask,id))

def c17669 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17669 : Upper (D 7) (R 7) [12,288,18,66,192,1] 13 := by
  apply FastRouting.sound _ _ [12,288,18,66,192,1] 13 (by decide) (choices 1) [1,32,128] r17669 c17669
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4475
  · exact u4476
  · exact u4477

def r17670 : Route 9 := (fun mask => (mask,id))

def c17670 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17670 : Upper (D 7) (R 7) [12,288,18,66,192,128] 13 := by
  apply FastRouting.sound _ _ [12,288,18,66,192,128] 13 (by decide) (choices 1) [1,32] r17670 c17670
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4478
  · exact u4479

def b17671 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 40, targets := 130 },{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(2,6),(3,1),(3,7)], upper := (rows 13 290 22 104 81 33 194 130 386), lower := (rows 13 290 22 104 81 33 64 128 256), losses := [] }

theorem u17671 : Upper (D 7) (R 7) [12,288,18,96,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17671 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17672 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 0, region := 208, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(4,1)], upper := (rows 13 290 22 104 81 34 193 129 385), lower := (rows 13 290 22 104 81 34 64 128 256), losses := [] }

theorem u17672 : Upper (D 7) (R 7) [12,288,18,96,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17672 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17673 : Route 9 := (fun mask => (mask,id))

def c17673 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17673 : Upper (D 7) (R 7) [12,288,18,96,65,128] 13 := by
  apply FastRouting.sound _ _ [12,288,18,96,65,128] 13 (by decide) (choices 1) [1,2,128] r17673 c17673
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4480
  · exact u4481
  · exact u4482

def r17674 : Route 9 := (fun mask => (mask,id))

def c17674 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17674 : Upper (D 7) (R 7) [12,288,18,96,129,1] 13 := by
  apply FastRouting.sound _ _ [12,288,18,96,129,1] 13 (by decide) (choices 1) [2,128] r17674 c17674
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4483
  · exact u4484

def b17675 : PairBound 9 := { available := 193, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 0, region := 208, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(4,1)], upper := (rows 13 290 22 104 145 34 193 193 449), lower := (rows 13 290 22 104 145 34 64 128 256), losses := [] }

theorem u17675 : Upper (D 7) (R 7) [12,288,18,96,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17675 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17676 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 13 290 22 104 145 96 195 131 387), lower := (rows 13 290 22 104 145 96 64 128 256), losses := [] }

theorem u17676 : Upper (D 7) (R 7) [12,288,18,96,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17676 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17677 : Route 9 := (fun mask => (mask,id))

def c17677 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17677 : Upper (D 7) (R 7) [12,288,18,96,129,128] 13 := by
  apply FastRouting.sound _ _ [12,288,18,96,129,128] 13 (by decide) (choices 1) [1,2] r17677 c17677
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4485
  · exact u4486

def r17678 : Route 9 := (fun mask => (mask,id))

def c17678 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17678 : Upper (D 7) (R 7) [12,288,18,96,192,1] 13 := by
  apply FastRouting.sound _ _ [12,288,18,96,192,1] 13 (by decide) (choices 1) [1,2,128] r17678 c17678
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4487
  · exact u4488
  · exact u4489

def b17679 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 0, region := 208, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(4,1)], upper := (rows 13 290 22 104 208 34 193 129 385), lower := (rows 13 290 22 104 208 34 64 128 256), losses := [] }

theorem u17679 : Upper (D 7) (R 7) [12,288,18,96,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17679 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17680 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 40, targets := 3 },{ cop := 0, region := 418, targets := 64 }], pairs := [(0,1),(1,6),(3,0),(3,1)], upper := (rows 13 290 22 104 208 160 67 131 259), lower := (rows 13 290 22 104 208 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 24 16 176 64 128 256), good := (rows 13 288 61 104 248 160 64 160 256) }] }

theorem u17680 : Upper (D 7) (R 7) [12,288,18,96,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17680 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17681 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 48, targets := 194 },{ cop := 4, region := 450, targets := 1 }], pairs := [(1,0),(4,1),(4,6),(4,7)], upper := (rows 13 290 22 200 49 33 194 194 450), lower := (rows 13 290 22 200 49 33 64 128 256), losses := [] }

theorem u17681 : Upper (D 7) (R 7) [12,288,18,192,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17681 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17682 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 201, targets := 34 }], pairs := [(0,1),(0,5),(3,1),(3,5)], upper := (rows 13 290 22 200 49 34 193 193 449), lower := (rows 13 290 22 200 49 34 64 128 256), losses := [] }

theorem u17682 : Upper (D 7) (R 7) [12,288,18,192,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17682 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17683 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 201, targets := 32 },{ cop := 4, region := 390, targets := 64 }], pairs := [(0,5),(1,6),(2,6),(3,5)], upper := (rows 13 290 22 200 49 96 195 131 387), lower := (rows 13 290 22 200 49 96 64 128 256), losses := [] }

theorem u17683 : Upper (D 7) (R 7) [12,288,18,192,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17683 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17684 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 422, targets := 64 },{ cop := 5, region := 458, targets := 1 }], pairs := [(1,0),(1,6),(2,6),(3,0)], upper := (rows 13 290 22 200 81 33 226 162 418), lower := (rows 13 290 22 200 81 33 64 128 256), losses := [] }

theorem u17684 : Upper (D 7) (R 7) [12,288,18,192,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17684 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17685 : PairBound 9 := { available := 161, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 4, region := 422, targets := 64 }], pairs := [(1,0),(1,6),(1,7),(2,6)], upper := (rows 13 290 22 200 81 34 225 161 417), lower := (rows 13 290 22 200 81 34 64 128 256), losses := [] }

theorem u17685 : Upper (D 7) (R 7) [12,288,18,192,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17685 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17686 : Route 9 := (fun mask => (mask,id))

def c17686 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17686 : Upper (D 7) (R 7) [12,288,18,192,65,128] 13 := by
  apply FastRouting.sound _ _ [12,288,18,192,65,128] 13 (by decide) (choices 1) [1,2,32] r17686 c17686
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4490
  · exact u4491
  · exact u4492

def b17687 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 201, targets := 32 },{ cop := 0, region := 418, targets := 64 }], pairs := [(0,5),(1,6),(2,6),(3,5)], upper := (rows 13 290 22 200 112 33 195 131 387), lower := (rows 13 290 22 200 112 33 64 128 256), losses := [{ target := 6, region := (rows 1 51 20 8 16 33 0 161 289), good := (rows 431 418 22 136 438 419 0 128 256) }] }

theorem u17687 : Upper (D 7) (R 7) [12,288,18,192,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17687 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17688 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 201, targets := 34 }], pairs := [(0,1),(0,5),(3,1),(3,5)], upper := (rows 13 290 22 200 112 34 193 129 385), lower := (rows 13 290 22 200 112 34 64 128 256), losses := [] }

theorem u17688 : Upper (D 7) (R 7) [12,288,18,192,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17688 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17689 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 201, targets := 32 },{ cop := 3, region := 48, targets := 3 }], pairs := [(0,5),(3,5),(4,0),(4,1)], upper := (rows 13 290 22 200 112 160 67 131 259), lower := (rows 13 290 22 200 112 160 64 128 256), losses := [] }

theorem u17689 : Upper (D 7) (R 7) [12,288,18,192,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17689 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17690 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 8, region := 34, targets := 192 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 13 290 37 73 146 34 208 208 464), lower := (rows 13 290 37 73 146 34 64 128 256), losses := [] }

theorem u17690 : Upper (D 7) (R 7) [12,288,33,65,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17690 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17691 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 1, region := 208, targets := 32 }], pairs := [(1,0),(4,0),(4,5)], upper := (rows 13 290 37 73 146 48 194 194 450), lower := (rows 13 290 37 73 146 48 64 128 256), losses := [] }

theorem u17691 : Upper (D 7) (R 7) [12,288,33,65,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17691 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17692 : PairBound 9 := { available := 146, camps := [{ cop := 5, region := 13, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 290 37 73 146 96 210 146 402), lower := (rows 13 290 37 73 146 96 64 128 256), losses := [] }

theorem u17692 : Upper (D 7) (R 7) [12,288,33,65,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17692 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17693 : Route 9 := (fun mask => (mask,id))

def c17693 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17693 : Upper (D 7) (R 7) [12,288,33,65,130,128] 13 := by
  apply FastRouting.sound _ _ [12,288,33,65,130,128] 13 (by decide) (choices 1) [2,16] r17693 c17693
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4493
  · exact u4494

def b17694 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 13 290 37 74 145 34 208 208 464), lower := (rows 13 290 37 74 145 34 64 128 256), losses := [] }

theorem u17694 : Upper (D 7) (R 7) [12,288,33,66,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17694 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17695 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 36, targets := 194 }], pairs := [(2,1),(2,6),(2,7)], upper := (rows 13 290 37 74 145 48 194 194 450), lower := (rows 13 290 37 74 145 48 64 128 256), losses := [] }

theorem u17695 : Upper (D 7) (R 7) [12,288,33,66,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17695 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17696 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 290 37 74 145 96 210 146 402), lower := (rows 13 290 37 74 145 96 64 128 256), losses := [] }

theorem u17696 : Upper (D 7) (R 7) [12,288,33,66,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17696 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17697 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 4, region := 36, targets := 66 }], pairs := [(1,0),(2,1),(2,6),(3,0)], upper := (rows 13 290 37 74 145 160 82 210 338), lower := (rows 13 290 37 74 145 160 64 128 256), losses := [] }

theorem u17697 : Upper (D 7) (R 7) [12,288,33,66,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17697 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17698 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 13 290 37 74 146 33 208 208 464), lower := (rows 13 290 37 74 146 33 64 128 256), losses := [] }

theorem u17698 : Upper (D 7) (R 7) [12,288,33,66,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17698 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17699 : Route 9 := (fun mask => (mask,id))

def c17699 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17699 : Upper (D 7) (R 7) [12,288,33,66,130,16] 13 := by
  apply FastRouting.sound _ _ [12,288,33,66,130,16] 13 (by decide) (choices 1) [1,128] r17699 c17699
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4495
  · exact u4496

#print axioms u17699
end Delivery.IrregularNine14.P07

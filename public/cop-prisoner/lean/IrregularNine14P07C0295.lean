import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0074
import IrregularNine14P07C0075

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b17700 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 290 37 74 146 96 209 145 401), lower := (rows 13 290 37 74 146 96 64 128 256), losses := [] }

theorem u17700 : Upper (D 7) (R 7) [12,288,33,66,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17700 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17701 : Route 9 := (fun mask => (mask,id))

def c17701 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17701 : Upper (D 7) (R 7) [12,288,33,66,130,128] 13 := by
  apply FastRouting.sound _ _ [12,288,33,66,130,128] 13 (by decide) (choices 1) [1,16] r17701 c17701
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4497
  · exact u4498

def b17702 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 13 290 37 74 208 33 210 146 402), lower := (rows 13 290 37 74 208 33 64 128 256), losses := [] }

theorem u17702 : Upper (D 7) (R 7) [12,288,33,66,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17702 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17703 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 13 290 37 74 208 34 209 145 401), lower := (rows 13 290 37 74 208 34 64 128 256), losses := [] }

theorem u17703 : Upper (D 7) (R 7) [12,288,33,66,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17703 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17704 : Route 9 := (fun mask => (mask,id))

def c17704 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17704 : Upper (D 7) (R 7) [12,288,33,66,192,16] 13 := by
  apply FastRouting.sound _ _ [12,288,33,66,192,16] 13 (by decide) (choices 1) [1,2,128] r17704 c17704
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4499
  · exact u4500
  · exact u4501

def r17705 : Route 9 := (fun mask => (mask,id))

def c17705 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17705 : Upper (D 7) (R 7) [12,288,33,66,192,128] 13 := by
  apply FastRouting.sound _ _ [12,288,33,66,192,128] 13 (by decide) (choices 1) [1,2,16] r17705 c17705
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4502
  · exact u4503
  · exact u4504

def b17706 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 4, region := 200, targets := 34 }], pairs := [(1,0),(3,0),(3,1),(3,5)], upper := (rows 13 290 37 88 19 34 192 192 448), lower := (rows 13 290 37 88 19 34 64 128 256), losses := [] }

theorem u17706 : Upper (D 7) (R 7) [12,288,33,80,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17706 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17707 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 290 37 88 19 96 194 130 386), lower := (rows 13 290 37 88 19 96 64 128 256), losses := [] }

theorem u17707 : Upper (D 7) (R 7) [12,288,33,80,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17707 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17708 : Route 9 := (fun mask => (mask,id))

def c17708 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17708 : Upper (D 7) (R 7) [12,288,33,80,3,128] 13 := by
  apply FastRouting.sound _ _ [12,288,33,80,3,128] 13 (by decide) (choices 1) [2,128] r17708 c17708
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4505
  · exact u4506

def b17709 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 8, region := 34, targets := 192 }], pairs := [(1,0),(1,6),(1,7),(3,0)], upper := (rows 13 290 37 88 145 34 194 194 450), lower := (rows 13 290 37 88 145 34 64 128 256), losses := [] }

theorem u17709 : Upper (D 7) (R 7) [12,288,33,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17709 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17710 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 290 37 88 145 96 194 130 386), lower := (rows 13 290 37 88 145 96 64 128 256), losses := [] }

theorem u17710 : Upper (D 7) (R 7) [12,288,33,80,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17710 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17711 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 4, region := 36, targets := 66 }], pairs := [(1,0),(2,1),(2,6),(3,0)], upper := (rows 13 290 37 88 145 160 66 194 322), lower := (rows 13 290 37 88 145 160 64 128 256), losses := [] }

theorem u17711 : Upper (D 7) (R 7) [12,288,33,80,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17711 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17712 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 13 290 37 88 146 33 194 194 450), lower := (rows 13 290 37 88 146 33 64 128 256), losses := [] }

theorem u17712 : Upper (D 7) (R 7) [12,288,33,80,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17712 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17713 : PairBound 9 := { available := 193, camps := [{ cop := 8, region := 34, targets := 193 }], pairs := [(0,6),(1,0),(1,6),(1,7)], upper := (rows 13 290 37 88 146 34 193 193 449), lower := (rows 13 290 37 88 146 34 64 128 256), losses := [{ target := 6, region := (rows 9 258 12 8 16 306 0 128 256), good := (rows 13 290 37 61 178 34 0 128 290) }] }

theorem u17713 : Upper (D 7) (R 7) [12,288,33,80,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17713 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17714 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 290 37 88 146 96 195 131 387), lower := (rows 13 290 37 88 146 96 64 128 256), losses := [] }

theorem u17714 : Upper (D 7) (R 7) [12,288,33,80,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17714 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17715 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 322, targets := 128 }], pairs := [(0,1),(0,6),(1,7),(2,1)], upper := (rows 13 290 37 88 146 160 67 195 323), lower := (rows 13 290 37 88 146 160 64 128 256), losses := [{ target := 1, region := (rows 9 0 12 8 16 176 64 128 256), good := (rows 13 288 37 125 176 160 64 160 256) },{ target := 6, region := (rows 9 2 12 8 16 176 0 128 256), good := (rows 13 290 37 61 178 160 0 160 256) }] }

theorem u17715 : Upper (D 7) (R 7) [12,288,33,80,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17715 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17716 : PairBound 9 := { available := 208, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 4, region := 200, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(3,1)], upper := (rows 13 290 37 200 19 34 208 208 464), lower := (rows 13 290 37 200 19 34 64 128 256), losses := [] }

theorem u17716 : Upper (D 7) (R 7) [12,288,33,192,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17716 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17717 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 36, targets := 194 }], pairs := [(2,1),(2,6),(2,7)], upper := (rows 13 290 37 200 19 48 194 194 450), lower := (rows 13 290 37 200 19 48 64 128 256), losses := [] }

theorem u17717 : Upper (D 7) (R 7) [12,288,33,192,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17717 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17718 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 290 37 200 19 96 210 146 402), lower := (rows 13 290 37 200 19 96 64 128 256), losses := [] }

theorem u17718 : Upper (D 7) (R 7) [12,288,33,192,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17718 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17719 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 13 290 37 200 82 33 210 146 402), lower := (rows 13 290 37 200 82 33 64 128 256), losses := [] }

theorem u17719 : Upper (D 7) (R 7) [12,288,33,192,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17719 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17720 : Route 9 := (fun mask => (mask,id))

def c17720 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17720 : Upper (D 7) (R 7) [12,288,33,192,66,2] 13 := by
  apply FastRouting.sound _ _ [12,288,33,192,66,2] 13 (by decide) (choices 1) [1,16,128] r17720 c17720
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4507
  · exact u4508
  · exact u4509

def r17721 : Route 9 := (fun mask => (mask,id))

def c17721 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17721 : Upper (D 7) (R 7) [12,288,33,192,66,16] 13 := by
  apply FastRouting.sound _ _ [12,288,33,192,66,16] 13 (by decide) (choices 1) [1,2,128] r17721 c17721
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4510
  · exact u4511
  · exact u4512

def b17722 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 13 290 37 200 82 160 83 147 275), lower := (rows 13 290 37 200 82 160 64 128 256), losses := [] }

theorem u17722 : Upper (D 7) (R 7) [12,288,33,192,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17722 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17723 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 45, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 290 52 73 82 33 194 130 386), lower := (rows 13 290 52 73 82 33 64 128 256), losses := [] }

theorem u17723 : Upper (D 7) (R 7) [12,288,48,65,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17723 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17724 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 201, targets := 34 }], pairs := [(0,1),(0,5),(3,1),(3,5)], upper := (rows 13 290 52 73 82 34 193 129 385), lower := (rows 13 290 52 73 82 34 64 128 256), losses := [] }

theorem u17724 : Upper (D 7) (R 7) [12,288,48,65,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17724 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17725 : Route 9 := (fun mask => (mask,id))

def c17725 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17725 : Upper (D 7) (R 7) [12,288,48,65,66,128] 13 := by
  apply FastRouting.sound _ _ [12,288,48,65,66,128] 13 (by decide) (choices 1) [1,2,128] r17725 c17725
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4513
  · exact u4514
  · exact u4515

def b17726 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 358, targets := 1 },{ cop := 8, region := 34, targets := 192 }], pairs := [(1,0),(1,6),(1,7),(2,0)], upper := (rows 13 290 52 73 145 34 194 194 450), lower := (rows 13 290 52 73 145 34 64 128 256), losses := [] }

theorem u17726 : Upper (D 7) (R 7) [12,288,48,65,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17726 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17727 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 358, targets := 1 },{ cop := 2, region := 386, targets := 64 }], pairs := [(1,0),(1,6),(2,0),(4,6)], upper := (rows 13 290 52 73 145 96 194 130 386), lower := (rows 13 290 52 73 145 96 64 128 256), losses := [{ target := 6, region := (rows 1 38 4 8 25 32 0 167 295), good := (rows 415 418 438 409 401 418 0 128 256) }] }

theorem u17727 : Upper (D 7) (R 7) [12,288,48,65,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17727 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17728 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 331, targets := 128 },{ cop := 4, region := 354, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(3,7)], upper := (rows 13 290 52 73 145 160 66 194 322), lower := (rows 13 290 52 73 145 160 64 128 256), losses := [] }

theorem u17728 : Upper (D 7) (R 7) [12,288,48,65,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17728 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17729 : PairBound 9 := { available := 194, camps := [{ cop := 5, region := 470, targets := 1 },{ cop := 1, region := 208, targets := 32 }], pairs := [(1,0),(2,0),(4,0),(4,5)], upper := (rows 13 290 52 73 146 33 194 194 450), lower := (rows 13 290 52 73 146 33 64 128 256), losses := [] }

theorem u17729 : Upper (D 7) (R 7) [12,288,48,65,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17729 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17730 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 201, targets := 34 }], pairs := [(0,1),(0,5),(3,1),(3,5)], upper := (rows 13 290 52 73 146 34 193 193 449), lower := (rows 13 290 52 73 146 34 64 128 256), losses := [] }

theorem u17730 : Upper (D 7) (R 7) [12,288,48,65,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17730 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17731 : Route 9 := (fun mask => (mask,id))

def c17731 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17731 : Upper (D 7) (R 7) [12,288,48,65,130,64] 13 := by
  apply FastRouting.sound _ _ [12,288,48,65,130,64] 13 (by decide) (choices 1) [1,2,128] r17731 c17731
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4516
  · exact u4517
  · exact u4518

def b17732 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 331, targets := 128 },{ cop := 4, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 13 290 52 73 146 160 67 195 323), lower := (rows 13 290 52 73 146 160 64 128 256), losses := [] }

theorem u17732 : Upper (D 7) (R 7) [12,288,48,65,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17732 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17733 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 45, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 290 52 73 208 33 194 130 386), lower := (rows 13 290 52 73 208 33 64 128 256), losses := [] }

theorem u17733 : Upper (D 7) (R 7) [12,288,48,65,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17733 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17734 : Route 9 := (fun mask => (mask,id))

def c17734 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17734 : Upper (D 7) (R 7) [12,288,48,65,192,2] 13 := by
  apply FastRouting.sound _ _ [12,288,48,65,192,2] 13 (by decide) (choices 1) [1,2,128] r17734 c17734
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4519
  · exact u4520
  · exact u4521

def b17735 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 331, targets := 128 },{ cop := 4, region := 45, targets := 2 }], pairs := [(0,1),(0,7),(1,7),(3,7)], upper := (rows 13 290 52 73 208 160 67 131 259), lower := (rows 13 290 52 73 208 160 64 128 256), losses := [] }

theorem u17735 : Upper (D 7) (R 7) [12,288,48,65,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17735 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17736 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 53, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 13 290 52 74 19 33 192 192 448), lower := (rows 13 290 52 74 19 33 64 128 256), losses := [] }

theorem u17736 : Upper (D 7) (R 7) [12,288,48,66,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17736 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17737 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 53, targets := 128 },{ cop := 4, region := 228, targets := 2 }], pairs := [(0,7),(2,1),(2,7),(4,7)], upper := (rows 13 290 52 74 19 96 193 129 385), lower := (rows 13 290 52 74 19 96 64 128 256), losses := [] }

theorem u17737 : Upper (D 7) (R 7) [12,288,48,66,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17737 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17738 : Route 9 := (fun mask => (mask,id))

def c17738 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17738 : Upper (D 7) (R 7) [12,288,48,66,3,128] 13 := by
  apply FastRouting.sound _ _ [12,288,48,66,3,128] 13 (by decide) (choices 1) [1,128] r17738 c17738
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4522
  · exact u4523

def b17739 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 53, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 290 52 74 81 33 194 130 386), lower := (rows 13 290 52 74 81 33 64 128 256), losses := [] }

theorem u17739 : Upper (D 7) (R 7) [12,288,48,66,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17739 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17740 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 53, targets := 128 },{ cop := 8, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 13 290 52 74 81 34 193 129 385), lower := (rows 13 290 52 74 81 34 64 128 256), losses := [] }

theorem u17740 : Upper (D 7) (R 7) [12,288,48,66,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17740 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17741 : Route 9 := (fun mask => (mask,id))

def c17741 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17741 : Upper (D 7) (R 7) [12,288,48,66,65,128] 13 := by
  apply FastRouting.sound _ _ [12,288,48,66,65,128] 13 (by decide) (choices 1) [1,2,128] r17741 c17741
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4524
  · exact u4525
  · exact u4526

def b17742 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 36, targets := 194 },{ cop := 1, region := 200, targets := 1 }], pairs := [(2,1),(2,6),(2,7),(3,0)], upper := (rows 13 290 52 74 145 33 194 194 450), lower := (rows 13 290 52 74 145 33 64 128 256), losses := [] }

theorem u17742 : Upper (D 7) (R 7) [12,288,48,66,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17742 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17743 : PairBound 9 := { available := 193, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 0, region := 208, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(4,1)], upper := (rows 13 290 52 74 145 34 193 193 449), lower := (rows 13 290 52 74 145 34 64 128 256), losses := [] }

theorem u17743 : Upper (D 7) (R 7) [12,288,48,66,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17743 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17744 : Route 9 := (fun mask => (mask,id))

def c17744 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17744 : Upper (D 7) (R 7) [12,288,48,66,129,64] 13 := by
  apply FastRouting.sound _ _ [12,288,48,66,129,64] 13 (by decide) (choices 1) [1,2,128] r17744 c17744
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4527
  · exact u4528
  · exact u4529

def b17745 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 331, targets := 128 },{ cop := 4, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 13 290 52 74 145 160 67 195 323), lower := (rows 13 290 52 74 145 160 64 128 256), losses := [] }

theorem u17745 : Upper (D 7) (R 7) [12,288,48,66,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17745 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17746 : Route 9 := (fun mask => (mask,id))

def c17746 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17746 : Upper (D 7) (R 7) [12,288,48,66,130,1] 13 := by
  apply FastRouting.sound _ _ [12,288,48,66,130,1] 13 (by decide) (choices 1) [1,128] r17746 c17746
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4530
  · exact u4531

def r17747 : Route 9 := (fun mask => (mask,id))

def c17747 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17747 : Upper (D 7) (R 7) [12,288,48,66,130,64] 13 := by
  apply FastRouting.sound _ _ [12,288,48,66,130,64] 13 (by decide) (choices 1) [1,128] r17747 c17747
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4532
  · exact u4533

def b17748 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 331, targets := 128 },{ cop := 4, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 13 290 52 74 146 160 65 193 321), lower := (rows 13 290 52 74 146 160 64 128 256), losses := [] }

theorem u17748 : Upper (D 7) (R 7) [12,288,48,66,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17748 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17749 : Route 9 := (fun mask => (mask,id))

def c17749 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17749 : Upper (D 7) (R 7) [12,288,48,66,192,1] 13 := by
  apply FastRouting.sound _ _ [12,288,48,66,192,1] 13 (by decide) (choices 1) [1,2,128] r17749 c17749
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4534
  · exact u4535
  · exact u4536

def b17750 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 0, region := 208, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(4,1)], upper := (rows 13 290 52 74 208 34 193 129 385), lower := (rows 13 290 52 74 208 34 64 128 256), losses := [] }

theorem u17750 : Upper (D 7) (R 7) [12,288,48,66,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17750 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17751 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 331, targets := 128 },{ cop := 4, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 13 290 52 74 208 160 67 131 259), lower := (rows 13 290 52 74 208 160 64 128 256), losses := [] }

theorem u17751 : Upper (D 7) (R 7) [12,288,48,66,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17751 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17752 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 36, targets := 194 },{ cop := 1, region := 200, targets := 1 }], pairs := [(2,1),(2,6),(2,7),(3,0)], upper := (rows 13 290 52 200 19 33 194 194 450), lower := (rows 13 290 52 200 19 33 64 128 256), losses := [] }

theorem u17752 : Upper (D 7) (R 7) [12,288,48,192,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17752 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17753 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 201, targets := 34 }], pairs := [(0,1),(0,5),(3,1),(3,5)], upper := (rows 13 290 52 200 19 34 193 193 449), lower := (rows 13 290 52 200 19 34 64 128 256), losses := [] }

theorem u17753 : Upper (D 7) (R 7) [12,288,48,192,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17753 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17754 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 200, targets := 32 }], pairs := [(0,5),(1,6),(3,5),(4,6)], upper := (rows 13 290 52 200 19 96 195 131 387), lower := (rows 13 290 52 200 19 96 64 128 256), losses := [{ target := 5, region := (rows 5 2 4 28 16 0 80 144 272), good := (rows 13 258 477 200 475 64 64 128 256) },{ target := 6, region := (rows 1 6 4 8 17 32 0 145 273), good := (rows 415 290 438 136 403 32 0 128 256) }] }

theorem u17754 : Upper (D 7) (R 7) [12,288,48,192,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17754 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17755 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 53, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 290 52 200 81 33 194 130 386), lower := (rows 13 290 52 200 81 33 64 128 256), losses := [] }

theorem u17755 : Upper (D 7) (R 7) [12,288,48,192,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17755 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17756 : PairBound 9 := { available := 131, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 4, region := 422, targets := 64 }], pairs := [(1,0),(1,6),(1,7),(2,6)], upper := (rows 13 290 52 200 81 34 195 131 387), lower := (rows 13 290 52 200 81 34 64 128 256), losses := [] }

theorem u17756 : Upper (D 7) (R 7) [12,288,48,192,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17756 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17757 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 53, targets := 2 },{ cop := 4, region := 418, targets := 64 }], pairs := [(0,1),(1,6),(2,1),(4,1)], upper := (rows 13 290 52 200 81 160 67 131 259), lower := (rows 13 290 52 200 81 160 64 128 256), losses := [] }

theorem u17757 : Upper (D 7) (R 7) [12,288,48,192,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17757 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17758 : Route 9 := (fun mask => (mask,id))

def c17758 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17758 : Upper (D 7) (R 7) [12,288,48,192,66,1] 13 := by
  apply FastRouting.sound _ _ [12,288,48,192,66,1] 13 (by decide) (choices 1) [1,2,128] r17758 c17758
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4537
  · exact u4538
  · exact u4539

def b17759 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 201, targets := 34 }], pairs := [(0,1),(0,5),(3,1),(3,5)], upper := (rows 13 290 52 200 82 34 193 129 385), lower := (rows 13 290 52 200 82 34 64 128 256), losses := [] }

theorem u17759 : Upper (D 7) (R 7) [12,288,48,192,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17759 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u17759
end Delivery.IrregularNine14.P07

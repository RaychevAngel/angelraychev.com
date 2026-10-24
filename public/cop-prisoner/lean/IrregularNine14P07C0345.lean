import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0097

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b20700 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 35 259 13 74 176 36 208 208 464), lower := (rows 35 259 13 74 176 36 64 128 256), losses := [] }

theorem u20700 : Upper (D 7) (R 7) [34,257,9,66,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20700 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20701 : PairBound 9 := { available := 196, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 259 13 74 176 48 196 196 452), lower := (rows 35 259 13 74 176 48 64 128 256), losses := [] }

theorem u20701 : Upper (D 7) (R 7) [34,257,9,66,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20701 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20702 : PairBound 9 := { available := 148, camps := [{ cop := 2, region := 240, targets := 3 },{ cop := 3, region := 37, targets := 128 }], pairs := [(0,7),(2,7),(4,0),(4,1)], upper := (rows 35 259 13 74 176 96 212 148 404), lower := (rows 35 259 13 74 176 96 64 128 256), losses := [] }

theorem u20702 : Upper (D 7) (R 7) [34,257,9,66,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20702 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20703 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 259 13 74 176 160 84 212 340), lower := (rows 35 259 13 74 176 160 64 128 256), losses := [] }

theorem u20703 : Upper (D 7) (R 7) [34,257,9,66,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20703 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20704 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 35 259 13 74 208 36 240 176 432), lower := (rows 35 259 13 74 208 36 64 128 256), losses := [] }

theorem u20704 : Upper (D 7) (R 7) [34,257,9,66,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20704 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20705 : Route 9 := (fun mask => (mask,id))

def c20705 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u20705 : Upper (D 7) (R 7) [34,257,9,66,192,16] 13 := by
  apply FastRouting.sound _ _ [34,257,9,66,192,16] 13 (by decide) (choices 1) [4,32,128] r20705 c20705
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5836
  · exact u5837
  · exact u5838

def r20706 : Route 9 := (fun mask => (mask,id))

def c20706 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20706 : Upper (D 7) (R 7) [34,257,9,66,192,128] 13 := by
  apply FastRouting.sound _ _ [34,257,9,66,192,128] 13 (by decide) (choices 1) [4,16,32] r20706 c20706
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5839
  · exact u5840
  · exact u5841

def b20707 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 204, targets := 2 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1)], upper := (rows 35 259 13 76 146 48 224 224 480), lower := (rows 35 259 13 76 146 48 64 128 256), losses := [] }

theorem u20707 : Upper (D 7) (R 7) [34,257,9,68,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20707 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20708 : PairBound 9 := { available := 176, camps := [{ cop := 5, region := 403, targets := 64 },{ cop := 0, region := 144, targets := 1 }], pairs := [(0,6),(1,6),(4,0),(4,6)], upper := (rows 35 259 13 76 146 96 240 176 432), lower := (rows 35 259 13 76 146 96 64 128 256), losses := [] }

theorem u20708 : Upper (D 7) (R 7) [34,257,9,68,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20708 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20709 : Route 9 := (fun mask => (mask,id))

def c20709 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20709 : Upper (D 7) (R 7) [34,257,9,68,130,128] 13 := by
  apply FastRouting.sound _ _ [34,257,9,68,130,128] 13 (by decide) (choices 1) [16,32] r20709 c20709
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5842
  · exact u5843

def b20710 : PairBound 9 := { available := 208, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 13 76 176 34 208 208 464), lower := (rows 35 259 13 76 176 34 64 128 256), losses := [] }

theorem u20710 : Upper (D 7) (R 7) [34,257,9,68,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20710 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20711 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 259 13 76 176 48 194 194 450), lower := (rows 35 259 13 76 176 48 64 128 256), losses := [] }

theorem u20711 : Upper (D 7) (R 7) [34,257,9,68,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20711 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20712 : PairBound 9 := { available := 146, camps := [{ cop := 5, region := 403, targets := 64 },{ cop := 0, region := 144, targets := 1 }], pairs := [(0,6),(1,6),(4,0),(4,6)], upper := (rows 35 259 13 76 176 96 210 146 402), lower := (rows 35 259 13 76 176 96 64 128 256), losses := [] }

theorem u20712 : Upper (D 7) (R 7) [34,257,9,68,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20712 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20713 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 259 13 76 176 160 82 210 338), lower := (rows 35 259 13 76 176 160 64 128 256), losses := [] }

theorem u20713 : Upper (D 7) (R 7) [34,257,9,68,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20713 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20714 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 232, targets := 3 },{ cop := 5, region := 387, targets := 64 }], pairs := [(0,6),(1,6),(3,0),(3,1)], upper := (rows 35 259 13 88 22 96 224 160 416), lower := (rows 35 259 13 88 22 96 64 128 256), losses := [] }

theorem u20714 : Upper (D 7) (R 7) [34,257,9,80,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20714 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20715 : Route 9 := (fun mask => (mask,id))

def c20715 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u20715 : Upper (D 7) (R 7) [34,257,9,80,6,128] 13 := by
  apply FastRouting.sound _ _ [34,257,9,80,6,128] 13 (by decide) (choices 1) [32,128] r20715 c20715
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5844
  · exact u5845

def r20716 : Route 9 := (fun mask => (mask,id))

def c20716 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u20716 : Upper (D 7) (R 7) [34,257,9,80,130,4] 13 := by
  apply FastRouting.sound _ _ [34,257,9,80,130,4] 13 (by decide) (choices 1) [32,128] r20716 c20716
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5846
  · exact u5847

def r20717 : Route 9 := (fun mask => (mask,id))

def c20717 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u20717 : Upper (D 7) (R 7) [34,257,9,80,130,64] 13 := by
  apply FastRouting.sound _ _ [34,257,9,80,130,64] 13 (by decide) (choices 1) [4,32,128] r20717 c20717
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5848
  · exact u5849
  · exact u5850

def r20718 : Route 9 := (fun mask => (mask,id))

def c20718 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20718 : Upper (D 7) (R 7) [34,257,9,80,130,128] 13 := by
  apply FastRouting.sound _ _ [34,257,9,80,130,128] 13 (by decide) (choices 1) [4,32] r20718 c20718
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5851
  · exact u5852

def b20719 : PairBound 9 := { available := 224, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 13 88 148 34 224 224 480), lower := (rows 35 259 13 88 148 34 64 128 256), losses := [] }

theorem u20719 : Upper (D 7) (R 7) [34,257,9,80,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20719 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20720 : PairBound 9 := { available := 162, camps := [{ cop := 5, region := 387, targets := 64 }], pairs := [(0,6),(1,6),(3,0),(4,0)], upper := (rows 35 259 13 88 148 96 226 162 418), lower := (rows 35 259 13 88 148 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 20 111 67 131 259), good := (rows 482 482 508 120 188 96 96 128 256) }] }

theorem u20720 : Upper (D 7) (R 7) [34,257,9,80,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20720 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20721 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 323, targets := 128 }], pairs := [(0,7),(1,7),(3,0),(4,0)], upper := (rows 35 259 13 88 148 160 98 226 354), lower := (rows 35 259 13 88 148 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 20 183 67 131 259), good := (rows 482 482 508 120 188 160 64 160 256) }] }

theorem u20721 : Upper (D 7) (R 7) [34,257,9,80,132,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20721 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20722 : PairBound 9 := { available := 196, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 13 88 176 34 196 196 452), lower := (rows 35 259 13 88 176 34 64 128 256), losses := [] }

theorem u20722 : Upper (D 7) (R 7) [34,257,9,80,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20722 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20723 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 216, targets := 1 },{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5),(3,0),(4,0)], upper := (rows 35 259 13 88 176 36 194 194 450), lower := (rows 35 259 13 88 176 36 64 128 256), losses := [] }

theorem u20723 : Upper (D 7) (R 7) [34,257,9,80,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20723 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20724 : Route 9 := (fun mask => (mask,id))

def c20724 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u20724 : Upper (D 7) (R 7) [34,257,9,80,160,64] 13 := by
  apply FastRouting.sound _ _ [34,257,9,80,160,64] 13 (by decide) (choices 1) [2,4,128] r20724 c20724
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5853
  · exact u5854
  · exact u5855

def b20725 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 259 13 88 176 160 70 198 326), lower := (rows 35 259 13 88 176 160 64 128 256), losses := [] }

theorem u20725 : Upper (D 7) (R 7) [34,257,9,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20725 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20726 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 45, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 35 259 13 104 82 36 208 144 400), lower := (rows 35 259 13 104 82 36 64 128 256), losses := [] }

theorem u20726 : Upper (D 7) (R 7) [34,257,9,96,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20726 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20727 : PairBound 9 := { available := 132, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 259 13 104 82 48 196 132 388), lower := (rows 35 259 13 104 82 48 64 128 256), losses := [] }

theorem u20727 : Upper (D 7) (R 7) [34,257,9,96,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20727 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20728 : Route 9 := (fun mask => (mask,id))

def c20728 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u20728 : Upper (D 7) (R 7) [34,257,9,96,66,128] 13 := by
  apply FastRouting.sound _ _ [34,257,9,96,66,128] 13 (by decide) (choices 1) [4,16,128] r20728 c20728
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5856
  · exact u5857
  · exact u5858

def b20729 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 216, targets := 1 },{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5),(3,0),(4,0)], upper := (rows 35 259 13 104 146 36 208 208 464), lower := (rows 35 259 13 104 146 36 64 128 256), losses := [] }

theorem u20729 : Upper (D 7) (R 7) [34,257,9,96,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20729 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20730 : PairBound 9 := { available := 196, camps := [{ cop := 0, region := 204, targets := 2 },{ cop := 2, region := 450, targets := 32 }], pairs := [(1,5),(2,1),(3,1)], upper := (rows 35 259 13 104 146 48 196 196 452), lower := (rows 35 259 13 104 146 48 64 128 256), losses := [] }

theorem u20730 : Upper (D 7) (R 7) [34,257,9,96,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20730 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20731 : PairBound 9 := { available := 148, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 35 259 13 104 146 96 212 148 404), lower := (rows 35 259 13 104 146 96 64 128 256), losses := [] }

theorem u20731 : Upper (D 7) (R 7) [34,257,9,96,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20731 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20732 : Route 9 := (fun mask => (mask,id))

def c20732 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20732 : Upper (D 7) (R 7) [34,257,9,96,130,128] 13 := by
  apply FastRouting.sound _ _ [34,257,9,96,130,128] 13 (by decide) (choices 1) [4,16] r20732 c20732
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5859
  · exact u5860

def b20733 : PairBound 9 := { available := 208, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 13 104 148 34 208 208 464), lower := (rows 35 259 13 104 148 34 64 128 256), losses := [] }

theorem u20733 : Upper (D 7) (R 7) [34,257,9,96,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20733 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20734 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 0, region := 200, targets := 1 }], pairs := [(1,5),(3,0),(4,5)], upper := (rows 35 259 13 104 148 48 194 194 450), lower := (rows 35 259 13 104 148 48 64 128 256), losses := [] }

theorem u20734 : Upper (D 7) (R 7) [34,257,9,96,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20734 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20735 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 35 259 13 104 148 96 210 146 402), lower := (rows 35 259 13 104 148 96 64 128 256), losses := [] }

theorem u20735 : Upper (D 7) (R 7) [34,257,9,96,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20735 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20736 : Route 9 := (fun mask => (mask,id))

def c20736 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20736 : Upper (D 7) (R 7) [34,257,9,96,132,128] 13 := by
  apply FastRouting.sound _ _ [34,257,9,96,132,128] 13 (by decide) (choices 1) [2,16] r20736 c20736
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5861
  · exact u5862

def b20737 : PairBound 9 := { available := 148, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 13 104 208 34 212 148 404), lower := (rows 35 259 13 104 208 34 64 128 256), losses := [] }

theorem u20737 : Upper (D 7) (R 7) [34,257,9,96,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20737 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20738 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 216, targets := 1 },{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5),(3,0),(4,0)], upper := (rows 35 259 13 104 208 36 210 146 402), lower := (rows 35 259 13 104 208 36 64 128 256), losses := [] }

theorem u20738 : Upper (D 7) (R 7) [34,257,9,96,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20738 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20739 : PairBound 9 := { available := 134, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 259 13 104 208 48 198 134 390), lower := (rows 35 259 13 104 208 48 64 128 256), losses := [] }

theorem u20739 : Upper (D 7) (R 7) [34,257,9,96,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20739 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20740 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 4, region := 40, targets := 3 }], pairs := [(1,5),(3,0),(3,1),(4,5)], upper := (rows 35 259 13 104 208 160 86 150 278), lower := (rows 35 259 13 104 208 160 64 128 256), losses := [] }

theorem u20740 : Upper (D 7) (R 7) [34,257,9,96,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20740 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20741 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 204, targets := 2 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1)], upper := (rows 35 259 13 200 22 48 224 224 480), lower := (rows 35 259 13 200 22 48 64 128 256), losses := [] }

theorem u20741 : Upper (D 7) (R 7) [34,257,9,192,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20741 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20742 : Route 9 := (fun mask => (mask,id))

def c20742 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u20742 : Upper (D 7) (R 7) [34,257,9,192,6,64] 13 := by
  apply FastRouting.sound _ _ [34,257,9,192,6,64] 13 (by decide) (choices 1) [16,32,128] r20742 c20742
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5863
  · exact u5864
  · exact u5865

def b20743 : PairBound 9 := { available := 208, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 13 200 52 34 208 208 464), lower := (rows 35 259 13 200 52 34 64 128 256), losses := [] }

theorem u20743 : Upper (D 7) (R 7) [34,257,9,192,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20743 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20744 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 259 13 200 52 48 194 194 450), lower := (rows 35 259 13 200 52 48 64 128 256), losses := [] }

theorem u20744 : Upper (D 7) (R 7) [34,257,9,192,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20744 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20745 : PairBound 9 := { available := 146, camps := [{ cop := 4, region := 387, targets := 64 }], pairs := [(0,6),(1,6),(4,0),(4,1)], upper := (rows 35 259 13 200 52 96 210 146 402), lower := (rows 35 259 13 200 52 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 104 64 128 256), good := (rows 34 258 60 232 52 96 96 128 256) },{ target := 1, region := (rows 1 0 4 8 20 104 64 128 256), good := (rows 33 257 61 232 52 96 96 128 256) }] }

theorem u20745 : Upper (D 7) (R 7) [34,257,9,192,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20745 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20746 : Route 9 := (fun mask => (mask,id))

def c20746 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u20746 : Upper (D 7) (R 7) [34,257,9,192,66,4] 13 := by
  apply FastRouting.sound _ _ [34,257,9,192,66,4] 13 (by decide) (choices 1) [16,32,128] r20746 c20746
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5866
  · exact u5867
  · exact u5868

def b20747 : PairBound 9 := { available := 164, camps := [{ cop := 0, region := 204, targets := 2 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1)], upper := (rows 35 259 13 200 82 48 228 164 420), lower := (rows 35 259 13 200 82 48 64 128 256), losses := [] }

theorem u20747 : Upper (D 7) (R 7) [34,257,9,192,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20747 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20748 : Route 9 := (fun mask => (mask,id))

def c20748 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20748 : Upper (D 7) (R 7) [34,257,9,192,66,128] 13 := by
  apply FastRouting.sound _ _ [34,257,9,192,66,128] 13 (by decide) (choices 1) [4,16,32] r20748 c20748
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5869
  · exact u5870
  · exact u5871

def b20749 : PairBound 9 := { available := 176, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 13 200 84 34 240 176 432), lower := (rows 35 259 13 200 84 34 64 128 256), losses := [] }

theorem u20749 : Upper (D 7) (R 7) [34,257,9,192,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20749 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20750 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 419, targets := 64 },{ cop := 0, region := 200, targets := 1 }], pairs := [(0,6),(1,6),(3,0)], upper := (rows 35 259 13 200 84 48 226 162 418), lower := (rows 35 259 13 200 84 48 64 128 256), losses := [] }

theorem u20750 : Upper (D 7) (R 7) [34,257,9,192,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20750 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20751 : Route 9 := (fun mask => (mask,id))

def c20751 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20751 : Upper (D 7) (R 7) [34,257,9,192,68,128] 13 := by
  apply FastRouting.sound _ _ [34,257,9,192,68,128] 13 (by decide) (choices 1) [2,16,32] r20751 c20751
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5872
  · exact u5873
  · exact u5874

def b20752 : PairBound 9 := { available := 148, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 13 200 112 34 212 148 404), lower := (rows 35 259 13 200 112 34 64 128 256), losses := [] }

theorem u20752 : Upper (D 7) (R 7) [34,257,9,192,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20752 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20753 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 216, targets := 1 },{ cop := 4, region := 387, targets := 64 }], pairs := [(0,6),(3,0),(4,0)], upper := (rows 35 259 13 200 112 36 210 146 402), lower := (rows 35 259 13 200 112 36 64 128 256), losses := [] }

theorem u20753 : Upper (D 7) (R 7) [34,257,9,192,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20753 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20754 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 259 13 200 112 48 198 134 390), lower := (rows 35 259 13 200 112 48 64 128 256), losses := [] }

theorem u20754 : Upper (D 7) (R 7) [34,257,9,192,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20754 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20755 : Route 9 := (fun mask => (mask,id))

def c20755 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20755 : Upper (D 7) (R 7) [34,257,9,192,96,128] 13 := by
  apply FastRouting.sound _ _ [34,257,9,192,96,128] 13 (by decide) (choices 1) [2,4,16] r20755 c20755
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5875
  · exact u5876
  · exact u5877

def b20756 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 387, targets := 64 },{ cop := 0, region := 208, targets := 2 }], pairs := [(0,6),(1,6),(3,1),(4,1)], upper := (rows 35 259 14 28 81 96 224 160 416), lower := (rows 35 259 14 28 81 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 19 511 511 511 511), good := (rows 497 497 508 508 497 480 480 480 480) }] }

theorem u20756 : Upper (D 7) (R 7) [34,257,10,20,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20756 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20757 : Route 9 := (fun mask => (mask,id))

def c20757 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u20757 : Upper (D 7) (R 7) [34,257,10,20,65,128] 13 := by
  apply FastRouting.sound _ _ [34,257,10,20,65,128] 13 (by decide) (choices 1) [32,128] r20757 c20757
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5878
  · exact u5879

def b20758 : PairBound 9 := { available := 192, camps := [{ cop := 8, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 35 259 14 28 112 33 192 192 448), lower := (rows 35 259 14 28 112 33 64 128 256), losses := [] }

theorem u20758 : Upper (D 7) (R 7) [34,257,10,20,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20758 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20759 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(3,6)], upper := (rows 35 259 14 28 112 96 193 129 385), lower := (rows 35 259 14 28 112 96 64 128 256), losses := [] }

theorem u20759 : Upper (D 7) (R 7) [34,257,10,20,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20759 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u20759
end Delivery.IrregularNine14.P07

import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0232
import IrregularNine14P06C0233

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b31680 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 25, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 38 388 56 19 101 69 197 325), lower := (rows 11 38 388 56 19 32 64 128 256), losses := [] }

theorem u31680 : Upper (D 6) (R 6) [10,36,384,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31680 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31681 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 25, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 388 56 21 99 67 195 323), lower := (rows 11 38 388 56 21 32 64 128 256), losses := [] }

theorem u31681 : Upper (D 6) (R 6) [10,36,384,48,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31681 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31682 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 25, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 388 56 22 97 65 193 321), lower := (rows 11 38 388 56 22 32 64 128 256), losses := [] }

theorem u31682 : Upper (D 6) (R 6) [10,36,384,48,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31682 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31683 : Route 9 := (fun mask => (mask,id))

def c31683 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31683 : Upper (D 6) (R 6) [10,36,384,48,65] 13 := by
  apply FastRouting.sound _ _ [10,36,384,48,65] 13 (by decide) (choices 1) [1,2,4,64] r31683 c31683
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13933
  · exact u13934
  · exact u13935
  · exact u13936

def b31684 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 0, region := 452, targets := 2 }], pairs := [(2,1),(2,5),(4,5)], upper := (rows 11 38 388 56 82 101 69 197 325), lower := (rows 11 38 388 56 82 32 64 128 256), losses := [] }

theorem u31684 : Upper (D 6) (R 6) [10,36,384,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31684 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31685 : Route 9 := (fun mask => (mask,id))

def c31685 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31685 : Upper (D 6) (R 6) [10,36,384,48,68] 13 := by
  apply FastRouting.sound _ _ [10,36,384,48,68] 13 (by decide) (choices 1) [1,2,64] r31685 c31685
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13937
  · exact u13938
  · exact u13939

def b31686 : PairBound 9 := { available := 116, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 38 388 73 19 116 116 244 372), lower := (rows 11 38 388 73 19 32 64 128 256), losses := [] }

theorem u31686 : Upper (D 6) (R 6) [10,36,384,65,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31686 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31687 : Route 9 := (fun mask => (mask,id))

def c31687 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31687 : Upper (D 6) (R 6) [10,36,384,65,5] 13 := by
  apply FastRouting.sound _ _ [10,36,384,65,5] 13 (by decide) (choices 1) [2,16,64] r31687 c31687
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13940
  · exact u13941
  · exact u13942

def b31688 : PairBound 9 := { available := 113, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 11 38 388 73 22 113 113 241 369), lower := (rows 11 38 388 73 22 32 64 128 256), losses := [] }

theorem u31688 : Upper (D 6) (R 6) [10,36,384,65,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31688 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31689 : Route 9 := (fun mask => (mask,id))

def c31689 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31689 : Upper (D 6) (R 6) [10,36,384,65,33] 13 := by
  apply FastRouting.sound _ _ [10,36,384,65,33] 13 (by decide) (choices 1) [2,4,16,64] r31689 c31689
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13943
  · exact u13944
  · exact u13945
  · exact u13946

def b31690 : PairBound 9 := { available := 85, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 38 388 73 50 117 85 213 341), lower := (rows 11 38 388 73 50 32 64 128 256), losses := [] }

theorem u31690 : Upper (D 6) (R 6) [10,36,384,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31690 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31691 : PairBound 9 := { available := 83, camps := [{ cop := 1, region := 16, targets := 65 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,6)], upper := (rows 11 38 388 73 52 115 83 211 339), lower := (rows 11 38 388 73 52 32 64 128 256), losses := [] }

theorem u31691 : Upper (D 6) (R 6) [10,36,384,65,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31691 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31692 : PairBound 9 := { available := 54, camps := [{ cop := 3, region := 16, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 11 38 388 73 81 54 118 182 310), lower := (rows 11 38 388 73 81 32 64 128 256), losses := [] }

theorem u31692 : Upper (D 6) (R 6) [10,36,384,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31692 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31693 : PairBound 9 := { available := 53, camps := [{ cop := 4, region := 9, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 38 388 73 82 53 117 181 309), lower := (rows 11 38 388 73 82 32 64 128 256), losses := [] }

theorem u31693 : Upper (D 6) (R 6) [10,36,384,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31693 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31694 : Route 9 := (fun mask => (mask,id))

def c31694 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31694 : Upper (D 6) (R 6) [10,36,384,65,68] 13 := by
  apply FastRouting.sound _ _ [10,36,384,65,68] 13 (by decide) (choices 1) [1,2,16] r31694 c31694
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13947
  · exact u13948
  · exact u13949

def r31695 : Route 9 := (fun mask => (mask,id))

def c31695 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31695 : Upper (D 6) (R 6) [10,36,384,65,96] 13 := by
  apply FastRouting.sound _ _ [10,36,384,65,96] 13 (by decide) (choices 1) [1,2,4,16] r31695 c31695
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13950
  · exact u13951
  · exact u13952
  · exact u13953

def b31696 : PairBound 9 := { available := 113, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 4, region := 484, targets := 2 }], pairs := [(2,1),(4,5),(4,6)], upper := (rows 11 38 388 76 19 113 113 241 369), lower := (rows 11 38 388 76 19 32 64 128 256), losses := [] }

theorem u31696 : Upper (D 6) (R 6) [10,36,384,68,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31696 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31697 : Route 9 := (fun mask => (mask,id))

def c31697 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31697 : Upper (D 6) (R 6) [10,36,384,68,33] 13 := by
  apply FastRouting.sound _ _ [10,36,384,68,33] 13 (by decide) (choices 1) [1,2,16,64] r31697 c31697
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13954
  · exact u13955
  · exact u13956
  · exact u13957

def b31698 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 38 388 76 50 113 81 209 337), lower := (rows 11 38 388 76 50 32 64 128 256), losses := [] }

theorem u31698 : Upper (D 6) (R 6) [10,36,384,68,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31698 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31699 : PairBound 9 := { available := 51, camps := [{ cop := 4, region := 422, targets := 64 },{ cop := 0, region := 112, targets := 4 }], pairs := [(1,6),(2,6),(4,2)], upper := (rows 11 38 388 76 81 51 115 179 307), lower := (rows 11 38 388 76 81 32 64 128 256), losses := [] }

theorem u31699 : Upper (D 6) (R 6) [10,36,384,68,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31699 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31700 : Route 9 := (fun mask => (mask,id))

def c31700 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31700 : Upper (D 6) (R 6) [10,36,384,68,66] 13 := by
  apply FastRouting.sound _ _ [10,36,384,68,66] 13 (by decide) (choices 1) [1,16] r31700 c31700
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u13958
  · exact u13959

def r31701 : Route 9 := (fun mask => (mask,id))

def c31701 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31701 : Upper (D 6) (R 6) [10,36,384,68,96] 13 := by
  apply FastRouting.sound _ _ [10,36,384,68,96] 13 (by decide) (choices 1) [1,2,16] r31701 c31701
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13960
  · exact u13961
  · exact u13962

def b31702 : PairBound 9 := { available := 101, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 38 388 88 19 101 101 229 357), lower := (rows 11 38 388 88 19 32 64 128 256), losses := [] }

theorem u31702 : Upper (D 6) (R 6) [10,36,384,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31702 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31703 : Route 9 := (fun mask => (mask,id))

def c31703 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31703 : Upper (D 6) (R 6) [10,36,384,80,5] 13 := by
  apply FastRouting.sound _ _ [10,36,384,80,5] 13 (by decide) (choices 1) [1,2,64] r31703 c31703
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13963
  · exact u13964
  · exact u13965

def b31704 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 11 38 388 88 22 97 97 225 353), lower := (rows 11 38 388 88 22 32 64 128 256), losses := [] }

theorem u31704 : Upper (D 6) (R 6) [10,36,384,80,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31704 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31705 : Route 9 := (fun mask => (mask,id))

def c31705 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31705 : Upper (D 6) (R 6) [10,36,384,80,33] 13 := by
  apply FastRouting.sound _ _ [10,36,384,80,33] 13 (by decide) (choices 1) [1,2,4,64] r31705 c31705
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13966
  · exact u13967
  · exact u13968
  · exact u13969

def b31706 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 38 388 88 50 101 69 197 325), lower := (rows 11 38 388 88 50 32 64 128 256), losses := [] }

theorem u31706 : Upper (D 6) (R 6) [10,36,384,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31706 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31707 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 16, targets := 65 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,6)], upper := (rows 11 38 388 88 52 99 67 195 323), lower := (rows 11 38 388 88 52 32 64 128 256), losses := [] }

theorem u31707 : Upper (D 6) (R 6) [10,36,384,80,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31707 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31708 : PairBound 9 := { available := 39, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 38 388 88 81 39 103 167 295), lower := (rows 11 38 388 88 81 32 64 128 256), losses := [] }

theorem u31708 : Upper (D 6) (R 6) [10,36,384,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31708 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31709 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 9, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 38 388 88 82 37 101 165 293), lower := (rows 11 38 388 88 82 32 64 128 256), losses := [] }

theorem u31709 : Upper (D 6) (R 6) [10,36,384,80,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31709 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31710 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 38 388 88 84 35 99 163 291), lower := (rows 11 38 388 88 84 32 64 128 256), losses := [] }

theorem u31710 : Upper (D 6) (R 6) [10,36,384,80,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31710 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31711 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 38 388 88 112 39 71 135 263), lower := (rows 11 38 388 88 112 32 64 128 256), losses := [] }

theorem u31711 : Upper (D 6) (R 6) [10,36,384,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31711 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31712 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 0, region := 468, targets := 32 }], pairs := [(2,5),(4,2),(4,6)], upper := (rows 11 38 388 104 19 117 85 213 341), lower := (rows 11 38 388 104 19 32 64 128 256), losses := [] }

theorem u31712 : Upper (D 6) (R 6) [10,36,384,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31712 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31713 : Route 9 := (fun mask => (mask,id))

def c31713 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31713 : Upper (D 6) (R 6) [10,36,384,96,5] 13 := by
  apply FastRouting.sound _ _ [10,36,384,96,5] 13 (by decide) (choices 1) [1,2,16,64] r31713 c31713
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13970
  · exact u13971
  · exact u13972
  · exact u13973

def b31714 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 11 38 388 104 22 113 81 209 337), lower := (rows 11 38 388 104 22 32 64 128 256), losses := [] }

theorem u31714 : Upper (D 6) (R 6) [10,36,384,96,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31714 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31715 : PairBound 9 := { available := 23, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(2,5),(4,5)], upper := (rows 11 38 388 104 81 55 87 151 279), lower := (rows 11 38 388 104 81 32 64 128 256), losses := [] }

theorem u31715 : Upper (D 6) (R 6) [10,36,384,96,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31715 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31716 : Route 9 := (fun mask => (mask,id))

def c31716 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31716 : Upper (D 6) (R 6) [10,36,384,96,66] 13 := by
  apply FastRouting.sound _ _ [10,36,384,96,66] 13 (by decide) (choices 1) [1,4,16] r31716 c31716
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13974
  · exact u13975
  · exact u13976

def r31717 : Route 9 := (fun mask => (mask,id))

def c31717 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31717 : Upper (D 6) (R 6) [10,36,384,96,68] 13 := by
  apply FastRouting.sound _ _ [10,36,384,96,68] 13 (by decide) (choices 1) [1,2,16] r31717 c31717
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13977
  · exact u13978
  · exact u13979

def b31718 : PairBound 9 := { available := 452, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 2, region := 18, targets := 1 }], pairs := [(1,0),(2,1),(3,1)], upper := (rows 11 50 37 73 22 484 452 452 452), lower := (rows 11 50 37 73 22 32 64 128 256), losses := [] }

theorem u31718 : Upper (D 6) (R 6) [10,48,33,65,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31718 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31719 : PairBound 9 := { available := 388, camps := [{ cop := 4, region := 9, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 50 37 73 82 420 452 388 388), lower := (rows 11 50 37 73 82 32 64 128 256), losses := [] }

theorem u31719 : Upper (D 6) (R 6) [10,48,33,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31719 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31720 : PairBound 9 := { available := 390, camps := [{ cop := 2, region := 466, targets := 1 },{ cop := 0, region := 420, targets := 64 }], pairs := [(1,0),(2,6),(4,0)], upper := (rows 11 50 37 73 84 422 454 390 390), lower := (rows 11 50 37 73 84 32 64 128 256), losses := [] }

theorem u31720 : Upper (D 6) (R 6) [10,48,33,65,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31720 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31721 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 364, targets := 2 },{ cop := 2, region := 466, targets := 1 }], pairs := [(1,0),(2,1),(3,1)], upper := (rows 11 50 37 73 146 356 324 452 324), lower := (rows 11 50 37 73 146 32 64 128 256), losses := [] }

theorem u31721 : Upper (D 6) (R 6) [10,48,33,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31721 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31722 : Route 9 := (fun mask => (mask,id))

def c31722 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u31722 : Upper (D 6) (R 6) [10,48,33,65,132] 13 := by
  apply FastRouting.sound _ _ [10,48,33,65,132] 13 (by decide) (choices 1) [2,4,64,256] r31722 c31722
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13980
  · exact u13981
  · exact u13982
  · exact u13983

def b31723 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 466, targets := 1 },{ cop := 0, region := 292, targets := 64 }], pairs := [(1,0),(2,6),(4,0)], upper := (rows 11 50 37 73 208 294 326 390 262), lower := (rows 11 50 37 73 208 32 64 128 256), losses := [] }

theorem u31723 : Upper (D 6) (R 6) [10,48,33,65,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31723 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31724 : Route 9 := (fun mask => (mask,id))

def c31724 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31724 : Upper (D 6) (R 6) [10,48,33,65,384] 13 := by
  apply FastRouting.sound _ _ [10,48,33,65,384] 13 (by decide) (choices 1) [2,4,64] r31724 c31724
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13984
  · exact u13985
  · exact u13986

def b31725 : PairBound 9 := { available := 452, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 50 37 76 19 484 452 452 452), lower := (rows 11 50 37 76 19 32 64 128 256), losses := [] }

theorem u31725 : Upper (D 6) (R 6) [10,48,33,68,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31725 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31726 : PairBound 9 := { available := 450, camps := [{ cop := 2, region := 16, targets := 34 },{ cop := 2, region := 18, targets := 64 }], pairs := [(1,6),(4,1),(4,5)], upper := (rows 11 50 37 76 21 482 450 450 450), lower := (rows 11 50 37 76 21 32 64 128 256), losses := [] }

theorem u31726 : Upper (D 6) (R 6) [10,48,33,68,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31726 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31727 : PairBound 9 := { available := 449, camps := [{ cop := 2, region := 18, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 50 37 76 22 481 449 449 449), lower := (rows 11 50 37 76 22 32 64 128 256), losses := [] }

theorem u31727 : Upper (D 6) (R 6) [10,48,33,68,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31727 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31728 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c31728 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u31728 : Upper (D 6) (R 6) [10,48,33,68,65] 13 := by
  apply FastRouting.sound _ _ [10,48,33,68,65] 13 (by decide) (choices 1) [2,4,128] r31728 c31728
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13987
  · exact u13988
  · exact u13989

def b31729 : PairBound 9 := { available := 389, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 0, region := 420, targets := 64 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 11 50 37 76 82 421 453 389 389), lower := (rows 11 50 37 76 82 32 64 128 256), losses := [] }

theorem u31729 : Upper (D 6) (R 6) [10,48,33,68,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31729 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31730 : PairBound 9 := { available := 387, camps := [{ cop := 3, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 50 37 76 84 419 451 387 387), lower := (rows 11 50 37 76 84 32 64 128 256), losses := [] }

theorem u31730 : Upper (D 6) (R 6) [10,48,33,68,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31730 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31731 : Route 9 := (fun mask => (mask,id))

def c31731 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u31731 : Upper (D 6) (R 6) [10,48,33,68,129] 13 := by
  apply FastRouting.sound _ _ [10,48,33,68,129] 13 (by decide) (choices 1) [2,4,64,256] r31731 c31731
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13990
  · exact u13991
  · exact u13992
  · exact u13993

def b31732 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 364, targets := 2 },{ cop := 2, region := 328, targets := 32 }], pairs := [(2,1),(3,1),(3,5)], upper := (rows 11 50 37 76 146 357 325 453 325), lower := (rows 11 50 37 76 146 32 64 128 256), losses := [] }

theorem u31732 : Upper (D 6) (R 6) [10,48,33,68,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31732 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31733 : Route 9 := (fun mask => (mask,id))

def c31733 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u31733 : Upper (D 6) (R 6) [10,48,33,68,132] 13 := by
  apply FastRouting.sound _ _ [10,48,33,68,132] 13 (by decide) (choices 1) [1,2,64,256] r31733 c31733
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13994
  · exact u13995
  · exact u13996
  · exact u13997

def r31734 : Route 9 := (fun mask => (mask,id))

def c31734 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31734 : Upper (D 6) (R 6) [10,48,33,68,192] 13 := by
  apply FastRouting.sound _ _ [10,48,33,68,192] 13 (by decide) (choices 1) [1,2,4,256] r31734 c31734
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13998
  · exact u13999
  · exact u14000
  · exact u14001

def r31735 : Route 9 := (fun mask => (mask,id))

def c31735 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31735 : Upper (D 6) (R 6) [10,48,33,68,384] 13 := by
  apply FastRouting.sound _ _ [10,48,33,68,384] 13 (by decide) (choices 1) [1,2,4,64] r31735 c31735
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14002
  · exact u14003
  · exact u14004
  · exact u14005

def b31736 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 2, region := 18, targets := 1 }], pairs := [(1,0),(2,1),(3,1)], upper := (rows 11 50 37 137 22 356 324 452 324), lower := (rows 11 50 37 137 22 32 64 128 256), losses := [] }

theorem u31736 : Upper (D 6) (R 6) [10,48,33,129,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31736 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31737 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 2, region := 338, targets := 1 }], pairs := [(1,0),(2,1),(3,1)], upper := (rows 11 50 37 137 82 356 324 452 324), lower := (rows 11 50 37 137 82 32 64 128 256), losses := [] }

theorem u31737 : Upper (D 6) (R 6) [10,48,33,129,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31737 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31738 : Route 9 := (fun mask => (mask,id))

def c31738 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u31738 : Upper (D 6) (R 6) [10,48,33,129,68] 13 := by
  apply FastRouting.sound _ _ [10,48,33,129,68] 13 (by decide) (choices 1) [2,4,64,256] r31738 c31738
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14006
  · exact u14007
  · exact u14008
  · exact u14009

def b31739 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 2, region := 338, targets := 1 }], pairs := [(1,0),(2,1),(3,1)], upper := (rows 11 50 37 137 274 100 68 196 324), lower := (rows 11 50 37 137 274 32 64 128 256), losses := [] }

theorem u31739 : Upper (D 6) (R 6) [10,48,33,129,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31739 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u31739
end Delivery.IrregularNine14.P06

import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0133
import IrregularNine14P06C0134

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m25800_2 : Upper (D 6) (R 6) [40,80,384,68,36,2,2] 13 :=
  permutation_upper _ _ _ [40,80,384,68,36,1,1] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8019

def r25800 : Route 9 := (fun mask => (mask,id))

def c25800 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25800 : Upper (D 6) (R 6) [40,80,384,68,36,2] 13 := by
  apply FastRouting.sound _ _ [40,80,384,68,36,2] 13 (by decide) (choices 1) [1,2] r25800 c25800
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8020
  · exact m25800_2

def b25801 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 41 98 133 14 81 34 340 404 276), lower := (rows 41 98 133 14 81 34 64 128 256), losses := [] }

theorem u25801 : Upper (D 6) (R 6) [40,96,129,6,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25801 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25802 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 338, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 98 133 14 81 36 338 402 274), lower := (rows 41 98 133 14 81 36 64 128 256), losses := [] }

theorem u25802 : Upper (D 6) (R 6) [40,96,129,6,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25802 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25803 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 41 98 133 14 81 48 326 390 262), lower := (rows 41 98 133 14 81 48 64 128 256), losses := [] }

theorem u25803 : Upper (D 6) (R 6) [40,96,129,6,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25803 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25804 : Route 9 := (fun mask => (mask,id))

def c25804 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25804 : Upper (D 6) (R 6) [40,96,129,6,65,256] 13 := by
  apply FastRouting.sound _ _ [40,96,129,6,65,256] 13 (by decide) (choices 1) [2,4,16] r25804 c25804
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8021
  · exact u8022
  · exact u8023

def b25805 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 133 14 84 33 338 402 274), lower := (rows 41 98 133 14 84 33 64 128 256), losses := [] }

theorem u25805 : Upper (D 6) (R 6) [40,96,129,6,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25805 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25806 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 41 98 133 14 84 34 337 401 273), lower := (rows 41 98 133 14 84 34 64 128 256), losses := [] }

theorem u25806 : Upper (D 6) (R 6) [40,96,129,6,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25806 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25807 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 41 98 133 14 84 48 323 387 259), lower := (rows 41 98 133 14 84 48 64 128 256), losses := [] }

theorem u25807 : Upper (D 6) (R 6) [40,96,129,6,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25807 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25808 : Route 9 := (fun mask => (mask,id))

def c25808 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25808 : Upper (D 6) (R 6) [40,96,129,6,68,256] 13 := by
  apply FastRouting.sound _ _ [40,96,129,6,68,256] 13 (by decide) (choices 1) [1,2,16] r25808 c25808
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8024
  · exact u8025
  · exact u8026

def b25809 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 41 98 133 14 273 34 84 212 340), lower := (rows 41 98 133 14 273 34 64 128 256), losses := [] }

theorem u25809 : Upper (D 6) (R 6) [40,96,129,6,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25809 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25810 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 338, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 98 133 14 273 36 82 210 338), lower := (rows 41 98 133 14 273 36 64 128 256), losses := [] }

theorem u25810 : Upper (D 6) (R 6) [40,96,129,6,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25810 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25811 : PairBound 9 := { available := 70, camps := [], pairs := [(1,0),(3,0)], upper := (rows 41 98 133 14 273 48 70 198 326), lower := (rows 41 98 133 14 273 48 64 128 256), losses := [{ target := 0, region := (rows 0 3 4 12 16 48 76 140 268), good := (rows 490 98 462 462 306 48 64 128 256) }] }

theorem u25811 : Upper (D 6) (R 6) [40,96,129,6,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25811 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25812 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 98 133 14 273 96 86 150 278), lower := (rows 41 98 133 14 273 96 64 128 256), losses := [] }

theorem u25812 : Upper (D 6) (R 6) [40,96,129,6,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25812 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25813 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 133 14 274 33 84 212 340), lower := (rows 41 98 133 14 274 33 64 128 256), losses := [] }

theorem u25813 : Upper (D 6) (R 6) [40,96,129,6,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25813 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25814 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 338, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 98 133 14 274 36 81 209 337), lower := (rows 41 98 133 14 274 36 64 128 256), losses := [] }

theorem u25814 : Upper (D 6) (R 6) [40,96,129,6,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25814 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25815 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 196, targets := 34 }], pairs := [(2,1),(2,5)], upper := (rows 41 98 133 14 274 48 69 197 325), lower := (rows 41 98 133 14 274 48 64 128 256), losses := [] }

theorem u25815 : Upper (D 6) (R 6) [40,96,129,6,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25815 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25816 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 98 133 14 274 96 85 149 277), lower := (rows 41 98 133 14 274 96 64 128 256), losses := [] }

theorem u25816 : Upper (D 6) (R 6) [40,96,129,6,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25816 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25817 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 133 14 276 33 82 210 338), lower := (rows 41 98 133 14 276 33 64 128 256), losses := [] }

theorem u25817 : Upper (D 6) (R 6) [40,96,129,6,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25817 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25818 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 41 98 133 14 276 34 81 209 337), lower := (rows 41 98 133 14 276 34 64 128 256), losses := [] }

theorem u25818 : Upper (D 6) (R 6) [40,96,129,6,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25818 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25819 : Route 9 := (fun mask => (mask,id))

def c25819 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25819 : Upper (D 6) (R 6) [40,96,129,6,260,16] 13 := by
  apply FastRouting.sound _ _ [40,96,129,6,260,16] 13 (by decide) (choices 1) [1,2] r25819 c25819
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8027
  · exact u8028

def b25820 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 98 133 14 276 96 83 147 275), lower := (rows 41 98 133 14 276 96 64 128 256), losses := [] }

theorem u25820 : Upper (D 6) (R 6) [40,96,129,6,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25820 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25821 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 133 14 336 33 86 150 278), lower := (rows 41 98 133 14 336 33 64 128 256), losses := [] }

theorem u25821 : Upper (D 6) (R 6) [40,96,129,6,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25821 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25822 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 41 98 133 14 336 34 85 149 277), lower := (rows 41 98 133 14 336 34 64 128 256), losses := [] }

theorem u25822 : Upper (D 6) (R 6) [40,96,129,6,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25822 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25823 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 338, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 98 133 14 336 36 83 147 275), lower := (rows 41 98 133 14 336 36 64 128 256), losses := [] }

theorem u25823 : Upper (D 6) (R 6) [40,96,129,6,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25823 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25824 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 141, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 41 98 133 14 336 48 71 135 263), lower := (rows 41 98 133 14 336 48 64 128 256), losses := [] }

theorem u25824 : Upper (D 6) (R 6) [40,96,129,6,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25824 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25825 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 43, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 41 98 133 25 84 34 326 390 262), lower := (rows 41 98 133 25 84 34 64 128 256), losses := [] }

theorem u25825 : Upper (D 6) (R 6) [40,96,129,17,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25825 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25826 : PairBound 9 := { available := 258, camps := [{ cop := 4, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 98 133 25 84 36 322 386 258), lower := (rows 41 98 133 25 84 36 64 128 256), losses := [] }

theorem u25826 : Upper (D 6) (R 6) [40,96,129,17,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25826 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25827 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 370, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 41 98 133 25 84 288 70 134 262), lower := (rows 41 98 133 25 84 288 64 128 256), losses := [] }

theorem u25827 : Upper (D 6) (R 6) [40,96,129,17,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25827 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25828 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 98 133 25 274 34 68 196 324), lower := (rows 41 98 133 25 274 34 64 128 256), losses := [] }

theorem u25828 : Upper (D 6) (R 6) [40,96,129,17,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25828 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25829 : Route 9 := (fun mask => (mask,id))

def c25829 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25829 : Upper (D 6) (R 6) [40,96,129,17,258,4] 13 := by
  apply FastRouting.sound _ _ [40,96,129,17,258,4] 13 (by decide) (choices 1) [2,4] r25829 c25829
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8029
  · exact u8030

def b25830 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 98 133 25 274 96 70 134 262), lower := (rows 41 98 133 25 274 96 64 128 256), losses := [] }

theorem u25830 : Upper (D 6) (R 6) [40,96,129,17,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25830 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25831 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 370, targets := 1 },{ cop := 6, region := 34, targets := 4 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 41 98 133 25 276 34 70 198 326), lower := (rows 41 98 133 25 276 34 64 128 256), losses := [] }

theorem u25831 : Upper (D 6) (R 6) [40,96,129,17,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25831 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25832 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 98 133 25 276 36 66 194 322), lower := (rows 41 98 133 25 276 36 64 128 256), losses := [] }

theorem u25832 : Upper (D 6) (R 6) [40,96,129,17,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25832 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25833 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 98 133 25 276 96 70 134 262), lower := (rows 41 98 133 25 276 96 64 128 256), losses := [] }

theorem u25833 : Upper (D 6) (R 6) [40,96,129,17,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25833 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25834 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 43, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 41 98 133 25 336 34 70 134 262), lower := (rows 41 98 133 25 336 34 64 128 256), losses := [] }

theorem u25834 : Upper (D 6) (R 6) [40,96,129,17,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25834 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25835 : Route 9 := (fun mask => (mask,id))

def c25835 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25835 : Upper (D 6) (R 6) [40,96,129,17,320,4] 13 := by
  apply FastRouting.sound _ _ [40,96,129,17,320,4] 13 (by decide) (choices 1) [2,4] r25835 c25835
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8031
  · exact u8032

def b25836 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 43, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 41 98 133 26 84 33 326 390 262), lower := (rows 41 98 133 26 84 33 64 128 256), losses := [] }

theorem u25836 : Upper (D 6) (R 6) [40,96,129,18,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25836 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25837 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 41 98 133 26 84 34 325 389 261), lower := (rows 41 98 133 26 84 34 64 128 256), losses := [] }

theorem u25837 : Upper (D 6) (R 6) [40,96,129,18,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25837 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25838 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 421, targets := 64 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,6),(1,0),(2,6)], upper := (rows 41 98 133 26 84 36 323 387 259), lower := (rows 41 98 133 26 84 36 64 128 256), losses := [] }

theorem u25838 : Upper (D 6) (R 6) [40,96,129,18,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25838 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25839 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 421, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 41 98 133 26 84 288 71 135 263), lower := (rows 41 98 133 26 84 288 64 128 256), losses := [] }

theorem u25839 : Upper (D 6) (R 6) [40,96,129,18,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25839 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25840 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 41 98 133 26 273 34 68 196 324), lower := (rows 41 98 133 26 273 34 64 128 256), losses := [] }

theorem u25840 : Upper (D 6) (R 6) [40,96,129,18,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25840 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25841 : Route 9 := (fun mask => (mask,id))

def c25841 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25841 : Upper (D 6) (R 6) [40,96,129,18,257,4] 13 := by
  apply FastRouting.sound _ _ [40,96,129,18,257,4] 13 (by decide) (choices 1) [2,4] r25841 c25841
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8033
  · exact u8034

def b25842 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 98 133 26 273 96 70 134 262), lower := (rows 41 98 133 26 273 96 64 128 256), losses := [] }

theorem u25842 : Upper (D 6) (R 6) [40,96,129,18,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25842 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25843 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 133 26 276 33 70 198 326), lower := (rows 41 98 133 26 276 33 64 128 256), losses := [] }

theorem u25843 : Upper (D 6) (R 6) [40,96,129,18,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25843 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25844 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 41 98 133 26 276 34 69 197 325), lower := (rows 41 98 133 26 276 34 64 128 256), losses := [] }

theorem u25844 : Upper (D 6) (R 6) [40,96,129,18,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25844 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25845 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 66, targets := 4 }], pairs := [(0,1),(0,6),(1,2)], upper := (rows 41 98 133 26 276 36 67 195 323), lower := (rows 41 98 133 26 276 36 64 128 256), losses := [{ target := 1, region := (rows 9 0 4 8 16 52 64 128 256), good := (rows 41 96 165 57 308 36 64 128 256) },{ target := 6, region := (rows 9 2 4 8 16 52 0 128 256), good := (rows 41 34 165 59 308 36 0 128 256) }] }

theorem u25845 : Upper (D 6) (R 6) [40,96,129,18,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25845 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25846 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 98 133 26 276 96 71 135 263), lower := (rows 41 98 133 26 276 96 64 128 256), losses := [] }

theorem u25846 : Upper (D 6) (R 6) [40,96,129,18,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25846 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25847 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 43, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 41 98 133 26 336 33 70 134 262), lower := (rows 41 98 133 26 336 33 64 128 256), losses := [] }

theorem u25847 : Upper (D 6) (R 6) [40,96,129,18,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25847 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25848 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 41 98 133 26 336 34 69 133 261), lower := (rows 41 98 133 26 336 34 64 128 256), losses := [] }

theorem u25848 : Upper (D 6) (R 6) [40,96,129,18,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25848 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25849 : Route 9 := (fun mask => (mask,id))

def c25849 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25849 : Upper (D 6) (R 6) [40,96,129,18,320,4] 13 := by
  apply FastRouting.sound _ _ [40,96,129,18,320,4] 13 (by decide) (choices 1) [1,2,4] r25849 c25849
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8035
  · exact u8036
  · exact u8037

def b25850 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 34, targets := 5 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 41 98 133 28 81 34 326 390 262), lower := (rows 41 98 133 28 81 34 64 128 256), losses := [{ target := 2, region := (rows 9 82 0 8 16 122 64 128 256), good := (rows 41 98 129 59 115 34 98 128 256) }] }

theorem u25850 : Upper (D 6) (R 6) [40,96,129,20,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25850 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25851 : PairBound 9 := { available := 258, camps := [{ cop := 0, region := 338, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 98 133 28 81 36 322 386 258), lower := (rows 41 98 133 28 81 36 64 128 256), losses := [] }

theorem u25851 : Upper (D 6) (R 6) [40,96,129,20,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25851 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25852 : Route 9 := (fun mask => (mask,id))

def c25852 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25852 : Upper (D 6) (R 6) [40,96,129,20,65,256] 13 := by
  apply FastRouting.sound _ _ [40,96,129,20,65,256] 13 (by decide) (choices 1) [2,4] r25852 c25852
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8038
  · exact u8039

def r25853 : Route 9 := (fun mask => (mask,id))

def c25853 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25853 : Upper (D 6) (R 6) [40,96,129,20,257,2] 13 := by
  apply FastRouting.sound _ _ [40,96,129,20,257,2] 13 (by decide) (choices 1) [2,4] r25853 c25853
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8040
  · exact u8041

def b25854 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 338, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 98 133 28 273 36 66 194 322), lower := (rows 41 98 133 28 273 36 64 128 256), losses := [] }

theorem u25854 : Upper (D 6) (R 6) [40,96,129,20,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25854 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25855 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 98 133 28 273 96 70 134 262), lower := (rows 41 98 133 28 273 96 64 128 256), losses := [] }

theorem u25855 : Upper (D 6) (R 6) [40,96,129,20,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25855 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25856 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 133 28 274 33 70 198 326), lower := (rows 41 98 133 28 274 33 64 128 256), losses := [] }

theorem u25856 : Upper (D 6) (R 6) [40,96,129,20,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25856 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25857 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 196, targets := 34 },{ cop := 6, region := 34, targets := 1 }], pairs := [(1,0),(2,1),(2,5)], upper := (rows 41 98 133 28 274 34 69 197 325), lower := (rows 41 98 133 28 274 34 64 128 256), losses := [] }

theorem u25857 : Upper (D 6) (R 6) [40,96,129,20,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25857 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25858 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 338, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 98 133 28 274 36 67 195 323), lower := (rows 41 98 133 28 274 36 64 128 256), losses := [] }

theorem u25858 : Upper (D 6) (R 6) [40,96,129,20,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25858 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25859 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 98 133 28 274 96 71 135 263), lower := (rows 41 98 133 28 274 96 64 128 256), losses := [] }

theorem u25859 : Upper (D 6) (R 6) [40,96,129,20,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25859 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u25859
end Delivery.IrregularNine14.P06

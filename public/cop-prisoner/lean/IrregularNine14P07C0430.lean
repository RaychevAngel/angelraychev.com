import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0151
import IrregularNine14P07C0152

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b25800 : PairBound 9 := { available := 74, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 259 69 138 176 48 74 202 330), lower := (rows 37 259 69 138 176 48 64 128 256), losses := [] }

theorem u25800 : Upper (D 7) (R 7) [36,257,65,130,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25800 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25801 : PairBound 9 := { available := 26, camps := [{ cop := 5, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 259 69 138 176 96 90 154 282), lower := (rows 37 259 69 138 176 96 64 128 256), losses := [] }

theorem u25801 : Upper (D 7) (R 7) [36,257,65,130,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25801 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25802 : Route 9 := (fun mask => (mask,id))

def c25802 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25802 : Upper (D 7) (R 7) [36,257,65,130,192,2] 13 := by
  apply FastRouting.sound _ _ [36,257,65,130,192,2] 13 (by decide) (choices 1) [8,16,32] r25802 c25802
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9073
  · exact u9074
  · exact u9075

def r25803 : Route 9 := (fun mask => (mask,id))

def c25803 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25803 : Upper (D 7) (R 7) [36,257,65,130,192,8] 13 := by
  apply FastRouting.sound _ _ [36,257,65,130,192,8] 13 (by decide) (choices 1) [2,16,32] r25803 c25803
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9076
  · exact u9077
  · exact u9078

def b25804 : PairBound 9 := { available := 42, camps := [{ cop := 4, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 259 69 138 208 48 106 170 298), lower := (rows 37 259 69 138 208 48 64 128 256), losses := [] }

theorem u25804 : Upper (D 7) (R 7) [36,257,65,130,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25804 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25805 : Route 9 := (fun mask => (mask,id))

def c25805 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25805 : Upper (D 7) (R 7) [36,257,65,160,192,2] 13 := by
  apply FastRouting.sound _ _ [36,257,65,160,192,2] 13 (by decide) (choices 1) [2,8,16] r25805 c25805
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9079
  · exact u9080
  · exact u9081

def b25806 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 37 259 69 168 208 40 82 146 274), lower := (rows 37 259 69 168 208 40 64 128 256), losses := [] }

theorem u25806 : Upper (D 7) (R 7) [36,257,65,160,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25806 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25807 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 259 69 168 208 48 74 138 266), lower := (rows 37 259 69 168 208 48 64 128 256), losses := [] }

theorem u25807 : Upper (D 7) (R 7) [36,257,65,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25807 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25808 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 57, targets := 192 }], pairs := [(0,6),(0,7),(3,6)], upper := (rows 37 259 70 25 50 40 192 192 448), lower := (rows 37 259 70 25 50 40 64 128 256), losses := [] }

theorem u25808 : Upper (D 7) (R 7) [36,257,66,17,34,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25808 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25809 : PairBound 9 := { available := 136, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7),(1,6),(3,6),(4,6)], upper := (rows 37 259 70 25 50 96 200 136 392), lower := (rows 37 259 70 25 50 96 64 128 256), losses := [] }

theorem u25809 : Upper (D 7) (R 7) [36,257,66,17,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25809 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25810 : Route 9 := (fun mask => (mask,id))

def c25810 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u25810 : Upper (D 7) (R 7) [36,257,66,17,34,128] 13 := by
  apply FastRouting.sound _ _ [36,257,66,17,34,128] 13 (by decide) (choices 1) [8,128] r25810 c25810
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9082
  · exact u9083

def b25811 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 57, targets := 128 },{ cop := 0, region := 216, targets := 2 }], pairs := [(0,7),(3,1),(3,7),(4,7)], upper := (rows 37 259 70 25 88 34 224 160 416), lower := (rows 37 259 70 25 88 34 64 128 256), losses := [] }

theorem u25811 : Upper (D 7) (R 7) [36,257,66,17,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25811 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25812 : Route 9 := (fun mask => (mask,id))

def c25812 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u25812 : Upper (D 7) (R 7) [36,257,66,17,72,128] 13 := by
  apply FastRouting.sound _ _ [36,257,66,17,72,128] 13 (by decide) (choices 1) [2,32,128] r25812 c25812
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9084
  · exact u9085
  · exact u9086

def b25813 : PairBound 9 := { available := 136, camps := [{ cop := 2, region := 57, targets := 128 },{ cop := 0, region := 216, targets := 2 }], pairs := [(0,7),(3,1),(3,7),(4,7)], upper := (rows 37 259 70 25 112 34 200 136 392), lower := (rows 37 259 70 25 112 34 64 128 256), losses := [] }

theorem u25813 : Upper (D 7) (R 7) [36,257,66,17,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25813 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25814 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 57, targets := 130 }], pairs := [(0,1),(0,7),(3,1)], upper := (rows 37 259 70 25 112 40 194 130 386), lower := (rows 37 259 70 25 112 40 64 128 256), losses := [] }

theorem u25814 : Upper (D 7) (R 7) [36,257,66,17,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25814 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25815 : Route 9 := (fun mask => (mask,id))

def c25815 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u25815 : Upper (D 7) (R 7) [36,257,66,17,96,128] 13 := by
  apply FastRouting.sound _ _ [36,257,66,17,96,128] 13 (by decide) (choices 1) [2,8,128] r25815 c25815
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9087
  · exact u9088
  · exact u9089

def r25816 : Route 9 := (fun mask => (mask,id))

def c25816 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u25816 : Upper (D 7) (R 7) [36,257,66,17,130,8] 13 := by
  apply FastRouting.sound _ _ [36,257,66,17,130,8] 13 (by decide) (choices 1) [32,128] r25816 c25816
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9090
  · exact u9091

def b25817 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 259 70 25 146 96 232 168 424), lower := (rows 37 259 70 25 146 96 64 128 256), losses := [] }

theorem u25817 : Upper (D 7) (R 7) [36,257,66,17,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25817 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25818 : Route 9 := (fun mask => (mask,id))

def c25818 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25818 : Upper (D 7) (R 7) [36,257,66,17,130,128] 13 := by
  apply FastRouting.sound _ _ [36,257,66,17,130,128] 13 (by decide) (choices 1) [8,32] r25818 c25818
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9092
  · exact u9093

def b25819 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 37 259 70 25 152 34 224 224 480), lower := (rows 37 259 70 25 152 34 64 128 256), losses := [] }

theorem u25819 : Upper (D 7) (R 7) [36,257,66,17,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25819 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25820 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 259 70 25 152 96 226 162 418), lower := (rows 37 259 70 25 152 96 64 128 256), losses := [] }

theorem u25820 : Upper (D 7) (R 7) [36,257,66,17,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25820 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25821 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 327, targets := 128 },{ cop := 1, region := 228, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(2,7)], upper := (rows 37 259 70 25 152 160 98 226 354), lower := (rows 37 259 70 25 152 160 64 128 256), losses := [] }

theorem u25821 : Upper (D 7) (R 7) [36,257,66,17,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25821 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25822 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 37 259 70 25 176 34 200 200 456), lower := (rows 37 259 70 25 176 34 64 128 256), losses := [] }

theorem u25822 : Upper (D 7) (R 7) [36,257,66,17,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25822 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25823 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 1, region := 196, targets := 1 }], pairs := [(1,5),(2,0),(2,5)], upper := (rows 37 259 70 25 176 40 194 194 450), lower := (rows 37 259 70 25 176 40 64 128 256), losses := [] }

theorem u25823 : Upper (D 7) (R 7) [36,257,66,17,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25823 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25824 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 259 70 25 176 96 202 138 394), lower := (rows 37 259 70 25 176 96 64 128 256), losses := [] }

theorem u25824 : Upper (D 7) (R 7) [36,257,66,17,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25824 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25825 : PairBound 9 := { available := 74, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 259 70 25 176 160 74 202 330), lower := (rows 37 259 70 25 176 160 64 128 256), losses := [] }

theorem u25825 : Upper (D 7) (R 7) [36,257,66,17,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25825 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25826 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 37 259 70 25 208 34 232 168 424), lower := (rows 37 259 70 25 208 34 64 128 256), losses := [] }

theorem u25826 : Upper (D 7) (R 7) [36,257,66,17,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25826 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25827 : Route 9 := (fun mask => (mask,id))

def c25827 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u25827 : Upper (D 7) (R 7) [36,257,66,17,192,8] 13 := by
  apply FastRouting.sound _ _ [36,257,66,17,192,8] 13 (by decide) (choices 1) [2,32,128] r25827 c25827
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9094
  · exact u9095
  · exact u9096

def r25828 : Route 9 := (fun mask => (mask,id))

def c25828 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25828 : Upper (D 7) (R 7) [36,257,66,17,192,128] 13 := by
  apply FastRouting.sound _ _ [36,257,66,17,192,128] 13 (by decide) (choices 1) [2,8,32] r25828 c25828
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9097
  · exact u9098
  · exact u9099

def b25829 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 57, targets := 128 }], pairs := [(0,7),(3,7),(4,7)], upper := (rows 37 259 70 26 81 40 224 160 416), lower := (rows 37 259 70 26 81 40 64 128 256), losses := [] }

theorem u25829 : Upper (D 7) (R 7) [36,257,66,18,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25829 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25830 : Route 9 := (fun mask => (mask,id))

def c25830 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u25830 : Upper (D 7) (R 7) [36,257,66,18,65,128] 13 := by
  apply FastRouting.sound _ _ [36,257,66,18,65,128] 13 (by decide) (choices 1) [8,32,128] r25830 c25830
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9100
  · exact u9101
  · exact u9102

def b25831 : PairBound 9 := { available := 136, camps := [{ cop := 2, region := 57, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(0,7),(3,7),(4,7)], upper := (rows 37 259 70 26 112 33 200 136 392), lower := (rows 37 259 70 26 112 33 64 128 256), losses := [] }

theorem u25831 : Upper (D 7) (R 7) [36,257,66,18,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25831 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25832 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 57, targets := 128 }], pairs := [(0,7),(3,7),(4,7)], upper := (rows 37 259 70 26 112 40 193 129 385), lower := (rows 37 259 70 26 112 40 64 128 256), losses := [] }

theorem u25832 : Upper (D 7) (R 7) [36,257,66,18,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25832 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25833 : Route 9 := (fun mask => (mask,id))

def c25833 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u25833 : Upper (D 7) (R 7) [36,257,66,18,96,128] 13 := by
  apply FastRouting.sound _ _ [36,257,66,18,96,128] 13 (by decide) (choices 1) [1,8,128] r25833 c25833
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9103
  · exact u9104
  · exact u9105

def r25834 : Route 9 := (fun mask => (mask,id))

def c25834 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u25834 : Upper (D 7) (R 7) [36,257,66,18,129,8] 13 := by
  apply FastRouting.sound _ _ [36,257,66,18,129,8] 13 (by decide) (choices 1) [32,128] r25834 c25834
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9106
  · exact u9107

def b25835 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 259 70 26 145 96 232 168 424), lower := (rows 37 259 70 26 145 96 64 128 256), losses := [] }

theorem u25835 : Upper (D 7) (R 7) [36,257,66,18,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25835 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25836 : Route 9 := (fun mask => (mask,id))

def c25836 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25836 : Upper (D 7) (R 7) [36,257,66,18,129,128] 13 := by
  apply FastRouting.sound _ _ [36,257,66,18,129,128] 13 (by decide) (choices 1) [8,32] r25836 c25836
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9108
  · exact u9109

def b25837 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 33, targets := 192 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(0,6),(0,7),(2,0)], upper := (rows 37 259 70 26 152 33 224 224 480), lower := (rows 37 259 70 26 152 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 6 14 19 32 97 161 289), good := (rows 508 478 94 30 152 496 64 128 256) }] }

theorem u25837 : Upper (D 7) (R 7) [36,257,66,18,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25837 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25838 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 259 70 26 152 96 225 161 417), lower := (rows 37 259 70 26 152 96 64 128 256), losses := [] }

theorem u25838 : Upper (D 7) (R 7) [36,257,66,18,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25838 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25839 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 327, targets := 128 },{ cop := 2, region := 161, targets := 2 }], pairs := [(0,1),(0,7),(1,7),(2,7)], upper := (rows 37 259 70 26 152 160 97 225 353), lower := (rows 37 259 70 26 152 160 64 128 256), losses := [] }

theorem u25839 : Upper (D 7) (R 7) [36,257,66,18,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25839 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25840 : PairBound 9 := { available := 200, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 3, region := 196, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(2,0)], upper := (rows 37 259 70 26 176 33 200 200 456), lower := (rows 37 259 70 26 176 33 64 128 256), losses := [] }

theorem u25840 : Upper (D 7) (R 7) [36,257,66,18,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25840 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25841 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 0, region := 208, targets := 2 }], pairs := [(1,5),(2,5),(4,1)], upper := (rows 37 259 70 26 176 40 193 193 449), lower := (rows 37 259 70 26 176 40 64 128 256), losses := [] }

theorem u25841 : Upper (D 7) (R 7) [36,257,66,18,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25841 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25842 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 259 70 26 176 96 201 137 393), lower := (rows 37 259 70 26 176 96 64 128 256), losses := [] }

theorem u25842 : Upper (D 7) (R 7) [36,257,66,18,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25842 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25843 : PairBound 9 := { available := 73, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 259 70 26 176 160 73 201 329), lower := (rows 37 259 70 26 176 160 64 128 256), losses := [] }

theorem u25843 : Upper (D 7) (R 7) [36,257,66,18,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25843 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25844 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 33, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,0)], upper := (rows 37 259 70 26 208 33 232 168 424), lower := (rows 37 259 70 26 208 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 6 14 51 32 65 129 257), good := (rows 508 478 94 30 208 496 64 128 256) }] }

theorem u25844 : Upper (D 7) (R 7) [36,257,66,18,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25844 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25845 : Route 9 := (fun mask => (mask,id))

def c25845 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u25845 : Upper (D 7) (R 7) [36,257,66,18,192,8] 13 := by
  apply FastRouting.sound _ _ [36,257,66,18,192,8] 13 (by decide) (choices 1) [1,32,128] r25845 c25845
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9110
  · exact u9111
  · exact u9112

def r25846 : Route 9 := (fun mask => (mask,id))

def c25846 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25846 : Upper (D 7) (R 7) [36,257,66,18,192,128] 13 := by
  apply FastRouting.sound _ _ [36,257,66,18,192,128] 13 (by decide) (choices 1) [1,8,32] r25846 c25846
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9113
  · exact u9114
  · exact u9115

def b25847 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 37 259 70 42 81 40 208 144 400), lower := (rows 37 259 70 42 81 40 64 128 256), losses := [] }

theorem u25847 : Upper (D 7) (R 7) [36,257,66,34,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25847 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25848 : PairBound 9 := { available := 136, camps := [{ cop := 2, region := 57, targets := 128 }], pairs := [(0,7),(3,7),(4,7)], upper := (rows 37 259 70 42 81 48 200 136 392), lower := (rows 37 259 70 42 81 48 64 128 256), losses := [] }

theorem u25848 : Upper (D 7) (R 7) [36,257,66,34,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25848 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25849 : Route 9 := (fun mask => (mask,id))

def c25849 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u25849 : Upper (D 7) (R 7) [36,257,66,34,65,128] 13 := by
  apply FastRouting.sound _ _ [36,257,66,34,65,128] 13 (by decide) (choices 1) [8,16,128] r25849 c25849
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9116
  · exact u9117
  · exact u9118

def b25850 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 212, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 37 259 70 42 88 33 208 144 400), lower := (rows 37 259 70 42 88 33 64 128 256), losses := [] }

theorem u25850 : Upper (D 7) (R 7) [36,257,66,34,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25850 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25851 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 57, targets := 128 }], pairs := [(0,7),(3,7),(4,7)], upper := (rows 37 259 70 42 88 48 193 129 385), lower := (rows 37 259 70 42 88 48 64 128 256), losses := [] }

theorem u25851 : Upper (D 7) (R 7) [36,257,66,34,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25851 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25852 : Route 9 := (fun mask => (mask,id))

def c25852 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u25852 : Upper (D 7) (R 7) [36,257,66,34,72,128] 13 := by
  apply FastRouting.sound _ _ [36,257,66,34,72,128] 13 (by decide) (choices 1) [1,16,128] r25852 c25852
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9119
  · exact u9120
  · exact u9121

def b25853 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6)], upper := (rows 37 259 70 42 145 40 208 208 464), lower := (rows 37 259 70 42 145 40 64 128 256), losses := [] }

theorem u25853 : Upper (D 7) (R 7) [36,257,66,34,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25853 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25854 : Route 9 := (fun mask => (mask,id))

def c25854 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u25854 : Upper (D 7) (R 7) [36,257,66,34,129,16] 13 := by
  apply FastRouting.sound _ _ [36,257,66,34,129,16] 13 (by decide) (choices 1) [8,128] r25854 c25854
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9122
  · exact u9123

def b25855 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7),(1,6),(3,6),(4,6)], upper := (rows 37 259 70 42 145 96 216 152 408), lower := (rows 37 259 70 42 145 96 64 128 256), losses := [] }

theorem u25855 : Upper (D 7) (R 7) [36,257,66,34,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25855 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25856 : Route 9 := (fun mask => (mask,id))

def c25856 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25856 : Upper (D 7) (R 7) [36,257,66,34,129,128] 13 := by
  apply FastRouting.sound _ _ [36,257,66,34,129,128] 13 (by decide) (choices 1) [8,16] r25856 c25856
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9124
  · exact u9125

def b25857 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 37 259 70 42 152 33 208 208 464), lower := (rows 37 259 70 42 152 33 64 128 256), losses := [] }

theorem u25857 : Upper (D 7) (R 7) [36,257,66,34,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25857 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25858 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5),(4,1)], upper := (rows 37 259 70 42 152 48 193 193 449), lower := (rows 37 259 70 42 152 48 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 24 56 67 131 259), good := (rows 485 449 452 504 184 48 64 128 256) }] }

theorem u25858 : Upper (D 7) (R 7) [36,257,66,34,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25858 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25859 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7),(1,6),(3,6),(4,6)], upper := (rows 37 259 70 42 152 96 209 145 401), lower := (rows 37 259 70 42 152 96 64 128 256), losses := [] }

theorem u25859 : Upper (D 7) (R 7) [36,257,66,34,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25859 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u25859
end Delivery.IrregularNine14.P07

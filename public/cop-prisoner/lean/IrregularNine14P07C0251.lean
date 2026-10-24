import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0046
import IrregularNine14P07C0047

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b15060 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 45, targets := 128 },{ cop := 5, region := 466, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 7 290 13 104 82 33 208 144 400), lower := (rows 7 290 13 104 82 33 64 128 256), losses := [] }

theorem u15060 : Upper (D 7) (R 7) [6,288,9,96,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15060 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15061 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 290 13 104 82 48 193 129 385), lower := (rows 7 290 13 104 82 48 64 128 256), losses := [] }

theorem u15061 : Upper (D 7) (R 7) [6,288,9,96,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15061 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15062 : Route 9 := (fun mask => (mask,id))

def c15062 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15062 : Upper (D 7) (R 7) [6,288,9,96,66,128] 13 := by
  apply FastRouting.sound _ _ [6,288,9,96,66,128] 13 (by decide) (choices 1) [1,16,128] r15062 c15062
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2817
  · exact u2818
  · exact u2819

def b15063 : PairBound 9 := { available := 208, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 0, region := 208, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(4,1)], upper := (rows 7 290 13 104 145 34 208 208 464), lower := (rows 7 290 13 104 145 34 64 128 256), losses := [] }

theorem u15063 : Upper (D 7) (R 7) [6,288,9,96,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15063 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15064 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 0, region := 208, targets := 32 }], pairs := [(1,0),(3,0),(4,5)], upper := (rows 7 290 13 104 145 48 194 194 450), lower := (rows 7 290 13 104 145 48 64 128 256), losses := [] }

theorem u15064 : Upper (D 7) (R 7) [6,288,9,96,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15064 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15065 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 7 290 13 104 145 96 210 146 402), lower := (rows 7 290 13 104 145 96 64 128 256), losses := [] }

theorem u15065 : Upper (D 7) (R 7) [6,288,9,96,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15065 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15066 : Route 9 := (fun mask => (mask,id))

def c15066 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15066 : Upper (D 7) (R 7) [6,288,9,96,129,128] 13 := by
  apply FastRouting.sound _ _ [6,288,9,96,129,128] 13 (by decide) (choices 1) [2,16] r15066 c15066
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2820
  · exact u2821

def b15067 : PairBound 9 := { available := 208, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 0, region := 208, targets := 32 }], pairs := [(1,0),(3,0),(4,0),(4,5)], upper := (rows 7 290 13 104 146 33 208 208 464), lower := (rows 7 290 13 104 146 33 64 128 256), losses := [] }

theorem u15067 : Upper (D 7) (R 7) [6,288,9,96,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15067 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15068 : Route 9 := (fun mask => (mask,id))

def c15068 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15068 : Upper (D 7) (R 7) [6,288,9,96,130,16] 13 := by
  apply FastRouting.sound _ _ [6,288,9,96,130,16] 13 (by decide) (choices 1) [1,128] r15068 c15068
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2822
  · exact u2823

def b15069 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 7 290 13 104 146 96 209 145 401), lower := (rows 7 290 13 104 146 96 64 128 256), losses := [] }

theorem u15069 : Upper (D 7) (R 7) [6,288,9,96,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15069 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15070 : Route 9 := (fun mask => (mask,id))

def c15070 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15070 : Upper (D 7) (R 7) [6,288,9,96,130,128] 13 := by
  apply FastRouting.sound _ _ [6,288,9,96,130,128] 13 (by decide) (choices 1) [1,16] r15070 c15070
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2824
  · exact u2825

def b15071 : PairBound 9 := { available := 146, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 0, region := 208, targets := 32 }], pairs := [(1,0),(3,0),(4,0),(4,5)], upper := (rows 7 290 13 104 208 33 210 146 402), lower := (rows 7 290 13 104 208 33 64 128 256), losses := [] }

theorem u15071 : Upper (D 7) (R 7) [6,288,9,96,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15071 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15072 : PairBound 9 := { available := 145, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 0, region := 208, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(4,1)], upper := (rows 7 290 13 104 208 34 209 145 401), lower := (rows 7 290 13 104 208 34 64 128 256), losses := [] }

theorem u15072 : Upper (D 7) (R 7) [6,288,9,96,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15072 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15073 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 290 13 104 208 48 195 131 387), lower := (rows 7 290 13 104 208 48 64 128 256), losses := [] }

theorem u15073 : Upper (D 7) (R 7) [6,288,9,96,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15073 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15074 : Route 9 := (fun mask => (mask,id))

def c15074 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15074 : Upper (D 7) (R 7) [6,288,9,96,192,128] 13 := by
  apply FastRouting.sound _ _ [6,288,9,96,192,128] 13 (by decide) (choices 1) [1,2,16] r15074 c15074
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2826
  · exact u2827
  · exact u2828

def b15075 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 204, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,5)], upper := (rows 7 290 13 200 49 34 208 208 464), lower := (rows 7 290 13 200 49 34 64 128 256), losses := [] }

theorem u15075 : Upper (D 7) (R 7) [6,288,9,192,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15075 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15076 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 48, targets := 194 }], pairs := [(4,1),(4,6),(4,7)], upper := (rows 7 290 13 200 49 48 194 194 450), lower := (rows 7 290 13 200 49 48 64 128 256), losses := [] }

theorem u15076 : Upper (D 7) (R 7) [6,288,9,192,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15076 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15077 : PairBound 9 := { available := 146, camps := [{ cop := 4, region := 458, targets := 1 },{ cop := 4, region := 386, targets := 64 }], pairs := [(1,0),(1,6),(3,0),(4,1)], upper := (rows 7 290 13 200 49 96 210 146 402), lower := (rows 7 290 13 200 49 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 20 104 64 128 256), good := (rows 21 288 61 232 49 96 96 128 256) }] }

theorem u15077 : Upper (D 7) (R 7) [6,288,9,192,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15077 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15078 : PairBound 9 := { available := 176, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 4, region := 426, targets := 1 }], pairs := [(1,0),(1,6),(1,7),(3,0)], upper := (rows 7 290 13 200 81 34 240 176 432), lower := (rows 7 290 13 200 81 34 64 128 256), losses := [] }

theorem u15078 : Upper (D 7) (R 7) [6,288,9,192,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15078 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15079 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 426, targets := 1 },{ cop := 4, region := 418, targets := 64 }], pairs := [(1,0),(1,6),(3,0)], upper := (rows 7 290 13 200 81 48 226 162 418), lower := (rows 7 290 13 200 81 48 64 128 256), losses := [] }

theorem u15079 : Upper (D 7) (R 7) [6,288,9,192,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15079 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15080 : Route 9 := (fun mask => (mask,id))

def c15080 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15080 : Upper (D 7) (R 7) [6,288,9,192,65,128] 13 := by
  apply FastRouting.sound _ _ [6,288,9,192,65,128] 13 (by decide) (choices 1) [2,16,32] r15080 c15080
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2829
  · exact u2830
  · exact u2831

def r15081 : Route 9 := (fun mask => (mask,id))

def c15081 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u15081 : Upper (D 7) (R 7) [6,288,9,192,66,1] 13 := by
  apply FastRouting.sound _ _ [6,288,9,192,66,1] 13 (by decide) (choices 1) [16,32,128] r15081 c15081
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2832
  · exact u2833
  · exact u2834

def r15082 : Route 9 := (fun mask => (mask,id))

def c15082 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u15082 : Upper (D 7) (R 7) [6,288,9,192,66,16] 13 := by
  apply FastRouting.sound _ _ [6,288,9,192,66,16] 13 (by decide) (choices 1) [1,32,128] r15082 c15082
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2835
  · exact u2836
  · exact u2837

def r15083 : Route 9 := (fun mask => (mask,id))

def c15083 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15083 : Upper (D 7) (R 7) [6,288,9,192,66,128] 13 := by
  apply FastRouting.sound _ _ [6,288,9,192,66,128] 13 (by decide) (choices 1) [1,16,32] r15083 c15083
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2838
  · exact u2839
  · exact u2840

def b15084 : PairBound 9 := { available := 146, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 4, region := 386, targets := 64 }], pairs := [(1,0),(1,6),(3,0),(4,0)], upper := (rows 7 290 13 200 112 33 210 146 402), lower := (rows 7 290 13 200 112 33 64 128 256), losses := [] }

theorem u15084 : Upper (D 7) (R 7) [6,288,9,192,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15084 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15085 : Route 9 := (fun mask => (mask,id))

def c15085 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15085 : Upper (D 7) (R 7) [6,288,9,192,96,2] 13 := by
  apply FastRouting.sound _ _ [6,288,9,192,96,2] 13 (by decide) (choices 1) [1,16,128] r15085 c15085
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2841
  · exact u2842
  · exact u2843

def b15086 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 205, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 290 13 200 112 48 195 131 387), lower := (rows 7 290 13 200 112 48 64 128 256), losses := [] }

theorem u15086 : Upper (D 7) (R 7) [6,288,9,192,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15086 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15087 : Route 9 := (fun mask => (mask,id))

def c15087 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15087 : Upper (D 7) (R 7) [6,288,9,192,96,128] 13 := by
  apply FastRouting.sound _ _ [6,288,9,192,96,128] 13 (by decide) (choices 1) [1,2,16] r15087 c15087
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2844
  · exact u2845
  · exact u2846

def b15088 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 212, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 7 290 28 41 81 34 192 192 448), lower := (rows 7 290 28 41 81 34 64 128 256), losses := [] }

theorem u15088 : Upper (D 7) (R 7) [6,288,24,33,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15088 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15089 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 44, targets := 130 }], pairs := [(2,1),(2,7),(3,1),(3,7)], upper := (rows 7 290 28 41 81 96 194 130 386), lower := (rows 7 290 28 41 81 96 64 128 256), losses := [] }

theorem u15089 : Upper (D 7) (R 7) [6,288,24,33,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15089 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15090 : Route 9 := (fun mask => (mask,id))

def c15090 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15090 : Upper (D 7) (R 7) [6,288,24,33,65,128] 13 := by
  apply FastRouting.sound _ _ [6,288,24,33,65,128] 13 (by decide) (choices 1) [2,128] r15090 c15090
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2847
  · exact u2848

def b15091 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 45, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 290 28 41 82 33 192 192 448), lower := (rows 7 290 28 41 82 33 64 128 256), losses := [] }

theorem u15091 : Upper (D 7) (R 7) [6,288,24,33,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15091 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15092 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 45, targets := 128 },{ cop := 0, region := 232, targets := 2 }], pairs := [(0,7),(2,7),(3,1),(3,7)], upper := (rows 7 290 28 41 82 96 193 129 385), lower := (rows 7 290 28 41 82 96 64 128 256), losses := [] }

theorem u15092 : Upper (D 7) (R 7) [6,288,24,33,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15092 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15093 : Route 9 := (fun mask => (mask,id))

def c15093 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15093 : Upper (D 7) (R 7) [6,288,24,33,66,128] 13 := by
  apply FastRouting.sound _ _ [6,288,24,33,66,128] 13 (by decide) (choices 1) [1,128] r15093 c15093
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2849
  · exact u2850

def b15094 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 40, targets := 194 },{ cop := 3, region := 450, targets := 1 }], pairs := [(1,0),(3,1),(3,6),(3,7)], upper := (rows 7 290 28 41 208 33 194 194 450), lower := (rows 7 290 28 41 208 33 64 128 256), losses := [] }

theorem u15094 : Upper (D 7) (R 7) [6,288,24,33,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15094 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15095 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 212, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 7 290 28 41 208 34 193 193 449), lower := (rows 7 290 28 41 208 34 64 128 256), losses := [] }

theorem u15095 : Upper (D 7) (R 7) [6,288,24,33,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15095 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15096 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 208, targets := 32 },{ cop := 3, region := 386, targets := 64 }], pairs := [(0,6),(1,6),(2,5),(4,5)], upper := (rows 7 290 28 41 208 96 195 131 387), lower := (rows 7 290 28 41 208 96 64 128 256), losses := [{ target := 5, region := (rows 1 2 12 8 25 0 65 129 257), good := (rows 471 258 28 477 208 64 64 128 256) },{ target := 6, region := (rows 5 10 4 8 16 32 0 141 269), good := (rows 391 290 415 427 144 32 0 128 256) }] }

theorem u15096 : Upper (D 7) (R 7) [6,288,24,33,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15096 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15097 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 52, targets := 130 }], pairs := [(2,1),(2,7),(4,1),(4,7)], upper := (rows 7 290 28 73 112 33 194 130 386), lower := (rows 7 290 28 73 112 33 64 128 256), losses := [] }

theorem u15097 : Upper (D 7) (R 7) [6,288,24,65,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15097 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15098 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 0, region := 200, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(3,1)], upper := (rows 7 290 28 73 112 34 193 129 385), lower := (rows 7 290 28 73 112 34 64 128 256), losses := [] }

theorem u15098 : Upper (D 7) (R 7) [6,288,24,65,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15098 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15099 : Route 9 := (fun mask => (mask,id))

def c15099 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15099 : Upper (D 7) (R 7) [6,288,24,65,96,128] 13 := by
  apply FastRouting.sound _ _ [6,288,24,65,96,128] 13 (by decide) (choices 1) [1,2,128] r15099 c15099
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2851
  · exact u2852
  · exact u2853

def b15100 : PairBound 9 := { available := 224, camps := [{ cop := 8, region := 34, targets := 192 },{ cop := 0, region := 482, targets := 1 }], pairs := [(1,0),(1,6),(1,7),(2,1)], upper := (rows 7 290 28 73 145 34 224 224 480), lower := (rows 7 290 28 73 145 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 29 9 17 32 98 162 290), good := (rows 477 480 28 93 157 480 64 128 256) }] }

theorem u15100 : Upper (D 7) (R 7) [6,288,24,65,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15100 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15101 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 482, targets := 1 },{ cop := 5, region := 386, targets := 64 }], pairs := [(1,0),(1,6),(2,6),(4,6)], upper := (rows 7 290 28 73 145 96 226 162 418), lower := (rows 7 290 28 73 145 96 64 128 256), losses := [{ target := 6, region := (rows 1 34 12 8 17 32 0 162 290), good := (rows 407 418 28 29 145 418 0 128 256) }] }

theorem u15101 : Upper (D 7) (R 7) [6,288,24,65,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15101 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15102 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 466, targets := 1 },{ cop := 0, region := 232, targets := 2 }], pairs := [(1,0),(2,0),(3,1),(4,0)], upper := (rows 7 290 28 73 146 33 224 224 480), lower := (rows 7 290 28 73 146 33 64 128 256), losses := [{ target := 0, region := (rows 0 34 12 8 51 32 98 162 290), good := (rows 470 498 28 92 466 498 64 128 256) }] }

theorem u15102 : Upper (D 7) (R 7) [6,288,24,65,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15102 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15103 : Route 9 := (fun mask => (mask,id))

def c15103 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u15103 : Upper (D 7) (R 7) [6,288,24,65,130,64] 13 := by
  apply FastRouting.sound _ _ [6,288,24,65,130,64] 13 (by decide) (choices 1) [1,32,128] r15103 c15103
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2854
  · exact u2855
  · exact u2856

def r15104 : Route 9 := (fun mask => (mask,id))

def c15104 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15104 : Upper (D 7) (R 7) [6,288,24,65,130,128] 13 := by
  apply FastRouting.sound _ _ [6,288,24,65,130,128] 13 (by decide) (choices 1) [1,32] r15104 c15104
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2857
  · exact u2858

def b15105 : PairBound 9 := { available := 194, camps := [{ cop := 5, region := 466, targets := 1 },{ cop := 0, region := 200, targets := 32 }], pairs := [(1,0),(2,5),(3,5),(4,0)], upper := (rows 7 290 28 73 176 33 194 194 450), lower := (rows 7 290 28 73 176 33 64 128 256), losses := [{ target := 5, region := (rows 1 2 20 41 16 0 67 131 259), good := (rows 463 458 28 457 156 457 64 128 256) }] }

theorem u15105 : Upper (D 7) (R 7) [6,288,24,65,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15105 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15106 : PairBound 9 := { available := 193, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 0, region := 200, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(3,1)], upper := (rows 7 290 28 73 176 34 193 193 449), lower := (rows 7 290 28 73 176 34 64 128 256), losses := [] }

theorem u15106 : Upper (D 7) (R 7) [6,288,24,65,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15106 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15107 : Route 9 := (fun mask => (mask,id))

def c15107 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15107 : Upper (D 7) (R 7) [6,288,24,65,160,64] 13 := by
  apply FastRouting.sound _ _ [6,288,24,65,160,64] 13 (by decide) (choices 1) [1,2,128] r15107 c15107
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2859
  · exact u2860
  · exact u2861

def b15108 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 290 28 73 176 160 67 195 323), lower := (rows 7 290 28 73 176 160 64 128 256), losses := [] }

theorem u15108 : Upper (D 7) (R 7) [6,288,24,65,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15108 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15109 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 5, region := 466, targets := 1 }], pairs := [(0,6),(1,0),(1,6),(4,0)], upper := (rows 7 290 28 73 208 33 226 162 418), lower := (rows 7 290 28 73 208 33 64 128 256), losses := [] }

theorem u15109 : Upper (D 7) (R 7) [6,288,24,65,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15109 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15110 : PairBound 9 := { available := 161, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,0),(1,6),(1,7)], upper := (rows 7 290 28 73 208 34 225 161 417), lower := (rows 7 290 28 73 208 34 64 128 256), losses := [] }

theorem u15110 : Upper (D 7) (R 7) [6,288,24,65,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15110 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15111 : Route 9 := (fun mask => (mask,id))

def c15111 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15111 : Upper (D 7) (R 7) [6,288,24,65,192,128] 13 := by
  apply FastRouting.sound _ _ [6,288,24,65,192,128] 13 (by decide) (choices 1) [1,2,32] r15111 c15111
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2862
  · exact u2863
  · exact u2864

def r15112 : Route 9 := (fun mask => (mask,id))

def c15112 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15112 : Upper (D 7) (R 7) [6,288,24,66,160,1] 13 := by
  apply FastRouting.sound _ _ [6,288,24,66,160,1] 13 (by decide) (choices 1) [1,128] r15112 c15112
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2865
  · exact u2866

def r15113 : Route 9 := (fun mask => (mask,id))

def c15113 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15113 : Upper (D 7) (R 7) [6,288,24,66,160,64] 13 := by
  apply FastRouting.sound _ _ [6,288,24,66,160,64] 13 (by decide) (choices 1) [1,128] r15113 c15113
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2867
  · exact u2868

def b15114 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 290 28 74 176 160 65 193 321), lower := (rows 7 290 28 74 176 160 64 128 256), losses := [] }

theorem u15114 : Upper (D 7) (R 7) [6,288,24,66,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15114 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15115 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 0, region := 240, targets := 2 }], pairs := [(0,6),(1,6),(2,1),(4,1)], upper := (rows 7 290 28 74 208 33 225 161 417), lower := (rows 7 290 28 74 208 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 51 33 97 161 289), good := (rows 501 496 28 92 208 497 64 128 256) }] }

theorem u15115 : Upper (D 7) (R 7) [6,288,24,66,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15115 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15116 : Route 9 := (fun mask => (mask,id))

def c15116 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15116 : Upper (D 7) (R 7) [6,288,24,66,192,128] 13 := by
  apply FastRouting.sound _ _ [6,288,24,66,192,128] 13 (by decide) (choices 1) [1,32] r15116 c15116
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2869
  · exact u2870

def b15117 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 0, region := 208, targets := 32 }], pairs := [(0,6),(1,6),(2,5),(4,5)], upper := (rows 7 290 28 104 208 33 195 131 387), lower := (rows 7 290 28 104 208 33 64 128 256), losses := [{ target := 5, region := (rows 1 2 12 8 49 0 65 129 257), good := (rows 471 274 28 92 208 465 64 128 256) }] }

theorem u15117 : Upper (D 7) (R 7) [6,288,24,96,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15117 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15118 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 0, region := 208, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(4,1)], upper := (rows 7 290 28 104 208 34 193 129 385), lower := (rows 7 290 28 104 208 34 64 128 256), losses := [] }

theorem u15118 : Upper (D 7) (R 7) [6,288,24,96,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15118 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15119 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0),(3,1)], upper := (rows 7 290 28 104 208 160 67 131 259), lower := (rows 7 290 28 104 208 160 64 128 256), losses := [] }

theorem u15119 : Upper (D 7) (R 7) [6,288,24,96,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15119 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u15119
end Delivery.IrregularNine14.P07

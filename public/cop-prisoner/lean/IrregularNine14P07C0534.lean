import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0250
import IrregularNine14P07C0251
import IrregularNine14P07C0252

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r32040 : Route 9 := (fun mask => (mask,id))

def c32040 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32040 : Upper (D 7) (R 7) [6,264,96,160,129] 13 := by
  apply FastRouting.sound _ _ [6,264,96,160,129] 13 (by decide) (choices 1) [1,2,16,64] r32040 c32040
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15031
  · exact u15032
  · exact u15033
  · exact u15034

def r32041 : Route 9 := (fun mask => (mask,id))

def c32041 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32041 : Upper (D 7) (R 7) [6,264,96,160,130] 13 := by
  apply FastRouting.sound _ _ [6,264,96,160,130] 13 (by decide) (choices 1) [1,16,64] r32041 c32041
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15035
  · exact u15036
  · exact u15037

def r32042 : Route 9 := (fun mask => (mask,id))

def c32042 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32042 : Upper (D 7) (R 7) [6,264,96,160,192] 13 := by
  apply FastRouting.sound _ _ [6,264,96,160,192] 13 (by decide) (choices 1) [1,2,16] r32042 c32042
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15038
  · exact u15039
  · exact u15040

def b32043 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 29, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 290 13 56 19 224 192 192 448), lower := (rows 7 290 13 56 19 32 64 128 256), losses := [] }

theorem u32043 : Upper (D 7) (R 7) [6,288,9,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32043 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32044 : Route 9 := (fun mask => (mask,id))

def c32044 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32044 : Upper (D 7) (R 7) [6,288,9,48,65] 13 := by
  apply FastRouting.sound _ _ [6,288,9,48,65] 13 (by decide) (choices 1) [2,64,128] r32044 c32044
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15041
  · exact u15042
  · exact u15043

def r32045 : Route 9 := (fun mask => (mask,id))

def c32045 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32045 : Upper (D 7) (R 7) [6,288,9,48,66] 13 := by
  apply FastRouting.sound _ _ [6,288,9,48,66] 13 (by decide) (choices 1) [1,64,128] r32045 c32045
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15044
  · exact u15045
  · exact u15046

def r32046 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c32046 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32046 : Upper (D 7) (R 7) [6,288,9,48,192] 13 := by
  apply FastRouting.sound _ _ [6,288,9,48,192] 13 (by decide) (choices 1) [1,2,64] r32046 c32046
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15047
  · exact u15048
  · exact u15049

def b32047 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 16, targets := 224 },{ cop := 4, region := 482, targets := 1 }], pairs := [(1,0),(4,5),(4,6),(4,7)], upper := (rows 7 290 13 88 19 224 224 224 480), lower := (rows 7 290 13 88 19 32 64 128 256), losses := [] }

theorem u32047 : Upper (D 7) (R 7) [6,288,9,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32047 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32048 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 458, targets := 1 }], pairs := [(1,0),(2,5),(3,0),(3,5)], upper := (rows 7 290 13 88 49 226 194 194 450), lower := (rows 7 290 13 88 49 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 20 24 16 0 67 131 259), good := (rows 455 450 461 92 477 0 64 128 256) }] }

theorem u32048 : Upper (D 7) (R 7) [6,288,9,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32048 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32049 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 205, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 7 290 13 88 50 225 193 193 449), lower := (rows 7 290 13 88 50 32 64 128 256), losses := [] }

theorem u32049 : Upper (D 7) (R 7) [6,288,9,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32049 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32050 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 12, targets := 162 }], pairs := [(2,1),(2,5),(2,7),(3,1)], upper := (rows 7 290 13 88 81 162 226 162 418), lower := (rows 7 290 13 88 81 32 64 128 256), losses := [] }

theorem u32050 : Upper (D 7) (R 7) [6,288,9,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32050 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32051 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 13, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 290 13 88 82 161 225 161 417), lower := (rows 7 290 13 88 82 32 64 128 256), losses := [] }

theorem u32051 : Upper (D 7) (R 7) [6,288,9,80,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32051 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32052 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 7 290 13 88 112 163 195 131 387), lower := (rows 7 290 13 88 112 32 64 128 256), losses := [] }

theorem u32052 : Upper (D 7) (R 7) [6,288,9,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32052 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32053 : Route 9 := (fun mask => (mask,id))

def c32053 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32053 : Upper (D 7) (R 7) [6,288,9,80,129] 13 := by
  apply FastRouting.sound _ _ [6,288,9,80,129] 13 (by decide) (choices 1) [2,64,128] r32053 c32053
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15050
  · exact u15051
  · exact u15052

def r32054 : Route 9 := (fun mask => (mask,id))

def c32054 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32054 : Upper (D 7) (R 7) [6,288,9,80,130] 13 := by
  apply FastRouting.sound _ _ [6,288,9,80,130] 13 (by decide) (choices 1) [1,64,128] r32054 c32054
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15053
  · exact u15054
  · exact u15055

def r32055 : Route 9 := (fun mask => (mask,id))

def c32055 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32055 : Upper (D 7) (R 7) [6,288,9,80,160] 13 := by
  apply FastRouting.sound _ _ [6,288,9,80,160] 13 (by decide) (choices 1) [1,2,64,128] r32055 c32055
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15056
  · exact u15057
  · exact u15058
  · exact u15059

def b32056 : PairBound 9 := { available := 163, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 7 290 13 88 208 163 227 163 419), lower := (rows 7 290 13 88 208 32 64 128 256), losses := [] }

theorem u32056 : Upper (D 7) (R 7) [6,288,9,80,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32056 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32057 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 16, targets := 192 },{ cop := 4, region := 490, targets := 1 }], pairs := [(1,0),(3,0),(4,6),(4,7)], upper := (rows 7 290 13 104 19 240 208 208 464), lower := (rows 7 290 13 104 19 32 64 128 256), losses := [] }

theorem u32057 : Upper (D 7) (R 7) [6,288,9,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32057 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32058 : PairBound 9 := { available := 146, camps := [{ cop := 4, region := 426, targets := 1 },{ cop := 0, region := 208, targets := 32 },{ cop := 4, region := 418, targets := 64 }], pairs := [(1,0),(1,6),(3,0),(4,5)], upper := (rows 7 290 13 104 81 178 210 146 402), lower := (rows 7 290 13 104 81 32 64 128 256), losses := [] }

theorem u32058 : Upper (D 7) (R 7) [6,288,9,96,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32058 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32059 : Route 9 := (fun mask => (mask,id))

def c32059 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32059 : Upper (D 7) (R 7) [6,288,9,96,66] 13 := by
  apply FastRouting.sound _ _ [6,288,9,96,66] 13 (by decide) (choices 1) [1,16,128] r32059 c32059
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15060
  · exact u15061
  · exact u15062

def r32060 : Route 9 := (fun mask => (mask,id))

def c32060 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u32060 : Upper (D 7) (R 7) [6,288,9,96,129] 13 := by
  apply FastRouting.sound _ _ [6,288,9,96,129] 13 (by decide) (choices 1) [2,16,64,128] r32060 c32060
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15063
  · exact u15064
  · exact u15065
  · exact u15066

def r32061 : Route 9 := (fun mask => (mask,id))

def c32061 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u32061 : Upper (D 7) (R 7) [6,288,9,96,130] 13 := by
  apply FastRouting.sound _ _ [6,288,9,96,130] 13 (by decide) (choices 1) [1,16,64,128] r32061 c32061
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15067
  · exact u15068
  · exact u15069
  · exact u15070

def r32062 : Route 9 := (fun mask => (mask,id))

def c32062 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32062 : Upper (D 7) (R 7) [6,288,9,96,192] 13 := by
  apply FastRouting.sound _ _ [6,288,9,96,192] 13 (by decide) (choices 1) [1,2,16,128] r32062 c32062
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15071
  · exact u15072
  · exact u15073
  · exact u15074

def b32063 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 16, targets := 224 },{ cop := 4, region := 482, targets := 1 }], pairs := [(1,0),(4,5),(4,6),(4,7)], upper := (rows 7 290 13 200 19 240 240 240 496), lower := (rows 7 290 13 200 19 32 64 128 256), losses := [] }

theorem u32063 : Upper (D 7) (R 7) [6,288,9,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32063 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32064 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c32064 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u32064 : Upper (D 7) (R 7) [6,288,9,192,33] 13 := by
  apply FastRouting.sound _ _ [6,288,9,192,33] 13 (by decide) (choices 1) [2,16,64] r32064 c32064
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15075
  · exact u15076
  · exact u15077

def b32065 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 205, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 7 290 13 200 50 241 209 209 465), lower := (rows 7 290 13 200 50 32 64 128 256), losses := [] }

theorem u32065 : Upper (D 7) (R 7) [6,288,9,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32065 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32066 : Route 9 := (fun mask => (mask,id))

def c32066 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32066 : Upper (D 7) (R 7) [6,288,9,192,65] 13 := by
  apply FastRouting.sound _ _ [6,288,9,192,65] 13 (by decide) (choices 1) [2,16,128] r32066 c32066
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15078
  · exact u15079
  · exact u15080

def r32067 : Route 9 := (fun mask => (mask,id))

def c32067 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32067 : Upper (D 7) (R 7) [6,288,9,192,66] 13 := by
  apply FastRouting.sound _ _ [6,288,9,192,66] 13 (by decide) (choices 1) [1,16,128] r32067 c32067
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15081
  · exact u15082
  · exact u15083

def r32068 : Route 9 := (fun mask => (mask,id))

def c32068 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32068 : Upper (D 7) (R 7) [6,288,9,192,96] 13 := by
  apply FastRouting.sound _ _ [6,288,9,192,96] 13 (by decide) (choices 1) [1,2,16,128] r32068 c32068
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15084
  · exact u15085
  · exact u15086
  · exact u15087

def b32069 : PairBound 9 := { available := 51, camps := [{ cop := 3, region := 16, targets := 35 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,1),(4,5)], upper := (rows 7 290 13 200 208 51 115 179 307), lower := (rows 7 290 13 200 208 32 64 128 256), losses := [] }

theorem u32069 : Upper (D 7) (R 7) [6,288,9,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32069 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32070 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 29, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 290 28 11 49 224 192 192 448), lower := (rows 7 290 28 11 49 32 64 128 256), losses := [] }

theorem u32070 : Upper (D 7) (R 7) [6,288,24,3,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32070 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32071 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 244, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 7 290 28 11 81 224 224 224 480), lower := (rows 7 290 28 11 81 32 64 128 256), losses := [] }

theorem u32071 : Upper (D 7) (R 7) [6,288,24,3,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32071 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32072 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 8, targets := 192 },{ cop := 3, region := 244, targets := 2 }], pairs := [(2,1),(3,6),(3,7),(4,1)], upper := (rows 7 290 28 11 112 225 193 193 449), lower := (rows 7 290 28 11 112 32 64 128 256), losses := [] }

theorem u32072 : Upper (D 7) (R 7) [6,288,24,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32072 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32073 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 244, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 7 290 28 11 208 225 225 225 481), lower := (rows 7 290 28 11 208 32 64 128 256), losses := [] }

theorem u32073 : Upper (D 7) (R 7) [6,288,24,3,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32073 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32074 : Route 9 := (fun mask => (mask,id))

def c32074 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32074 : Upper (D 7) (R 7) [6,288,24,33,65] 13 := by
  apply FastRouting.sound _ _ [6,288,24,33,65] 13 (by decide) (choices 1) [2,64,128] r32074 c32074
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15088
  · exact u15089
  · exact u15090

def r32075 : Route 9 := (fun mask => (mask,id))

def c32075 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32075 : Upper (D 7) (R 7) [6,288,24,33,66] 13 := by
  apply FastRouting.sound _ _ [6,288,24,33,66] 13 (by decide) (choices 1) [1,64,128] r32075 c32075
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15091
  · exact u15092
  · exact u15093

def r32076 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c32076 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32076 : Upper (D 7) (R 7) [6,288,24,33,192] 13 := by
  apply FastRouting.sound _ _ [6,288,24,33,192] 13 (by decide) (choices 1) [1,2,64] r32076 c32076
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15094
  · exact u15095
  · exact u15096

def b32077 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 8, targets := 193 },{ cop := 3, region := 213, targets := 32 }], pairs := [(0,5),(3,0),(3,6),(3,7)], upper := (rows 7 290 28 42 81 225 193 193 449), lower := (rows 7 290 28 42 81 32 64 128 256), losses := [] }

theorem u32077 : Upper (D 7) (R 7) [6,288,24,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32077 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32078 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 8, targets := 193 },{ cop := 3, region := 213, targets := 32 }], pairs := [(0,5),(3,0),(3,6),(3,7)], upper := (rows 7 290 28 42 208 225 193 193 449), lower := (rows 7 290 28 42 208 32 64 128 256), losses := [] }

theorem u32078 : Upper (D 7) (R 7) [6,288,24,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32078 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32079 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 20, targets := 162 }], pairs := [(2,1),(2,5),(2,7),(4,1)], upper := (rows 7 290 28 73 81 162 226 162 418), lower := (rows 7 290 28 73 81 32 64 128 256), losses := [] }

theorem u32079 : Upper (D 7) (R 7) [6,288,24,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32079 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32080 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 13, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 290 28 73 82 161 225 161 417), lower := (rows 7 290 28 73 82 32 64 128 256), losses := [] }

theorem u32080 : Upper (D 7) (R 7) [6,288,24,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32080 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32081 : Route 9 := (fun mask => (mask,id))

def c32081 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32081 : Upper (D 7) (R 7) [6,288,24,65,96] 13 := by
  apply FastRouting.sound _ _ [6,288,24,65,96] 13 (by decide) (choices 1) [1,2,128] r32081 c32081
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15097
  · exact u15098
  · exact u15099

theorem m32082_128 : Upper (D 7) (R 7) [6,288,24,65,129,128] 13 :=
  permutation_upper _ _ _ [6,288,24,65,129,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15101

def r32082 : Route 9 := (fun mask => (mask,id))

def c32082 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32082 : Upper (D 7) (R 7) [6,288,24,65,129] 13 := by
  apply FastRouting.sound _ _ [6,288,24,65,129] 13 (by decide) (choices 1) [2,64,128] r32082 c32082
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15100
  · exact u15101
  · exact m32082_128

def r32083 : Route 9 := (fun mask => (mask,id))

def c32083 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32083 : Upper (D 7) (R 7) [6,288,24,65,130] 13 := by
  apply FastRouting.sound _ _ [6,288,24,65,130] 13 (by decide) (choices 1) [1,64,128] r32083 c32083
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15102
  · exact u15103
  · exact u15104

def r32084 : Route 9 := (fun mask => (mask,id))

def c32084 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32084 : Upper (D 7) (R 7) [6,288,24,65,160] 13 := by
  apply FastRouting.sound _ _ [6,288,24,65,160] 13 (by decide) (choices 1) [1,2,64,128] r32084 c32084
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15105
  · exact u15106
  · exact u15107
  · exact u15108

def r32085 : Route 9 := (fun mask => (mask,id))

def c32085 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32085 : Upper (D 7) (R 7) [6,288,24,65,192] 13 := by
  apply FastRouting.sound _ _ [6,288,24,65,192] 13 (by decide) (choices 1) [1,2,128] r32085 c32085
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15109
  · exact u15110
  · exact u15111

def b32086 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 0, region := 240, targets := 2 },{ cop := 0, region := 200, targets := 32 }], pairs := [(0,6),(1,6),(3,5),(4,1)], upper := (rows 7 290 28 74 112 161 193 129 385), lower := (rows 7 290 28 74 112 32 64 128 256), losses := [] }

theorem u32086 : Upper (D 7) (R 7) [6,288,24,66,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32086 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32087 : Route 9 := (fun mask => (mask,id))

def c32087 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32087 : Upper (D 7) (R 7) [6,288,24,66,160] 13 := by
  apply FastRouting.sound _ _ [6,288,24,66,160] 13 (by decide) (choices 1) [1,64,128] r32087 c32087
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15112
  · exact u15113
  · exact u15114

def r32088 : Route 9 := (fun mask => (mask,id))

def c32088 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32088 : Upper (D 7) (R 7) [6,288,24,66,192] 13 := by
  apply FastRouting.sound _ _ [6,288,24,66,192] 13 (by decide) (choices 1) [1,128] r32088 c32088
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u15115
  · exact u15116

def r32089 : Route 9 := (fun mask => (mask,id))

def c32089 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32089 : Upper (D 7) (R 7) [6,288,24,96,192] 13 := by
  apply FastRouting.sound _ _ [6,288,24,96,192] 13 (by decide) (choices 1) [1,2,128] r32089 c32089
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15117
  · exact u15118
  · exact u15119

def b32090 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 20, targets := 35 }], pairs := [(2,0),(2,1),(2,5),(4,0)], upper := (rows 7 290 28 200 208 35 99 163 291), lower := (rows 7 290 28 200 208 32 64 128 256), losses := [] }

theorem u32090 : Upper (D 7) (R 7) [6,288,24,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32090 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32091 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 29, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 290 44 25 19 224 192 192 448), lower := (rows 7 290 44 25 19 32 64 128 256), losses := [] }

theorem u32091 : Upper (D 7) (R 7) [6,288,40,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32091 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32092 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 7 290 44 25 81 226 194 194 450), lower := (rows 7 290 44 25 81 32 64 128 256), losses := [] }

theorem u32092 : Upper (D 7) (R 7) [6,288,40,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32092 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32093 : Route 9 := (fun mask => (mask,id))

def c32093 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32093 : Upper (D 7) (R 7) [6,288,40,17,66] 13 := by
  apply FastRouting.sound _ _ [6,288,40,17,66] 13 (by decide) (choices 1) [1,64,128] r32093 c32093
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15120
  · exact u15121
  · exact u15122

def r32094 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c32094 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32094 : Upper (D 7) (R 7) [6,288,40,17,192] 13 := by
  apply FastRouting.sound _ _ [6,288,40,17,192] 13 (by decide) (choices 1) [1,2,64] r32094 c32094
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15123
  · exact u15124
  · exact u15125

def b32095 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 208, targets := 2 }], pairs := [(2,1),(3,5),(4,1),(4,5)], upper := (rows 7 290 44 26 81 225 193 193 449), lower := (rows 7 290 44 26 81 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 17 49 81 145 273), good := (rows 501 288 44 508 497 32 64 128 256) }] }

theorem u32095 : Upper (D 7) (R 7) [6,288,40,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32095 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32096 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c32096 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32096 : Upper (D 7) (R 7) [6,288,40,18,192] 13 := by
  apply FastRouting.sound _ _ [6,288,40,18,192] 13 (by decide) (choices 1) [1,64] r32096 c32096
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u15126
  · exact u15127

def b32097 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 16, targets := 192 }], pairs := [(3,5),(4,5),(4,6),(4,7)], upper := (rows 7 290 44 73 19 240 208 208 464), lower := (rows 7 290 44 73 19 32 64 128 256), losses := [] }

theorem u32097 : Upper (D 7) (R 7) [6,288,40,65,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32097 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32098 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 16, targets := 162 },{ cop := 4, region := 8, targets := 2 }], pairs := [(3,1),(4,1),(4,5),(4,7)], upper := (rows 7 290 44 73 81 178 210 146 402), lower := (rows 7 290 44 73 81 32 64 128 256), losses := [] }

theorem u32098 : Upper (D 7) (R 7) [6,288,40,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32098 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32099 : Route 9 := (fun mask => (mask,id))

def c32099 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32099 : Upper (D 7) (R 7) [6,288,40,65,66] 13 := by
  apply FastRouting.sound _ _ [6,288,40,65,66] 13 (by decide) (choices 1) [1,16,128] r32099 c32099
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15128
  · exact u15129
  · exact u15130

#print axioms u32099
end Delivery.IrregularNine14.P07

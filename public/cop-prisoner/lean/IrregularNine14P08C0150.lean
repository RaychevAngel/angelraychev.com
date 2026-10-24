import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0035
import IrregularNine14P08C0036

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r9000 : Route 9 := (fun mask => (mask,id))

def c9000 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9000 : Upper (D 8) (R 8) [34,68,129,80,384] 13 := by
  apply FastRouting.sound _ _ [34,68,129,80,384] 13 (by decide) (choices 1) [1,8] r9000 c9000
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2117
  · exact u2118

def b9001 : PairBound 9 := { available := 312, camps := [{ cop := 2, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 35 70 133 104 145 312 376 440 312), lower := (rows 35 70 133 104 145 32 64 128 256), losses := [] }

theorem u9001 : Upper (D 8) (R 8) [34,68,129,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9001 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9002 : Route 9 := (fun mask => (mask,id))

def c9002 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u9002 : Upper (D 8) (R 8) [34,68,129,96,136] 13 := by
  apply FastRouting.sound _ _ [34,68,129,96,136] 13 (by decide) (choices 1) [1,16,256] r9002 c9002
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2119
  · exact u2120
  · exact u2121

def r9003 : Route 9 := (fun mask => (mask,id))

def c9003 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u9003 : Upper (D 8) (R 8) [34,68,129,96,160] 13 := by
  apply FastRouting.sound _ _ [34,68,129,96,160] 13 (by decide) (choices 1) [1,8,16,256] r9003 c9003
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2122
  · exact u2123
  · exact u2124
  · exact u2125

def b9004 : PairBound 9 := { available := 184, camps := [{ cop := 4, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 133 104 273 184 248 184 440), lower := (rows 35 70 133 104 273 32 64 128 256), losses := [] }

theorem u9004 : Upper (D 8) (R 8) [34,68,129,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9004 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9005 : Route 9 := (fun mask => (mask,id))

def c9005 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9005 : Upper (D 8) (R 8) [34,68,129,96,264] 13 := by
  apply FastRouting.sound _ _ [34,68,129,96,264] 13 (by decide) (choices 1) [1,16,128] r9005 c9005
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2126
  · exact u2127
  · exact u2128

def r9006 : Route 9 := (fun mask => (mask,id))

def c9006 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9006 : Upper (D 8) (R 8) [34,68,129,96,288] 13 := by
  apply FastRouting.sound _ _ [34,68,129,96,288] 13 (by decide) (choices 1) [1,8,16,128] r9006 c9006
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2129
  · exact u2130
  · exact u2131
  · exact u2132

def r9007 : Route 9 := (fun mask => (mask,id))

def c9007 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9007 : Upper (D 8) (R 8) [34,68,129,96,384] 13 := by
  apply FastRouting.sound _ _ [34,68,129,96,384] 13 (by decide) (choices 1) [1,8,16] r9007 c9007
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2133
  · exact u2134
  · exact u2135

def b9008 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 70 133 137 280 112 112 240 368), lower := (rows 35 70 133 137 280 32 64 128 256), losses := [] }

theorem u9008 : Upper (D 8) (R 8) [34,68,129,129,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9008 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9009 : PairBound 9 := { available := 120, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 70 133 137 304 120 120 248 376), lower := (rows 35 70 133 137 304 32 64 128 256), losses := [] }

theorem u9009 : Upper (D 8) (R 8) [34,68,129,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9009 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9010 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 70 133 137 336 56 120 184 312), lower := (rows 35 70 133 137 336 32 64 128 256), losses := [] }

theorem u9010 : Upper (D 8) (R 8) [34,68,129,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9010 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9011 : PairBound 9 := { available := 104, camps := [{ cop := 4, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 133 152 273 104 104 232 360), lower := (rows 35 70 133 152 273 32 64 128 256), losses := [] }

theorem u9011 : Upper (D 8) (R 8) [34,68,129,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9011 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9012 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 133 152 280 97 97 225 353), lower := (rows 35 70 133 152 280 32 64 128 256), losses := [] }

theorem u9012 : Upper (D 8) (R 8) [34,68,129,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9012 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9013 : Route 9 := (fun mask => (mask,id))

def c9013 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9013 : Upper (D 8) (R 8) [34,68,129,144,288] 13 := by
  apply FastRouting.sound _ _ [34,68,129,144,288] 13 (by decide) (choices 1) [1,8,64] r9013 c9013
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2136
  · exact u2137
  · exact u2138

def r9014 : Route 9 := (fun mask => (mask,id))

def c9014 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9014 : Upper (D 8) (R 8) [34,68,129,144,320] 13 := by
  apply FastRouting.sound _ _ [34,68,129,144,320] 13 (by decide) (choices 1) [1,8] r9014 c9014
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2139
  · exact u2140

def b9015 : PairBound 9 := { available := 120, camps := [{ cop := 4, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 133 168 273 120 120 248 376), lower := (rows 35 70 133 168 273 32 64 128 256), losses := [] }

theorem u9015 : Upper (D 8) (R 8) [34,68,129,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9015 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9016 : Route 9 := (fun mask => (mask,id))

def c9016 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9016 : Upper (D 8) (R 8) [34,68,129,160,264] 13 := by
  apply FastRouting.sound _ _ [34,68,129,160,264] 13 (by decide) (choices 1) [1,16,64] r9016 c9016
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2141
  · exact u2142
  · exact u2143

def r9017 : Route 9 := (fun mask => (mask,id))

def c9017 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9017 : Upper (D 8) (R 8) [34,68,129,160,288] 13 := by
  apply FastRouting.sound _ _ [34,68,129,160,288] 13 (by decide) (choices 1) [1,8,16,64] r9017 c9017
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2144
  · exact u2145
  · exact u2146
  · exact u2147

def r9018 : Route 9 := (fun mask => (mask,id))

def c9018 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9018 : Upper (D 8) (R 8) [34,68,129,160,320] 13 := by
  apply FastRouting.sound _ _ [34,68,129,160,320] 13 (by decide) (choices 1) [1,8,16] r9018 c9018
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2148
  · exact u2149
  · exact u2150

def b9019 : PairBound 9 := { available := 56, camps := [{ cop := 4, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 133 200 273 56 120 184 312), lower := (rows 35 70 133 200 273 32 64 128 256), losses := [] }

theorem u9019 : Upper (D 8) (R 8) [34,68,129,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9019 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9020 : Route 9 := (fun mask => (mask,id))

def c9020 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9020 : Upper (D 8) (R 8) [34,68,129,192,264] 13 := by
  apply FastRouting.sound _ _ [34,68,129,192,264] 13 (by decide) (choices 1) [1,16] r9020 c9020
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2151
  · exact u2152

def r9021 : Route 9 := (fun mask => (mask,id))

def c9021 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9021 : Upper (D 8) (R 8) [34,68,129,192,288] 13 := by
  apply FastRouting.sound _ _ [34,68,129,192,288] 13 (by decide) (choices 1) [1,8,16] r9021 c9021
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2153
  · exact u2154
  · exact u2155

def b9022 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 24, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 140 25 49 480 480 480 480), lower := (rows 35 70 140 25 49 32 64 128 256), losses := [] }

theorem u9022 : Upper (D 8) (R 8) [34,68,136,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9022 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9023 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 486, targets := 1 }], pairs := [(1,0)], upper := (rows 35 70 140 25 81 416 480 416 416), lower := (rows 35 70 140 25 81 32 64 128 256), losses := [] }

theorem u9023 : Upper (D 8) (R 8) [34,68,136,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9023 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9024 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 140 25 112 417 481 417 417), lower := (rows 35 70 140 25 112 32 64 128 256), losses := [] }

theorem u9024 : Upper (D 8) (R 8) [34,68,136,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9024 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9025 : PairBound 9 := { available := 352, camps := [{ cop := 4, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 70 140 25 145 352 352 480 352), lower := (rows 35 70 140 25 145 32 64 128 256), losses := [] }

theorem u9025 : Upper (D 8) (R 8) [34,68,136,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9025 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9026 : PairBound 9 := { available := 353, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 140 25 176 353 353 481 353), lower := (rows 35 70 140 25 176 32 64 128 256), losses := [] }

theorem u9026 : Upper (D 8) (R 8) [34,68,136,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9026 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9027 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 140 25 208 289 353 417 289), lower := (rows 35 70 140 25 208 32 64 128 256), losses := [] }

theorem u9027 : Upper (D 8) (R 8) [34,68,136,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9027 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9028 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 70 140 25 273 224 224 224 480), lower := (rows 35 70 140 25 273 32 64 128 256), losses := [] }

theorem u9028 : Upper (D 8) (R 8) [34,68,136,17,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9028 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9029 : Route 9 := (fun mask => (mask,id))

def c9029 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u9029 : Upper (D 8) (R 8) [34,68,136,17,288] 13 := by
  apply FastRouting.sound _ _ [34,68,136,17,288] 13 (by decide) (choices 1) [1,64,128] r9029 c9029
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2156
  · exact u2157
  · exact u2158

def b9030 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 140 25 336 161 225 161 417), lower := (rows 35 70 140 25 336 32 64 128 256), losses := [] }

theorem u9030 : Upper (D 8) (R 8) [34,68,136,17,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9030 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9031 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 140 25 400 97 97 225 353), lower := (rows 35 70 140 25 400 32 64 128 256), losses := [] }

theorem u9031 : Upper (D 8) (R 8) [34,68,136,17,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9031 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9032 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 24, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 140 56 49 481 449 449 449), lower := (rows 35 70 140 56 49 32 64 128 256), losses := [] }

theorem u9032 : Upper (D 8) (R 8) [34,68,136,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9032 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9033 : PairBound 9 := { available := 417, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 140 56 81 417 481 417 417), lower := (rows 35 70 140 56 81 32 64 128 256), losses := [] }

theorem u9033 : Upper (D 8) (R 8) [34,68,136,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9033 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9034 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 140 56 112 417 449 385 385), lower := (rows 35 70 140 56 112 32 64 128 256), losses := [] }

theorem u9034 : Upper (D 8) (R 8) [34,68,136,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9034 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9035 : PairBound 9 := { available := 353, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 140 56 145 353 353 481 353), lower := (rows 35 70 140 56 145 32 64 128 256), losses := [] }

theorem u9035 : Upper (D 8) (R 8) [34,68,136,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9035 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9036 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 35 70 140 56 176 353 321 449 321), lower := (rows 35 70 140 56 176 32 64 128 256), losses := [] }

theorem u9036 : Upper (D 8) (R 8) [34,68,136,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9036 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9037 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 140 56 208 289 353 417 289), lower := (rows 35 70 140 56 208 32 64 128 256), losses := [] }

theorem u9037 : Upper (D 8) (R 8) [34,68,136,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9037 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9038 : Route 9 := (fun mask => (mask,id))

def c9038 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u9038 : Upper (D 8) (R 8) [34,68,136,48,257] 13 := by
  apply FastRouting.sound _ _ [34,68,136,48,257] 13 (by decide) (choices 1) [1,64,128] r9038 c9038
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2159
  · exact u2160
  · exact u2161

def b9039 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 140 56 304 225 193 193 449), lower := (rows 35 70 140 56 304 32 64 128 256), losses := [] }

theorem u9039 : Upper (D 8) (R 8) [34,68,136,48,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9039 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9040 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 140 56 336 161 225 161 417), lower := (rows 35 70 140 56 336 32 64 128 256), losses := [] }

theorem u9040 : Upper (D 8) (R 8) [34,68,136,48,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9040 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9041 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 140 56 400 97 97 225 353), lower := (rows 35 70 140 56 400 32 64 128 256), losses := [] }

theorem u9041 : Upper (D 8) (R 8) [34,68,136,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9041 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9042 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 35 70 140 265 49 240 240 240 496), lower := (rows 35 70 140 265 49 32 64 128 256), losses := [] }

theorem u9042 : Upper (D 8) (R 8) [34,68,136,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9042 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9043 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 140 265 81 176 240 176 432), lower := (rows 35 70 140 265 81 32 64 128 256), losses := [] }

theorem u9043 : Upper (D 8) (R 8) [34,68,136,257,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9043 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9044 : Route 9 := (fun mask => (mask,id))

def c9044 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9044 : Upper (D 8) (R 8) [34,68,136,257,96] 13 := by
  apply FastRouting.sound _ _ [34,68,136,257,96] 13 (by decide) (choices 1) [1,16,128] r9044 c9044
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2162
  · exact u2163
  · exact u2164

def b9045 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 360, targets := 128 }], pairs := [(3,7)], upper := (rows 35 70 140 265 145 112 112 240 368), lower := (rows 35 70 140 265 145 32 64 128 256), losses := [] }

theorem u9045 : Upper (D 8) (R 8) [34,68,136,257,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9045 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9046 : Route 9 := (fun mask => (mask,id))

def c9046 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9046 : Upper (D 8) (R 8) [34,68,136,257,160] 13 := by
  apply FastRouting.sound _ _ [34,68,136,257,160] 13 (by decide) (choices 1) [1,16,64] r9046 c9046
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2165
  · exact u2166
  · exact u2167

def r9047 : Route 9 := (fun mask => (mask,id))

def c9047 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9047 : Upper (D 8) (R 8) [34,68,136,257,192] 13 := by
  apply FastRouting.sound _ _ [34,68,136,257,192] 13 (by decide) (choices 1) [1,16] r9047 c9047
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2168
  · exact u2169

def b9048 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 35 70 140 280 49 225 225 225 481), lower := (rows 35 70 140 280 49 32 64 128 256), losses := [] }

theorem u9048 : Upper (D 8) (R 8) [34,68,136,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9048 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9049 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 140 280 81 161 225 161 417), lower := (rows 35 70 140 280 81 32 64 128 256), losses := [] }

theorem u9049 : Upper (D 8) (R 8) [34,68,136,272,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9049 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9050 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 140 280 112 161 225 161 417), lower := (rows 35 70 140 280 112 32 64 128 256), losses := [] }

theorem u9050 : Upper (D 8) (R 8) [34,68,136,272,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9050 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9051 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 140 280 145 97 97 225 353), lower := (rows 35 70 140 280 145 32 64 128 256), losses := [] }

theorem u9051 : Upper (D 8) (R 8) [34,68,136,272,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9051 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9052 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 140 280 176 97 97 225 353), lower := (rows 35 70 140 280 176 32 64 128 256), losses := [] }

theorem u9052 : Upper (D 8) (R 8) [34,68,136,272,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9052 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9053 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 140 280 208 33 97 161 289), lower := (rows 35 70 140 280 208 32 64 128 256), losses := [] }

theorem u9053 : Upper (D 8) (R 8) [34,68,136,272,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9053 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9054 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 35 70 140 296 49 241 209 209 465), lower := (rows 35 70 140 296 49 32 64 128 256), losses := [] }

theorem u9054 : Upper (D 8) (R 8) [34,68,136,288,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9054 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9055 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 140 296 81 177 241 177 433), lower := (rows 35 70 140 296 81 32 64 128 256), losses := [] }

theorem u9055 : Upper (D 8) (R 8) [34,68,136,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9055 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9056 : Route 9 := (fun mask => (mask,id))

def c9056 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9056 : Upper (D 8) (R 8) [34,68,136,288,96] 13 := by
  apply FastRouting.sound _ _ [34,68,136,288,96] 13 (by decide) (choices 1) [1,16,128] r9056 c9056
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2170
  · exact u2171
  · exact u2172

def b9057 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 360, targets := 128 }], pairs := [(3,7)], upper := (rows 35 70 140 296 145 113 113 241 369), lower := (rows 35 70 140 296 145 32 64 128 256), losses := [] }

theorem u9057 : Upper (D 8) (R 8) [34,68,136,288,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9057 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9058 : Route 9 := (fun mask => (mask,id))

def c9058 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9058 : Upper (D 8) (R 8) [34,68,136,288,160] 13 := by
  apply FastRouting.sound _ _ [34,68,136,288,160] 13 (by decide) (choices 1) [1,16,64] r9058 c9058
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2173
  · exact u2174
  · exact u2175

def r9059 : Route 9 := (fun mask => (mask,id))

def c9059 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9059 : Upper (D 8) (R 8) [34,68,136,288,192] 13 := by
  apply FastRouting.sound _ _ [34,68,136,288,192] 13 (by decide) (choices 1) [1,16] r9059 c9059
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2176
  · exact u2177

#print axioms u9059
end Delivery.IrregularNine14.P08

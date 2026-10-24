import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P10C0013
import IrregularNine14P10C0014

namespace Delivery.IrregularNine14.P10
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r2100 : Route 9 := (fun mask => (mask,id))

def c2100 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2100 : Upper (D 10) (R 10) [34,68,129,288,384] 13 := by
  apply FastRouting.sound _ _ [34,68,129,288,384] 13 (by decide) (choices 1) [8,16,64] r2100 c2100
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u800
  · exact u801
  · exact u802

def b2101 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 176, targets := 64 },{ cop := 4, region := 104, targets := 128 }], pairs := [(3,7),(4,6)], upper := (rows 35 70 133 328 400 56 120 184 312), lower := (rows 35 70 133 328 400 32 64 128 256), losses := [] }

theorem u2101 : Upper (D 10) (R 10) [34,68,129,320,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2101 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2102 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 8, targets := 192 }], pairs := [(3,6),(3,7)], upper := (rows 35 70 140 56 112 417 449 385 385), lower := (rows 35 70 140 56 112 32 64 128 256), losses := [] }

theorem u2102 : Upper (D 10) (R 10) [34,68,136,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2102 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2103 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 12, targets := 320 }], pairs := [(2,6),(2,8)], upper := (rows 35 70 140 56 176 353 321 449 321), lower := (rows 35 70 140 56 176 32 64 128 256), losses := [] }

theorem u2103 : Upper (D 10) (R 10) [34,68,136,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2103 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2104 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 70 140 56 208 289 353 417 289), lower := (rows 35 70 140 56 208 32 64 128 256), losses := [] }

theorem u2104 : Upper (D 10) (R 10) [34,68,136,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2104 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2105 : PairBound 9 := { available := 449, camps := [{ cop := 4, region := 8, targets := 192 }], pairs := [(3,6),(3,7)], upper := (rows 35 70 140 56 304 481 449 449 449), lower := (rows 35 70 140 56 304 32 64 128 256), losses := [] }

theorem u2105 : Upper (D 10) (R 10) [34,68,136,48,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2105 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2106 : Route 9 := (fun mask => (mask,id))

def c2106 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u2106 : Upper (D 10) (R 10) [34,68,136,48,320] 13 := by
  apply FastRouting.sound _ _ [34,68,136,48,320] 13 (by decide) (choices 1) [1,128,256] r2106 c2106
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u803
  · exact u804
  · exact u805

def b2107 : PairBound 9 := { available := 353, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 70 140 56 400 353 353 481 353), lower := (rows 35 70 140 56 400 32 64 128 256), losses := [] }

theorem u2107 : Upper (D 10) (R 10) [34,68,136,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2107 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2108 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 70 140 73 176 304 368 432 304), lower := (rows 35 70 140 73 176 32 64 128 256), losses := [] }

theorem u2108 : Upper (D 10) (R 10) [34,68,136,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2108 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2109 : PairBound 9 := { available := 432, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 70 140 73 304 432 496 432 432), lower := (rows 35 70 140 73 304 32 64 128 256), losses := [] }

theorem u2109 : Upper (D 10) (R 10) [34,68,136,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2109 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2110 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 70 140 73 400 304 368 432 304), lower := (rows 35 70 140 73 400 32 64 128 256), losses := [] }

theorem u2110 : Upper (D 10) (R 10) [34,68,136,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2110 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2111 : PairBound 9 := { available := 288, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 70 140 88 145 288 352 416 288), lower := (rows 35 70 140 88 145 32 64 128 256), losses := [] }

theorem u2111 : Upper (D 10) (R 10) [34,68,136,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2111 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2112 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 70 140 88 176 289 353 417 289), lower := (rows 35 70 140 88 176 32 64 128 256), losses := [] }

theorem u2112 : Upper (D 10) (R 10) [34,68,136,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2112 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2113 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 70 140 88 273 416 480 416 416), lower := (rows 35 70 140 88 273 32 64 128 256), losses := [] }

theorem u2113 : Upper (D 10) (R 10) [34,68,136,80,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2113 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2114 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 70 140 88 304 417 481 417 417), lower := (rows 35 70 140 88 304 32 64 128 256), losses := [] }

theorem u2114 : Upper (D 10) (R 10) [34,68,136,80,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2114 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2115 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 70 140 88 400 289 353 417 289), lower := (rows 35 70 140 88 400 32 64 128 256), losses := [] }

theorem u2115 : Upper (D 10) (R 10) [34,68,136,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2115 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2116 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 70 140 104 145 304 368 432 304), lower := (rows 35 70 140 104 145 32 64 128 256), losses := [] }

theorem u2116 : Upper (D 10) (R 10) [34,68,136,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2116 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2117 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 70 140 104 176 305 337 401 273), lower := (rows 35 70 140 104 176 32 64 128 256), losses := [] }

theorem u2117 : Upper (D 10) (R 10) [34,68,136,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2117 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2118 : PairBound 9 := { available := 432, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 70 140 104 273 432 496 432 432), lower := (rows 35 70 140 104 273 32 64 128 256), losses := [] }

theorem u2118 : Upper (D 10) (R 10) [34,68,136,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2118 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2119 : PairBound 9 := { available := 401, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 70 140 104 304 433 465 401 401), lower := (rows 35 70 140 104 304 32 64 128 256), losses := [] }

theorem u2119 : Upper (D 10) (R 10) [34,68,136,96,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2119 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2120 : PairBound 9 := { available := 305, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 70 140 104 400 305 369 433 305), lower := (rows 35 70 140 104 400 32 64 128 256), losses := [] }

theorem u2120 : Upper (D 10) (R 10) [34,68,136,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2120 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2121 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 70 140 137 112 304 368 432 304), lower := (rows 35 70 140 137 112 32 64 128 256), losses := [] }

theorem u2121 : Upper (D 10) (R 10) [34,68,136,129,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2121 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2122 : PairBound 9 := { available := 368, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 70 140 137 304 368 368 496 368), lower := (rows 35 70 140 137 304 32 64 128 256), losses := [] }

theorem u2122 : Upper (D 10) (R 10) [34,68,136,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2122 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2123 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 70 140 137 336 304 368 432 304), lower := (rows 35 70 140 137 336 32 64 128 256), losses := [] }

theorem u2123 : Upper (D 10) (R 10) [34,68,136,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2123 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2124 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 70 140 152 112 289 353 417 289), lower := (rows 35 70 140 152 112 32 64 128 256), losses := [] }

theorem u2124 : Upper (D 10) (R 10) [34,68,136,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2124 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2125 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 70 140 152 273 352 352 480 352), lower := (rows 35 70 140 152 273 32 64 128 256), losses := [] }

theorem u2125 : Upper (D 10) (R 10) [34,68,136,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2125 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2126 : PairBound 9 := { available := 353, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 70 140 152 304 353 353 481 353), lower := (rows 35 70 140 152 304 32 64 128 256), losses := [] }

theorem u2126 : Upper (D 10) (R 10) [34,68,136,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2126 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2127 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 70 140 152 336 289 353 417 289), lower := (rows 35 70 140 152 336 32 64 128 256), losses := [] }

theorem u2127 : Upper (D 10) (R 10) [34,68,136,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2127 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2128 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 70 140 168 112 305 337 401 273), lower := (rows 35 70 140 168 112 32 64 128 256), losses := [] }

theorem u2128 : Upper (D 10) (R 10) [34,68,136,160,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2128 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2129 : PairBound 9 := { available := 368, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 70 140 168 273 368 368 496 368), lower := (rows 35 70 140 168 273 32 64 128 256), losses := [] }

theorem u2129 : Upper (D 10) (R 10) [34,68,136,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2129 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2130 : PairBound 9 := { available := 337, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 70 140 168 304 369 337 465 337), lower := (rows 35 70 140 168 304 32 64 128 256), losses := [] }

theorem u2130 : Upper (D 10) (R 10) [34,68,136,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2130 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2131 : PairBound 9 := { available := 305, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 70 140 168 336 305 369 433 305), lower := (rows 35 70 140 168 336 32 64 128 256), losses := [] }

theorem u2131 : Upper (D 10) (R 10) [34,68,136,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2131 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2132 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 6, targets := 288 }], pairs := [(1,5),(1,8)], upper := (rows 35 70 140 200 273 304 368 432 304), lower := (rows 35 70 140 200 273 32 64 128 256), losses := [] }

theorem u2132 : Upper (D 10) (R 10) [34,68,136,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2132 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2133 : PairBound 9 := { available := 305, camps := [{ cop := 3, region := 6, targets := 288 }], pairs := [(1,5),(1,8)], upper := (rows 35 70 140 200 304 305 369 433 305), lower := (rows 35 70 140 200 304 32 64 128 256), losses := [] }

theorem u2133 : Upper (D 10) (R 10) [34,68,136,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2133 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2134 : Route 9 := (fun mask => (mask,id))

def c2134 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u2134 : Upper (D 10) (R 10) [34,68,136,257,96] 13 := by
  apply FastRouting.sound _ _ [34,68,136,257,96] 13 (by decide) (choices 1) [16,128,256] r2134 c2134
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u806
  · exact u807
  · exact u808

def r2135 : Route 9 := (fun mask => (mask,id))

def c2135 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u2135 : Upper (D 10) (R 10) [34,68,136,257,160] 13 := by
  apply FastRouting.sound _ _ [34,68,136,257,160] 13 (by decide) (choices 1) [16,64,256] r2135 c2135
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u809
  · exact u810
  · exact u811

def r2136 : Route 9 := (fun mask => (mask,id))

def c2136 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u2136 : Upper (D 10) (R 10) [34,68,136,257,192] 13 := by
  apply FastRouting.sound _ _ [34,68,136,257,192] 13 (by decide) (choices 1) [16,256] r2136 c2136
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u812
  · exact u813

def r2137 : Route 9 := (fun mask => (mask,id))

def c2137 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2137 : Upper (D 10) (R 10) [34,68,136,257,288] 13 := by
  apply FastRouting.sound _ _ [34,68,136,257,288] 13 (by decide) (choices 1) [16,64,128] r2137 c2137
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u814
  · exact u815
  · exact u816

def r2138 : Route 9 := (fun mask => (mask,id))

def c2138 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2138 : Upper (D 10) (R 10) [34,68,136,257,320] 13 := by
  apply FastRouting.sound _ _ [34,68,136,257,320] 13 (by decide) (choices 1) [16,128] r2138 c2138
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u817
  · exact u818

def r2139 : Route 9 := (fun mask => (mask,id))

def c2139 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2139 : Upper (D 10) (R 10) [34,68,136,257,384] 13 := by
  apply FastRouting.sound _ _ [34,68,136,257,384] 13 (by decide) (choices 1) [16,64] r2139 c2139
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u819
  · exact u820

def b2140 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 70 140 280 81 416 480 416 416), lower := (rows 35 70 140 280 81 32 64 128 256), losses := [] }

theorem u2140 : Upper (D 10) (R 10) [34,68,136,272,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2140 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2141 : Route 9 := (fun mask => (mask,id))

def c2141 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u2141 : Upper (D 10) (R 10) [34,68,136,272,96] 13 := by
  apply FastRouting.sound _ _ [34,68,136,272,96] 13 (by decide) (choices 1) [1,128,256] r2141 c2141
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u821
  · exact u822
  · exact u823

def b2142 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 70 140 280 145 352 352 480 352), lower := (rows 35 70 140 280 145 32 64 128 256), losses := [] }

theorem u2142 : Upper (D 10) (R 10) [34,68,136,272,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2142 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2143 : PairBound 9 := { available := 353, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 70 140 280 176 353 353 481 353), lower := (rows 35 70 140 280 176 32 64 128 256), losses := [] }

theorem u2143 : Upper (D 10) (R 10) [34,68,136,272,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2143 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2144 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 70 140 280 208 289 353 417 289), lower := (rows 35 70 140 280 208 32 64 128 256), losses := [] }

theorem u2144 : Upper (D 10) (R 10) [34,68,136,272,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2144 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2145 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 35 70 140 280 273 224 224 224 480), lower := (rows 35 70 140 280 273 32 64 128 256), losses := [] }

theorem u2145 : Upper (D 10) (R 10) [34,68,136,272,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2145 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2146 : PairBound 9 := { available := 225, camps := [{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 35 70 140 280 304 225 225 225 481), lower := (rows 35 70 140 280 304 32 64 128 256), losses := [] }

theorem u2146 : Upper (D 10) (R 10) [34,68,136,272,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2146 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2147 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 35 70 140 280 336 161 225 161 417), lower := (rows 35 70 140 280 336 32 64 128 256), losses := [] }

theorem u2147 : Upper (D 10) (R 10) [34,68,136,272,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2147 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2148 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 12, targets := 96 }], pairs := [(2,5),(2,6)], upper := (rows 35 70 140 280 400 97 97 225 353), lower := (rows 35 70 140 280 400 32 64 128 256), losses := [] }

theorem u2148 : Upper (D 10) (R 10) [34,68,136,272,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2148 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2149 : PairBound 9 := { available := 432, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 70 140 296 81 432 496 432 432), lower := (rows 35 70 140 296 81 32 64 128 256), losses := [] }

theorem u2149 : Upper (D 10) (R 10) [34,68,136,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2149 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2150 : Route 9 := (fun mask => (mask,id))

def c2150 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u2150 : Upper (D 10) (R 10) [34,68,136,288,96] 13 := by
  apply FastRouting.sound _ _ [34,68,136,288,96] 13 (by decide) (choices 1) [1,16,128,256] r2150 c2150
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u824
  · exact u825
  · exact u826
  · exact u827

def r2151 : Route 9 := (fun mask => (mask,id))

def c2151 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u2151 : Upper (D 10) (R 10) [34,68,136,288,129] 13 := by
  apply FastRouting.sound _ _ [34,68,136,288,129] 13 (by decide) (choices 1) [16,64,256] r2151 c2151
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u828
  · exact u829
  · exact u830

def r2152 : Route 9 := (fun mask => (mask,id))

def c2152 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u2152 : Upper (D 10) (R 10) [34,68,136,288,160] 13 := by
  apply FastRouting.sound _ _ [34,68,136,288,160] 13 (by decide) (choices 1) [1,16,64,256] r2152 c2152
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u831
  · exact u832
  · exact u833
  · exact u834

def r2153 : Route 9 := (fun mask => (mask,id))

def c2153 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u2153 : Upper (D 10) (R 10) [34,68,136,288,192] 13 := by
  apply FastRouting.sound _ _ [34,68,136,288,192] 13 (by decide) (choices 1) [1,16,256] r2153 c2153
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u835
  · exact u836
  · exact u837

def r2154 : Route 9 := (fun mask => (mask,id))

def c2154 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2154 : Upper (D 10) (R 10) [34,68,136,288,257] 13 := by
  apply FastRouting.sound _ _ [34,68,136,288,257] 13 (by decide) (choices 1) [16,64,128] r2154 c2154
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u838
  · exact u839
  · exact u840

def b2155 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 16, targets := 192 }], pairs := [(4,6),(4,7)], upper := (rows 35 70 140 296 304 241 209 209 465), lower := (rows 35 70 140 296 304 32 64 128 256), losses := [] }

theorem u2155 : Upper (D 10) (R 10) [34,68,136,288,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2155 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2156 : Route 9 := (fun mask => (mask,id))

def c2156 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2156 : Upper (D 10) (R 10) [34,68,136,288,320] 13 := by
  apply FastRouting.sound _ _ [34,68,136,288,320] 13 (by decide) (choices 1) [1,16,128] r2156 c2156
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u841
  · exact u842
  · exact u843

def r2157 : Route 9 := (fun mask => (mask,id))

def c2157 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2157 : Upper (D 10) (R 10) [34,68,136,288,384] 13 := by
  apply FastRouting.sound _ _ [34,68,136,288,384] 13 (by decide) (choices 1) [1,16,64] r2157 c2157
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u844
  · exact u845
  · exact u846

def b2158 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 70 140 328 145 304 368 432 304), lower := (rows 35 70 140 328 145 32 64 128 256), losses := [] }

theorem u2158 : Upper (D 10) (R 10) [34,68,136,320,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2158 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2159 : PairBound 9 := { available := 305, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 70 140 328 176 305 369 433 305), lower := (rows 35 70 140 328 176 32 64 128 256), losses := [] }

theorem u2159 : Upper (D 10) (R 10) [34,68,136,320,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2159 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

#print axioms u2159
end Delivery.IrregularNine14.P10

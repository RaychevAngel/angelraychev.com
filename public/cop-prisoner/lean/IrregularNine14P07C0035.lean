import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0001

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r2100 : Route 9 := (fun mask => (mask,id))

def c2100 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2100 : Upper (D 7) (R 7) [6,96,9,144,288,2,128] 13 := by
  apply FastRouting.sound _ _ [6,96,9,144,288,2,128] 13 (by decide) (choices 1) [1,64] r2100 c2100
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u110
  · exact u111

def b2101 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 1, region := 272, targets := 128 }], pairs := [(1,0),(3,0),(4,0),(4,7)], upper := (rows 7 98 13 152 304 160 65 194 322), lower := (rows 7 98 13 152 304 160 65 128 256), losses := [] }

theorem u2101 : Upper (D 7) (R 7) [6,96,9,144,288,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2101 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2102 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 66, targets := 129 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 7 98 13 152 304 160 66 193 321), lower := (rows 7 98 13 152 304 160 66 128 256), losses := [{ target := 7, region := (rows 9 50 12 8 16 32 123 0 269), good := (rows 327 98 333 351 370 98 66 0 256) }] }

theorem u2102 : Upper (D 7) (R 7) [6,96,9,144,288,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2102 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2103 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 98 13 168 146 288 65 208 336), lower := (rows 7 98 13 168 146 288 65 128 256), losses := [] }

theorem u2103 : Upper (D 7) (R 7) [6,96,9,160,130,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2103 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2104 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 82, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 7 98 13 168 146 288 80 193 321), lower := (rows 7 98 13 168 146 288 80 128 256), losses := [] }

theorem u2104 : Upper (D 7) (R 7) [6,96,9,160,130,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2104 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2105 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 98 13 168 208 288 65 146 274), lower := (rows 7 98 13 168 208 288 65 128 256), losses := [] }

theorem u2105 : Upper (D 7) (R 7) [6,96,9,160,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2105 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2106 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 98 13 168 208 288 66 145 273), lower := (rows 7 98 13 168 208 288 66 128 256), losses := [] }

theorem u2106 : Upper (D 7) (R 7) [6,96,9,160,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2106 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2107 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 141, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 98 13 168 208 288 80 131 259), lower := (rows 7 98 13 168 208 288 80 128 256), losses := [] }

theorem u2107 : Upper (D 7) (R 7) [6,96,9,160,192,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2107 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2108 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 98 13 168 274 48 65 192 448), lower := (rows 7 98 13 168 274 48 65 128 256), losses := [] }

theorem u2108 : Upper (D 7) (R 7) [6,96,9,160,258,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2108 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r2109 : Route 9 := (fun mask => (mask,id))

def c2109 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2109 : Upper (D 7) (R 7) [6,96,9,160,258,16,128] 13 := by
  apply FastRouting.sound _ _ [6,96,9,160,258,16,128] 13 (by decide) (choices 1) [1,64] r2109 c2109
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u112
  · exact u113

def b2110 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 6, region := 34, targets := 128 }], pairs := [(1,0),(1,7),(2,1),(3,0)], upper := (rows 7 98 13 280 145 34 192 224 352), lower := (rows 7 98 13 280 145 34 192 128 256), losses := [{ target := 1, region := (rows 1 0 21 9 17 32 243 162 290), good := (rows 477 480 93 348 221 480 192 192 256) }] }

theorem u2110 : Upper (D 7) (R 7) [6,96,9,272,129,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2110 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2111 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 13 280 145 96 192 162 290), lower := (rows 7 98 13 280 145 96 192 128 256), losses := [] }

theorem u2111 : Upper (D 7) (R 7) [6,96,9,272,129,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2111 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2112 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(3,1),(4,0)], upper := (rows 7 98 13 280 146 33 192 224 352), lower := (rows 7 98 13 280 146 33 192 128 256), losses := [{ target := 1, region := (rows 1 0 4 24 16 37 247 167 295), good := (rows 485 480 493 344 472 481 192 192 256) }] }

theorem u2112 : Upper (D 7) (R 7) [6,96,9,272,130,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2112 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2113 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 13 280 146 96 192 161 289), lower := (rows 7 98 13 280 146 96 192 128 256), losses := [] }

theorem u2113 : Upper (D 7) (R 7) [6,96,9,272,130,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2113 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2114 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 103, targets := 128 },{ cop := 5, region := 66, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 7 98 13 280 176 33 66 192 448), lower := (rows 7 98 13 280 176 33 66 128 256), losses := [] }

theorem u2114 : Upper (D 7) (R 7) [6,96,9,272,160,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2114 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r2115 : Route 9 := (fun mask => (mask,id))

def c2115 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2115 : Upper (D 7) (R 7) [6,96,9,272,160,1,128] 13 := by
  apply FastRouting.sound _ _ [6,96,9,272,160,1,128] 13 (by decide) (choices 1) [2,64] r2115 c2115
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u114
  · exact u115

def b2116 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 103, targets := 128 },{ cop := 6, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 7 98 13 280 176 34 65 192 448), lower := (rows 7 98 13 280 176 34 65 128 256), losses := [] }

theorem u2116 : Upper (D 7) (R 7) [6,96,9,272,160,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2116 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r2117 : Route 9 := (fun mask => (mask,id))

def c2117 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2117 : Upper (D 7) (R 7) [6,96,9,272,160,2,128] 13 := by
  apply FastRouting.sound _ _ [6,96,9,272,160,2,128] 13 (by decide) (choices 1) [1,64] r2117 c2117
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u116
  · exact u117

def b2118 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 87, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 98 13 296 81 160 66 144 400), lower := (rows 7 98 13 296 81 160 66 128 256), losses := [] }

theorem u2118 : Upper (D 7) (R 7) [6,96,9,288,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2118 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2119 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 87, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 98 13 296 81 160 80 130 386), lower := (rows 7 98 13 296 81 160 80 128 256), losses := [] }

theorem u2119 : Upper (D 7) (R 7) [6,96,9,288,65,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2119 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2120 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 7 98 13 296 81 160 192 146 274), lower := (rows 7 98 13 296 81 160 192 128 256), losses := [] }

theorem u2120 : Upper (D 7) (R 7) [6,96,9,288,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2120 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2121 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 71, targets := 128 },{ cop := 4, region := 98, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 7 98 13 296 145 160 66 208 336), lower := (rows 7 98 13 296 145 160 66 128 256), losses := [] }

theorem u2121 : Upper (D 7) (R 7) [6,96,9,288,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2121 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2122 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 269, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 7 98 13 296 145 160 80 194 322), lower := (rows 7 98 13 296 145 160 80 128 256), losses := [] }

theorem u2122 : Upper (D 7) (R 7) [6,96,9,288,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2122 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2123 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 98 13 296 146 48 65 192 448), lower := (rows 7 98 13 296 146 48 65 128 256), losses := [] }

theorem u2123 : Upper (D 7) (R 7) [6,96,9,288,130,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2123 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2124 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 269, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 7 98 13 296 146 48 192 193 321), lower := (rows 7 98 13 296 146 48 192 128 256), losses := [] }

theorem u2124 : Upper (D 7) (R 7) [6,96,9,288,130,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2124 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2125 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 71, targets := 128 },{ cop := 6, region := 178, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 7 98 13 296 146 160 65 208 336), lower := (rows 7 98 13 296 146 160 65 128 256), losses := [] }

theorem u2125 : Upper (D 7) (R 7) [6,96,9,288,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2125 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2126 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 269, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 7 98 13 296 146 160 80 193 321), lower := (rows 7 98 13 296 146 160 80 128 256), losses := [] }

theorem u2126 : Upper (D 7) (R 7) [6,96,9,288,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2126 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2127 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 71, targets := 128 },{ cop := 6, region := 178, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 7 98 13 296 208 160 65 146 274), lower := (rows 7 98 13 296 208 160 65 128 256), losses := [] }

theorem u2127 : Upper (D 7) (R 7) [6,96,9,288,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2127 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2128 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 71, targets := 128 },{ cop := 5, region := 66, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 7 98 13 296 208 160 66 145 273), lower := (rows 7 98 13 296 208 160 66 128 256), losses := [] }

theorem u2128 : Upper (D 7) (R 7) [6,96,9,288,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2128 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2129 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 269, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 13 296 208 160 80 131 259), lower := (rows 7 98 13 296 208 160 80 128 256), losses := [] }

theorem u2129 : Upper (D 7) (R 7) [6,96,9,288,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2129 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2130 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 1, region := 392, targets := 2 }], pairs := [(1,0),(3,0),(3,1)], upper := (rows 7 98 13 392 145 34 80 224 352), lower := (rows 7 98 13 392 145 34 80 128 256), losses := [] }

theorem u2130 : Upper (D 7) (R 7) [6,96,9,384,129,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2130 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2131 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5),(4,5)], upper := (rows 7 98 13 392 145 34 96 208 336), lower := (rows 7 98 13 392 145 34 96 128 256), losses := [] }

theorem u2131 : Upper (D 7) (R 7) [6,96,9,384,129,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2131 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2132 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 7 98 13 392 146 33 80 224 352), lower := (rows 7 98 13 392 146 33 80 128 256), losses := [] }

theorem u2132 : Upper (D 7) (R 7) [6,96,9,384,130,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2132 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2133 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5),(4,5)], upper := (rows 7 98 13 392 146 33 96 208 336), lower := (rows 7 98 13 392 146 33 96 128 256), losses := [] }

theorem u2133 : Upper (D 7) (R 7) [6,96,9,384,130,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2133 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2134 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 397, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 98 13 392 146 48 96 193 321), lower := (rows 7 98 13 392 146 48 96 128 256), losses := [] }

theorem u2134 : Upper (D 7) (R 7) [6,96,9,384,130,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2134 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2135 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 103, targets := 128 },{ cop := 6, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 7 98 13 392 176 34 65 208 336), lower := (rows 7 98 13 392 176 34 65 128 256), losses := [] }

theorem u2135 : Upper (D 7) (R 7) [6,96,9,384,160,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2135 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2136 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 397, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 98 13 392 176 34 80 193 321), lower := (rows 7 98 13 392 176 34 80 128 256), losses := [] }

theorem u2136 : Upper (D 7) (R 7) [6,96,9,384,160,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2136 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2137 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 226, targets := 1 },{ cop := 0, region := 464, targets := 32 },{ cop := 3, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(2,1),(4,5)], upper := (rows 7 98 28 41 273 160 66 192 448), lower := (rows 7 98 28 41 273 160 66 128 256), losses := [{ target := 1, region := (rows 1 0 29 25 17 227 64 194 322), good := (rows 445 480 28 61 317 160 480 160 256) }] }

theorem u2137 : Upper (D 7) (R 7) [6,96,24,33,257,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2137 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2138 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 7 98 28 41 273 160 192 194 322), lower := (rows 7 98 28 41 273 160 192 128 256), losses := [] }

theorem u2138 : Upper (D 7) (R 7) [6,96,24,33,257,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2138 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2139 : PairBound 9 := { available := 192, camps := [{ cop := 6, region := 434, targets := 1 },{ cop := 0, region := 232, targets := 2 },{ cop := 0, region := 464, targets := 32 }], pairs := [(1,0),(3,1),(4,0),(4,5)], upper := (rows 7 98 28 41 274 160 65 192 448), lower := (rows 7 98 28 41 274 160 65 128 256), losses := [] }

theorem u2139 : Upper (D 7) (R 7) [6,96,24,33,258,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2139 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2140 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 7 98 28 41 274 160 192 193 321), lower := (rows 7 98 28 41 274 160 192 128 256), losses := [] }

theorem u2140 : Upper (D 7) (R 7) [6,96,24,33,258,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2140 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2141 : PairBound 9 := { available := 130, camps := [{ cop := 6, region := 434, targets := 1 },{ cop := 0, region := 464, targets := 32 },{ cop := 0, region := 168, targets := 64 }], pairs := [(1,0),(3,6),(4,0),(4,5)], upper := (rows 7 98 28 41 336 160 65 130 386), lower := (rows 7 98 28 41 336 160 65 128 256), losses := [] }

theorem u2141 : Upper (D 7) (R 7) [6,96,24,33,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2141 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2142 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 168, targets := 66 },{ cop := 3, region := 66, targets := 129 }], pairs := [(1,0),(1,7),(3,1),(3,6)], upper := (rows 7 98 28 41 336 160 66 129 385), lower := (rows 7 98 28 41 336 160 66 128 256), losses := [] }

theorem u2142 : Upper (D 7) (R 7) [6,96,24,33,320,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2142 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2143 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 7 98 28 41 336 160 192 131 259), lower := (rows 7 98 28 41 336 160 192 128 256), losses := [] }

theorem u2143 : Upper (D 7) (R 7) [6,96,24,33,320,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2143 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2144 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 466, targets := 1 },{ cop := 0, region := 232, targets := 2 },{ cop := 1, region := 272, targets := 128 }], pairs := [(1,0),(3,1),(4,0),(4,7)], upper := (rows 7 98 28 137 274 33 192 224 352), lower := (rows 7 98 28 137 274 33 192 128 256), losses := [] }

theorem u2144 : Upper (D 7) (R 7) [6,96,24,129,258,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2144 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2145 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 28 137 274 96 192 161 289), lower := (rows 7 98 28 137 274 96 192 128 256), losses := [] }

theorem u2145 : Upper (D 7) (R 7) [6,96,24,129,258,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2145 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2146 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 434, targets := 1 },{ cop := 0, region := 200, targets := 32 },{ cop := 1, region := 272, targets := 128 }], pairs := [(1,0),(3,5),(4,0),(4,7)], upper := (rows 7 98 28 137 304 160 65 194 322), lower := (rows 7 98 28 137 304 160 65 128 256), losses := [] }

theorem u2146 : Upper (D 7) (R 7) [6,96,24,129,288,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2146 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2147 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 66, targets := 129 },{ cop := 0, region := 200, targets := 32 }], pairs := [(0,7),(1,0),(1,7),(3,5)], upper := (rows 7 98 28 137 304 160 66 193 321), lower := (rows 7 98 28 137 304 160 66 128 256), losses := [{ target := 7, region := (rows 5 50 4 8 16 32 119 0 269), good := (rows 327 98 351 329 370 98 66 0 256) }] }

theorem u2147 : Upper (D 7) (R 7) [6,96,24,129,288,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2147 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2148 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 5, region := 466, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(4,0)], upper := (rows 7 98 28 137 400 33 66 224 352), lower := (rows 7 98 28 137 400 33 66 128 256), losses := [] }

theorem u2148 : Upper (D 7) (R 7) [6,96,24,129,384,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2148 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2149 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5),(4,5)], upper := (rows 7 98 28 137 400 34 96 193 321), lower := (rows 7 98 28 137 400 34 96 128 256), losses := [] }

theorem u2149 : Upper (D 7) (R 7) [6,96,24,129,384,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2149 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2150 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 202, targets := 1 },{ cop := 0, region := 496, targets := 2 }], pairs := [(1,0),(2,0),(3,0),(4,1)], upper := (rows 7 98 28 138 273 33 192 224 352), lower := (rows 7 98 28 138 273 33 192 128 256), losses := [{ target := 0, region := (rows 0 34 20 43 16 32 235 162 290), good := (rows 462 490 92 458 348 490 192 192 256) }] }

theorem u2150 : Upper (D 7) (R 7) [6,96,24,130,257,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2150 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2151 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 28 138 273 96 192 161 289), lower := (rows 7 98 28 138 273 96 192 128 256), losses := [] }

theorem u2151 : Upper (D 7) (R 7) [6,96,24,130,257,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2151 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2152 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 7 98 28 138 304 33 65 192 448), lower := (rows 7 98 28 138 304 33 65 128 256), losses := [] }

theorem u2152 : Upper (D 7) (R 7) [6,96,24,130,288,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2152 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r2153 : Route 9 := (fun mask => (mask,id))

def c2153 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2153 : Upper (D 7) (R 7) [6,96,24,130,288,1,128] 13 := by
  apply FastRouting.sound _ _ [6,96,24,130,288,1,128] 13 (by decide) (choices 1) [1,64] r2153 c2153
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u118
  · exact u119

def b2154 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 496, targets := 2 },{ cop := 0, region := 200, targets := 32 }], pairs := [(0,7),(2,1),(3,5),(4,1)], upper := (rows 7 98 28 138 304 160 65 193 321), lower := (rows 7 98 28 138 304 160 65 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 83 235 65 193 321), good := (rows 501 496 60 188 304 160 497 160 256) },{ target := 7, region := (rows 9 2 12 8 18 32 77 0 333), good := (rows 343 370 349 351 304 32 321 0 256) }] }

theorem u2154 : Upper (D 7) (R 7) [6,96,24,130,288,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2154 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2155 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 7 98 28 168 274 33 65 192 448), lower := (rows 7 98 28 168 274 33 65 128 256), losses := [] }

theorem u2155 : Upper (D 7) (R 7) [6,96,24,160,258,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2155 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2156 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 232, targets := 2 },{ cop := 0, region := 464, targets := 32 },{ cop := 3, region := 66, targets := 1 }], pairs := [(1,0),(2,1),(3,1),(4,5)], upper := (rows 7 98 28 168 274 33 192 193 321), lower := (rows 7 98 28 168 274 33 192 128 256), losses := [{ target := 1, region := (rows 1 0 20 43 16 33 235 161 289), good := (rows 493 488 92 488 348 489 192 192 256) }] }

theorem u2156 : Upper (D 7) (R 7) [6,96,24,160,258,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2156 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2157 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 7 98 28 168 336 33 65 130 386), lower := (rows 7 98 28 168 336 33 65 128 256), losses := [] }

theorem u2157 : Upper (D 7) (R 7) [6,96,24,160,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2157 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2158 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 168, targets := 66 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(1,7),(3,1),(3,6)], upper := (rows 7 98 28 168 336 33 66 129 385), lower := (rows 7 98 28 168 336 33 66 128 256), losses := [] }

theorem u2158 : Upper (D 7) (R 7) [6,96,24,160,320,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2158 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2159 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 464, targets := 32 },{ cop := 0, region := 168, targets := 64 },{ cop := 3, region := 66, targets := 1 }], pairs := [(1,0),(2,5),(3,6),(4,5)], upper := (rows 7 98 28 168 336 33 192 131 259), lower := (rows 7 98 28 168 336 33 192 128 256), losses := [{ target := 5, region := (rows 1 2 12 8 49 0 233 129 257), good := (rows 471 82 92 220 336 465 192 192 256) }] }

theorem u2159 : Upper (D 7) (R 7) [6,96,24,160,320,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2159 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u2159
end Delivery.IrregularNine14.P07

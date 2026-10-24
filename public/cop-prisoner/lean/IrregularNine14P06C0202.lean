import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0037

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r12120 : Route 9 := (fun mask => (mask,id))

def c12120 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12120 : Upper (D 6) (R 6) [10,33,65,384,66,4] 13 := by
  apply FastRouting.sound _ _ [10,33,65,384,66,4] 13 (by decide) (choices 1) [4,16,32] r12120 c12120
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2222
  · exact u2223
  · exact u2224

def b12121 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 460, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 11 35 69 392 82 48 100 164 292), lower := (rows 11 35 69 392 82 48 64 128 256), losses := [] }

theorem u12121 : Upper (D 6) (R 6) [10,33,65,384,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12121 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12122 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 69 392 112 34 84 148 276), lower := (rows 11 35 69 392 112 34 64 128 256), losses := [] }

theorem u12122 : Upper (D 6) (R 6) [10,33,65,384,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12122 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12123 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 48, targets := 3 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6),(4,0),(4,1)], upper := (rows 11 35 69 392 112 36 86 150 278), lower := (rows 11 35 69 392 112 36 64 128 256), losses := [] }

theorem u12123 : Upper (D 6) (R 6) [10,33,65,384,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12123 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12124 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 35 69 392 112 48 70 134 262), lower := (rows 11 35 69 392 112 48 64 128 256), losses := [] }

theorem u12124 : Upper (D 6) (R 6) [10,33,65,384,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12124 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12125 : PairBound 9 := { available := 324, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 70 28 176 33 324 452 324), lower := (rows 11 35 70 28 176 33 64 128 256), losses := [] }

theorem u12125 : Upper (D 6) (R 6) [10,33,66,20,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12125 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12126 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 0, region := 324, targets := 32 }], pairs := [(0,6),(1,6),(2,5)], upper := (rows 11 35 70 28 176 36 321 449 321), lower := (rows 11 35 70 28 176 36 64 128 256), losses := [] }

theorem u12126 : Upper (D 6) (R 6) [10,33,66,20,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12126 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12127 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 324, targets := 32 }], pairs := [(0,2),(1,2),(2,5)], upper := (rows 11 35 70 28 176 96 325 389 261), lower := (rows 11 35 70 28 176 96 64 128 256), losses := [{ target := 2, region := (rows 9 10 0 8 16 100 64 128 256), good := (rows 11 35 98 59 176 96 96 128 256) }] }

theorem u12127 : Upper (D 6) (R 6) [10,33,66,20,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12127 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12128 : Route 9 := (fun mask => (mask,id))

def c12128 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12128 : Upper (D 6) (R 6) [10,33,66,20,160,256] 13 := by
  apply FastRouting.sound _ _ [10,33,66,20,160,256] 13 (by decide) (choices 1) [1,4] r12128 c12128
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2225
  · exact u2226

def b12129 : PairBound 9 := { available := 292, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 35 70 28 208 33 356 420 292), lower := (rows 11 35 70 28 208 33 64 128 256), losses := [] }

theorem u12129 : Upper (D 6) (R 6) [10,33,66,20,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12129 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12130 : PairBound 9 := { available := 289, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 1, region := 464, targets := 2 }], pairs := [(0,6),(1,6),(4,1)], upper := (rows 11 35 70 28 208 36 353 417 289), lower := (rows 11 35 70 28 208 36 64 128 256), losses := [] }

theorem u12130 : Upper (D 6) (R 6) [10,33,66,20,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12130 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12131 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 291, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 35 70 28 208 288 101 165 293), lower := (rows 11 35 70 28 208 288 64 128 256), losses := [] }

theorem u12131 : Upper (D 6) (R 6) [10,33,66,20,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12131 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12132 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 70 28 400 33 100 228 356), lower := (rows 11 35 70 28 400 33 64 128 256), losses := [] }

theorem u12132 : Upper (D 6) (R 6) [10,33,66,20,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12132 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12133 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 1, region := 464, targets := 2 }], pairs := [(0,6),(1,6),(4,1)], upper := (rows 11 35 70 28 400 36 97 225 353), lower := (rows 11 35 70 28 400 36 64 128 256), losses := [] }

theorem u12133 : Upper (D 6) (R 6) [10,33,66,20,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12133 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12134 : Route 9 := (fun mask => (mask,id))

def c12134 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12134 : Upper (D 6) (R 6) [10,33,66,20,384,64] 13 := by
  apply FastRouting.sound _ _ [10,33,66,20,384,64] 13 (by decide) (choices 1) [1,4,32] r12134 c12134
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2227
  · exact u2228
  · exact u2229

def b12135 : PairBound 9 := { available := 388, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 70 88 52 33 452 388 388), lower := (rows 11 35 70 88 52 33 64 128 256), losses := [] }

theorem u12135 : Upper (D 6) (R 6) [10,33,66,80,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12135 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12136 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 56, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 35 70 88 52 36 449 385 385), lower := (rows 11 35 70 88 52 36 64 128 256), losses := [] }

theorem u12136 : Upper (D 6) (R 6) [10,33,66,80,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12136 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12137 : Route 9 := (fun mask => (mask,id))

def c12137 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u12137 : Upper (D 6) (R 6) [10,33,66,80,36,128] 13 := by
  apply FastRouting.sound _ _ [10,33,66,80,36,128] 13 (by decide) (choices 1) [1,4,256] r12137 c12137
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2230
  · exact u2231
  · exact u2232

def b12138 : PairBound 9 := { available := 292, camps := [{ cop := 0, region := 356, targets := 1 }], pairs := [(2,0),(3,0),(3,1)], upper := (rows 11 35 70 88 145 36 356 420 292), lower := (rows 11 35 70 88 145 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 7 24 16 55 119 183 311), good := (rows 494 486 486 504 508 484 64 128 256) },{ target := 1, region := (rows 1 0 4 14 18 36 100 164 292), good := (rows 25 505 508 88 145 492 64 128 256) }] }

theorem u12138 : Upper (D 6) (R 6) [10,33,66,80,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12138 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12139 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 356, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 11 35 70 88 145 288 100 164 292), lower := (rows 11 35 70 88 145 288 64 128 256), losses := [{ target := 0, region := (rows 0 2 7 24 16 319 87 151 279), good := (rows 494 486 486 504 508 288 64 128 288) }] }

theorem u12139 : Upper (D 6) (R 6) [10,33,66,80,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12139 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12140 : PairBound 9 := { available := 292, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 70 88 148 33 356 420 292), lower := (rows 11 35 70 88 148 33 64 128 256), losses := [] }

theorem u12140 : Upper (D 6) (R 6) [10,33,66,80,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12140 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12141 : PairBound 9 := { available := 289, camps := [], pairs := [(0,6),(3,1),(4,1)], upper := (rows 11 35 70 88 148 36 353 417 289), lower := (rows 11 35 70 88 148 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 20 52 66 130 258), good := (rows 457 481 508 120 188 60 64 128 256) },{ target := 6, region := (rows 9 10 4 8 20 52 0 138 266), good := (rows 395 419 438 443 180 52 0 128 256) }] }

theorem u12141 : Upper (D 6) (R 6) [10,33,66,80,132,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12141 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12142 : Route 9 := (fun mask => (mask,id))

def c12142 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12142 : Upper (D 6) (R 6) [10,33,66,80,132,256] 13 := by
  apply FastRouting.sound _ _ [10,33,66,80,132,256] 13 (by decide) (choices 1) [1,4,32] r12142 c12142
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2233
  · exact u2234
  · exact u2235

def b12143 : PairBound 9 := { available := 260, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 70 88 176 33 324 388 260), lower := (rows 11 35 70 88 176 33 64 128 256), losses := [] }

theorem u12143 : Upper (D 6) (R 6) [10,33,66,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12143 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12144 : Route 9 := (fun mask => (mask,id))

def c12144 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u12144 : Upper (D 6) (R 6) [10,33,66,80,160,4] 13 := by
  apply FastRouting.sound _ _ [10,33,66,80,160,4] 13 (by decide) (choices 1) [1,4,256] r12144 c12144
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2236
  · exact u2237
  · exact u2238

def r12145 : Route 9 := (fun mask => (mask,id))

def c12145 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12145 : Upper (D 6) (R 6) [10,33,66,80,160,256] 13 := by
  apply FastRouting.sound _ _ [10,33,66,80,160,256] 13 (by decide) (choices 1) [1,4] r12145 c12145
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2239
  · exact u2240

def b12146 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 70 88 400 33 100 164 292), lower := (rows 11 35 70 88 400 33 64 128 256), losses := [] }

theorem u12146 : Upper (D 6) (R 6) [10,33,66,80,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12146 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12147 : Route 9 := (fun mask => (mask,id))

def c12147 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12147 : Upper (D 6) (R 6) [10,33,66,80,384,4] 13 := by
  apply FastRouting.sound _ _ [10,33,66,80,384,4] 13 (by decide) (choices 1) [1,4,32] r12147 c12147
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2241
  · exact u2242
  · exact u2243

def b12148 : PairBound 9 := { available := 336, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 35 70 140 52 33 336 464 336), lower := (rows 11 35 70 140 52 33 64 128 256), losses := [] }

theorem u12148 : Upper (D 6) (R 6) [10,33,66,132,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12148 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12149 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 35 70 140 52 48 321 449 321), lower := (rows 11 35 70 140 52 48 64 128 256), losses := [] }

theorem u12149 : Upper (D 6) (R 6) [10,33,66,132,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12149 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12150 : PairBound 9 := { available := 273, camps := [{ cop := 4, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 70 140 52 96 337 401 273), lower := (rows 11 35 70 140 52 96 64 128 256), losses := [] }

theorem u12150 : Upper (D 6) (R 6) [10,33,66,132,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12150 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12151 : Route 9 := (fun mask => (mask,id))

def c12151 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12151 : Upper (D 6) (R 6) [10,33,66,132,36,256] 13 := by
  apply FastRouting.sound _ _ [10,33,66,132,36,256] 13 (by decide) (choices 1) [1,16] r12151 c12151
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2244
  · exact u2245

def b12152 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 1, region := 336, targets := 2 }], pairs := [(0,6),(1,6),(4,1)], upper := (rows 11 35 70 140 81 36 368 432 304), lower := (rows 11 35 70 140 81 36 64 128 256), losses := [] }

theorem u12152 : Upper (D 6) (R 6) [10,33,66,132,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12152 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12153 : PairBound 9 := { available := 292, camps := [{ cop := 1, region := 460, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 11 35 70 140 81 48 356 420 292), lower := (rows 11 35 70 140 81 48 64 128 256), losses := [] }

theorem u12153 : Upper (D 6) (R 6) [10,33,66,132,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12153 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12154 : Route 9 := (fun mask => (mask,id))

def c12154 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12154 : Upper (D 6) (R 6) [10,33,66,132,65,256] 13 := by
  apply FastRouting.sound _ _ [10,33,66,132,65,256] 13 (by decide) (choices 1) [4,16,32] r12154 c12154
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2246
  · exact u2247
  · exact u2248

def b12155 : PairBound 9 := { available := 276, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 70 140 112 33 340 404 276), lower := (rows 11 35 70 140 112 33 64 128 256), losses := [] }

theorem u12155 : Upper (D 6) (R 6) [10,33,66,132,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12155 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12156 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 48, targets := 3 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(4,0),(4,1)], upper := (rows 11 35 70 140 112 36 337 401 273), lower := (rows 11 35 70 140 112 36 64 128 256), losses := [] }

theorem u12156 : Upper (D 6) (R 6) [10,33,66,132,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12156 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12157 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 35 70 140 112 48 325 389 261), lower := (rows 11 35 70 140 112 48 64 128 256), losses := [] }

theorem u12157 : Upper (D 6) (R 6) [10,33,66,132,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12157 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12158 : Route 9 := (fun mask => (mask,id))

def c12158 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12158 : Upper (D 6) (R 6) [10,33,66,132,96,256] 13 := by
  apply FastRouting.sound _ _ [10,33,66,132,96,256] 13 (by decide) (choices 1) [1,4,16] r12158 c12158
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2249
  · exact u2250
  · exact u2251

def b12159 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 1, region := 336, targets := 2 }], pairs := [(0,6),(1,6),(4,1)], upper := (rows 11 35 70 140 273 36 112 240 368), lower := (rows 11 35 70 140 273 36 64 128 256), losses := [] }

theorem u12159 : Upper (D 6) (R 6) [10,33,66,132,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12159 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12160 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 204, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 11 35 70 140 273 48 100 228 356), lower := (rows 11 35 70 140 273 48 64 128 256), losses := [] }

theorem u12160 : Upper (D 6) (R 6) [10,33,66,132,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12160 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12161 : Route 9 := (fun mask => (mask,id))

def c12161 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12161 : Upper (D 6) (R 6) [10,33,66,132,257,64] 13 := by
  apply FastRouting.sound _ _ [10,33,66,132,257,64] 13 (by decide) (choices 1) [4,16,32] r12161 c12161
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2252
  · exact u2253
  · exact u2254

def b12162 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 70 140 276 33 112 240 368), lower := (rows 11 35 70 140 276 33 64 128 256), losses := [] }

theorem u12162 : Upper (D 6) (R 6) [10,33,66,132,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12162 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12163 : PairBound 9 := { available := 97, camps := [], pairs := [(3,1),(4,1)], upper := (rows 11 35 70 140 276 48 97 225 353), lower := (rows 11 35 70 140 276 48 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 20 60 67 131 259), good := (rows 489 481 508 188 316 48 64 128 256) }] }

theorem u12163 : Upper (D 6) (R 6) [10,33,66,132,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12163 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12164 : Route 9 := (fun mask => (mask,id))

def c12164 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12164 : Upper (D 6) (R 6) [10,33,66,132,260,64] 13 := by
  apply FastRouting.sound _ _ [10,33,66,132,260,64] 13 (by decide) (choices 1) [1,16,32] r12164 c12164
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2255
  · exact u2256
  · exact u2257

def b12165 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 70 140 304 33 84 212 340), lower := (rows 11 35 70 140 304 33 64 128 256), losses := [] }

theorem u12165 : Upper (D 6) (R 6) [10,33,66,132,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12165 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12166 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 1, region := 336, targets := 2 }], pairs := [(0,6),(1,6),(4,1)], upper := (rows 11 35 70 140 304 36 81 209 337), lower := (rows 11 35 70 140 304 36 64 128 256), losses := [] }

theorem u12166 : Upper (D 6) (R 6) [10,33,66,132,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12166 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12167 : PairBound 9 := { available := 69, camps := [{ cop := 8, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 11 35 70 140 304 48 69 197 325), lower := (rows 11 35 70 140 304 48 64 128 256), losses := [] }

theorem u12167 : Upper (D 6) (R 6) [10,33,66,132,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12167 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12168 : Route 9 := (fun mask => (mask,id))

def c12168 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12168 : Upper (D 6) (R 6) [10,33,66,132,288,64] 13 := by
  apply FastRouting.sound _ _ [10,33,66,132,288,64] 13 (by decide) (choices 1) [1,4,16] r12168 c12168
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2258
  · exact u2259
  · exact u2260

def b12169 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 70 140 336 33 116 180 308), lower := (rows 11 35 70 140 336 33 64 128 256), losses := [] }

theorem u12169 : Upper (D 6) (R 6) [10,33,66,132,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12169 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12170 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 1, region := 336, targets := 2 }], pairs := [(0,6),(1,6),(4,1)], upper := (rows 11 35 70 140 336 36 113 177 305), lower := (rows 11 35 70 140 336 36 64 128 256), losses := [] }

theorem u12170 : Upper (D 6) (R 6) [10,33,66,132,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12170 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12171 : Route 9 := (fun mask => (mask,id))

def c12171 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12171 : Upper (D 6) (R 6) [10,33,66,132,320,16] 13 := by
  apply FastRouting.sound _ _ [10,33,66,132,320,16] 13 (by decide) (choices 1) [1,4,32] r12171 c12171
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2261
  · exact u2262
  · exact u2263

def b12172 : PairBound 9 := { available := 324, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 70 152 52 33 324 452 324), lower := (rows 11 35 70 152 52 33 64 128 256), losses := [] }

theorem u12172 : Upper (D 6) (R 6) [10,33,66,144,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12172 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12173 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 35 70 152 52 36 321 449 321), lower := (rows 11 35 70 152 52 36 64 128 256), losses := [] }

theorem u12173 : Upper (D 6) (R 6) [10,33,66,144,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12173 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12174 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 70 152 52 96 325 389 261), lower := (rows 11 35 70 152 52 96 64 128 256), losses := [] }

theorem u12174 : Upper (D 6) (R 6) [10,33,66,144,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12174 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12175 : Route 9 := (fun mask => (mask,id))

def c12175 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12175 : Upper (D 6) (R 6) [10,33,66,144,36,256] 13 := by
  apply FastRouting.sound _ _ [10,33,66,144,36,256] 13 (by decide) (choices 1) [1,4] r12175 c12175
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2264
  · exact u2265

def b12176 : PairBound 9 := { available := 292, camps := [{ cop := 0, region := 356, targets := 1 }], pairs := [(2,0),(3,0),(3,1)], upper := (rows 11 35 70 152 81 36 356 420 292), lower := (rows 11 35 70 152 81 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 7 24 16 55 119 183 311), good := (rows 494 486 486 504 508 484 64 128 256) },{ target := 1, region := (rows 1 0 4 14 18 36 100 164 292), good := (rows 25 505 508 152 81 492 64 128 256) }] }

theorem u12176 : Upper (D 6) (R 6) [10,33,66,144,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12176 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12177 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 356, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 11 35 70 152 81 288 100 164 292), lower := (rows 11 35 70 152 81 288 64 128 256), losses := [{ target := 0, region := (rows 0 2 7 24 16 319 87 151 279), good := (rows 494 486 486 504 508 288 64 128 288) }] }

theorem u12177 : Upper (D 6) (R 6) [10,33,66,144,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12177 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12178 : PairBound 9 := { available := 260, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 70 152 112 33 324 388 260), lower := (rows 11 35 70 152 112 33 64 128 256), losses := [] }

theorem u12178 : Upper (D 6) (R 6) [10,33,66,144,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12178 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12179 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 48, targets := 3 },{ cop := 0, region := 324, targets := 32 }], pairs := [(2,5),(4,0),(4,1)], upper := (rows 11 35 70 152 112 36 325 389 261), lower := (rows 11 35 70 152 112 36 64 128 256), losses := [] }

theorem u12179 : Upper (D 6) (R 6) [10,33,66,144,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12179 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u12179
end Delivery.IrregularNine14.P06

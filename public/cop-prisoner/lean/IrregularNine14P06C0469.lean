import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0154
import IrregularNine14P06C0155

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b28140 : PairBound 9 := { available := 353, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 8, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 7 26 133 14 112 353 353 481 353), lower := (rows 7 26 133 14 112 32 64 128 256), losses := [] }

theorem u28140 : Upper (D 6) (R 6) [6,24,129,6,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28140 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28141 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 8, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 7 26 133 14 273 96 96 224 352), lower := (rows 7 26 133 14 273 32 64 128 256), losses := [] }

theorem u28141 : Upper (D 6) (R 6) [6,24,129,6,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28141 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28142 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 8, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 7 26 133 14 304 97 97 225 353), lower := (rows 7 26 133 14 304 32 64 128 256), losses := [] }

theorem u28142 : Upper (D 6) (R 6) [6,24,129,6,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28142 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28143 : PairBound 9 := { available := 324, camps := [{ cop := 3, region := 18, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 26 133 41 50 356 324 452 324), lower := (rows 7 26 133 41 50 32 64 128 256), losses := [] }

theorem u28143 : Upper (D 6) (R 6) [6,24,129,33,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28143 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28144 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 11, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 26 133 41 52 354 322 450 322), lower := (rows 7 26 133 41 52 32 64 128 256), losses := [] }

theorem u28144 : Upper (D 6) (R 6) [6,24,129,33,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28144 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28145 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 0, region := 368, targets := 1 }], pairs := [(2,1),(3,1),(4,0)], upper := (rows 7 26 133 41 82 356 356 484 356), lower := (rows 7 26 133 41 82 32 64 128 256), losses := [] }

theorem u28145 : Upper (D 6) (R 6) [6,24,129,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28145 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28146 : PairBound 9 := { available := 354, camps := [{ cop := 0, region := 368, targets := 1 },{ cop := 0, region := 360, targets := 4 }], pairs := [(1,0),(3,2),(4,0)], upper := (rows 7 26 133 41 84 354 354 482 354), lower := (rows 7 26 133 41 84 32 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 21 43 75 139 267), good := (rows 502 506 500 506 84 32 64 128 256) }] }

theorem u28146 : Upper (D 6) (R 6) [6,24,129,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28146 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28147 : PairBound 9 := { available := 326, camps := [{ cop := 1, region := 453, targets := 32 },{ cop := 0, region := 368, targets := 1 }], pairs := [(0,5),(2,5),(4,0)], upper := (rows 7 26 133 41 112 358 326 454 326), lower := (rows 7 26 133 41 112 32 64 128 256), losses := [] }

theorem u28147 : Upper (D 6) (R 6) [6,24,129,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28147 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28148 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 0, region := 368, targets := 1 }], pairs := [(2,1),(3,1),(4,0)], upper := (rows 7 26 133 41 274 100 100 228 356), lower := (rows 7 26 133 41 274 32 64 128 256), losses := [] }

theorem u28148 : Upper (D 6) (R 6) [6,24,129,33,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28148 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28149 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 368, targets := 1 },{ cop := 0, region := 104, targets := 4 }], pairs := [(1,0),(3,2),(4,0)], upper := (rows 7 26 133 41 276 98 98 226 354), lower := (rows 7 26 133 41 276 32 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 21 43 75 139 267), good := (rows 502 506 500 506 276 32 64 128 256) }] }

theorem u28149 : Upper (D 6) (R 6) [6,24,129,33,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28149 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28150 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 197, targets := 32 },{ cop := 0, region := 368, targets := 1 }], pairs := [(0,5),(2,5),(4,0)], upper := (rows 7 26 133 41 304 102 70 198 326), lower := (rows 7 26 133 41 304 32 64 128 256), losses := [] }

theorem u28150 : Upper (D 6) (R 6) [6,24,129,33,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28150 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28151 : Route 9 := (fun mask => (mask,id))

def c28151 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28151 : Upper (D 6) (R 6) [6,24,129,33,320] 13 := by
  apply FastRouting.sound _ _ [6,24,129,33,320] 13 (by decide) (choices 1) [2,4,64] r28151 c28151
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9276
  · exact u9277
  · exact u9278

def b28152 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 10, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 26 133 42 52 353 321 449 321), lower := (rows 7 26 133 42 52 32 64 128 256), losses := [] }

theorem u28152 : Upper (D 6) (R 6) [6,24,129,34,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28152 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28153 : PairBound 9 := { available := 353, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 360, targets := 4 }], pairs := [(2,1),(3,2),(4,1)], upper := (rows 7 26 133 42 84 353 353 481 353), lower := (rows 7 26 133 42 84 32 64 128 256), losses := [] }

theorem u28153 : Upper (D 6) (R 6) [6,24,129,34,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28153 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28154 : PairBound 9 := { available := 325, camps := [{ cop := 4, region := 10, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 26 133 42 112 357 325 453 325), lower := (rows 7 26 133 42 112 32 64 128 256), losses := [] }

theorem u28154 : Upper (D 6) (R 6) [6,24,129,34,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28154 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28155 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 104, targets := 1 }], pairs := [(2,1),(3,0),(4,1)], upper := (rows 7 26 133 42 273 100 100 228 356), lower := (rows 7 26 133 42 273 32 64 128 256), losses := [] }

theorem u28155 : Upper (D 6) (R 6) [6,24,129,34,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28155 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28156 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 104, targets := 4 }], pairs := [(2,1),(3,2),(4,1)], upper := (rows 7 26 133 42 276 97 97 225 353), lower := (rows 7 26 133 42 276 32 64 128 256), losses := [] }

theorem u28156 : Upper (D 6) (R 6) [6,24,129,34,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28156 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28157 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 10, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 26 133 42 304 101 69 197 325), lower := (rows 7 26 133 42 304 32 64 128 256), losses := [] }

theorem u28157 : Upper (D 6) (R 6) [6,24,129,34,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28157 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28158 : Route 9 := (fun mask => (mask,id))

def c28158 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28158 : Upper (D 6) (R 6) [6,24,129,34,320] 13 := by
  apply FastRouting.sound _ _ [6,24,129,34,320] 13 (by decide) (choices 1) [1,4,64] r28158 c28158
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9279
  · exact u9280
  · exact u9281

def b28159 : PairBound 9 := { available := 323, camps := [{ cop := 1, region := 453, targets := 32 },{ cop := 0, region := 368, targets := 4 }], pairs := [(0,5),(2,5),(4,2)], upper := (rows 7 26 133 44 112 355 323 451 323), lower := (rows 7 26 133 44 112 32 64 128 256), losses := [] }

theorem u28159 : Upper (D 6) (R 6) [6,24,129,36,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28159 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28160 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 104, targets := 1 },{ cop := 0, region := 368, targets := 4 }], pairs := [(1,0),(3,0),(4,2)], upper := (rows 7 26 133 44 273 98 98 226 354), lower := (rows 7 26 133 44 273 32 64 128 256), losses := [{ target := 0, region := (rows 0 18 4 13 16 51 83 147 275), good := (rows 494 506 492 44 506 32 64 128 256) }] }

theorem u28160 : Upper (D 6) (R 6) [6,24,129,36,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28160 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28161 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 0, region := 368, targets := 4 }], pairs := [(2,1),(3,1),(4,2)], upper := (rows 7 26 133 44 274 97 97 225 353), lower := (rows 7 26 133 44 274 32 64 128 256), losses := [] }

theorem u28161 : Upper (D 6) (R 6) [6,24,129,36,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28161 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28162 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 197, targets := 32 },{ cop := 0, region := 368, targets := 4 }], pairs := [(0,5),(2,5),(4,2)], upper := (rows 7 26 133 44 304 99 67 195 323), lower := (rows 7 26 133 44 304 32 64 128 256), losses := [] }

theorem u28162 : Upper (D 6) (R 6) [6,24,129,36,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28162 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28163 : Route 9 := (fun mask => (mask,id))

def c28163 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28163 : Upper (D 6) (R 6) [6,24,129,36,320] 13 := by
  apply FastRouting.sound _ _ [6,24,129,36,320] 13 (by decide) (choices 1) [1,2,64] r28163 c28163
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9282
  · exact u9283
  · exact u9284

def b28164 : PairBound 9 := { available := 263, camps := [{ cop := 3, region := 18, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 7 26 133 104 112 295 327 391 263), lower := (rows 7 26 133 104 112 32 64 128 256), losses := [] }

theorem u28164 : Upper (D 6) (R 6) [6,24,129,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28164 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28165 : Route 9 := (fun mask => (mask,id))

def c28165 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28165 : Upper (D 6) (R 6) [6,24,129,96,257] 13 := by
  apply FastRouting.sound _ _ [6,24,129,96,257] 13 (by decide) (choices 1) [2,4,64] r28165 c28165
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9285
  · exact u9286
  · exact u9287

def r28166 : Route 9 := (fun mask => (mask,id))

def c28166 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28166 : Upper (D 6) (R 6) [6,24,129,96,258] 13 := by
  apply FastRouting.sound _ _ [6,24,129,96,258] 13 (by decide) (choices 1) [1,4,64] r28166 c28166
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9288
  · exact u9289
  · exact u9290

def r28167 : Route 9 := (fun mask => (mask,id))

def c28167 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28167 : Upper (D 6) (R 6) [6,24,129,96,260] 13 := by
  apply FastRouting.sound _ _ [6,24,129,96,260] 13 (by decide) (choices 1) [1,2,64] r28167 c28167
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9291
  · exact u9292
  · exact u9293

def r28168 : Route 9 := (fun mask => (mask,id))

def c28168 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28168 : Upper (D 6) (R 6) [6,24,129,96,288] 13 := by
  apply FastRouting.sound _ _ [6,24,129,96,288] 13 (by decide) (choices 1) [1,2,4,64] r28168 c28168
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9294
  · exact u9295
  · exact u9296
  · exact u9297

def b28169 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 10, targets := 100 }], pairs := [(1,2),(1,5),(1,6)], upper := (rows 7 26 164 11 49 356 324 452 324), lower := (rows 7 26 164 11 49 32 64 128 256), losses := [] }

theorem u28169 : Upper (D 6) (R 6) [6,24,160,3,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28169 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28170 : PairBound 9 := { available := 356, camps := [{ cop := 4, region := 10, targets := 100 }], pairs := [(1,2),(1,5),(1,6)], upper := (rows 7 26 164 11 81 356 356 484 356), lower := (rows 7 26 164 11 81 32 64 128 256), losses := [] }

theorem u28170 : Upper (D 6) (R 6) [6,24,160,3,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28170 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28171 : PairBound 9 := { available := 353, camps := [{ cop := 4, region := 11, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 26 164 11 84 353 353 481 353), lower := (rows 7 26 164 11 84 32 64 128 256), losses := [] }

theorem u28171 : Upper (D 6) (R 6) [6,24,160,3,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28171 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28172 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 8, targets := 4 }], pairs := [(2,1),(3,2),(4,1)], upper := (rows 7 26 164 11 112 357 325 453 325), lower := (rows 7 26 164 11 112 32 64 128 256), losses := [] }

theorem u28172 : Upper (D 6) (R 6) [6,24,160,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28172 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28173 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 10, targets := 100 }], pairs := [(1,2),(1,5),(1,6)], upper := (rows 7 26 164 11 273 100 100 228 356), lower := (rows 7 26 164 11 273 32 64 128 256), losses := [] }

theorem u28173 : Upper (D 6) (R 6) [6,24,160,3,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28173 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28174 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 11, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 26 164 11 276 97 97 225 353), lower := (rows 7 26 164 11 276 32 64 128 256), losses := [] }

theorem u28174 : Upper (D 6) (R 6) [6,24,160,3,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28174 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28175 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 8, targets := 4 }], pairs := [(2,1),(3,2),(4,1)], upper := (rows 7 26 164 11 304 101 69 197 325), lower := (rows 7 26 164 11 304 32 64 128 256), losses := [] }

theorem u28175 : Upper (D 6) (R 6) [6,24,160,3,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28175 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28176 : PairBound 9 := { available := 101, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 7 26 164 11 336 101 101 229 357), lower := (rows 7 26 164 11 336 32 64 128 256), losses := [] }

theorem u28176 : Upper (D 6) (R 6) [6,24,160,3,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28176 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28177 : PairBound 9 := { available := 322, camps := [{ cop := 2, region := 27, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 26 164 13 49 354 322 450 322), lower := (rows 7 26 164 13 49 32 64 128 256), losses := [] }

theorem u28177 : Upper (D 6) (R 6) [6,24,160,5,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28177 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28178 : PairBound 9 := { available := 354, camps := [{ cop := 0, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 7 26 164 13 81 354 354 482 354), lower := (rows 7 26 164 13 81 32 64 128 256), losses := [] }

theorem u28178 : Upper (D 6) (R 6) [6,24,160,5,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28178 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28179 : PairBound 9 := { available := 353, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 0, region := 8, targets := 32 }], pairs := [(2,1),(3,1),(3,5)], upper := (rows 7 26 164 13 82 353 353 481 353), lower := (rows 7 26 164 13 82 32 64 128 256), losses := [] }

theorem u28179 : Upper (D 6) (R 6) [6,24,160,5,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28179 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28180 : PairBound 9 := { available := 323, camps := [{ cop := 0, region := 8, targets := 66 },{ cop := 3, region := 370, targets := 4 }], pairs := [(1,2),(3,1),(3,6)], upper := (rows 7 26 164 13 112 355 323 451 323), lower := (rows 7 26 164 13 112 32 64 128 256), losses := [] }

theorem u28180 : Upper (D 6) (R 6) [6,24,160,5,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28180 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28181 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 7 26 164 13 273 98 98 226 354), lower := (rows 7 26 164 13 273 32 64 128 256), losses := [] }

theorem u28181 : Upper (D 6) (R 6) [6,24,160,5,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28181 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28182 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 0, region := 8, targets := 32 }], pairs := [(2,1),(3,1),(3,5)], upper := (rows 7 26 164 13 274 97 97 225 353), lower := (rows 7 26 164 13 274 32 64 128 256), losses := [] }

theorem u28182 : Upper (D 6) (R 6) [6,24,160,5,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28182 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28183 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 8, targets := 66 },{ cop := 3, region := 370, targets := 4 }], pairs := [(1,2),(3,1),(3,6)], upper := (rows 7 26 164 13 304 99 67 195 323), lower := (rows 7 26 164 13 304 32 64 128 256), losses := [] }

theorem u28183 : Upper (D 6) (R 6) [6,24,160,5,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28183 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28184 : PairBound 9 := { available := 99, camps := [{ cop := 0, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 7 26 164 13 336 99 99 227 355), lower := (rows 7 26 164 13 336 32 64 128 256), losses := [] }

theorem u28184 : Upper (D 6) (R 6) [6,24,160,5,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28184 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28185 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 27, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 26 164 14 49 353 321 449 321), lower := (rows 7 26 164 14 49 32 64 128 256), losses := [] }

theorem u28185 : Upper (D 6) (R 6) [6,24,160,6,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28185 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28186 : PairBound 9 := { available := 353, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 8, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 7 26 164 14 81 353 353 481 353), lower := (rows 7 26 164 14 81 32 64 128 256), losses := [] }

theorem u28186 : Upper (D 6) (R 6) [6,24,160,6,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28186 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28187 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 8, targets := 1 }], pairs := [(2,1),(3,0),(4,1)], upper := (rows 7 26 164 14 112 353 321 449 321), lower := (rows 7 26 164 14 112 32 64 128 256), losses := [] }

theorem u28187 : Upper (D 6) (R 6) [6,24,160,6,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28187 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28188 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 8, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 7 26 164 14 273 97 97 225 353), lower := (rows 7 26 164 14 273 32 64 128 256), losses := [] }

theorem u28188 : Upper (D 6) (R 6) [6,24,160,6,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28188 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28189 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 8, targets := 1 }], pairs := [(2,1),(3,0),(4,1)], upper := (rows 7 26 164 14 304 97 65 193 321), lower := (rows 7 26 164 14 304 32 64 128 256), losses := [] }

theorem u28189 : Upper (D 6) (R 6) [6,24,160,6,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28189 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28190 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 8, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 7 26 164 14 336 97 97 225 353), lower := (rows 7 26 164 14 336 32 64 128 256), losses := [] }

theorem u28190 : Upper (D 6) (R 6) [6,24,160,6,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28190 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28191 : PairBound 9 := { available := 326, camps := [{ cop := 0, region := 484, targets := 1 },{ cop := 0, region := 336, targets := 32 }], pairs := [(1,5),(2,0),(4,5)], upper := (rows 7 26 164 41 81 358 326 454 326), lower := (rows 7 26 164 41 81 32 64 128 256), losses := [{ target := 5, region := (rows 1 10 4 8 25 0 65 129 257), good := (rows 471 26 132 475 465 0 64 128 256) }] }

theorem u28191 : Upper (D 6) (R 6) [6,24,160,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28191 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28192 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 0, region := 336, targets := 32 }], pairs := [(2,1),(3,1),(4,5)], upper := (rows 7 26 164 41 82 357 325 453 325), lower := (rows 7 26 164 41 82 32 64 128 256), losses := [] }

theorem u28192 : Upper (D 6) (R 6) [6,24,160,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28192 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28193 : PairBound 9 := { available := 323, camps := [{ cop := 0, region := 360, targets := 4 },{ cop := 0, region := 336, targets := 32 }], pairs := [(1,5),(3,2),(4,5)], upper := (rows 7 26 164 41 84 355 323 451 323), lower := (rows 7 26 164 41 84 32 64 128 256), losses := [{ target := 5, region := (rows 1 10 4 8 17 0 73 137 265), good := (rows 471 474 132 475 84 0 64 128 256) }] }

theorem u28193 : Upper (D 6) (R 6) [6,24,160,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28193 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28194 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 228, targets := 1 },{ cop := 0, region := 336, targets := 32 }], pairs := [(1,5),(2,0),(4,5)], upper := (rows 7 26 164 41 273 102 70 198 326), lower := (rows 7 26 164 41 273 32 64 128 256), losses := [{ target := 5, region := (rows 1 10 4 8 25 0 65 129 257), good := (rows 471 26 132 475 465 0 64 128 256) }] }

theorem u28194 : Upper (D 6) (R 6) [6,24,160,33,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28194 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28195 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 0, region := 336, targets := 32 }], pairs := [(2,1),(3,1),(4,5)], upper := (rows 7 26 164 41 274 101 69 197 325), lower := (rows 7 26 164 41 274 32 64 128 256), losses := [] }

theorem u28195 : Upper (D 6) (R 6) [6,24,160,33,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28195 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28196 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 104, targets := 4 },{ cop := 0, region := 336, targets := 32 }], pairs := [(1,5),(3,2),(4,5)], upper := (rows 7 26 164 41 276 99 67 195 323), lower := (rows 7 26 164 41 276 32 64 128 256), losses := [{ target := 5, region := (rows 1 10 4 8 17 0 73 137 265), good := (rows 471 474 132 475 276 0 64 128 256) }] }

theorem u28196 : Upper (D 6) (R 6) [6,24,160,33,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28196 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28197 : Route 9 := (fun mask => (mask,id))

def c28197 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28197 : Upper (D 6) (R 6) [6,24,160,33,320] 13 := by
  apply FastRouting.sound _ _ [6,24,160,33,320] 13 (by decide) (choices 1) [1,2,4,64] r28197 c28197
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9298
  · exact u9299
  · exact u9300
  · exact u9301

def b28198 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 336, targets := 32 }], pairs := [(2,1),(4,1),(4,5)], upper := (rows 7 26 164 42 81 357 325 453 325), lower := (rows 7 26 164 42 81 32 64 128 256), losses := [] }

theorem u28198 : Upper (D 6) (R 6) [6,24,160,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28198 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28199 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 360, targets := 4 }], pairs := [(2,1),(3,2),(4,1)], upper := (rows 7 26 164 42 84 353 321 449 321), lower := (rows 7 26 164 42 84 32 64 128 256), losses := [] }

theorem u28199 : Upper (D 6) (R 6) [6,24,160,34,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28199 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u28199
end Delivery.IrregularNine14.P06

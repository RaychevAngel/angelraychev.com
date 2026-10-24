import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0319
import IrregularNine14P06C0320

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b35400 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 9, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 25 131 262 41 112 102 70 198 326), lower := (rows 25 131 262 41 112 32 64 128 256), losses := [] }

theorem u35400 : Upper (D 6) (R 6) [24,129,258,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35400 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35401 : Route 9 := (fun mask => (mask,id))

def c35401 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35401 : Upper (D 6) (R 6) [24,129,258,34,36] 13 := by
  apply FastRouting.sound _ _ [24,129,258,34,36] 13 (by decide) (choices 1) [1,4,64] r35401 c35401
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19143
  · exact u19144
  · exact u19145

def r35402 : Route 9 := (fun mask => (mask,id))

def c35402 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35402 : Upper (D 6) (R 6) [24,129,258,34,68] 13 := by
  apply FastRouting.sound _ _ [24,129,258,34,68] 13 (by decide) (choices 1) [1,4,64] r35402 c35402
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19146
  · exact u19147
  · exact u19148

def r35403 : Route 9 := (fun mask => (mask,id))

def c35403 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35403 : Upper (D 6) (R 6) [24,129,258,34,96] 13 := by
  apply FastRouting.sound _ _ [24,129,258,34,96] 13 (by decide) (choices 1) [1,4,64] r35403 c35403
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19149
  · exact u19150
  · exact u19151

def b35404 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 17, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 25 131 262 44 52 99 67 195 323), lower := (rows 25 131 262 44 52 32 64 128 256), losses := [] }

theorem u35404 : Upper (D 6) (R 6) [24,129,258,36,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35404 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35405 : Route 9 := (fun mask => (mask,id))

def c35405 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35405 : Upper (D 6) (R 6) [24,129,258,36,68] 13 := by
  apply FastRouting.sound _ _ [24,129,258,36,68] 13 (by decide) (choices 1) [1,2,64] r35405 c35405
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19152
  · exact u19153
  · exact u19154

def r35406 : Route 9 := (fun mask => (mask,id))

def c35406 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35406 : Upper (D 6) (R 6) [24,129,258,36,96] 13 := by
  apply FastRouting.sound _ _ [24,129,258,36,96] 13 (by decide) (choices 1) [1,2,4,64] r35406 c35406
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19155
  · exact u19156
  · exact u19157
  · exact u19158

def b35407 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 17, targets := 6 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 25 131 262 104 112 39 71 135 263), lower := (rows 25 131 262 104 112 32 64 128 256), losses := [] }

theorem u35407 : Upper (D 6) (R 6) [24,129,258,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35407 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35408 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 25 131 292 11 22 100 100 228 356), lower := (rows 25 131 292 11 22 32 64 128 256), losses := [] }

theorem u35408 : Upper (D 6) (R 6) [24,129,288,3,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35408 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35409 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 25 131 292 11 50 100 68 196 324), lower := (rows 25 131 292 11 50 32 64 128 256), losses := [] }

theorem u35409 : Upper (D 6) (R 6) [24,129,288,3,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35409 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35410 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 25 131 292 11 82 100 100 228 356), lower := (rows 25 131 292 11 82 32 64 128 256), losses := [] }

theorem u35410 : Upper (D 6) (R 6) [24,129,288,3,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35410 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35411 : PairBound 9 := { available := 102, camps := [{ cop := 1, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 25 131 292 11 84 102 102 230 358), lower := (rows 25 131 292 11 84 32 64 128 256), losses := [] }

theorem u35411 : Upper (D 6) (R 6) [24,129,288,3,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35411 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35412 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 25 131 292 11 112 102 70 198 326), lower := (rows 25 131 292 11 112 32 64 128 256), losses := [] }

theorem u35412 : Upper (D 6) (R 6) [24,129,288,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35412 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35413 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 9, targets := 98 }], pairs := [(0,1),(0,5),(0,6)], upper := (rows 25 131 292 13 22 98 98 226 354), lower := (rows 25 131 292 13 22 32 64 128 256), losses := [] }

theorem u35413 : Upper (D 6) (R 6) [24,129,288,5,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35413 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35414 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 372, targets := 1 },{ cop := 3, region := 194, targets := 32 }], pairs := [(1,5),(2,0),(4,0)], upper := (rows 25 131 292 13 50 102 70 198 326), lower := (rows 25 131 292 13 50 32 64 128 256), losses := [] }

theorem u35414 : Upper (D 6) (R 6) [24,129,288,5,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35414 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35415 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 25, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 25 131 292 13 52 98 66 194 322), lower := (rows 25 131 292 13 52 32 64 128 256), losses := [] }

theorem u35415 : Upper (D 6) (R 6) [24,129,288,5,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35415 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35416 : Route 9 := (fun mask => (mask,id))

def c35416 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35416 : Upper (D 6) (R 6) [24,129,288,5,66] 13 := by
  apply FastRouting.sound _ _ [24,129,288,5,66] 13 (by decide) (choices 1) [2,4,64] r35416 c35416
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19159
  · exact u19160
  · exact u19161

def b35417 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 9, targets := 98 }], pairs := [(0,1),(0,5),(0,6)], upper := (rows 25 131 292 13 84 98 98 226 354), lower := (rows 25 131 292 13 84 32 64 128 256), losses := [] }

theorem u35417 : Upper (D 6) (R 6) [24,129,288,5,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35417 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35418 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 372, targets := 1 },{ cop := 3, region := 194, targets := 32 }], pairs := [(1,5),(2,0),(4,0)], upper := (rows 25 131 292 13 112 102 70 198 326), lower := (rows 25 131 292 13 112 32 64 128 256), losses := [] }

theorem u35418 : Upper (D 6) (R 6) [24,129,288,5,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35418 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35419 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 17, targets := 96 }], pairs := [(0,5),(0,6),(4,5)], upper := (rows 25 131 292 14 22 97 97 225 353), lower := (rows 25 131 292 14 22 32 64 128 256), losses := [] }

theorem u35419 : Upper (D 6) (R 6) [24,129,288,6,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35419 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35420 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 364, targets := 1 }], pairs := [(1,5),(2,0),(3,0)], upper := (rows 25 131 292 14 49 102 70 198 326), lower := (rows 25 131 292 14 49 32 64 128 256), losses := [{ target := 5, region := (rows 1 3 4 8 16 0 72 136 264), good := (rows 475 131 260 462 19 0 64 128 256) }] }

theorem u35420 : Upper (D 6) (R 6) [24,129,288,6,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35420 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35421 : Route 9 := (fun mask => (mask,id))

def c35421 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35421 : Upper (D 6) (R 6) [24,129,288,6,34] 13 := by
  apply FastRouting.sound _ _ [24,129,288,6,34] 13 (by decide) (choices 1) [1,4,64] r35421 c35421
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19162
  · exact u19163
  · exact u19164

def b35422 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 25 131 292 14 52 99 67 195 323), lower := (rows 25 131 292 14 52 32 64 128 256), losses := [] }

theorem u35422 : Upper (D 6) (R 6) [24,129,288,6,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35422 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35423 : Route 9 := (fun mask => (mask,id))

def c35423 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35423 : Upper (D 6) (R 6) [24,129,288,6,65] 13 := by
  apply FastRouting.sound _ _ [24,129,288,6,65] 13 (by decide) (choices 1) [2,4,64] r35423 c35423
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19165
  · exact u19166
  · exact u19167

def r35424 : Route 9 := (fun mask => (mask,id))

def c35424 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35424 : Upper (D 6) (R 6) [24,129,288,6,66] 13 := by
  apply FastRouting.sound _ _ [24,129,288,6,66] 13 (by decide) (choices 1) [1,4,64] r35424 c35424
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19168
  · exact u19169
  · exact u19170

def r35425 : Route 9 := (fun mask => (mask,id))

def c35425 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35425 : Upper (D 6) (R 6) [24,129,288,6,68] 13 := by
  apply FastRouting.sound _ _ [24,129,288,6,68] 13 (by decide) (choices 1) [1,2,64] r35425 c35425
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19171
  · exact u19172
  · exact u19173

def r35426 : Route 9 := (fun mask => (mask,id))

def c35426 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35426 : Upper (D 6) (R 6) [24,129,288,6,96] 13 := by
  apply FastRouting.sound _ _ [24,129,288,6,96] 13 (by decide) (choices 1) [1,2,4,64] r35426 c35426
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19174
  · exact u19175
  · exact u19176
  · exact u19177

def r35427 : Route 9 := (fun mask => (mask,id))

def c35427 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35427 : Upper (D 6) (R 6) [24,129,288,33,66] 13 := by
  apply FastRouting.sound _ _ [24,129,288,33,66] 13 (by decide) (choices 1) [2,4,64] r35427 c35427
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19178
  · exact u19179
  · exact u19180

def r35428 : Route 9 := (fun mask => (mask,id))

def c35428 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35428 : Upper (D 6) (R 6) [24,129,288,33,68] 13 := by
  apply FastRouting.sound _ _ [24,129,288,33,68] 13 (by decide) (choices 1) [2,4,64] r35428 c35428
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19181
  · exact u19182
  · exact u19183

def r35429 : Route 9 := (fun mask => (mask,id))

def c35429 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35429 : Upper (D 6) (R 6) [24,129,288,34,65] 13 := by
  apply FastRouting.sound _ _ [24,129,288,34,65] 13 (by decide) (choices 1) [2,4,64] r35429 c35429
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19184
  · exact u19185
  · exact u19186

def r35430 : Route 9 := (fun mask => (mask,id))

def c35430 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35430 : Upper (D 6) (R 6) [24,129,288,34,66] 13 := by
  apply FastRouting.sound _ _ [24,129,288,34,66] 13 (by decide) (choices 1) [1,4,64] r35430 c35430
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19187
  · exact u19188
  · exact u19189

def r35431 : Route 9 := (fun mask => (mask,id))

def c35431 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35431 : Upper (D 6) (R 6) [24,129,288,34,68] 13 := by
  apply FastRouting.sound _ _ [24,129,288,34,68] 13 (by decide) (choices 1) [1,2,4,64] r35431 c35431
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19190
  · exact u19191
  · exact u19192
  · exact u19193

def b35432 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 8, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 25 131 292 44 81 102 70 198 326), lower := (rows 25 131 292 44 81 32 64 128 256), losses := [] }

theorem u35432 : Upper (D 6) (R 6) [24,129,288,36,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35432 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35433 : PairBound 9 := { available := 71, camps := [{ cop := 2, region := 8, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 25 131 292 44 82 103 71 199 327), lower := (rows 25 131 292 44 82 32 64 128 256), losses := [] }

theorem u35433 : Upper (D 6) (R 6) [24,129,288,36,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35433 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35434 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 8, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 25 131 292 44 84 99 67 195 323), lower := (rows 25 131 292 44 84 32 64 128 256), losses := [] }

theorem u35434 : Upper (D 6) (R 6) [24,129,288,36,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35434 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35435 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 9, targets := 38 }], pairs := [(0,1),(0,2),(0,5)], upper := (rows 25 131 292 73 82 38 102 166 294), lower := (rows 25 131 292 73 82 32 64 128 256), losses := [] }

theorem u35435 : Upper (D 6) (R 6) [24,129,288,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35435 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35436 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 9, targets := 38 }], pairs := [(0,1),(0,2),(0,5)], upper := (rows 25 131 292 73 84 38 102 166 294), lower := (rows 25 131 292 73 84 32 64 128 256), losses := [] }

theorem u35436 : Upper (D 6) (R 6) [24,129,288,65,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35436 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35437 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 9, targets := 38 }], pairs := [(0,1),(0,2),(0,5)], upper := (rows 25 131 292 73 112 38 70 134 262), lower := (rows 25 131 292 73 112 32 64 128 256), losses := [] }

theorem u35437 : Upper (D 6) (R 6) [24,129,288,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35437 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35438 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 17, targets := 36 }], pairs := [(0,2),(0,5),(4,2)], upper := (rows 25 131 292 74 82 37 101 165 293), lower := (rows 25 131 292 74 82 32 64 128 256), losses := [] }

theorem u35438 : Upper (D 6) (R 6) [24,129,288,66,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35438 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35439 : Route 9 := (fun mask => (mask,id))

def c35439 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35439 : Upper (D 6) (R 6) [24,129,288,66,68] 13 := by
  apply FastRouting.sound _ _ [24,129,288,66,68] 13 (by decide) (choices 1) [1,2,4] r35439 c35439
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19194
  · exact u19195
  · exact u19196

def r35440 : Route 9 := (fun mask => (mask,id))

def c35440 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35440 : Upper (D 6) (R 6) [24,129,288,66,96] 13 := by
  apply FastRouting.sound _ _ [24,129,288,66,96] 13 (by decide) (choices 1) [1,2,4] r35440 c35440
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19197
  · exact u19198
  · exact u19199

def b35441 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 17, targets := 34 }], pairs := [(0,1),(0,5),(4,1)], upper := (rows 25 131 292 76 84 35 99 163 291), lower := (rows 25 131 292 76 84 32 64 128 256), losses := [] }

theorem u35441 : Upper (D 6) (R 6) [24,129,288,68,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35441 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35442 : Route 9 := (fun mask => (mask,id))

def c35442 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35442 : Upper (D 6) (R 6) [24,129,288,68,96] 13 := by
  apply FastRouting.sound _ _ [24,129,288,68,96] 13 (by decide) (choices 1) [1,2,4] r35442 c35442
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19200
  · exact u19201
  · exact u19202

def b35443 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 25, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 25 134 262 11 21 96 96 224 352), lower := (rows 25 134 262 11 21 32 64 128 256), losses := [] }

theorem u35443 : Upper (D 6) (R 6) [24,132,258,3,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35443 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35444 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 486, targets := 1 }], pairs := [(0,1),(1,0),(2,0)], upper := (rows 25 134 262 11 49 100 100 228 356), lower := (rows 25 134 262 11 49 32 64 128 256), losses := [{ target := 1, region := (rows 9 0 4 8 24 38 70 134 262), good := (rows 25 484 484 505 49 32 64 128 256) }] }

theorem u35444 : Upper (D 6) (R 6) [24,132,258,3,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35444 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35445 : Route 9 := (fun mask => (mask,id))

def c35445 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35445 : Upper (D 6) (R 6) [24,132,258,3,36] 13 := by
  apply FastRouting.sound _ _ [24,132,258,3,36] 13 (by decide) (choices 1) [1,64] r35445 c35445
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u19203
  · exact u19204

def r35446 : Route 9 := (fun mask => (mask,id))

def c35446 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35446 : Upper (D 6) (R 6) [24,132,258,3,96] 13 := by
  apply FastRouting.sound _ _ [24,132,258,3,96] 13 (by decide) (choices 1) [1,4,64] r35446 c35446
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19205
  · exact u19206
  · exact u19207

def b35447 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 113, targets := 6 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 25 134 262 14 49 97 97 225 353), lower := (rows 25 134 262 14 49 32 64 128 256), losses := [] }

theorem u35447 : Upper (D 6) (R 6) [24,132,258,6,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35447 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35448 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 113, targets := 6 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 25 134 262 14 112 97 97 225 353), lower := (rows 25 134 262 14 112 32 64 128 256), losses := [] }

theorem u35448 : Upper (D 6) (R 6) [24,132,258,6,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35448 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35449 : PairBound 9 := { available := 70, camps := [{ cop := 5, region := 25, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 25 134 262 41 49 102 70 198 326), lower := (rows 25 134 262 41 49 32 64 128 256), losses := [] }

theorem u35449 : Upper (D 6) (R 6) [24,132,258,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35449 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35450 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 9, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 25 134 262 41 50 101 69 197 325), lower := (rows 25 134 262 41 50 32 64 128 256), losses := [] }

theorem u35450 : Upper (D 6) (R 6) [24,132,258,33,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35450 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m35451_4 : Upper (D 6) (R 6) [24,132,258,33,65,4] 13 :=
  permutation_upper _ _ _ [24,132,258,33,65,2] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19208

def r35451 : Route 9 := (fun mask => (mask,id))

def c35451 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35451 : Upper (D 6) (R 6) [24,132,258,33,65] 13 := by
  apply FastRouting.sound _ _ [24,132,258,33,65] 13 (by decide) (choices 1) [2,4,64] r35451 c35451
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19208
  · exact m35451_4
  · exact u19209

def r35452 : Route 9 := (fun mask => (mask,id))

def c35452 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35452 : Upper (D 6) (R 6) [24,132,258,33,66] 13 := by
  apply FastRouting.sound _ _ [24,132,258,33,66] 13 (by decide) (choices 1) [1,4,64] r35452 c35452
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19210
  · exact u19211
  · exact u19212

def b35453 : PairBound 9 := { available := 71, camps := [{ cop := 4, region := 9, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 25 134 262 41 112 103 71 199 327), lower := (rows 25 134 262 41 112 32 64 128 256), losses := [] }

theorem u35453 : Upper (D 6) (R 6) [24,132,258,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35453 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35454 : Route 9 := (fun mask => (mask,id))

def c35454 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35454 : Upper (D 6) (R 6) [24,132,258,34,36] 13 := by
  apply FastRouting.sound _ _ [24,132,258,34,36] 13 (by decide) (choices 1) [1,64] r35454 c35454
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u19213
  · exact u19214

def r35455 : Route 9 := (fun mask => (mask,id))

def c35455 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35455 : Upper (D 6) (R 6) [24,132,258,34,68] 13 := by
  apply FastRouting.sound _ _ [24,132,258,34,68] 13 (by decide) (choices 1) [1,64] r35455 c35455
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u19215
  · exact u19216

def r35456 : Route 9 := (fun mask => (mask,id))

def c35456 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35456 : Upper (D 6) (R 6) [24,132,258,34,96] 13 := by
  apply FastRouting.sound _ _ [24,132,258,34,96] 13 (by decide) (choices 1) [1,4,64] r35456 c35456
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19217
  · exact u19218
  · exact u19219

def b35457 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 17, targets := 6 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 25 134 262 104 112 39 71 135 263), lower := (rows 25 134 262 104 112 32 64 128 256), losses := [] }

theorem u35457 : Upper (D 6) (R 6) [24,132,258,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35457 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35458 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 25, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 25 134 292 11 19 100 100 228 356), lower := (rows 25 134 292 11 19 32 64 128 256), losses := [] }

theorem u35458 : Upper (D 6) (R 6) [24,132,288,3,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35458 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35459 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 25, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 25 134 292 11 21 98 98 226 354), lower := (rows 25 134 292 11 21 32 64 128 256), losses := [] }

theorem u35459 : Upper (D 6) (R 6) [24,132,288,3,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35459 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u35459
end Delivery.IrregularNine14.P06

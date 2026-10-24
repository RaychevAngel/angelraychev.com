import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0221
import IrregularNine14P07C0222
import IrregularNine14P07C0223

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r31020 : Route 9 := (fun mask => (mask,id))

def c31020 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31020 : Upper (D 7) (R 7) [6,40,96,257,192] 13 := by
  apply FastRouting.sound _ _ [6,40,96,257,192] 13 (by decide) (choices 1) [1,2,16,128] r31020 c31020
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13312
  · exact u13313
  · exact u13314
  · exact u13315

def b31021 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 16, targets := 192 }], pairs := [(3,5),(4,5),(4,6),(4,7)], upper := (rows 7 42 100 280 19 225 193 193 449), lower := (rows 7 42 100 280 19 32 64 128 256), losses := [] }

theorem u31021 : Upper (D 7) (R 7) [6,40,96,272,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31021 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31022 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,6),(3,5),(3,6),(4,5)], upper := (rows 7 42 100 280 81 163 195 131 387), lower := (rows 7 42 100 280 81 32 64 128 256), losses := [] }

theorem u31022 : Upper (D 7) (R 7) [6,40,96,272,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31022 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31023 : Route 9 := (fun mask => (mask,id))

def c31023 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31023 : Upper (D 7) (R 7) [6,40,96,272,66] 13 := by
  apply FastRouting.sound _ _ [6,40,96,272,66] 13 (by decide) (choices 1) [1,128] r31023 c31023
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u13316
  · exact u13317

def r31024 : Route 9 := (fun mask => (mask,id))

def c31024 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31024 : Upper (D 7) (R 7) [6,40,96,272,129] 13 := by
  apply FastRouting.sound _ _ [6,40,96,272,129] 13 (by decide) (choices 1) [1,2,64,128] r31024 c31024
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13318
  · exact u13319
  · exact u13320
  · exact u13321

def r31025 : Route 9 := (fun mask => (mask,id))

def c31025 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31025 : Upper (D 7) (R 7) [6,40,96,272,130] 13 := by
  apply FastRouting.sound _ _ [6,40,96,272,130] 13 (by decide) (choices 1) [1,64,128] r31025 c31025
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13322
  · exact u13323
  · exact u13324

def r31026 : Route 9 := (fun mask => (mask,id))

def c31026 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31026 : Upper (D 7) (R 7) [6,40,96,272,192] 13 := by
  apply FastRouting.sound _ _ [6,40,96,272,192] 13 (by decide) (choices 1) [1,2,128] r31026 c31026
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13325
  · exact u13326
  · exact u13327

def b31027 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 4, region := 492, targets := 2 }], pairs := [(2,1),(3,1),(3,5),(4,5)], upper := (rows 7 42 100 328 19 177 209 145 401), lower := (rows 7 42 100 328 19 32 64 128 256), losses := [] }

theorem u31027 : Upper (D 7) (R 7) [6,40,96,320,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31027 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31028 : Route 9 := (fun mask => (mask,id))

def c31028 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31028 : Upper (D 7) (R 7) [6,40,96,320,129] 13 := by
  apply FastRouting.sound _ _ [6,40,96,320,129] 13 (by decide) (choices 1) [1,2,16,128] r31028 c31028
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13328
  · exact u13329
  · exact u13330
  · exact u13331

def r31029 : Route 9 := (fun mask => (mask,id))

def c31029 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31029 : Upper (D 7) (R 7) [6,40,96,320,130] 13 := by
  apply FastRouting.sound _ _ [6,40,96,320,130] 13 (by decide) (choices 1) [1,16,128] r31029 c31029
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13332
  · exact u13333
  · exact u13334

def b31030 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 16, targets := 192 }], pairs := [(3,5),(4,5),(4,6),(4,7)], upper := (rows 7 42 100 392 19 241 209 209 465), lower := (rows 7 42 100 392 19 32 64 128 256), losses := [] }

theorem u31030 : Upper (D 7) (R 7) [6,40,96,384,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31030 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31031 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,6),(3,5),(3,6),(4,5)], upper := (rows 7 42 100 392 81 179 211 147 403), lower := (rows 7 42 100 392 81 32 64 128 256), losses := [] }

theorem u31031 : Upper (D 7) (R 7) [6,40,96,384,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31031 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31032 : Route 9 := (fun mask => (mask,id))

def c31032 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31032 : Upper (D 7) (R 7) [6,40,96,384,66] 13 := by
  apply FastRouting.sound _ _ [6,40,96,384,66] 13 (by decide) (choices 1) [1,16,128] r31032 c31032
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13335
  · exact u13336
  · exact u13337

def r31033 : Route 9 := (fun mask => (mask,id))

def c31033 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31033 : Upper (D 7) (R 7) [6,40,96,384,129] 13 := by
  apply FastRouting.sound _ _ [6,40,96,384,129] 13 (by decide) (choices 1) [1,2,16,64] r31033 c31033
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13338
  · exact u13339
  · exact u13340
  · exact u13341

def b31034 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 4, region := 101, targets := 128 }], pairs := [(0,7),(2,7),(3,5),(4,5)], upper := (rows 7 42 100 392 146 113 81 209 337), lower := (rows 7 42 100 392 146 32 64 128 256), losses := [] }

theorem u31034 : Upper (D 7) (R 7) [6,40,96,384,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31034 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31035 : Route 9 := (fun mask => (mask,id))

def c31035 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31035 : Upper (D 7) (R 7) [6,40,96,384,192] 13 := by
  apply FastRouting.sound _ _ [6,40,96,384,192] 13 (by decide) (choices 1) [1,2,16] r31035 c31035
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13342
  · exact u13343
  · exact u13344

def b31036 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 24, targets := 224 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 7 42 196 25 19 480 480 480 480), lower := (rows 7 42 196 25 19 32 64 128 256), losses := [] }

theorem u31036 : Upper (D 7) (R 7) [6,40,192,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31036 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31037 : PairBound 9 := { available := 450, camps := [{ cop := 4, region := 10, targets := 192 }], pairs := [(1,6),(1,7),(3,6),(3,7)], upper := (rows 7 42 196 25 49 482 450 450 450), lower := (rows 7 42 196 25 49 32 64 128 256), losses := [] }

theorem u31037 : Upper (D 7) (R 7) [6,40,192,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31037 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31038 : PairBound 9 := { available := 449, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 453, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 7 42 196 25 50 481 449 449 449), lower := (rows 7 42 196 25 50 32 64 128 256), losses := [] }

theorem u31038 : Upper (D 7) (R 7) [6,40,192,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31038 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31039 : PairBound 9 := { available := 418, camps := [{ cop := 4, region := 8, targets := 162 },{ cop := 3, region := 418, targets := 1 }], pairs := [(1,0),(3,1),(3,5),(3,7)], upper := (rows 7 42 196 25 81 418 482 418 418), lower := (rows 7 42 196 25 81 32 64 128 256), losses := [] }

theorem u31039 : Upper (D 7) (R 7) [6,40,192,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31039 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31040 : Route 9 := (fun mask => (mask,id))

def c31040 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u31040 : Upper (D 7) (R 7) [6,40,192,17,66] 13 := by
  apply FastRouting.sound _ _ [6,40,192,17,66] 13 (by decide) (choices 1) [1,128,256] r31040 c31040
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13345
  · exact u13346
  · exact u13347

def r31041 : Route 9 := (fun mask => (mask,id))

def c31041 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u31041 : Upper (D 7) (R 7) [6,40,192,17,96] 13 := by
  apply FastRouting.sound _ _ [6,40,192,17,96] 13 (by decide) (choices 1) [1,2,128,256] r31041 c31041
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13348
  · exact u13349
  · exact u13350
  · exact u13351

def b31042 : PairBound 9 := { available := 291, camps := [{ cop := 2, region := 16, targets := 35 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,1),(4,5)], upper := (rows 7 42 196 25 208 291 355 419 291), lower := (rows 7 42 196 25 208 32 64 128 256), losses := [] }

theorem u31042 : Upper (D 7) (R 7) [6,40,192,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31042 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31043 : PairBound 9 := { available := 226, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 7 42 196 25 273 226 226 226 482), lower := (rows 7 42 196 25 273 32 64 128 256), losses := [] }

theorem u31043 : Upper (D 7) (R 7) [6,40,192,17,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31043 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31044 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c31044 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31044 : Upper (D 7) (R 7) [6,40,192,17,258] 13 := by
  apply FastRouting.sound _ _ [6,40,192,17,258] 13 (by decide) (choices 1) [1,64] r31044 c31044
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u13352
  · exact u13353

def r31045 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c31045 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31045 : Upper (D 7) (R 7) [6,40,192,17,288] 13 := by
  apply FastRouting.sound _ _ [6,40,192,17,288] 13 (by decide) (choices 1) [1,2,64] r31045 c31045
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13354
  · exact u13355
  · exact u13356

def r31046 : Route 9 := (fun mask => (mask,id))

def c31046 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31046 : Upper (D 7) (R 7) [6,40,192,17,320] 13 := by
  apply FastRouting.sound _ _ [6,40,192,17,320] 13 (by decide) (choices 1) [1,2,128] r31046 c31046
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13357
  · exact u13358
  · exact u13359

def b31047 : PairBound 9 := { available := 449, camps := [{ cop := 4, region := 10, targets := 193 }], pairs := [(1,0),(1,6),(1,7),(3,0)], upper := (rows 7 42 196 26 49 481 449 449 449), lower := (rows 7 42 196 26 49 32 64 128 256), losses := [] }

theorem u31047 : Upper (D 7) (R 7) [6,40,192,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31047 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31048 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,6),(2,1),(3,6),(4,1)], upper := (rows 7 42 196 26 81 417 481 417 417), lower := (rows 7 42 196 26 81 32 64 128 256), losses := [] }

theorem u31048 : Upper (D 7) (R 7) [6,40,192,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31048 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31049 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 10, targets := 193 }], pairs := [(1,0),(1,6),(1,7),(3,0)], upper := (rows 7 42 196 26 112 417 449 385 385), lower := (rows 7 42 196 26 112 32 64 128 256), losses := [] }

theorem u31049 : Upper (D 7) (R 7) [6,40,192,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31049 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31050 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 16, targets := 35 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,1),(4,5)], upper := (rows 7 42 196 26 208 289 353 417 289), lower := (rows 7 42 196 26 208 32 64 128 256), losses := [] }

theorem u31050 : Upper (D 7) (R 7) [6,40,192,18,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31050 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31051 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c31051 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31051 : Upper (D 7) (R 7) [6,40,192,18,257] 13 := by
  apply FastRouting.sound _ _ [6,40,192,18,257] 13 (by decide) (choices 1) [1,64] r31051 c31051
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u13360
  · exact u13361

def b31052 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 10, targets := 193 }], pairs := [(1,0),(1,6),(1,7),(3,0)], upper := (rows 7 42 196 26 304 225 193 193 449), lower := (rows 7 42 196 26 304 32 64 128 256), losses := [] }

theorem u31052 : Upper (D 7) (R 7) [6,40,192,18,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31052 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31053 : Route 9 := (fun mask => (mask,id))

def c31053 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31053 : Upper (D 7) (R 7) [6,40,192,18,320] 13 := by
  apply FastRouting.sound _ _ [6,40,192,18,320] 13 (by decide) (choices 1) [1,128] r31053 c31053
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u13362
  · exact u13363

def b31054 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 16, targets := 160 },{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6),(4,5),(4,6),(4,7)], upper := (rows 7 42 196 73 19 432 496 432 432), lower := (rows 7 42 196 73 19 32 64 128 256), losses := [] }

theorem u31054 : Upper (D 7) (R 7) [6,40,192,65,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31054 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31055 : Route 9 := (fun mask => (mask,id))

def c31055 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u31055 : Upper (D 7) (R 7) [6,40,192,65,33] 13 := by
  apply FastRouting.sound _ _ [6,40,192,65,33] 13 (by decide) (choices 1) [2,16,128,256] r31055 c31055
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13364
  · exact u13365
  · exact u13366
  · exact u13367

def b31056 : PairBound 9 := { available := 401, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 453, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 7 42 196 73 50 433 465 401 401), lower := (rows 7 42 196 73 50 32 64 128 256), losses := [] }

theorem u31056 : Upper (D 7) (R 7) [6,40,192,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31056 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31057 : PairBound 9 := { available := 306, camps := [{ cop := 3, region := 434, targets := 64 },{ cop := 4, region := 362, targets := 128 }], pairs := [(1,6),(1,7),(3,7),(4,6)], upper := (rows 7 42 196 73 145 306 370 434 306), lower := (rows 7 42 196 73 145 32 64 128 256), losses := [] }

theorem u31057 : Upper (D 7) (R 7) [6,40,192,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31057 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31058 : Route 9 := (fun mask => (mask,id))

def c31058 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31058 : Upper (D 7) (R 7) [6,40,192,65,130] 13 := by
  apply FastRouting.sound _ _ [6,40,192,65,130] 13 (by decide) (choices 1) [1,16,256] r31058 c31058
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13368
  · exact u13369
  · exact u13370

def r31059 : Route 9 := (fun mask => (mask,id))

def c31059 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31059 : Upper (D 7) (R 7) [6,40,192,65,160] 13 := by
  apply FastRouting.sound _ _ [6,40,192,65,160] 13 (by decide) (choices 1) [1,2,16,256] r31059 c31059
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13371
  · exact u13372
  · exact u13373
  · exact u13374

def r31060 : Route 9 := (fun mask => (mask,id))

def c31060 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31060 : Upper (D 7) (R 7) [6,40,192,65,257] 13 := by
  apply FastRouting.sound _ _ [6,40,192,65,257] 13 (by decide) (choices 1) [2,16,128] r31060 c31060
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13375
  · exact u13376
  · exact u13377

def r31061 : Route 9 := (fun mask => (mask,id))

def c31061 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31061 : Upper (D 7) (R 7) [6,40,192,65,258] 13 := by
  apply FastRouting.sound _ _ [6,40,192,65,258] 13 (by decide) (choices 1) [1,16,128] r31061 c31061
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13378
  · exact u13379
  · exact u13380

def r31062 : Route 9 := (fun mask => (mask,id))

def c31062 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31062 : Upper (D 7) (R 7) [6,40,192,65,288] 13 := by
  apply FastRouting.sound _ _ [6,40,192,65,288] 13 (by decide) (choices 1) [1,2,16,128] r31062 c31062
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13381
  · exact u13382
  · exact u13383
  · exact u13384

def r31063 : Route 9 := (fun mask => (mask,id))

def c31063 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31063 : Upper (D 7) (R 7) [6,40,192,65,384] 13 := by
  apply FastRouting.sound _ _ [6,40,192,65,384] 13 (by decide) (choices 1) [1,2,16] r31063 c31063
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13385
  · exact u13386
  · exact u13387

def b31064 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 432, targets := 64 },{ cop := 4, region := 452, targets := 32 }], pairs := [(2,1),(2,5),(4,1),(4,6)], upper := (rows 7 42 196 74 49 433 465 401 401), lower := (rows 7 42 196 74 49 32 64 128 256), losses := [] }

theorem u31064 : Upper (D 7) (R 7) [6,40,192,66,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31064 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31065 : PairBound 9 := { available := 305, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 4, region := 362, targets := 128 }], pairs := [(1,7),(2,1),(3,7),(4,1)], upper := (rows 7 42 196 74 145 305 369 433 305), lower := (rows 7 42 196 74 145 32 64 128 256), losses := [] }

theorem u31065 : Upper (D 7) (R 7) [6,40,192,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31065 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31066 : Route 9 := (fun mask => (mask,id))

def c31066 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31066 : Upper (D 7) (R 7) [6,40,192,66,160] 13 := by
  apply FastRouting.sound _ _ [6,40,192,66,160] 13 (by decide) (choices 1) [1,16,256] r31066 c31066
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13388
  · exact u13389
  · exact u13390

def r31067 : Route 9 := (fun mask => (mask,id))

def c31067 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31067 : Upper (D 7) (R 7) [6,40,192,66,257] 13 := by
  apply FastRouting.sound _ _ [6,40,192,66,257] 13 (by decide) (choices 1) [1,16,128] r31067 c31067
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13391
  · exact u13392
  · exact u13393

def r31068 : Route 9 := (fun mask => (mask,id))

def c31068 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31068 : Upper (D 7) (R 7) [6,40,192,66,288] 13 := by
  apply FastRouting.sound _ _ [6,40,192,66,288] 13 (by decide) (choices 1) [1,16,128] r31068 c31068
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13394
  · exact u13395
  · exact u13396

def r31069 : Route 9 := (fun mask => (mask,id))

def c31069 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31069 : Upper (D 7) (R 7) [6,40,192,66,384] 13 := by
  apply FastRouting.sound _ _ [6,40,192,66,384] 13 (by decide) (choices 1) [1,16] r31069 c31069
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u13397
  · exact u13398

def b31070 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 16, targets := 160 },{ cop := 4, region := 492, targets := 2 }], pairs := [(2,1),(3,1),(4,5),(4,7)], upper := (rows 7 42 196 88 19 417 481 417 417), lower := (rows 7 42 196 88 19 32 64 128 256), losses := [] }

theorem u31070 : Upper (D 7) (R 7) [6,40,192,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31070 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31071 : PairBound 9 := { available := 387, camps := [{ cop := 1, region := 453, targets := 32 },{ cop := 0, region := 432, targets := 64 }], pairs := [(0,5),(2,5),(3,5),(4,6)], upper := (rows 7 42 196 88 49 419 451 387 387), lower := (rows 7 42 196 88 49 32 64 128 256), losses := [{ target := 5, region := (rows 3 2 23 24 16 0 67 131 259), good := (rows 455 463 196 92 477 0 64 128 256) }] }

theorem u31071 : Upper (D 7) (R 7) [6,40,192,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31071 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31072 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 453, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 7 42 196 88 50 417 449 385 385), lower := (rows 7 42 196 88 50 32 64 128 256), losses := [] }

theorem u31072 : Upper (D 7) (R 7) [6,40,192,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31072 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31073 : Route 9 := (fun mask => (mask,id))

def c31073 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31073 : Upper (D 7) (R 7) [6,40,192,80,129] 13 := by
  apply FastRouting.sound _ _ [6,40,192,80,129] 13 (by decide) (choices 1) [1,2,256] r31073 c31073
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13399
  · exact u13400
  · exact u13401

def r31074 : Route 9 := (fun mask => (mask,id))

def c31074 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31074 : Upper (D 7) (R 7) [6,40,192,80,130] 13 := by
  apply FastRouting.sound _ _ [6,40,192,80,130] 13 (by decide) (choices 1) [1,256] r31074 c31074
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u13402
  · exact u13403

def r31075 : Route 9 := (fun mask => (mask,id))

def c31075 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31075 : Upper (D 7) (R 7) [6,40,192,80,160] 13 := by
  apply FastRouting.sound _ _ [6,40,192,80,160] 13 (by decide) (choices 1) [1,2,256] r31075 c31075
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13404
  · exact u13405
  · exact u13406

def r31076 : Route 9 := (fun mask => (mask,id))

def c31076 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31076 : Upper (D 7) (R 7) [6,40,192,80,257] 13 := by
  apply FastRouting.sound _ _ [6,40,192,80,257] 13 (by decide) (choices 1) [1,2,128] r31076 c31076
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13407
  · exact u13408
  · exact u13409

def r31077 : Route 9 := (fun mask => (mask,id))

def c31077 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31077 : Upper (D 7) (R 7) [6,40,192,80,258] 13 := by
  apply FastRouting.sound _ _ [6,40,192,80,258] 13 (by decide) (choices 1) [1,128] r31077 c31077
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u13410
  · exact u13411

def r31078 : Route 9 := (fun mask => (mask,id))

def c31078 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31078 : Upper (D 7) (R 7) [6,40,192,80,288] 13 := by
  apply FastRouting.sound _ _ [6,40,192,80,288] 13 (by decide) (choices 1) [1,2,128] r31078 c31078
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13412
  · exact u13413
  · exact u13414

def r31079 : Route 9 := (fun mask => (mask,id))

def c31079 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31079 : Upper (D 7) (R 7) [6,40,192,80,384] 13 := by
  apply FastRouting.sound _ _ [6,40,192,80,384] 13 (by decide) (choices 1) [1,2] r31079 c31079
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u13415
  · exact u13416

#print axioms u31079
end Delivery.IrregularNine14.P07

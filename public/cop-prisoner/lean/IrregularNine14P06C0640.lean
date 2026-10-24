import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0403
import IrregularNine14P06C0404
import IrregularNine14P06C0405

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r38400 : Route 9 := (fun mask => (mask,id))

def c38400 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38400 : Upper (D 6) (R 6) [34,136,258,65,36] 13 := by
  apply FastRouting.sound _ _ [34,136,258,65,36] 13 (by decide) (choices 1) [1,4,16,64] r38400 c38400
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24233
  · exact u24234
  · exact u24235
  · exact u24236

def b38401 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 16, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 35 138 262 73 81 52 116 180 308), lower := (rows 35 138 262 73 81 32 64 128 256), losses := [] }

theorem u38401 : Upper (D 6) (R 6) [34,136,258,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38401 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38402 : Route 9 := (fun mask => (mask,id))

def c38402 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38402 : Upper (D 6) (R 6) [34,136,258,65,68] 13 := by
  apply FastRouting.sound _ _ [34,136,258,65,68] 13 (by decide) (choices 1) [1,4,16] r38402 c38402
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24237
  · exact u24238
  · exact u24239

def r38403 : Route 9 := (fun mask => (mask,id))

def c38403 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38403 : Upper (D 6) (R 6) [34,136,258,65,96] 13 := by
  apply FastRouting.sound _ _ [34,136,258,65,96] 13 (by decide) (choices 1) [1,4,16] r38403 c38403
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24240
  · exact u24241
  · exact u24242

def r38404 : Route 9 := (fun mask => (mask,id))

def c38404 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38404 : Upper (D 6) (R 6) [34,136,258,68,5] 13 := by
  apply FastRouting.sound _ _ [34,136,258,68,5] 13 (by decide) (choices 1) [1,16,64] r38404 c38404
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24243
  · exact u24244
  · exact u24245

def b38405 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 138 262 76 49 117 85 213 341), lower := (rows 35 138 262 76 49 32 64 128 256), losses := [] }

theorem u38405 : Upper (D 6) (R 6) [34,136,258,68,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38405 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38406 : Route 9 := (fun mask => (mask,id))

def c38406 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38406 : Upper (D 6) (R 6) [34,136,258,68,36] 13 := by
  apply FastRouting.sound _ _ [34,136,258,68,36] 13 (by decide) (choices 1) [1,16,64] r38406 c38406
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24246
  · exact u24247
  · exact u24248

def r38407 : Route 9 := (fun mask => (mask,id))

def c38407 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38407 : Upper (D 6) (R 6) [34,136,258,68,65] 13 := by
  apply FastRouting.sound _ _ [34,136,258,68,65] 13 (by decide) (choices 1) [1,4,16] r38407 c38407
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24249
  · exact u24250
  · exact u24251

def b38408 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 138 262 76 84 49 113 177 305), lower := (rows 35 138 262 76 84 32 64 128 256), losses := [] }

theorem u38408 : Upper (D 6) (R 6) [34,136,258,68,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38408 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38409 : Route 9 := (fun mask => (mask,id))

def c38409 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38409 : Upper (D 6) (R 6) [34,136,258,68,96] 13 := by
  apply FastRouting.sound _ _ [34,136,258,68,96] 13 (by decide) (choices 1) [1,4,16] r38409 c38409
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24252
  · exact u24253
  · exact u24254

def r38410 : Route 9 := (fun mask => (mask,id))

def c38410 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38410 : Upper (D 6) (R 6) [34,136,258,80,5] 13 := by
  apply FastRouting.sound _ _ [34,136,258,80,5] 13 (by decide) (choices 1) [1,4,64] r38410 c38410
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24255
  · exact u24256
  · exact u24257

def b38411 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 138 262 88 49 101 69 197 325), lower := (rows 35 138 262 88 49 32 64 128 256), losses := [] }

theorem u38411 : Upper (D 6) (R 6) [34,136,258,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38411 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38412 : Route 9 := (fun mask => (mask,id))

def c38412 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38412 : Upper (D 6) (R 6) [34,136,258,80,36] 13 := by
  apply FastRouting.sound _ _ [34,136,258,80,36] 13 (by decide) (choices 1) [1,4,64] r38412 c38412
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24258
  · exact u24259
  · exact u24260

def b38413 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 35 138 262 88 81 37 101 165 293), lower := (rows 35 138 262 88 81 32 64 128 256), losses := [] }

theorem u38413 : Upper (D 6) (R 6) [34,136,258,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38413 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38414 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 35 138 262 88 84 37 101 165 293), lower := (rows 35 138 262 88 84 32 64 128 256), losses := [] }

theorem u38414 : Upper (D 6) (R 6) [34,136,258,80,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38414 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38415 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 35 138 262 88 112 37 69 133 261), lower := (rows 35 138 262 88 112 32 64 128 256), losses := [] }

theorem u38415 : Upper (D 6) (R 6) [34,136,258,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38415 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38416 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 4, region := 104, targets := 2 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 35 138 262 104 21 117 85 213 341), lower := (rows 35 138 262 104 21 32 64 128 256), losses := [] }

theorem u38416 : Upper (D 6) (R 6) [34,136,258,96,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38416 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38417 : Route 9 := (fun mask => (mask,id))

def c38417 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38417 : Upper (D 6) (R 6) [34,136,258,96,65] 13 := by
  apply FastRouting.sound _ _ [34,136,258,96,65] 13 (by decide) (choices 1) [1,4,16] r38417 c38417
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24261
  · exact u24262
  · exact u24263

def r38418 : Route 9 := (fun mask => (mask,id))

def c38418 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38418 : Upper (D 6) (R 6) [34,136,258,96,68] 13 := by
  apply FastRouting.sound _ _ [34,136,258,96,68] 13 (by decide) (choices 1) [1,4,16] r38418 c38418
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24264
  · exact u24265
  · exact u24266

def b38419 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 138 276 13 19 100 100 228 356), lower := (rows 35 138 276 13 19 32 64 128 256), losses := [] }

theorem u38419 : Upper (D 6) (R 6) [34,136,272,5,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38419 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38420 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 35 138 276 13 21 98 98 226 354), lower := (rows 35 138 276 13 21 32 64 128 256), losses := [] }

theorem u38420 : Upper (D 6) (R 6) [34,136,272,5,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38420 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38421 : Route 9 := (fun mask => (mask,id))

def c38421 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38421 : Upper (D 6) (R 6) [34,136,272,5,6] 13 := by
  apply FastRouting.sound _ _ [34,136,272,5,6] 13 (by decide) (choices 1) [1,64] r38421 c38421
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u24267
  · exact u24268

def b38422 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 138 276 13 49 102 70 198 326), lower := (rows 35 138 276 13 49 32 64 128 256), losses := [] }

theorem u38422 : Upper (D 6) (R 6) [34,136,272,5,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38422 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38423 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 138 276 13 50 101 69 197 325), lower := (rows 35 138 276 13 50 32 64 128 256), losses := [] }

theorem u38423 : Upper (D 6) (R 6) [34,136,272,5,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38423 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38424 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 227, targets := 4 },{ cop := 3, region := 194, targets := 32 }], pairs := [(0,2),(1,2),(1,5)], upper := (rows 35 138 276 13 52 99 67 195 323), lower := (rows 35 138 276 13 52 32 64 128 256), losses := [] }

theorem u38424 : Upper (D 6) (R 6) [34,136,272,5,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38424 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38425 : Route 9 := (fun mask => (mask,id))

def c38425 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38425 : Upper (D 6) (R 6) [34,136,272,5,65] 13 := by
  apply FastRouting.sound _ _ [34,136,272,5,65] 13 (by decide) (choices 1) [2,4,64] r38425 c38425
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24269
  · exact u24270
  · exact u24271

def r38426 : Route 9 := (fun mask => (mask,id))

def c38426 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38426 : Upper (D 6) (R 6) [34,136,272,5,66] 13 := by
  apply FastRouting.sound _ _ [34,136,272,5,66] 13 (by decide) (choices 1) [1,4,64] r38426 c38426
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24272
  · exact u24273
  · exact u24274

def r38427 : Route 9 := (fun mask => (mask,id))

def c38427 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38427 : Upper (D 6) (R 6) [34,136,272,5,68] 13 := by
  apply FastRouting.sound _ _ [34,136,272,5,68] 13 (by decide) (choices 1) [1,2,64] r38427 c38427
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24275
  · exact u24276
  · exact u24277

def r38428 : Route 9 := (fun mask => (mask,id))

def c38428 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38428 : Upper (D 6) (R 6) [34,136,272,5,96] 13 := by
  apply FastRouting.sound _ _ [34,136,272,5,96] 13 (by decide) (choices 1) [1,2,4,64] r38428 c38428
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24278
  · exact u24279
  · exact u24280
  · exact u24281

def b38429 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 3, region := 97, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 138 276 14 21 97 97 225 353), lower := (rows 35 138 276 14 21 32 64 128 256), losses := [] }

theorem u38429 : Upper (D 6) (R 6) [34,136,272,6,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38429 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38430 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 138 276 14 49 101 69 197 325), lower := (rows 35 138 276 14 49 32 64 128 256), losses := [] }

theorem u38430 : Upper (D 6) (R 6) [34,136,272,6,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38430 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38431 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 3, region := 97, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 138 276 14 52 97 65 193 321), lower := (rows 35 138 276 14 52 32 64 128 256), losses := [] }

theorem u38431 : Upper (D 6) (R 6) [34,136,272,6,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38431 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38432 : Route 9 := (fun mask => (mask,id))

def c38432 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38432 : Upper (D 6) (R 6) [34,136,272,6,65] 13 := by
  apply FastRouting.sound _ _ [34,136,272,6,65] 13 (by decide) (choices 1) [1,4,64] r38432 c38432
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24282
  · exact u24283
  · exact u24284

def b38433 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 3, region := 97, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 138 276 14 84 97 97 225 353), lower := (rows 35 138 276 14 84 32 64 128 256), losses := [] }

theorem u38433 : Upper (D 6) (R 6) [34,136,272,6,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38433 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38434 : Route 9 := (fun mask => (mask,id))

def c38434 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38434 : Upper (D 6) (R 6) [34,136,272,6,96] 13 := by
  apply FastRouting.sound _ _ [34,136,272,6,96] 13 (by decide) (choices 1) [1,4,64] r38434 c38434
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24285
  · exact u24286
  · exact u24287

def b38435 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(4,2),(4,6)], upper := (rows 35 138 276 44 19 101 69 197 325), lower := (rows 35 138 276 44 19 32 64 128 256), losses := [] }

theorem u38435 : Upper (D 6) (R 6) [34,136,272,36,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38435 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38436 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 3, region := 195, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 138 276 44 21 99 67 195 323), lower := (rows 35 138 276 44 21 32 64 128 256), losses := [] }

theorem u38436 : Upper (D 6) (R 6) [34,136,272,36,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38436 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38437 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 3, region := 195, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 138 276 44 22 97 65 193 321), lower := (rows 35 138 276 44 22 32 64 128 256), losses := [] }

theorem u38437 : Upper (D 6) (R 6) [34,136,272,36,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38437 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38438 : Route 9 := (fun mask => (mask,id))

def c38438 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38438 : Upper (D 6) (R 6) [34,136,272,36,65] 13 := by
  apply FastRouting.sound _ _ [34,136,272,36,65] 13 (by decide) (choices 1) [1,2,4,64] r38438 c38438
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24288
  · exact u24289
  · exact u24290
  · exact u24291

def r38439 : Route 9 := (fun mask => (mask,id))

def c38439 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38439 : Upper (D 6) (R 6) [34,136,272,36,66] 13 := by
  apply FastRouting.sound _ _ [34,136,272,36,66] 13 (by decide) (choices 1) [1,4,64] r38439 c38439
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24292
  · exact u24293
  · exact u24294

def b38440 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 3, region := 195, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 138 276 44 84 99 67 195 323), lower := (rows 35 138 276 44 84 32 64 128 256), losses := [] }

theorem u38440 : Upper (D 6) (R 6) [34,136,272,36,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38440 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38441 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 138 276 73 19 100 100 228 356), lower := (rows 35 138 276 73 19 32 64 128 256), losses := [] }

theorem u38441 : Upper (D 6) (R 6) [34,136,272,65,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38441 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38442 : Route 9 := (fun mask => (mask,id))

def c38442 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38442 : Upper (D 6) (R 6) [34,136,272,65,5] 13 := by
  apply FastRouting.sound _ _ [34,136,272,65,5] 13 (by decide) (choices 1) [2,4,64] r38442 c38442
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24295
  · exact u24296
  · exact u24297

def r38443 : Route 9 := (fun mask => (mask,id))

def c38443 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38443 : Upper (D 6) (R 6) [34,136,272,65,6] 13 := by
  apply FastRouting.sound _ _ [34,136,272,65,6] 13 (by decide) (choices 1) [1,4,64] r38443 c38443
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24298
  · exact u24299
  · exact u24300

def b38444 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 138 276 73 49 102 70 198 326), lower := (rows 35 138 276 73 49 32 64 128 256), losses := [] }

theorem u38444 : Upper (D 6) (R 6) [34,136,272,65,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38444 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38445 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 138 276 73 50 101 69 197 325), lower := (rows 35 138 276 73 50 32 64 128 256), losses := [] }

theorem u38445 : Upper (D 6) (R 6) [34,136,272,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38445 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38446 : Route 9 := (fun mask => (mask,id))

def c38446 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38446 : Upper (D 6) (R 6) [34,136,272,65,36] 13 := by
  apply FastRouting.sound _ _ [34,136,272,65,36] 13 (by decide) (choices 1) [1,2,4,64] r38446 c38446
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24301
  · exact u24302
  · exact u24303
  · exact u24304

def b38447 : PairBound 9 := { available := 38, camps := [{ cop := 3, region := 16, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 35 138 276 73 81 38 102 166 294), lower := (rows 35 138 276 73 81 32 64 128 256), losses := [] }

theorem u38447 : Upper (D 6) (R 6) [34,136,272,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38447 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38448 : Route 9 := (fun mask => (mask,id))

def c38448 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38448 : Upper (D 6) (R 6) [34,136,272,65,66] 13 := by
  apply FastRouting.sound _ _ [34,136,272,65,66] 13 (by decide) (choices 1) [1,4] r38448 c38448
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u24305
  · exact u24306

def r38449 : Route 9 := (fun mask => (mask,id))

def c38449 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38449 : Upper (D 6) (R 6) [34,136,272,65,68] 13 := by
  apply FastRouting.sound _ _ [34,136,272,65,68] 13 (by decide) (choices 1) [1,2,4] r38449 c38449
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24307
  · exact u24308
  · exact u24309

def r38450 : Route 9 := (fun mask => (mask,id))

def c38450 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38450 : Upper (D 6) (R 6) [34,136,272,65,96] 13 := by
  apply FastRouting.sound _ _ [34,136,272,65,96] 13 (by decide) (choices 1) [1,2,4] r38450 c38450
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24310
  · exact u24311
  · exact u24312

def r38451 : Route 9 := (fun mask => (mask,id))

def c38451 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38451 : Upper (D 6) (R 6) [34,136,272,66,5] 13 := by
  apply FastRouting.sound _ _ [34,136,272,66,5] 13 (by decide) (choices 1) [1,4,64] r38451 c38451
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24313
  · exact u24314
  · exact u24315

def b38452 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 138 276 74 49 101 69 197 325), lower := (rows 35 138 276 74 49 32 64 128 256), losses := [] }

theorem u38452 : Upper (D 6) (R 6) [34,136,272,66,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38452 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38453 : Route 9 := (fun mask => (mask,id))

def c38453 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38453 : Upper (D 6) (R 6) [34,136,272,66,36] 13 := by
  apply FastRouting.sound _ _ [34,136,272,66,36] 13 (by decide) (choices 1) [1,4,64] r38453 c38453
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24316
  · exact u24317
  · exact u24318

def b38454 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 4, region := 292, targets := 64 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 35 138 276 74 81 37 101 165 293), lower := (rows 35 138 276 74 81 32 64 128 256), losses := [] }

theorem u38454 : Upper (D 6) (R 6) [34,136,272,66,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38454 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38455 : Route 9 := (fun mask => (mask,id))

def c38455 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38455 : Upper (D 6) (R 6) [34,136,272,66,68] 13 := by
  apply FastRouting.sound _ _ [34,136,272,66,68] 13 (by decide) (choices 1) [1,4] r38455 c38455
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u24319
  · exact u24320

def r38456 : Route 9 := (fun mask => (mask,id))

def c38456 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38456 : Upper (D 6) (R 6) [34,136,272,66,96] 13 := by
  apply FastRouting.sound _ _ [34,136,272,66,96] 13 (by decide) (choices 1) [1,4] r38456 c38456
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u24321
  · exact u24322

def b38457 : PairBound 9 := { available := 101, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 138 276 76 19 101 101 229 357), lower := (rows 35 138 276 76 19 32 64 128 256), losses := [] }

theorem u38457 : Upper (D 6) (R 6) [34,136,272,68,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38457 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38458 : Route 9 := (fun mask => (mask,id))

def c38458 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38458 : Upper (D 6) (R 6) [34,136,272,68,5] 13 := by
  apply FastRouting.sound _ _ [34,136,272,68,5] 13 (by decide) (choices 1) [1,2,64] r38458 c38458
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24323
  · exact u24324
  · exact u24325

def r38459 : Route 9 := (fun mask => (mask,id))

def c38459 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38459 : Upper (D 6) (R 6) [34,136,272,68,6] 13 := by
  apply FastRouting.sound _ _ [34,136,272,68,6] 13 (by decide) (choices 1) [1,64] r38459 c38459
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u24326
  · exact u24327

#print axioms u38459
end Delivery.IrregularNine14.P06

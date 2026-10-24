import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0487
import IrregularNine14P07C0488
import IrregularNine14P07C0489

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r40500 : Route 9 := (fun mask => (mask,id))

def c40500 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40500 : Upper (D 7) (R 7) [96,260,136,3,130] 13 := by
  apply FastRouting.sound _ _ [96,260,136,3,130] 13 (by decide) (choices 1) [1,16,64] r40500 c40500
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29254
  · exact u29255
  · exact u29256

def r40501 : Route 9 := (fun mask => (mask,id))

def c40501 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40501 : Upper (D 7) (R 7) [96,260,136,3,160] 13 := by
  apply FastRouting.sound _ _ [96,260,136,3,160] 13 (by decide) (choices 1) [1,2,16,64] r40501 c40501
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29257
  · exact u29258
  · exact u29259
  · exact u29260

def b40502 : PairBound 9 := { available := 226, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 97 262 140 25 19 226 226 226 482), lower := (rows 97 262 140 25 19 32 64 128 256), losses := [] }

theorem u40502 : Upper (D 7) (R 7) [96,260,136,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40502 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40503 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 24, targets := 194 }], pairs := [(3,1),(3,6),(3,7),(4,1)], upper := (rows 97 262 140 25 49 226 194 194 450), lower := (rows 97 262 140 25 49 32 64 128 256), losses := [] }

theorem u40503 : Upper (D 7) (R 7) [96,260,136,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40503 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40504 : Route 9 := (fun mask => (mask,id))

def c40504 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40504 : Upper (D 7) (R 7) [96,260,136,17,34] 13 := by
  apply FastRouting.sound _ _ [96,260,136,17,34] 13 (by decide) (choices 1) [1,2,64,128] r40504 c40504
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29261
  · exact u29262
  · exact u29263
  · exact u29264

def b40505 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 24, targets := 130 }], pairs := [(3,1),(3,7),(4,1),(4,7)], upper := (rows 97 262 140 25 112 163 195 131 387), lower := (rows 97 262 140 25 112 32 64 128 256), losses := [] }

theorem u40505 : Upper (D 7) (R 7) [96,260,136,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40505 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40506 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 12, targets := 98 }], pairs := [(2,1),(2,5),(2,6),(3,1)], upper := (rows 97 262 140 25 145 98 98 226 354), lower := (rows 97 262 140 25 145 32 64 128 256), losses := [] }

theorem u40506 : Upper (D 7) (R 7) [96,260,136,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40506 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40507 : Route 9 := (fun mask => (mask,id))

def c40507 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40507 : Upper (D 7) (R 7) [96,260,136,17,130] 13 := by
  apply FastRouting.sound _ _ [96,260,136,17,130] 13 (by decide) (choices 1) [1,2,64] r40507 c40507
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29265
  · exact u29266
  · exact u29267

def b40508 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 3, region := 454, targets := 32 }], pairs := [(0,7),(1,5),(1,7),(2,5)], upper := (rows 97 262 140 25 176 99 67 195 323), lower := (rows 97 262 140 25 176 32 64 128 256), losses := [] }

theorem u40508 : Upper (D 7) (R 7) [96,260,136,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40508 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40509 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 97 262 140 26 19 225 225 225 481), lower := (rows 97 262 140 26 19 32 64 128 256), losses := [] }

theorem u40509 : Upper (D 7) (R 7) [96,260,136,18,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40509 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40510 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 97 262 140 26 49 227 195 195 451), lower := (rows 97 262 140 26 49 32 64 128 256), losses := [] }

theorem u40510 : Upper (D 7) (R 7) [96,260,136,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40510 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40511 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 97 262 140 26 50 225 193 193 449), lower := (rows 97 262 140 26 50 32 64 128 256), losses := [] }

theorem u40511 : Upper (D 7) (R 7) [96,260,136,18,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40511 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40512 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 16, targets := 130 },{ cop := 4, region := 1, targets := 130 }], pairs := [(0,1),(0,7),(4,1),(4,7)], upper := (rows 97 262 140 26 112 163 195 131 387), lower := (rows 97 262 140 26 112 32 64 128 256), losses := [] }

theorem u40512 : Upper (D 7) (R 7) [96,260,136,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40512 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40513 : Route 9 := (fun mask => (mask,id))

def c40513 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40513 : Upper (D 7) (R 7) [96,260,136,18,129] 13 := by
  apply FastRouting.sound _ _ [96,260,136,18,129] 13 (by decide) (choices 1) [1,2,64] r40513 c40513
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29268
  · exact u29269
  · exact u29270

def b40514 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 12, targets := 97 }], pairs := [(2,0),(2,5),(2,6),(3,0)], upper := (rows 97 262 140 26 146 97 97 225 353), lower := (rows 97 262 140 26 146 32 64 128 256), losses := [] }

theorem u40514 : Upper (D 7) (R 7) [96,260,136,18,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40514 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40515 : Route 9 := (fun mask => (mask,id))

def c40515 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40515 : Upper (D 7) (R 7) [96,260,136,18,160] 13 := by
  apply FastRouting.sound _ _ [96,260,136,18,160] 13 (by decide) (choices 1) [1,2,64] r40515 c40515
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29271
  · exact u29272
  · exact u29273

def r40516 : Route 9 := (fun mask => (mask,id))

def c40516 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u40516 : Upper (D 7) (R 7) [96,260,136,34,3] 13 := by
  apply FastRouting.sound _ _ [96,260,136,34,3] 13 (by decide) (choices 1) [1,16,64,128] r40516 c40516
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29274
  · exact u29275
  · exact u29276
  · exact u29277

def b40517 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 16, targets := 162 },{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6),(4,1),(4,5),(4,7)], upper := (rows 97 262 140 42 81 179 211 147 403), lower := (rows 97 262 140 42 81 32 64 128 256), losses := [] }

theorem u40517 : Upper (D 7) (R 7) [96,260,136,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40517 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40518 : Route 9 := (fun mask => (mask,id))

def c40518 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40518 : Upper (D 7) (R 7) [96,260,136,34,66] 13 := by
  apply FastRouting.sound _ _ [96,260,136,34,66] 13 (by decide) (choices 1) [1,16,128] r40518 c40518
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29278
  · exact u29279
  · exact u29280

def r40519 : Route 9 := (fun mask => (mask,id))

def c40519 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40519 : Upper (D 7) (R 7) [96,260,136,34,129] 13 := by
  apply FastRouting.sound _ _ [96,260,136,34,129] 13 (by decide) (choices 1) [1,2,16,64] r40519 c40519
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29281
  · exact u29282
  · exact u29283
  · exact u29284

def r40520 : Route 9 := (fun mask => (mask,id))

def c40520 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40520 : Upper (D 7) (R 7) [96,260,136,34,130] 13 := by
  apply FastRouting.sound _ _ [96,260,136,34,130] 13 (by decide) (choices 1) [1,16,64] r40520 c40520
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29285
  · exact u29286
  · exact u29287

def r40521 : Route 9 := (fun mask => (mask,id))

def c40521 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40521 : Upper (D 7) (R 7) [96,260,136,34,192] 13 := by
  apply FastRouting.sound _ _ [96,260,136,34,192] 13 (by decide) (choices 1) [1,2,16] r40521 c40521
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29288
  · exact u29289
  · exact u29290

def r40522 : Route 9 := (fun mask => (mask,id))

def c40522 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40522 : Upper (D 7) (R 7) [96,260,136,48,3] 13 := by
  apply FastRouting.sound _ _ [96,260,136,48,3] 13 (by decide) (choices 1) [1,2,64,128] r40522 c40522
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29291
  · exact u29292
  · exact u29293
  · exact u29294

def b40523 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 24, targets := 130 }], pairs := [(3,1),(3,7),(4,1),(4,7)], upper := (rows 97 262 140 56 81 163 195 131 387), lower := (rows 97 262 140 56 81 32 64 128 256), losses := [] }

theorem u40523 : Upper (D 7) (R 7) [96,260,136,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40523 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40524 : Route 9 := (fun mask => (mask,id))

def c40524 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40524 : Upper (D 7) (R 7) [96,260,136,48,66] 13 := by
  apply FastRouting.sound _ _ [96,260,136,48,66] 13 (by decide) (choices 1) [1,2,128] r40524 c40524
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29295
  · exact u29296
  · exact u29297

def r40525 : Route 9 := (fun mask => (mask,id))

def c40525 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40525 : Upper (D 7) (R 7) [96,260,136,48,129] 13 := by
  apply FastRouting.sound _ _ [96,260,136,48,129] 13 (by decide) (choices 1) [1,2,64] r40525 c40525
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29298
  · exact u29299
  · exact u29300

def r40526 : Route 9 := (fun mask => (mask,id))

def c40526 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40526 : Upper (D 7) (R 7) [96,260,136,48,130] 13 := by
  apply FastRouting.sound _ _ [96,260,136,48,130] 13 (by decide) (choices 1) [1,2,64] r40526 c40526
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29301
  · exact u29302
  · exact u29303

def r40527 : Route 9 := (fun mask => (mask,id))

def c40527 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40527 : Upper (D 7) (R 7) [96,260,136,48,192] 13 := by
  apply FastRouting.sound _ _ [96,260,136,48,192] 13 (by decide) (choices 1) [1,2] r40527 c40527
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u29304
  · exact u29305

def b40528 : PairBound 9 := { available := 216, camps := [{ cop := 3, region := 16, targets := 192 },{ cop := 4, region := 8, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 97 262 164 11 19 248 216 216 472), lower := (rows 97 262 164 11 19 32 64 128 256), losses := [] }

theorem u40528 : Upper (D 7) (R 7) [96,260,160,3,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40528 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40529 : PairBound 9 := { available := 210, camps := [{ cop := 3, region := 16, targets := 194 },{ cop := 4, region := 486, targets := 1 }], pairs := [(1,0),(4,1),(4,6),(4,7)], upper := (rows 97 262 164 11 25 242 210 210 466), lower := (rows 97 262 164 11 25 32 64 128 256), losses := [] }

theorem u40529 : Upper (D 7) (R 7) [96,260,160,3,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40529 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40530 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 16, targets := 193 },{ cop := 4, region := 225, targets := 2 }], pairs := [(0,1),(4,0),(4,6),(4,7)], upper := (rows 97 262 164 11 26 241 209 209 465), lower := (rows 97 262 164 11 26 32 64 128 256), losses := [] }

theorem u40530 : Upper (D 7) (R 7) [96,260,160,3,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40530 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40531 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 16, targets := 162 },{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6),(4,1),(4,5),(4,7)], upper := (rows 97 262 164 11 81 186 218 154 410), lower := (rows 97 262 164 11 81 32 64 128 256), losses := [] }

theorem u40531 : Upper (D 7) (R 7) [96,260,160,3,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40531 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40532 : Route 9 := (fun mask => (mask,id))

def c40532 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40532 : Upper (D 7) (R 7) [96,260,160,3,66] 13 := by
  apply FastRouting.sound _ _ [96,260,160,3,66] 13 (by decide) (choices 1) [1,8,16,128] r40532 c40532
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29306
  · exact u29307
  · exact u29308
  · exact u29309

def r40533 : Route 9 := (fun mask => (mask,id))

def c40533 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40533 : Upper (D 7) (R 7) [96,260,160,3,72] 13 := by
  apply FastRouting.sound _ _ [96,260,160,3,72] 13 (by decide) (choices 1) [1,2,16,128] r40533 c40533
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29310
  · exact u29311
  · exact u29312
  · exact u29313

def r40534 : Route 9 := (fun mask => (mask,id))

def c40534 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40534 : Upper (D 7) (R 7) [96,260,160,3,129] 13 := by
  apply FastRouting.sound _ _ [96,260,160,3,129] 13 (by decide) (choices 1) [2,8,16,64] r40534 c40534
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29314
  · exact u29315
  · exact u29316
  · exact u29317

def r40535 : Route 9 := (fun mask => (mask,id))

def c40535 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40535 : Upper (D 7) (R 7) [96,260,160,3,130] 13 := by
  apply FastRouting.sound _ _ [96,260,160,3,130] 13 (by decide) (choices 1) [1,8,16,64] r40535 c40535
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29318
  · exact u29319
  · exact u29320
  · exact u29321

def r40536 : Route 9 := (fun mask => (mask,id))

def c40536 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40536 : Upper (D 7) (R 7) [96,260,160,3,136] 13 := by
  apply FastRouting.sound _ _ [96,260,160,3,136] 13 (by decide) (choices 1) [1,2,16,64] r40536 c40536
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29322
  · exact u29323
  · exact u29324
  · exact u29325

def r40537 : Route 9 := (fun mask => (mask,id))

def c40537 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40537 : Upper (D 7) (R 7) [96,260,160,3,192] 13 := by
  apply FastRouting.sound _ _ [96,260,160,3,192] 13 (by decide) (choices 1) [1,2,8,16] r40537 c40537
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29326
  · exact u29327
  · exact u29328
  · exact u29329

def b40538 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 24, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 97 262 164 25 25 226 194 194 450), lower := (rows 97 262 164 25 25 32 64 128 256), losses := [] }

theorem u40538 : Upper (D 7) (R 7) [96,260,160,17,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40538 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40539 : Route 9 := (fun mask => (mask,id))

def c40539 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40539 : Upper (D 7) (R 7) [96,260,160,17,10] 13 := by
  apply FastRouting.sound _ _ [96,260,160,17,10] 13 (by decide) (choices 1) [1,2,64,128] r40539 c40539
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29330
  · exact u29331
  · exact u29332
  · exact u29333

def b40540 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 24, targets := 162 }], pairs := [(3,1),(3,5),(3,7),(4,1)], upper := (rows 97 262 164 25 81 170 202 138 394), lower := (rows 97 262 164 25 81 32 64 128 256), losses := [] }

theorem u40540 : Upper (D 7) (R 7) [96,260,160,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40540 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40541 : Route 9 := (fun mask => (mask,id))

def c40541 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40541 : Upper (D 7) (R 7) [96,260,160,17,66] 13 := by
  apply FastRouting.sound _ _ [96,260,160,17,66] 13 (by decide) (choices 1) [1,2,8,128] r40541 c40541
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29334
  · exact u29335
  · exact u29336
  · exact u29337

def b40542 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 24, targets := 162 }], pairs := [(3,1),(3,5),(3,7),(4,1)], upper := (rows 97 262 164 25 88 163 195 131 387), lower := (rows 97 262 164 25 88 32 64 128 256), losses := [] }

theorem u40542 : Upper (D 7) (R 7) [96,260,160,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40542 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40543 : PairBound 9 := { available := 74, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 97 262 164 25 145 106 74 202 330), lower := (rows 97 262 164 25 145 32 64 128 256), losses := [] }

theorem u40543 : Upper (D 7) (R 7) [96,260,160,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40543 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40544 : Route 9 := (fun mask => (mask,id))

def c40544 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40544 : Upper (D 7) (R 7) [96,260,160,17,130] 13 := by
  apply FastRouting.sound _ _ [96,260,160,17,130] 13 (by decide) (choices 1) [1,2,8,64] r40544 c40544
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29338
  · exact u29339
  · exact u29340
  · exact u29341

def r40545 : Route 9 := (fun mask => (mask,id))

def c40545 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40545 : Upper (D 7) (R 7) [96,260,160,17,136] 13 := by
  apply FastRouting.sound _ _ [96,260,160,17,136] 13 (by decide) (choices 1) [1,2,64] r40545 c40545
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29342
  · exact u29343
  · exact u29344

def r40546 : Route 9 := (fun mask => (mask,id))

def c40546 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40546 : Upper (D 7) (R 7) [96,260,160,17,192] 13 := by
  apply FastRouting.sound _ _ [96,260,160,17,192] 13 (by decide) (choices 1) [1,2,8] r40546 c40546
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29345
  · exact u29346
  · exact u29347

def b40547 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 24, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 97 262 164 26 26 225 193 193 449), lower := (rows 97 262 164 26 26 32 64 128 256), losses := [] }

theorem u40547 : Upper (D 7) (R 7) [96,260,160,18,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40547 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40548 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 16, targets := 162 },{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6),(4,1),(4,5),(4,7)], upper := (rows 97 262 164 26 81 171 203 139 395), lower := (rows 97 262 164 26 81 32 64 128 256), losses := [] }

theorem u40548 : Upper (D 7) (R 7) [96,260,160,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40548 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40549 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 97 262 164 26 82 169 201 137 393), lower := (rows 97 262 164 26 82 32 64 128 256), losses := [] }

theorem u40549 : Upper (D 7) (R 7) [96,260,160,18,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40549 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40550 : Route 9 := (fun mask => (mask,id))

def c40550 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40550 : Upper (D 7) (R 7) [96,260,160,18,72] 13 := by
  apply FastRouting.sound _ _ [96,260,160,18,72] 13 (by decide) (choices 1) [1,2,128] r40550 c40550
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29348
  · exact u29349
  · exact u29350

def r40551 : Route 9 := (fun mask => (mask,id))

def c40551 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40551 : Upper (D 7) (R 7) [96,260,160,18,129] 13 := by
  apply FastRouting.sound _ _ [96,260,160,18,129] 13 (by decide) (choices 1) [1,2,8,64] r40551 c40551
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29351
  · exact u29352
  · exact u29353
  · exact u29354

def b40552 : PairBound 9 := { available := 73, camps := [{ cop := 4, region := 8, targets := 97 },{ cop := 3, region := 97, targets := 2 }], pairs := [(0,1),(3,0),(3,5),(3,6)], upper := (rows 97 262 164 26 146 105 73 201 329), lower := (rows 97 262 164 26 146 32 64 128 256), losses := [] }

theorem u40552 : Upper (D 7) (R 7) [96,260,160,18,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40552 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40553 : Route 9 := (fun mask => (mask,id))

def c40553 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40553 : Upper (D 7) (R 7) [96,260,160,18,136] 13 := by
  apply FastRouting.sound _ _ [96,260,160,18,136] 13 (by decide) (choices 1) [1,2,64] r40553 c40553
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29355
  · exact u29356
  · exact u29357

def r40554 : Route 9 := (fun mask => (mask,id))

def c40554 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40554 : Upper (D 7) (R 7) [96,260,160,18,192] 13 := by
  apply FastRouting.sound _ _ [96,260,160,18,192] 13 (by decide) (choices 1) [1,2,8] r40554 c40554
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29358
  · exact u29359
  · exact u29360

def b40555 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 8, targets := 162 },{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6),(3,1),(3,5),(3,7)], upper := (rows 97 262 164 73 145 58 90 154 282), lower := (rows 97 262 164 73 145 32 64 128 256), losses := [] }

theorem u40555 : Upper (D 7) (R 7) [96,260,160,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40555 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40556 : PairBound 9 := { available := 27, camps := [{ cop := 0, region := 8, targets := 162 },{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6),(3,1),(3,5),(3,7)], upper := (rows 97 262 164 73 146 59 91 155 283), lower := (rows 97 262 164 73 146 32 64 128 256), losses := [] }

theorem u40556 : Upper (D 7) (R 7) [96,260,160,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40556 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40557 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 8, targets := 162 },{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6),(3,1),(3,5),(3,7)], upper := (rows 97 262 164 73 152 51 83 147 275), lower := (rows 97 262 164 73 152 32 64 128 256), losses := [] }

theorem u40557 : Upper (D 7) (R 7) [96,260,160,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40557 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40558 : Route 9 := (fun mask => (mask,id))

def c40558 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40558 : Upper (D 7) (R 7) [96,260,160,66,129] 13 := by
  apply FastRouting.sound _ _ [96,260,160,66,129] 13 (by decide) (choices 1) [1,2,8,16] r40558 c40558
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29361
  · exact u29362
  · exact u29363
  · exact u29364

def r40559 : Route 9 := (fun mask => (mask,id))

def c40559 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40559 : Upper (D 7) (R 7) [96,260,160,66,130] 13 := by
  apply FastRouting.sound _ _ [96,260,160,66,130] 13 (by decide) (choices 1) [1,8,16] r40559 c40559
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29365
  · exact u29366
  · exact u29367

#print axioms u40559
end Delivery.IrregularNine14.P07

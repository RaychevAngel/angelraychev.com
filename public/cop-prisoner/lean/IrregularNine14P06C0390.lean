import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0120

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b23400 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 134 262 76 112 40 81 145 273), lower := (rows 35 134 262 76 112 40 64 128 256), losses := [] }

theorem u23400 : Upper (D 6) (R 6) [34,132,258,68,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23400 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23401 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 134 262 76 112 48 73 137 265), lower := (rows 35 134 262 76 112 48 64 128 256), losses := [] }

theorem u23401 : Upper (D 6) (R 6) [34,132,258,68,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23401 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23402 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 268 13 81 34 112 240 368), lower := (rows 35 134 268 13 81 34 64 128 256), losses := [] }

theorem u23402 : Upper (D 6) (R 6) [34,132,264,5,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23402 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23403 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 113, targets := 4 }], pairs := [(0,2),(4,2)], upper := (rows 35 134 268 13 81 48 98 226 354), lower := (rows 35 134 268 13 81 48 64 128 256), losses := [] }

theorem u23403 : Upper (D 6) (R 6) [34,132,264,5,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23403 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23404 : Route 9 := (fun mask => (mask,id))

def c23404 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23404 : Upper (D 6) (R 6) [34,132,264,5,65,64] 13 := by
  apply FastRouting.sound _ _ [34,132,264,5,65,64] 13 (by decide) (choices 1) [2,16,32] r23404 c23404
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7202
  · exact u7203
  · exact u7204

def b23405 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 113, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 134 268 13 82 33 112 240 368), lower := (rows 35 134 268 13 82 33 64 128 256), losses := [] }

theorem u23405 : Upper (D 6) (R 6) [34,132,264,5,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23405 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23406 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 134 268 13 82 48 97 225 353), lower := (rows 35 134 268 13 82 48 64 128 256), losses := [] }

theorem u23406 : Upper (D 6) (R 6) [34,132,264,5,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23406 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23407 : Route 9 := (fun mask => (mask,id))

def c23407 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23407 : Upper (D 6) (R 6) [34,132,264,5,66,64] 13 := by
  apply FastRouting.sound _ _ [34,132,264,5,66,64] 13 (by decide) (choices 1) [1,16,32] r23407 c23407
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7205
  · exact u7206
  · exact u7207

def b23408 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 113, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 134 268 13 112 33 82 210 338), lower := (rows 35 134 268 13 112 33 64 128 256), losses := [] }

theorem u23408 : Upper (D 6) (R 6) [34,132,264,5,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23408 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23409 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 268 13 112 34 81 209 337), lower := (rows 35 134 268 13 112 34 64 128 256), losses := [] }

theorem u23409 : Upper (D 6) (R 6) [34,132,264,5,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23409 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23410 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 134 268 13 112 48 67 195 323), lower := (rows 35 134 268 13 112 48 64 128 256), losses := [] }

theorem u23410 : Upper (D 6) (R 6) [34,132,264,5,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23410 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23411 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 134 268 13 112 96 83 147 275), lower := (rows 35 134 268 13 112 96 64 128 256), losses := [] }

theorem u23411 : Upper (D 6) (R 6) [34,132,264,5,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23411 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23412 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 134 268 25 82 33 100 228 356), lower := (rows 35 134 268 25 82 33 64 128 256), losses := [] }

theorem u23412 : Upper (D 6) (R 6) [34,132,264,17,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23412 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23413 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 88, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 35 134 268 25 82 36 97 225 353), lower := (rows 35 134 268 25 82 36 64 128 256), losses := [] }

theorem u23413 : Upper (D 6) (R 6) [34,132,264,17,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23413 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23414 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 41, targets := 4 },{ cop := 3, region := 356, targets := 2 }], pairs := [(0,2),(2,1),(3,2)], upper := (rows 35 134 268 25 82 96 101 165 293), lower := (rows 35 134 268 25 82 96 64 128 256), losses := [] }

theorem u23414 : Upper (D 6) (R 6) [34,132,264,17,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23414 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23415 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 33, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(1,0)], upper := (rows 35 134 268 25 84 33 98 226 354), lower := (rows 35 134 268 25 84 33 64 128 256), losses := [{ target := 0, region := (rows 0 10 12 8 24 32 65 129 257), good := (rows 482 134 286 478 84 480 64 128 256) }] }

theorem u23415 : Upper (D 6) (R 6) [34,132,264,17,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23415 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23416 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 268 25 84 34 97 225 353), lower := (rows 35 134 268 25 84 34 64 128 256), losses := [] }

theorem u23416 : Upper (D 6) (R 6) [34,132,264,17,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23416 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23417 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(1,6),(2,6)], upper := (rows 35 134 268 25 84 96 99 163 291), lower := (rows 35 134 268 25 84 96 64 128 256), losses := [{ target := 6, region := (rows 1 10 12 8 16 32 0 129 257), good := (rows 419 134 270 415 20 32 0 128 256) }] }

theorem u23417 : Upper (D 6) (R 6) [34,132,264,17,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23417 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23418 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 134 268 25 112 33 70 198 326), lower := (rows 35 134 268 25 112 33 64 128 256), losses := [] }

theorem u23418 : Upper (D 6) (R 6) [34,132,264,17,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23418 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23419 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 268 25 112 34 69 197 325), lower := (rows 35 134 268 25 112 34 64 128 256), losses := [] }

theorem u23419 : Upper (D 6) (R 6) [34,132,264,17,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23419 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23420 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 88, targets := 4 },{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5),(3,2),(4,2)], upper := (rows 35 134 268 25 112 36 67 195 323), lower := (rows 35 134 268 25 112 36 64 128 256), losses := [] }

theorem u23420 : Upper (D 6) (R 6) [34,132,264,17,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23420 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23421 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 134 268 25 112 96 71 135 263), lower := (rows 35 134 268 25 112 96 64 128 256), losses := [] }

theorem u23421 : Upper (D 6) (R 6) [34,132,264,17,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23421 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23422 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 35 134 268 26 21 33 96 224 352), lower := (rows 35 134 268 26 21 33 64 128 256), losses := [] }

theorem u23422 : Upper (D 6) (R 6) [34,132,264,18,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23422 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23423 : Route 9 := (fun mask => (mask,id))

def c23423 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23423 : Upper (D 6) (R 6) [34,132,264,18,5,64] 13 := by
  apply FastRouting.sound _ _ [34,132,264,18,5,64] 13 (by decide) (choices 1) [1,32] r23423 c23423
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7208
  · exact u7209

def b23424 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 35 134 268 26 52 33 65 193 321), lower := (rows 35 134 268 26 52 33 64 128 256), losses := [] }

theorem u23424 : Upper (D 6) (R 6) [34,132,264,18,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23424 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23425 : Route 9 := (fun mask => (mask,id))

def c23425 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23425 : Upper (D 6) (R 6) [34,132,264,18,36,64] 13 := by
  apply FastRouting.sound _ _ [34,132,264,18,36,64] 13 (by decide) (choices 1) [1] r23425 c23425
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u7210

def b23426 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(2,1)], upper := (rows 35 134 268 26 81 33 100 228 356), lower := (rows 35 134 268 26 81 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 16 49 72 136 264), good := (rows 33 132 460 508 113 33 64 128 256) }] }

theorem u23426 : Upper (D 6) (R 6) [34,132,264,18,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23426 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23427 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 88, targets := 4 },{ cop := 0, region := 80, targets := 2 }], pairs := [(3,2),(4,1),(4,2)], upper := (rows 35 134 268 26 81 36 97 225 353), lower := (rows 35 134 268 26 81 36 64 128 256), losses := [] }

theorem u23427 : Upper (D 6) (R 6) [34,132,264,18,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23427 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23428 : Route 9 := (fun mask => (mask,id))

def c23428 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23428 : Upper (D 6) (R 6) [34,132,264,18,65,64] 13 := by
  apply FastRouting.sound _ _ [34,132,264,18,65,64] 13 (by decide) (choices 1) [1,4,32] r23428 c23428
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7211
  · exact u7212
  · exact u7213

def r23429 : Route 9 := (fun mask => (mask,id))

def c23429 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23429 : Upper (D 6) (R 6) [34,132,264,18,68,1] 13 := by
  apply FastRouting.sound _ _ [34,132,264,18,68,1] 13 (by decide) (choices 1) [1,32] r23429 c23429
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7214
  · exact u7215

def r23430 : Route 9 := (fun mask => (mask,id))

def c23430 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23430 : Upper (D 6) (R 6) [34,132,264,18,68,64] 13 := by
  apply FastRouting.sound _ _ [34,132,264,18,68,64] 13 (by decide) (choices 1) [1,32] r23430 c23430
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7216
  · exact u7217

def r23431 : Route 9 := (fun mask => (mask,id))

def c23431 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23431 : Upper (D 6) (R 6) [34,132,264,18,96,1] 13 := by
  apply FastRouting.sound _ _ [34,132,264,18,96,1] 13 (by decide) (choices 1) [1,4] r23431 c23431
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7218
  · exact u7219

def b23432 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 88, targets := 4 },{ cop := 0, region := 80, targets := 2 }], pairs := [(3,2),(4,1),(4,2)], upper := (rows 35 134 268 26 112 36 65 193 321), lower := (rows 35 134 268 26 112 36 64 128 256), losses := [] }

theorem u23432 : Upper (D 6) (R 6) [34,132,264,18,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23432 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23433 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 134 268 26 112 96 69 133 261), lower := (rows 35 134 268 26 112 96 64 128 256), losses := [] }

theorem u23433 : Upper (D 6) (R 6) [34,132,264,18,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23433 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23434 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 113, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 134 268 28 81 33 98 226 354), lower := (rows 35 134 268 28 81 33 64 128 256), losses := [] }

theorem u23434 : Upper (D 6) (R 6) [34,132,264,20,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23434 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23435 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 268 28 81 34 97 225 353), lower := (rows 35 134 268 28 81 34 64 128 256), losses := [] }

theorem u23435 : Upper (D 6) (R 6) [34,132,264,20,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23435 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23436 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 113, targets := 4 }], pairs := [(0,2),(1,6),(4,2)], upper := (rows 35 134 268 28 81 96 99 163 291), lower := (rows 35 134 268 28 81 96 64 128 256), losses := [{ target := 6, region := (rows 1 18 20 24 16 32 0 129 257), good := (rows 419 134 268 30 415 32 0 128 256) }] }

theorem u23436 : Upper (D 6) (R 6) [34,132,264,20,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23436 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23437 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 113, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 134 268 28 82 33 97 225 353), lower := (rows 35 134 268 28 82 33 64 128 256), losses := [] }

theorem u23437 : Upper (D 6) (R 6) [34,132,264,20,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23437 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23438 : Route 9 := (fun mask => (mask,id))

def c23438 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23438 : Upper (D 6) (R 6) [34,132,264,20,66,64] 13 := by
  apply FastRouting.sound _ _ [34,132,264,20,66,64] 13 (by decide) (choices 1) [1,32] r23438 c23438
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7220
  · exact u7221

def b23439 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 113, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 134 268 28 112 33 67 195 323), lower := (rows 35 134 268 28 112 33 64 128 256), losses := [] }

theorem u23439 : Upper (D 6) (R 6) [34,132,264,20,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23439 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23440 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 268 28 112 34 65 193 321), lower := (rows 35 134 268 28 112 34 64 128 256), losses := [] }

theorem u23440 : Upper (D 6) (R 6) [34,132,264,20,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23440 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23441 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 134 268 28 112 96 67 131 259), lower := (rows 35 134 268 28 112 96 64 128 256), losses := [] }

theorem u23441 : Upper (D 6) (R 6) [34,132,264,20,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23441 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23442 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 134 268 56 81 33 70 198 326), lower := (rows 35 134 268 56 81 33 64 128 256), losses := [] }

theorem u23442 : Upper (D 6) (R 6) [34,132,264,48,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23442 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23443 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 268 56 81 34 69 197 325), lower := (rows 35 134 268 56 81 34 64 128 256), losses := [] }

theorem u23443 : Upper (D 6) (R 6) [34,132,264,48,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23443 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23444 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 88, targets := 4 },{ cop := 0, region := 80, targets := 32 }], pairs := [(3,2),(4,2),(4,5)], upper := (rows 35 134 268 56 81 36 67 195 323), lower := (rows 35 134 268 56 81 36 64 128 256), losses := [] }

theorem u23444 : Upper (D 6) (R 6) [34,132,264,48,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23444 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23445 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 134 268 56 81 96 71 135 263), lower := (rows 35 134 268 56 81 96 64 128 256), losses := [] }

theorem u23445 : Upper (D 6) (R 6) [34,132,264,48,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23445 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23446 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 134 268 56 82 33 69 197 325), lower := (rows 35 134 268 56 82 33 64 128 256), losses := [] }

theorem u23446 : Upper (D 6) (R 6) [34,132,264,48,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23446 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23447 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 88, targets := 4 },{ cop := 0, region := 80, targets := 32 }], pairs := [(3,2),(4,2),(4,5)], upper := (rows 35 134 268 56 82 36 65 193 321), lower := (rows 35 134 268 56 82 36 64 128 256), losses := [] }

theorem u23447 : Upper (D 6) (R 6) [34,132,264,48,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23447 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23448 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 134 268 56 82 96 69 133 261), lower := (rows 35 134 268 56 82 96 64 128 256), losses := [] }

theorem u23448 : Upper (D 6) (R 6) [34,132,264,48,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23448 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23449 : Route 9 := (fun mask => (mask,id))

def c23449 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23449 : Upper (D 6) (R 6) [34,132,264,48,68,1] 13 := by
  apply FastRouting.sound _ _ [34,132,264,48,68,1] 13 (by decide) (choices 1) [1,2] r23449 c23449
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7222
  · exact u7223

def b23450 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 268 56 84 34 65 193 321), lower := (rows 35 134 268 56 84 34 64 128 256), losses := [] }

theorem u23450 : Upper (D 6) (R 6) [34,132,264,48,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23450 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23451 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 134 268 56 84 96 67 131 259), lower := (rows 35 134 268 56 84 96 64 128 256), losses := [] }

theorem u23451 : Upper (D 6) (R 6) [34,132,264,48,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23451 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23452 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 268 73 21 34 112 240 368), lower := (rows 35 134 268 73 21 34 64 128 256), losses := [] }

theorem u23452 : Upper (D 6) (R 6) [34,132,264,65,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23452 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23453 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 49, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 134 268 73 21 48 98 226 354), lower := (rows 35 134 268 73 21 48 64 128 256), losses := [] }

theorem u23453 : Upper (D 6) (R 6) [34,132,264,65,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23453 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23454 : Route 9 := (fun mask => (mask,id))

def c23454 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23454 : Upper (D 6) (R 6) [34,132,264,65,5,64] 13 := by
  apply FastRouting.sound _ _ [34,132,264,65,5,64] 13 (by decide) (choices 1) [2,16,32] r23454 c23454
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7224
  · exact u7225
  · exact u7226

def b23455 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 49, targets := 64 },{ cop := 4, region := 194, targets := 1 }], pairs := [(0,6),(1,0),(4,6)], upper := (rows 35 134 268 73 52 33 82 210 338), lower := (rows 35 134 268 73 52 33 64 128 256), losses := [] }

theorem u23455 : Upper (D 6) (R 6) [34,132,264,65,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23455 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23456 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 268 73 52 34 81 209 337), lower := (rows 35 134 268 73 52 34 64 128 256), losses := [] }

theorem u23456 : Upper (D 6) (R 6) [34,132,264,65,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23456 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23457 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 134 268 73 52 48 67 195 323), lower := (rows 35 134 268 73 52 48 64 128 256), losses := [] }

theorem u23457 : Upper (D 6) (R 6) [34,132,264,65,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23457 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23458 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 131, targets := 64 }], pairs := [(0,6),(1,6),(4,0)], upper := (rows 35 134 268 73 52 96 83 147 275), lower := (rows 35 134 268 73 52 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 104 64 128 256), good := (rows 34 150 316 104 52 96 96 128 256) }] }

theorem u23458 : Upper (D 6) (R 6) [34,132,264,65,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23458 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23459 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 4, region := 41, targets := 4 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 134 268 73 82 33 116 180 308), lower := (rows 35 134 268 73 82 33 64 128 256), losses := [] }

theorem u23459 : Upper (D 6) (R 6) [34,132,264,65,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23459 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u23459
end Delivery.IrregularNine14.P06

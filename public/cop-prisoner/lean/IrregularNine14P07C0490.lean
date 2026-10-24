import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0187
import IrregularNine14P07C0188

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b29400 : PairBound 9 := { available := 196, camps := [{ cop := 2, region := 216, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 290 7 26 152 33 196 196 452), lower := (rows 97 290 7 26 152 33 64 128 256), losses := [] }

theorem u29400 : Upper (D 7) (R 7) [96,288,3,18,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29400 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29401 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 216, targets := 32 },{ cop := 1, region := 193, targets := 2 }], pairs := [(0,1),(3,5),(4,5)], upper := (rows 97 290 7 26 152 36 193 193 449), lower := (rows 97 290 7 26 152 36 64 128 256), losses := [] }

theorem u29401 : Upper (D 7) (R 7) [96,288,3,18,136,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29401 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29402 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 290 7 26 152 96 197 133 389), lower := (rows 97 290 7 26 152 96 64 128 256), losses := [] }

theorem u29402 : Upper (D 7) (R 7) [96,288,3,18,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29402 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29403 : PairBound 9 := { available := 69, camps := [{ cop := 5, region := 327, targets := 128 },{ cop := 2, region := 216, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(3,5)], upper := (rows 97 290 7 26 152 160 69 197 325), lower := (rows 97 290 7 26 152 160 64 128 256), losses := [] }

theorem u29403 : Upper (D 7) (R 7) [96,288,3,18,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29403 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29404 : PairBound 9 := { available := 140, camps := [{ cop := 2, region := 216, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 290 7 26 208 33 204 140 396), lower := (rows 97 290 7 26 208 33 64 128 256), losses := [] }

theorem u29404 : Upper (D 7) (R 7) [96,288,3,18,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29404 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29405 : Route 9 := (fun mask => (mask,id))

def c29405 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u29405 : Upper (D 7) (R 7) [96,288,3,18,192,4] 13 := by
  apply FastRouting.sound _ _ [96,288,3,18,192,4] 13 (by decide) (choices 1) [1,8,128] r29405 c29405
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11239
  · exact u11240
  · exact u11241

def b29406 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 390, targets := 64 },{ cop := 2, region := 216, targets := 32 }], pairs := [(1,6),(2,6),(3,5)], upper := (rows 97 290 7 26 208 40 197 133 389), lower := (rows 97 290 7 26 208 40 64 128 256), losses := [] }

theorem u29406 : Upper (D 7) (R 7) [96,288,3,18,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29406 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29407 : Route 9 := (fun mask => (mask,id))

def c29407 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29407 : Upper (D 7) (R 7) [96,288,3,18,192,128] 13 := by
  apply FastRouting.sound _ _ [96,288,3,18,192,128] 13 (by decide) (choices 1) [1,4,8] r29407 c29407
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11242
  · exact u11243
  · exact u11244

def b29408 : PairBound 9 := { available := 136, camps := [{ cop := 2, region := 216, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 290 7 28 82 33 200 136 392), lower := (rows 97 290 7 28 82 33 64 128 256), losses := [] }

theorem u29408 : Upper (D 7) (R 7) [96,288,3,20,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29408 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29409 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 45, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 97 290 7 28 82 40 193 129 385), lower := (rows 97 290 7 28 82 40 64 128 256), losses := [] }

theorem u29409 : Upper (D 7) (R 7) [96,288,3,20,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29409 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29410 : Route 9 := (fun mask => (mask,id))

def c29410 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u29410 : Upper (D 7) (R 7) [96,288,3,20,66,128] 13 := by
  apply FastRouting.sound _ _ [96,288,3,20,66,128] 13 (by decide) (choices 1) [1,8,128] r29410 c29410
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11245
  · exact u11246
  · exact u11247

def b29411 : PairBound 9 := { available := 200, camps := [{ cop := 2, region := 216, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 97 290 7 28 145 34 200 200 456), lower := (rows 97 290 7 28 145 34 64 128 256), losses := [] }

theorem u29411 : Upper (D 7) (R 7) [96,288,3,20,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29411 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29412 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 216, targets := 32 },{ cop := 0, region := 386, targets := 1 }], pairs := [(1,0),(3,5),(4,5)], upper := (rows 97 290 7 28 145 40 194 194 450), lower := (rows 97 290 7 28 145 40 64 128 256), losses := [] }

theorem u29412 : Upper (D 7) (R 7) [96,288,3,20,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29412 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29413 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 290 7 28 145 96 202 138 394), lower := (rows 97 290 7 28 145 96 64 128 256), losses := [] }

theorem u29413 : Upper (D 7) (R 7) [96,288,3,20,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29413 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29414 : Route 9 := (fun mask => (mask,id))

def c29414 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29414 : Upper (D 7) (R 7) [96,288,3,20,129,128] 13 := by
  apply FastRouting.sound _ _ [96,288,3,20,129,128] 13 (by decide) (choices 1) [2,8] r29414 c29414
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11248
  · exact u11249

def b29415 : PairBound 9 := { available := 200, camps := [{ cop := 2, region := 216, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 290 7 28 146 33 200 200 456), lower := (rows 97 290 7 28 146 33 64 128 256), losses := [] }

theorem u29415 : Upper (D 7) (R 7) [96,288,3,20,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29415 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29416 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 216, targets := 32 },{ cop := 1, region := 193, targets := 2 }], pairs := [(0,1),(3,5),(4,5)], upper := (rows 97 290 7 28 146 40 193 193 449), lower := (rows 97 290 7 28 146 40 64 128 256), losses := [] }

theorem u29416 : Upper (D 7) (R 7) [96,288,3,20,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29416 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29417 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 290 7 28 146 96 201 137 393), lower := (rows 97 290 7 28 146 96 64 128 256), losses := [] }

theorem u29417 : Upper (D 7) (R 7) [96,288,3,20,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29417 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29418 : Route 9 := (fun mask => (mask,id))

def c29418 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29418 : Upper (D 7) (R 7) [96,288,3,20,130,128] 13 := by
  apply FastRouting.sound _ _ [96,288,3,20,130,128] 13 (by decide) (choices 1) [1,8] r29418 c29418
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11250
  · exact u11251

def b29419 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 216, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 290 7 28 152 33 194 194 450), lower := (rows 97 290 7 28 152 33 64 128 256), losses := [] }

theorem u29419 : Upper (D 7) (R 7) [96,288,3,20,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29419 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29420 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 216, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 97 290 7 28 152 34 193 193 449), lower := (rows 97 290 7 28 152 34 64 128 256), losses := [] }

theorem u29420 : Upper (D 7) (R 7) [96,288,3,20,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29420 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29421 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 290 7 28 152 96 195 131 387), lower := (rows 97 290 7 28 152 96 64 128 256), losses := [] }

theorem u29421 : Upper (D 7) (R 7) [96,288,3,20,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29421 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29422 : PairBound 9 := { available := 67, camps := [{ cop := 5, region := 327, targets := 128 },{ cop := 2, region := 216, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(3,5)], upper := (rows 97 290 7 28 152 160 67 195 323), lower := (rows 97 290 7 28 152 160 64 128 256), losses := [] }

theorem u29422 : Upper (D 7) (R 7) [96,288,3,20,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29422 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29423 : PairBound 9 := { available := 138, camps := [{ cop := 2, region := 216, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 290 7 28 208 33 202 138 394), lower := (rows 97 290 7 28 208 33 64 128 256), losses := [] }

theorem u29423 : Upper (D 7) (R 7) [96,288,3,20,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29423 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29424 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 216, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 97 290 7 28 208 34 201 137 393), lower := (rows 97 290 7 28 208 34 64 128 256), losses := [] }

theorem u29424 : Upper (D 7) (R 7) [96,288,3,20,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29424 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29425 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 390, targets := 64 },{ cop := 2, region := 216, targets := 32 }], pairs := [(1,6),(2,6),(3,5)], upper := (rows 97 290 7 28 208 40 195 131 387), lower := (rows 97 290 7 28 208 40 64 128 256), losses := [] }

theorem u29425 : Upper (D 7) (R 7) [96,288,3,20,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29425 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29426 : Route 9 := (fun mask => (mask,id))

def c29426 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29426 : Upper (D 7) (R 7) [96,288,3,20,192,128] 13 := by
  apply FastRouting.sound _ _ [96,288,3,20,192,128] 13 (by decide) (choices 1) [1,2,8] r29426 c29426
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11252
  · exact u11253
  · exact u11254

def b29427 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 216, targets := 32 },{ cop := 3, region := 37, targets := 128 }], pairs := [(0,7),(3,5),(4,5)], upper := (rows 97 290 7 74 145 36 216 152 408), lower := (rows 97 290 7 74 145 36 64 128 256), losses := [] }

theorem u29427 : Upper (D 7) (R 7) [96,288,3,66,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29427 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29428 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 290 7 74 145 40 212 148 404), lower := (rows 97 290 7 74 145 40 64 128 256), losses := [] }

theorem u29428 : Upper (D 7) (R 7) [96,288,3,66,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29428 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29429 : PairBound 9 := { available := 140, camps := [{ cop := 2, region := 216, targets := 32 },{ cop := 2, region := 200, targets := 1 }], pairs := [(3,0),(3,5),(4,5)], upper := (rows 97 290 7 74 145 48 204 140 396), lower := (rows 97 290 7 74 145 48 64 128 256), losses := [] }

theorem u29429 : Upper (D 7) (R 7) [96,288,3,66,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29429 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29430 : Route 9 := (fun mask => (mask,id))

def c29430 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29430 : Upper (D 7) (R 7) [96,288,3,66,129,128] 13 := by
  apply FastRouting.sound _ _ [96,288,3,66,129,128] 13 (by decide) (choices 1) [4,8,16] r29430 c29430
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11255
  · exact u11256
  · exact u11257

def b29431 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 216, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 290 7 74 148 33 216 152 408), lower := (rows 97 290 7 74 148 33 64 128 256), losses := [] }

theorem u29431 : Upper (D 7) (R 7) [96,288,3,66,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29431 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29432 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 290 7 74 148 40 209 145 401), lower := (rows 97 290 7 74 148 40 64 128 256), losses := [] }

theorem u29432 : Upper (D 7) (R 7) [96,288,3,66,132,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29432 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29433 : Route 9 := (fun mask => (mask,id))

def c29433 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u29433 : Upper (D 7) (R 7) [96,288,3,66,132,16] 13 := by
  apply FastRouting.sound _ _ [96,288,3,66,132,16] 13 (by decide) (choices 1) [1,8,128] r29433 c29433
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11258
  · exact u11259
  · exact u11260

def r29434 : Route 9 := (fun mask => (mask,id))

def c29434 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29434 : Upper (D 7) (R 7) [96,288,3,66,132,128] 13 := by
  apply FastRouting.sound _ _ [96,288,3,66,132,128] 13 (by decide) (choices 1) [1,8,16] r29434 c29434
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11261
  · exact u11262
  · exact u11263

def b29435 : PairBound 9 := { available := 148, camps := [{ cop := 2, region := 216, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 290 7 74 152 33 212 148 404), lower := (rows 97 290 7 74 152 33 64 128 256), losses := [] }

theorem u29435 : Upper (D 7) (R 7) [96,288,3,66,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29435 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29436 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 216, targets := 32 },{ cop := 3, region := 37, targets := 128 }], pairs := [(0,7),(3,5),(4,5)], upper := (rows 97 290 7 74 152 36 209 145 401), lower := (rows 97 290 7 74 152 36 64 128 256), losses := [] }

theorem u29436 : Upper (D 7) (R 7) [96,288,3,66,136,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29436 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29437 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 390, targets := 64 },{ cop := 2, region := 200, targets := 32 }], pairs := [(1,6),(2,6),(3,5)], upper := (rows 97 290 7 74 152 48 197 133 389), lower := (rows 97 290 7 74 152 48 64 128 256), losses := [] }

theorem u29437 : Upper (D 7) (R 7) [96,288,3,66,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29437 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29438 : Route 9 := (fun mask => (mask,id))

def c29438 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29438 : Upper (D 7) (R 7) [96,288,3,66,136,128] 13 := by
  apply FastRouting.sound _ _ [96,288,3,66,136,128] 13 (by decide) (choices 1) [1,4,16] r29438 c29438
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11264
  · exact u11265
  · exact u11266

def b29439 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 216, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 97 290 7 76 145 34 216 152 408), lower := (rows 97 290 7 76 145 34 64 128 256), losses := [] }

theorem u29439 : Upper (D 7) (R 7) [96,288,3,68,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29439 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29440 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 290 7 76 145 40 210 146 402), lower := (rows 97 290 7 76 145 40 64 128 256), losses := [] }

theorem u29440 : Upper (D 7) (R 7) [96,288,3,68,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29440 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29441 : PairBound 9 := { available := 138, camps := [{ cop := 2, region := 216, targets := 32 },{ cop := 2, region := 200, targets := 1 }], pairs := [(3,0),(3,5),(4,5)], upper := (rows 97 290 7 76 145 48 202 138 394), lower := (rows 97 290 7 76 145 48 64 128 256), losses := [] }

theorem u29441 : Upper (D 7) (R 7) [96,288,3,68,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29441 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29442 : Route 9 := (fun mask => (mask,id))

def c29442 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29442 : Upper (D 7) (R 7) [96,288,3,68,129,128] 13 := by
  apply FastRouting.sound _ _ [96,288,3,68,129,128] 13 (by decide) (choices 1) [2,8,16] r29442 c29442
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11267
  · exact u11268
  · exact u11269

def b29443 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 216, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 290 7 76 146 33 216 152 408), lower := (rows 97 290 7 76 146 33 64 128 256), losses := [] }

theorem u29443 : Upper (D 7) (R 7) [96,288,3,68,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29443 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29444 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 290 7 76 146 40 209 145 401), lower := (rows 97 290 7 76 146 40 64 128 256), losses := [] }

theorem u29444 : Upper (D 7) (R 7) [96,288,3,68,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29444 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29445 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 216, targets := 32 },{ cop := 2, region := 200, targets := 2 }], pairs := [(3,1),(3,5),(4,5)], upper := (rows 97 290 7 76 146 48 201 137 393), lower := (rows 97 290 7 76 146 48 64 128 256), losses := [] }

theorem u29445 : Upper (D 7) (R 7) [96,288,3,68,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29445 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29446 : Route 9 := (fun mask => (mask,id))

def c29446 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29446 : Upper (D 7) (R 7) [96,288,3,68,130,128] 13 := by
  apply FastRouting.sound _ _ [96,288,3,68,130,128] 13 (by decide) (choices 1) [1,8,16] r29446 c29446
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11270
  · exact u11271
  · exact u11272

def b29447 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 216, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 290 7 76 152 33 210 146 402), lower := (rows 97 290 7 76 152 33 64 128 256), losses := [] }

theorem u29447 : Upper (D 7) (R 7) [96,288,3,68,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29447 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29448 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 216, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 97 290 7 76 152 34 209 145 401), lower := (rows 97 290 7 76 152 34 64 128 256), losses := [] }

theorem u29448 : Upper (D 7) (R 7) [96,288,3,68,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29448 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29449 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 390, targets := 64 },{ cop := 2, region := 200, targets := 32 }], pairs := [(1,6),(2,6),(3,5)], upper := (rows 97 290 7 76 152 48 195 131 387), lower := (rows 97 290 7 76 152 48 64 128 256), losses := [] }

theorem u29449 : Upper (D 7) (R 7) [96,288,3,68,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29449 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29450 : Route 9 := (fun mask => (mask,id))

def c29450 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29450 : Upper (D 7) (R 7) [96,288,3,68,136,128] 13 := by
  apply FastRouting.sound _ _ [96,288,3,68,136,128] 13 (by decide) (choices 1) [1,2,16] r29450 c29450
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11273
  · exact u11274
  · exact u11275

def b29451 : PairBound 9 := { available := 140, camps := [{ cop := 2, region := 216, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 97 290 7 88 145 34 204 140 396), lower := (rows 97 290 7 88 145 34 64 128 256), losses := [] }

theorem u29451 : Upper (D 7) (R 7) [96,288,3,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29451 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29452 : Route 9 := (fun mask => (mask,id))

def c29452 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u29452 : Upper (D 7) (R 7) [96,288,3,80,129,4] 13 := by
  apply FastRouting.sound _ _ [96,288,3,80,129,4] 13 (by decide) (choices 1) [2,8,128] r29452 c29452
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11276
  · exact u11277
  · exact u11278

def b29453 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 290 7 88 145 40 198 134 390), lower := (rows 97 290 7 88 145 40 64 128 256), losses := [] }

theorem u29453 : Upper (D 7) (R 7) [96,288,3,80,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29453 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29454 : Route 9 := (fun mask => (mask,id))

def c29454 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29454 : Upper (D 7) (R 7) [96,288,3,80,129,128] 13 := by
  apply FastRouting.sound _ _ [96,288,3,80,129,128] 13 (by decide) (choices 1) [2,4,8] r29454 c29454
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11279
  · exact u11280
  · exact u11281

def b29455 : PairBound 9 := { available := 140, camps := [{ cop := 2, region := 216, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 290 7 88 146 33 204 140 396), lower := (rows 97 290 7 88 146 33 64 128 256), losses := [] }

theorem u29455 : Upper (D 7) (R 7) [96,288,3,80,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29455 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29456 : Route 9 := (fun mask => (mask,id))

def c29456 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u29456 : Upper (D 7) (R 7) [96,288,3,80,130,4] 13 := by
  apply FastRouting.sound _ _ [96,288,3,80,130,4] 13 (by decide) (choices 1) [1,8,128] r29456 c29456
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11282
  · exact u11283
  · exact u11284

def b29457 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 290 7 88 146 40 197 133 389), lower := (rows 97 290 7 88 146 40 64 128 256), losses := [] }

theorem u29457 : Upper (D 7) (R 7) [96,288,3,80,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29457 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29458 : Route 9 := (fun mask => (mask,id))

def c29458 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29458 : Upper (D 7) (R 7) [96,288,3,80,130,128] 13 := by
  apply FastRouting.sound _ _ [96,288,3,80,130,128] 13 (by decide) (choices 1) [1,4,8] r29458 c29458
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11285
  · exact u11286
  · exact u11287

def b29459 : PairBound 9 := { available := 138, camps := [{ cop := 2, region := 216, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 290 7 88 148 33 202 138 394), lower := (rows 97 290 7 88 148 33 64 128 256), losses := [] }

theorem u29459 : Upper (D 7) (R 7) [96,288,3,80,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29459 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u29459
end Delivery.IrregularNine14.P07

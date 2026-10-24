import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0020
import IrregularNine14P07C0021

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r12360 : Route 9 := (fun mask => (mask,id))

def c12360 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12360 : Upper (D 7) (R 7) [6,33,72,257,130,128] 13 := by
  apply FastRouting.sound _ _ [6,33,72,257,130,128] 13 (by decide) (choices 1) [16,32] r12360 c12360
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1229
  · exact u1230

def b12361 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 76 265 176 34 208 208 464), lower := (rows 7 35 76 265 176 34 64 128 256), losses := [] }

theorem u12361 : Upper (D 7) (R 7) [6,33,72,257,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12361 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12362 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 35 76 265 176 48 194 194 450), lower := (rows 7 35 76 265 176 48 64 128 256), losses := [] }

theorem u12362 : Upper (D 7) (R 7) [6,33,72,257,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12362 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12363 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(3,6),(4,6)], upper := (rows 7 35 76 265 176 96 210 146 402), lower := (rows 7 35 76 265 176 96 64 128 256), losses := [] }

theorem u12363 : Upper (D 7) (R 7) [6,33,72,257,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12363 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12364 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 35 76 265 176 160 82 210 338), lower := (rows 7 35 76 265 176 160 64 128 256), losses := [] }

theorem u12364 : Upper (D 7) (R 7) [6,33,72,257,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12364 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12365 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 76 265 208 34 240 176 432), lower := (rows 7 35 76 265 208 34 64 128 256), losses := [] }

theorem u12365 : Upper (D 7) (R 7) [6,33,72,257,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12365 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12366 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 240, targets := 1 },{ cop := 1, region := 392, targets := 64 }], pairs := [(2,0),(3,6),(4,0)], upper := (rows 7 35 76 265 208 48 226 162 418), lower := (rows 7 35 76 265 208 48 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 27 63 67 131 259), good := (rows 502 498 124 508 240 48 64 128 256) }] }

theorem u12366 : Upper (D 7) (R 7) [6,33,72,257,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12366 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12367 : Route 9 := (fun mask => (mask,id))

def c12367 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12367 : Upper (D 7) (R 7) [6,33,72,257,192,128] 13 := by
  apply FastRouting.sound _ _ [6,33,72,257,192,128] 13 (by decide) (choices 1) [2,16,32] r12367 c12367
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1231
  · exact u1232
  · exact u1233

def b12368 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 7 35 76 266 112 33 208 144 400), lower := (rows 7 35 76 266 112 33 64 128 256), losses := [] }

theorem u12368 : Upper (D 7) (R 7) [6,33,72,258,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12368 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12369 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 35 76 266 112 48 193 129 385), lower := (rows 7 35 76 266 112 48 64 128 256), losses := [] }

theorem u12369 : Upper (D 7) (R 7) [6,33,72,258,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12369 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12370 : Route 9 := (fun mask => (mask,id))

def c12370 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12370 : Upper (D 7) (R 7) [6,33,72,258,96,128] 13 := by
  apply FastRouting.sound _ _ [6,33,72,258,96,128] 13 (by decide) (choices 1) [1,16,128] r12370 c12370
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1234
  · exact u1235
  · exact u1236

def b12371 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 460, targets := 1 },{ cop := 4, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0)], upper := (rows 7 35 76 266 145 48 224 224 480), lower := (rows 7 35 76 266 145 48 64 128 256), losses := [] }

theorem u12371 : Upper (D 7) (R 7) [6,33,72,258,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12371 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12372 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(3,6),(4,6)], upper := (rows 7 35 76 266 145 96 240 176 432), lower := (rows 7 35 76 266 145 96 64 128 256), losses := [] }

theorem u12372 : Upper (D 7) (R 7) [6,33,72,258,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12372 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12373 : Route 9 := (fun mask => (mask,id))

def c12373 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12373 : Upper (D 7) (R 7) [6,33,72,258,129,128] 13 := by
  apply FastRouting.sound _ _ [6,33,72,258,129,128] 13 (by decide) (choices 1) [16,32] r12373 c12373
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1237
  · exact u1238

def b12374 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 76 266 176 33 208 208 464), lower := (rows 7 35 76 266 176 33 64 128 256), losses := [] }

theorem u12374 : Upper (D 7) (R 7) [6,33,72,258,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12374 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12375 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 35 76 266 176 48 193 193 449), lower := (rows 7 35 76 266 176 48 64 128 256), losses := [] }

theorem u12375 : Upper (D 7) (R 7) [6,33,72,258,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12375 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12376 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(3,6),(4,6)], upper := (rows 7 35 76 266 176 96 209 145 401), lower := (rows 7 35 76 266 176 96 64 128 256), losses := [] }

theorem u12376 : Upper (D 7) (R 7) [6,33,72,258,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12376 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12377 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 35 76 266 176 160 81 209 337), lower := (rows 7 35 76 266 176 160 64 128 256), losses := [] }

theorem u12377 : Upper (D 7) (R 7) [6,33,72,258,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12377 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12378 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 76 266 208 33 240 176 432), lower := (rows 7 35 76 266 208 33 64 128 256), losses := [] }

theorem u12378 : Upper (D 7) (R 7) [6,33,72,258,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12378 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12379 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 240, targets := 2 },{ cop := 1, region := 392, targets := 64 }], pairs := [(2,1),(3,6),(4,1)], upper := (rows 7 35 76 266 208 48 225 161 417), lower := (rows 7 35 76 266 208 48 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 27 63 67 131 259), good := (rows 501 497 124 508 240 48 64 128 256) }] }

theorem u12379 : Upper (D 7) (R 7) [6,33,72,258,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12379 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12380 : Route 9 := (fun mask => (mask,id))

def c12380 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12380 : Upper (D 7) (R 7) [6,33,72,258,192,128] 13 := by
  apply FastRouting.sound _ _ [6,33,72,258,192,128] 13 (by decide) (choices 1) [1,16,32] r12380 c12380
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1239
  · exact u1240
  · exact u1241

def b12381 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 7 35 76 280 112 33 194 130 386), lower := (rows 7 35 76 280 112 33 64 128 256), losses := [] }

theorem u12381 : Upper (D 7) (R 7) [6,33,72,272,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12381 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12382 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 476, targets := 2 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 7 35 76 280 112 34 193 129 385), lower := (rows 7 35 76 280 112 34 64 128 256), losses := [] }

theorem u12382 : Upper (D 7) (R 7) [6,33,72,272,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12382 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12383 : Route 9 := (fun mask => (mask,id))

def c12383 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12383 : Upper (D 7) (R 7) [6,33,72,272,96,128] 13 := by
  apply FastRouting.sound _ _ [6,33,72,272,96,128] 13 (by decide) (choices 1) [1,2,128] r12383 c12383
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1242
  · exact u1243
  · exact u1244

def b12384 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 76 280 145 34 224 224 480), lower := (rows 7 35 76 280 145 34 64 128 256), losses := [] }

theorem u12384 : Upper (D 7) (R 7) [6,33,72,272,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12384 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12385 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(3,6),(4,6)], upper := (rows 7 35 76 280 145 96 226 162 418), lower := (rows 7 35 76 280 145 96 64 128 256), losses := [] }

theorem u12385 : Upper (D 7) (R 7) [6,33,72,272,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12385 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12386 : Route 9 := (fun mask => (mask,id))

def c12386 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12386 : Upper (D 7) (R 7) [6,33,72,272,129,128] 13 := by
  apply FastRouting.sound _ _ [6,33,72,272,129,128] 13 (by decide) (choices 1) [2,32] r12386 c12386
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1245
  · exact u1246

def b12387 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 76 280 146 33 224 224 480), lower := (rows 7 35 76 280 146 33 64 128 256), losses := [] }

theorem u12387 : Upper (D 7) (R 7) [6,33,72,272,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12387 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12388 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(3,6),(4,6)], upper := (rows 7 35 76 280 146 96 225 161 417), lower := (rows 7 35 76 280 146 96 64 128 256), losses := [] }

theorem u12388 : Upper (D 7) (R 7) [6,33,72,272,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12388 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12389 : PairBound 9 := { available := 97, camps := [], pairs := [(0,7),(2,1),(2,7),(3,1)], upper := (rows 7 35 76 280 146 160 97 225 353), lower := (rows 7 35 76 280 146 160 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 24 16 179 67 131 259), good := (rows 485 481 76 316 508 160 64 160 256) },{ target := 7, region := (rows 17 2 20 24 16 32 66 0 258), good := (rows 327 355 76 285 351 32 64 0 256) }] }

theorem u12389 : Upper (D 7) (R 7) [6,33,72,272,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12389 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12390 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 76 280 176 33 194 194 450), lower := (rows 7 35 76 280 176 33 64 128 256), losses := [] }

theorem u12390 : Upper (D 7) (R 7) [6,33,72,272,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12390 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12391 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 76 280 176 34 193 193 449), lower := (rows 7 35 76 280 176 34 64 128 256), losses := [] }

theorem u12391 : Upper (D 7) (R 7) [6,33,72,272,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12391 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12392 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(3,6),(4,6)], upper := (rows 7 35 76 280 176 96 195 131 387), lower := (rows 7 35 76 280 176 96 64 128 256), losses := [] }

theorem u12392 : Upper (D 7) (R 7) [6,33,72,272,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12392 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12393 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 35 76 280 176 160 67 195 323), lower := (rows 7 35 76 280 176 160 64 128 256), losses := [] }

theorem u12393 : Upper (D 7) (R 7) [6,33,72,272,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12393 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12394 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(2,0),(3,0),(4,0)], upper := (rows 7 35 76 280 208 33 226 162 418), lower := (rows 7 35 76 280 208 33 64 128 256), losses := [] }

theorem u12394 : Upper (D 7) (R 7) [6,33,72,272,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12394 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12395 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 476, targets := 2 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 7 35 76 280 208 34 225 161 417), lower := (rows 7 35 76 280 208 34 64 128 256), losses := [] }

theorem u12395 : Upper (D 7) (R 7) [6,33,72,272,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12395 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12396 : Route 9 := (fun mask => (mask,id))

def c12396 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12396 : Upper (D 7) (R 7) [6,33,72,272,192,128] 13 := by
  apply FastRouting.sound _ _ [6,33,72,272,192,128] 13 (by decide) (choices 1) [1,2,32] r12396 c12396
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1247
  · exact u1248
  · exact u1249

def b12397 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 476, targets := 2 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 7 35 76 296 81 34 208 144 400), lower := (rows 7 35 76 296 81 34 64 128 256), losses := [] }

theorem u12397 : Upper (D 7) (R 7) [6,33,72,288,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12397 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12398 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 51, targets := 128 }], pairs := [(0,7),(1,7),(4,7)], upper := (rows 7 35 76 296 81 48 194 130 386), lower := (rows 7 35 76 296 81 48 64 128 256), losses := [] }

theorem u12398 : Upper (D 7) (R 7) [6,33,72,288,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12398 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12399 : Route 9 := (fun mask => (mask,id))

def c12399 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12399 : Upper (D 7) (R 7) [6,33,72,288,65,128] 13 := by
  apply FastRouting.sound _ _ [6,33,72,288,65,128] 13 (by decide) (choices 1) [2,16,128] r12399 c12399
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1250
  · exact u1251
  · exact u1252

def b12400 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 7 35 76 296 82 33 208 144 400), lower := (rows 7 35 76 296 82 33 64 128 256), losses := [] }

theorem u12400 : Upper (D 7) (R 7) [6,33,72,288,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12400 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12401 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 51, targets := 128 }], pairs := [(0,7),(1,7),(4,7)], upper := (rows 7 35 76 296 82 48 193 129 385), lower := (rows 7 35 76 296 82 48 64 128 256), losses := [] }

theorem u12401 : Upper (D 7) (R 7) [6,33,72,288,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12401 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12402 : Route 9 := (fun mask => (mask,id))

def c12402 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12402 : Upper (D 7) (R 7) [6,33,72,288,66,128] 13 := by
  apply FastRouting.sound _ _ [6,33,72,288,66,128] 13 (by decide) (choices 1) [1,16,128] r12402 c12402
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1253
  · exact u1254
  · exact u1255

def b12403 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 76 296 145 34 208 208 464), lower := (rows 7 35 76 296 145 34 64 128 256), losses := [] }

theorem u12403 : Upper (D 7) (R 7) [6,33,72,288,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12403 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12404 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 460, targets := 1 },{ cop := 4, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0)], upper := (rows 7 35 76 296 145 48 194 194 450), lower := (rows 7 35 76 296 145 48 64 128 256), losses := [] }

theorem u12404 : Upper (D 7) (R 7) [6,33,72,288,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12404 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12405 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(3,6),(4,6)], upper := (rows 7 35 76 296 145 96 210 146 402), lower := (rows 7 35 76 296 145 96 64 128 256), losses := [] }

theorem u12405 : Upper (D 7) (R 7) [6,33,72,288,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12405 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12406 : Route 9 := (fun mask => (mask,id))

def c12406 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12406 : Upper (D 7) (R 7) [6,33,72,288,129,128] 13 := by
  apply FastRouting.sound _ _ [6,33,72,288,129,128] 13 (by decide) (choices 1) [2,16] r12406 c12406
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1256
  · exact u1257

def b12407 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 76 296 146 33 208 208 464), lower := (rows 7 35 76 296 146 33 64 128 256), losses := [] }

theorem u12407 : Upper (D 7) (R 7) [6,33,72,288,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12407 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12408 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 460, targets := 2 },{ cop := 0, region := 208, targets := 32 }], pairs := [(2,1),(3,1),(4,5)], upper := (rows 7 35 76 296 146 48 193 193 449), lower := (rows 7 35 76 296 146 48 64 128 256), losses := [] }

theorem u12408 : Upper (D 7) (R 7) [6,33,72,288,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12408 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12409 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(3,6),(4,6)], upper := (rows 7 35 76 296 146 96 209 145 401), lower := (rows 7 35 76 296 146 96 64 128 256), losses := [] }

theorem u12409 : Upper (D 7) (R 7) [6,33,72,288,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12409 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12410 : Route 9 := (fun mask => (mask,id))

def c12410 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12410 : Upper (D 7) (R 7) [6,33,72,288,130,128] 13 := by
  apply FastRouting.sound _ _ [6,33,72,288,130,128] 13 (by decide) (choices 1) [1,16] r12410 c12410
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1258
  · exact u1259

def b12411 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 76 296 208 33 210 146 402), lower := (rows 7 35 76 296 208 33 64 128 256), losses := [] }

theorem u12411 : Upper (D 7) (R 7) [6,33,72,288,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12411 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12412 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 76 296 208 34 209 145 401), lower := (rows 7 35 76 296 208 34 64 128 256), losses := [] }

theorem u12412 : Upper (D 7) (R 7) [6,33,72,288,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12412 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12413 : Route 9 := (fun mask => (mask,id))

def c12413 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12413 : Upper (D 7) (R 7) [6,33,72,288,192,16] 13 := by
  apply FastRouting.sound _ _ [6,33,72,288,192,16] 13 (by decide) (choices 1) [1,2,128] r12413 c12413
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1260
  · exact u1261
  · exact u1262

def r12414 : Route 9 := (fun mask => (mask,id))

def c12414 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12414 : Upper (D 7) (R 7) [6,33,72,288,192,128] 13 := by
  apply FastRouting.sound _ _ [6,33,72,288,192,128] 13 (by decide) (choices 1) [1,2,16] r12414 c12414
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1263
  · exact u1264
  · exact u1265

def b12415 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 476, targets := 2 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 7 35 76 392 81 34 240 176 432), lower := (rows 7 35 76 392 81 34 64 128 256), losses := [] }

theorem u12415 : Upper (D 7) (R 7) [6,33,72,384,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12415 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12416 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 51, targets := 128 }], pairs := [(0,7),(1,7),(4,7)], upper := (rows 7 35 76 392 81 48 226 162 418), lower := (rows 7 35 76 392 81 48 64 128 256), losses := [] }

theorem u12416 : Upper (D 7) (R 7) [6,33,72,384,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12416 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12417 : PairBound 9 := { available := 50, camps := [{ cop := 4, region := 426, targets := 64 },{ cop := 1, region := 80, targets := 128 }], pairs := [(0,6),(1,6),(3,6),(4,7)], upper := (rows 7 35 76 392 81 160 114 178 306), lower := (rows 7 35 76 392 81 160 64 128 256), losses := [{ target := 6, region := (rows 5 22 4 24 16 184 0 144 272), good := (rows 7 35 47 424 443 160 0 160 256) }] }

theorem u12417 : Upper (D 7) (R 7) [6,33,72,384,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12417 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12418 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 7 35 76 392 82 33 240 176 432), lower := (rows 7 35 76 392 82 33 64 128 256), losses := [] }

theorem u12418 : Upper (D 7) (R 7) [6,33,72,384,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12418 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12419 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 51, targets := 128 }], pairs := [(0,7),(1,7),(4,7)], upper := (rows 7 35 76 392 82 48 225 161 417), lower := (rows 7 35 76 392 82 48 64 128 256), losses := [] }

theorem u12419 : Upper (D 7) (R 7) [6,33,72,384,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12419 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u12419
end Delivery.IrregularNine14.P07

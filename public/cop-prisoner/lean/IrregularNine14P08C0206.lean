import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0068

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b12360 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 67 386 13 41 52 240 240 240 496), lower := (rows 67 386 13 41 52 32 64 128 256), losses := [] }

theorem u12360 : Upper (D 8) (R 8) [66,384,9,33,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12360 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12361 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 67 386 13 41 84 176 240 176 432), lower := (rows 67 386 13 41 84 32 64 128 256), losses := [] }

theorem u12361 : Upper (D 8) (R 8) [66,384,9,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12361 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12362 : PairBound 9 := { available := 180, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 67 386 13 41 112 180 244 180 436), lower := (rows 67 386 13 41 112 32 64 128 256), losses := [] }

theorem u12362 : Upper (D 8) (R 8) [66,384,9,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12362 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12363 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 67 386 13 41 148 112 112 240 368), lower := (rows 67 386 13 41 148 32 64 128 256), losses := [] }

theorem u12363 : Upper (D 8) (R 8) [66,384,9,33,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12363 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12364 : PairBound 9 := { available := 116, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 67 386 13 41 176 116 116 244 372), lower := (rows 67 386 13 41 176 32 64 128 256), losses := [] }

theorem u12364 : Upper (D 8) (R 8) [66,384,9,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12364 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12365 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 67 386 13 41 208 52 116 180 308), lower := (rows 67 386 13 41 208 32 64 128 256), losses := [] }

theorem u12365 : Upper (D 8) (R 8) [66,384,9,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12365 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12366 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 67 386 13 44 49 240 240 240 496), lower := (rows 67 386 13 44 49 32 64 128 256), losses := [] }

theorem u12366 : Upper (D 8) (R 8) [66,384,9,36,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12366 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12367 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 386 13 44 81 176 240 176 432), lower := (rows 67 386 13 44 81 32 64 128 256), losses := [] }

theorem u12367 : Upper (D 8) (R 8) [66,384,9,36,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12367 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12368 : Route 9 := (fun mask => (mask,id))

def c12368 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u12368 : Upper (D 8) (R 8) [66,384,9,36,96] 13 := by
  apply FastRouting.sound _ _ [66,384,9,36,96] 13 (by decide) (choices 1) [1,16,128] r12368 c12368
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4094
  · exact u4095
  · exact u4096

def b12369 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 108, targets := 128 }], pairs := [(2,7)], upper := (rows 67 386 13 44 145 112 112 240 368), lower := (rows 67 386 13 44 145 32 64 128 256), losses := [] }

theorem u12369 : Upper (D 8) (R 8) [66,384,9,36,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12369 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12370 : Route 9 := (fun mask => (mask,id))

def c12370 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12370 : Upper (D 8) (R 8) [66,384,9,36,160] 13 := by
  apply FastRouting.sound _ _ [66,384,9,36,160] 13 (by decide) (choices 1) [1,16,64] r12370 c12370
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4097
  · exact u4098
  · exact u4099

def r12371 : Route 9 := (fun mask => (mask,id))

def c12371 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12371 : Upper (D 8) (R 8) [66,384,9,36,192] 13 := by
  apply FastRouting.sound _ _ [66,384,9,36,192] 13 (by decide) (choices 1) [1,16] r12371 c12371
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4100
  · exact u4101

def b12372 : PairBound 9 := { available := 228, camps := [{ cop := 4, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 67 386 13 56 49 228 228 228 484), lower := (rows 67 386 13 56 49 32 64 128 256), losses := [] }

theorem u12372 : Upper (D 8) (R 8) [66,384,9,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12372 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12373 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 386 13 56 52 225 225 225 481), lower := (rows 67 386 13 56 52 32 64 128 256), losses := [] }

theorem u12373 : Upper (D 8) (R 8) [66,384,9,48,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12373 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12374 : PairBound 9 := { available := 164, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 386 13 56 81 164 228 164 420), lower := (rows 67 386 13 56 81 32 64 128 256), losses := [] }

theorem u12374 : Upper (D 8) (R 8) [66,384,9,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12374 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12375 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 386 13 56 84 161 225 161 417), lower := (rows 67 386 13 56 84 32 64 128 256), losses := [] }

theorem u12375 : Upper (D 8) (R 8) [66,384,9,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12375 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12376 : PairBound 9 := { available := 165, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 386 13 56 112 165 229 165 421), lower := (rows 67 386 13 56 112 32 64 128 256), losses := [] }

theorem u12376 : Upper (D 8) (R 8) [66,384,9,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12376 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12377 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 108, targets := 128 }], pairs := [(2,7)], upper := (rows 67 386 13 56 145 100 100 228 356), lower := (rows 67 386 13 56 145 32 64 128 256), losses := [] }

theorem u12377 : Upper (D 8) (R 8) [66,384,9,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12377 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12378 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 67 386 13 56 148 97 97 225 353), lower := (rows 67 386 13 56 148 32 64 128 256), losses := [] }

theorem u12378 : Upper (D 8) (R 8) [66,384,9,48,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12378 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12379 : PairBound 9 := { available := 101, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 386 13 56 176 101 101 229 357), lower := (rows 67 386 13 56 176 32 64 128 256), losses := [] }

theorem u12379 : Upper (D 8) (R 8) [66,384,9,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12379 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12380 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 386 13 56 208 37 101 165 293), lower := (rows 67 386 13 56 208 32 64 128 256), losses := [] }

theorem u12380 : Upper (D 8) (R 8) [66,384,9,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12380 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12381 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 67 386 13 73 52 176 240 176 432), lower := (rows 67 386 13 73 52 32 64 128 256), losses := [] }

theorem u12381 : Upper (D 8) (R 8) [66,384,9,65,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12381 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12382 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 67 386 13 73 148 48 112 176 304), lower := (rows 67 386 13 73 148 32 64 128 256), losses := [] }

theorem u12382 : Upper (D 8) (R 8) [66,384,9,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12382 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12383 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 67 386 13 73 176 52 116 180 308), lower := (rows 67 386 13 73 176 32 64 128 256), losses := [] }

theorem u12383 : Upper (D 8) (R 8) [66,384,9,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12383 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12384 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 67 386 13 76 49 176 240 176 432), lower := (rows 67 386 13 76 49 32 64 128 256), losses := [] }

theorem u12384 : Upper (D 8) (R 8) [66,384,9,68,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12384 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12385 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 67 386 13 76 176 49 113 177 305), lower := (rows 67 386 13 76 176 32 64 128 256), losses := [] }

theorem u12385 : Upper (D 8) (R 8) [66,384,9,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12385 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12386 : PairBound 9 := { available := 164, camps := [{ cop := 2, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 386 13 88 49 164 228 164 420), lower := (rows 67 386 13 88 49 32 64 128 256), losses := [] }

theorem u12386 : Upper (D 8) (R 8) [66,384,9,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12386 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12387 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 386 13 88 52 161 225 161 417), lower := (rows 67 386 13 88 52 32 64 128 256), losses := [] }

theorem u12387 : Upper (D 8) (R 8) [66,384,9,80,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12387 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12388 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 386 13 88 148 33 97 161 289), lower := (rows 67 386 13 88 148 32 64 128 256), losses := [] }

theorem u12388 : Upper (D 8) (R 8) [66,384,9,80,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12388 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12389 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 386 13 88 176 37 101 165 293), lower := (rows 67 386 13 88 176 32 64 128 256), losses := [] }

theorem u12389 : Upper (D 8) (R 8) [66,384,9,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12389 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12390 : PairBound 9 := { available := 180, camps := [{ cop := 2, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 67 386 13 104 49 180 244 180 436), lower := (rows 67 386 13 104 49 32 64 128 256), losses := [] }

theorem u12390 : Upper (D 8) (R 8) [66,384,9,96,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12390 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12391 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 67 386 13 104 52 177 241 177 433), lower := (rows 67 386 13 104 52 32 64 128 256), losses := [] }

theorem u12391 : Upper (D 8) (R 8) [66,384,9,96,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12391 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12392 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 67 386 13 104 148 49 113 177 305), lower := (rows 67 386 13 104 148 32 64 128 256), losses := [] }

theorem u12392 : Upper (D 8) (R 8) [66,384,9,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12392 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12393 : PairBound 9 := { available := 53, camps := [{ cop := 2, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 67 386 13 104 176 53 117 181 309), lower := (rows 67 386 13 104 176 32 64 128 256), losses := [] }

theorem u12393 : Upper (D 8) (R 8) [66,384,9,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12393 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12394 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 498, targets := 1 }], pairs := [(1,0)], upper := (rows 67 386 13 137 52 112 112 240 368), lower := (rows 67 386 13 137 52 32 64 128 256), losses := [] }

theorem u12394 : Upper (D 8) (R 8) [66,384,9,129,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12394 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12395 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 498, targets := 1 }], pairs := [(1,0)], upper := (rows 67 386 13 137 84 48 112 176 304), lower := (rows 67 386 13 137 84 32 64 128 256), losses := [] }

theorem u12395 : Upper (D 8) (R 8) [66,384,9,129,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12395 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12396 : PairBound 9 := { available := 52, camps := [{ cop := 2, region := 498, targets := 1 }], pairs := [(1,0)], upper := (rows 67 386 13 137 112 52 116 180 308), lower := (rows 67 386 13 137 112 32 64 128 256), losses := [] }

theorem u12396 : Upper (D 8) (R 8) [66,384,9,129,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12396 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12397 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 67 386 13 140 49 112 112 240 368), lower := (rows 67 386 13 140 49 32 64 128 256), losses := [] }

theorem u12397 : Upper (D 8) (R 8) [66,384,9,132,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12397 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12398 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 67 386 13 140 112 49 113 177 305), lower := (rows 67 386 13 140 112 32 64 128 256), losses := [] }

theorem u12398 : Upper (D 8) (R 8) [66,384,9,132,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12398 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12399 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 482, targets := 1 }], pairs := [(1,0)], upper := (rows 67 386 13 152 49 100 100 228 356), lower := (rows 67 386 13 152 49 32 64 128 256), losses := [] }

theorem u12399 : Upper (D 8) (R 8) [66,384,9,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12399 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12400 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 67 386 13 152 52 97 97 225 353), lower := (rows 67 386 13 152 52 32 64 128 256), losses := [] }

theorem u12400 : Upper (D 8) (R 8) [66,384,9,144,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12400 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12401 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 386 13 152 84 33 97 161 289), lower := (rows 67 386 13 152 84 32 64 128 256), losses := [] }

theorem u12401 : Upper (D 8) (R 8) [66,384,9,144,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12401 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12402 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 386 13 152 112 37 101 165 293), lower := (rows 67 386 13 152 112 32 64 128 256), losses := [] }

theorem u12402 : Upper (D 8) (R 8) [66,384,9,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12402 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12403 : PairBound 9 := { available := 116, camps := [{ cop := 2, region := 112, targets := 128 }], pairs := [(4,7)], upper := (rows 67 386 13 168 49 116 116 244 372), lower := (rows 67 386 13 168 49 32 64 128 256), losses := [] }

theorem u12403 : Upper (D 8) (R 8) [66,384,9,160,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12403 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12404 : PairBound 9 := { available := 113, camps := [{ cop := 2, region := 112, targets := 128 }], pairs := [(4,7)], upper := (rows 67 386 13 168 52 113 113 241 369), lower := (rows 67 386 13 168 52 32 64 128 256), losses := [] }

theorem u12404 : Upper (D 8) (R 8) [66,384,9,160,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12404 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12405 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 112, targets := 128 }], pairs := [(4,7)], upper := (rows 67 386 13 168 84 49 113 177 305), lower := (rows 67 386 13 168 84 32 64 128 256), losses := [] }

theorem u12405 : Upper (D 8) (R 8) [66,384,9,160,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12405 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12406 : PairBound 9 := { available := 53, camps := [{ cop := 2, region := 112, targets := 128 }], pairs := [(4,7)], upper := (rows 67 386 13 168 112 53 117 181 309), lower := (rows 67 386 13 168 112 32 64 128 256), losses := [] }

theorem u12406 : Upper (D 8) (R 8) [66,384,9,160,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12406 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12407 : PairBound 9 := { available := 52, camps := [{ cop := 2, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 67 386 13 200 49 52 116 180 308), lower := (rows 67 386 13 200 49 32 64 128 256), losses := [] }

theorem u12407 : Upper (D 8) (R 8) [66,384,9,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12407 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12408 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 67 386 13 200 52 49 113 177 305), lower := (rows 67 386 13 200 52 32 64 128 256), losses := [] }

theorem u12408 : Upper (D 8) (R 8) [66,384,9,192,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12408 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12409 : PairBound 9 := { available := 228, camps := [{ cop := 3, region := 20, targets := 64 }], pairs := [(2,6)], upper := (rows 67 386 28 41 49 228 228 228 484), lower := (rows 67 386 28 41 49 32 64 128 256), losses := [] }

theorem u12409 : Upper (D 8) (R 8) [66,384,24,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12409 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12410 : PairBound 9 := { available := 225, camps := [{ cop := 3, region := 20, targets := 1 }], pairs := [(2,0)], upper := (rows 67 386 28 41 52 225 225 225 481), lower := (rows 67 386 28 41 52 32 64 128 256), losses := [] }

theorem u12410 : Upper (D 8) (R 8) [66,384,24,33,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12410 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12411 : PairBound 9 := { available := 164, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 386 28 41 81 164 228 164 420), lower := (rows 67 386 28 41 81 32 64 128 256), losses := [] }

theorem u12411 : Upper (D 8) (R 8) [66,384,24,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12411 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12412 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 386 28 41 84 161 225 161 417), lower := (rows 67 386 28 41 84 32 64 128 256), losses := [] }

theorem u12412 : Upper (D 8) (R 8) [66,384,24,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12412 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12413 : Route 9 := (fun mask => (mask,id))

def c12413 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u12413 : Upper (D 8) (R 8) [66,384,24,33,96] 13 := by
  apply FastRouting.sound _ _ [66,384,24,33,96] 13 (by decide) (choices 1) [1,4,128] r12413 c12413
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4102
  · exact u4103
  · exact u4104

def b12414 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 108, targets := 128 }], pairs := [(2,7)], upper := (rows 67 386 28 41 145 100 100 228 356), lower := (rows 67 386 28 41 145 32 64 128 256), losses := [] }

theorem u12414 : Upper (D 8) (R 8) [66,384,24,33,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12414 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12415 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 67 386 28 41 148 97 97 225 353), lower := (rows 67 386 28 41 148 32 64 128 256), losses := [] }

theorem u12415 : Upper (D 8) (R 8) [66,384,24,33,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12415 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12416 : Route 9 := (fun mask => (mask,id))

def c12416 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12416 : Upper (D 8) (R 8) [66,384,24,33,160] 13 := by
  apply FastRouting.sound _ _ [66,384,24,33,160] 13 (by decide) (choices 1) [1,4,64] r12416 c12416
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4105
  · exact u4106
  · exact u4107

def r12417 : Route 9 := (fun mask => (mask,id))

def c12417 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12417 : Upper (D 8) (R 8) [66,384,24,33,192] 13 := by
  apply FastRouting.sound _ _ [66,384,24,33,192] 13 (by decide) (choices 1) [1,4] r12417 c12417
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4108
  · exact u4109

def b12418 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 386 28 44 81 161 225 161 417), lower := (rows 67 386 28 44 81 32 64 128 256), losses := [] }

theorem u12418 : Upper (D 8) (R 8) [66,384,24,36,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12418 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12419 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 386 28 44 112 161 225 161 417), lower := (rows 67 386 28 44 112 32 64 128 256), losses := [] }

theorem u12419 : Upper (D 8) (R 8) [66,384,24,36,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12419 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u12419
end Delivery.IrregularNine14.P08

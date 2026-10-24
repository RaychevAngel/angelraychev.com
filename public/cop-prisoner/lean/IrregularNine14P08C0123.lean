import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0018

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7380 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 428, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 268 200 81 176 240 176 432), lower := (rows 7 35 268 200 81 32 64 128 256), losses := [] }

theorem u7380 : Upper (D 8) (R 8) [6,33,264,192,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7380 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7381 : Route 9 := (fun mask => (mask,id))

def c7381 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7381 : Upper (D 8) (R 8) [6,33,264,192,96] 13 := by
  apply FastRouting.sound _ _ [6,33,264,192,96] 13 (by decide) (choices 1) [1,16,128] r7381 c7381
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1097
  · exact u1098
  · exact u1099

def b7382 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 35 268 200 208 49 113 177 305), lower := (rows 7 35 268 200 208 32 64 128 256), losses := [] }

theorem u7382 : Upper (D 8) (R 8) [6,33,264,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7382 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7383 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 24, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 324 25 56 224 224 224 480), lower := (rows 7 35 324 25 56 32 64 128 256), losses := [] }

theorem u7383 : Upper (D 8) (R 8) [6,33,320,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7383 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7384 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 324 25 88 160 224 160 416), lower := (rows 7 35 324 25 88 32 64 128 256), losses := [] }

theorem u7384 : Upper (D 8) (R 8) [6,33,320,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7384 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7385 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 484, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 324 25 112 168 232 168 424), lower := (rows 7 35 324 25 112 32 64 128 256), losses := [] }

theorem u7385 : Upper (D 8) (R 8) [6,33,320,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7385 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7386 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 484, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 324 25 152 224 224 224 480), lower := (rows 7 35 324 25 152 32 64 128 256), losses := [] }

theorem u7386 : Upper (D 8) (R 8) [6,33,320,17,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7386 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7387 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 484, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 324 25 176 232 232 232 488), lower := (rows 7 35 324 25 176 32 64 128 256), losses := [] }

theorem u7387 : Upper (D 8) (R 8) [6,33,320,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7387 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7388 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 484, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 324 25 208 168 232 168 424), lower := (rows 7 35 324 25 208 32 64 128 256), losses := [] }

theorem u7388 : Upper (D 8) (R 8) [6,33,320,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7388 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7389 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 324 41 56 240 208 208 464), lower := (rows 7 35 324 41 56 32 64 128 256), losses := [] }

theorem u7389 : Upper (D 8) (R 8) [6,33,320,33,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7389 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7390 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 324 41 88 176 240 176 432), lower := (rows 7 35 324 41 88 32 64 128 256), losses := [] }

theorem u7390 : Upper (D 8) (R 8) [6,33,320,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7390 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7391 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 324 41 112 184 216 152 408), lower := (rows 7 35 324 41 112 32 64 128 256), losses := [] }

theorem u7391 : Upper (D 8) (R 8) [6,33,320,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7391 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7392 : PairBound 9 := { available := 240, camps := [{ cop := 1, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 324 41 152 240 240 240 496), lower := (rows 7 35 324 41 152 32 64 128 256), losses := [] }

theorem u7392 : Upper (D 8) (R 8) [6,33,320,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7392 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7393 : PairBound 9 := { available := 216, camps := [{ cop := 1, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 324 41 176 248 216 216 472), lower := (rows 7 35 324 41 176 32 64 128 256), losses := [] }

theorem u7393 : Upper (D 8) (R 8) [6,33,320,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7393 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7394 : PairBound 9 := { available := 184, camps := [{ cop := 1, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 324 41 208 184 248 184 440), lower := (rows 7 35 324 41 208 32 64 128 256), losses := [] }

theorem u7394 : Upper (D 8) (R 8) [6,33,320,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7394 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7395 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 324 56 56 225 193 193 449), lower := (rows 7 35 324 56 56 32 64 128 256), losses := [] }

theorem u7395 : Upper (D 8) (R 8) [6,33,320,48,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7395 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7396 : PairBound 9 := { available := 168, camps := [{ cop := 4, region := 428, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 324 56 81 168 232 168 424), lower := (rows 7 35 324 56 81 32 64 128 256), losses := [] }

theorem u7396 : Upper (D 8) (R 8) [6,33,320,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7396 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7397 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 324 56 88 161 225 161 417), lower := (rows 7 35 324 56 88 32 64 128 256), losses := [] }

theorem u7397 : Upper (D 8) (R 8) [6,33,320,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7397 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7398 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 324 56 112 169 201 137 393), lower := (rows 7 35 324 56 112 32 64 128 256), losses := [] }

theorem u7398 : Upper (D 8) (R 8) [6,33,320,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7398 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7399 : PairBound 9 := { available := 232, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 324 56 145 232 232 232 488), lower := (rows 7 35 324 56 145 32 64 128 256), losses := [] }

theorem u7399 : Upper (D 8) (R 8) [6,33,320,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7399 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7400 : Route 9 := (fun mask => (mask,id))

def c7400 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7400 : Upper (D 8) (R 8) [6,33,320,48,136] 13 := by
  apply FastRouting.sound _ _ [6,33,320,48,136] 13 (by decide) (choices 1) [1,64,128] r7400 c7400
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1100
  · exact u1101
  · exact u1102

def b7401 : PairBound 9 := { available := 201, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 324 56 176 233 201 201 457), lower := (rows 7 35 324 56 176 32 64 128 256), losses := [] }

theorem u7401 : Upper (D 8) (R 8) [6,33,320,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7401 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7402 : Route 9 := (fun mask => (mask,id))

def c7402 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7402 : Upper (D 8) (R 8) [6,33,320,48,192] 13 := by
  apply FastRouting.sound _ _ [6,33,320,48,192] 13 (by decide) (choices 1) [1,8,128] r7402 c7402
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1103
  · exact u1104
  · exact u1105

def b7403 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 436, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 324 73 152 176 240 176 432), lower := (rows 7 35 324 73 152 32 64 128 256), losses := [] }

theorem u7403 : Upper (D 8) (R 8) [6,33,320,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7403 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7404 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 436, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 324 73 176 184 248 184 440), lower := (rows 7 35 324 73 176 32 64 128 256), losses := [] }

theorem u7404 : Upper (D 8) (R 8) [6,33,320,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7404 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7405 : PairBound 9 := { available := 168, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 324 88 145 168 232 168 424), lower := (rows 7 35 324 88 145 32 64 128 256), losses := [] }

theorem u7405 : Upper (D 8) (R 8) [6,33,320,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7405 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7406 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 324 88 152 161 225 161 417), lower := (rows 7 35 324 88 152 32 64 128 256), losses := [] }

theorem u7406 : Upper (D 8) (R 8) [6,33,320,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7406 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7407 : Route 9 := (fun mask => (mask,id))

def c7407 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7407 : Upper (D 8) (R 8) [6,33,320,80,160] 13 := by
  apply FastRouting.sound _ _ [6,33,320,80,160] 13 (by decide) (choices 1) [1,8,128] r7407 c7407
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1106
  · exact u1107
  · exact u1108

def b7408 : PairBound 9 := { available := 184, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 324 104 145 184 248 184 440), lower := (rows 7 35 324 104 145 32 64 128 256), losses := [] }

theorem u7408 : Upper (D 8) (R 8) [6,33,320,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7408 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7409 : Route 9 := (fun mask => (mask,id))

def c7409 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7409 : Upper (D 8) (R 8) [6,33,320,96,136] 13 := by
  apply FastRouting.sound _ _ [6,33,320,96,136] 13 (by decide) (choices 1) [1,16,128] r7409 c7409
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1109
  · exact u1110
  · exact u1111

def r7410 : Route 9 := (fun mask => (mask,id))

def c7410 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7410 : Upper (D 8) (R 8) [6,33,320,96,160] 13 := by
  apply FastRouting.sound _ _ [6,33,320,96,160] 13 (by decide) (choices 1) [1,8,16,128] r7410 c7410
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1112
  · exact u1113
  · exact u1114
  · exact u1115

def b7411 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 324 137 152 112 112 240 368), lower := (rows 7 35 324 137 152 32 64 128 256), losses := [] }

theorem u7411 : Upper (D 8) (R 8) [6,33,320,129,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7411 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7412 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 324 137 176 120 120 248 376), lower := (rows 7 35 324 137 176 32 64 128 256), losses := [] }

theorem u7412 : Upper (D 8) (R 8) [6,33,320,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7412 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7413 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 324 137 208 56 120 184 312), lower := (rows 7 35 324 137 208 32 64 128 256), losses := [] }

theorem u7413 : Upper (D 8) (R 8) [6,33,320,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7413 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7414 : PairBound 9 := { available := 97, camps := [{ cop := 7, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 324 152 152 97 97 225 353), lower := (rows 7 35 324 152 152 32 64 128 256), losses := [] }

theorem u7414 : Upper (D 8) (R 8) [6,33,320,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7414 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7415 : PairBound 9 := { available := 105, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 324 152 176 105 105 233 361), lower := (rows 7 35 324 152 176 32 64 128 256), losses := [] }

theorem u7415 : Upper (D 8) (R 8) [6,33,320,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7415 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7416 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 324 152 208 41 105 169 297), lower := (rows 7 35 324 152 208 32 64 128 256), losses := [] }

theorem u7416 : Upper (D 8) (R 8) [6,33,320,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7416 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7417 : PairBound 9 := { available := 89, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 35 324 168 176 121 89 217 345), lower := (rows 7 35 324 168 176 32 64 128 256), losses := [] }

theorem u7417 : Upper (D 8) (R 8) [6,33,320,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7417 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7418 : Route 9 := (fun mask => (mask,id))

def c7418 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7418 : Upper (D 8) (R 8) [6,33,320,160,192] 13 := by
  apply FastRouting.sound _ _ [6,33,320,160,192] 13 (by decide) (choices 1) [1,8,16] r7418 c7418
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1116
  · exact u1117
  · exact u1118

def b7419 : PairBound 9 := { available := 448, camps := [{ cop := 2, region := 11, targets := 64 }], pairs := [(0,6)], upper := (rows 7 42 52 41 81 480 448 448 448), lower := (rows 7 42 52 41 81 32 64 128 256), losses := [] }

theorem u7419 : Upper (D 8) (R 8) [6,40,48,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7419 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7420 : PairBound 9 := { available := 449, camps := [{ cop := 2, region := 11, targets := 64 }], pairs := [(0,6)], upper := (rows 7 42 52 41 208 481 449 449 449), lower := (rows 7 42 52 41 208 32 64 128 256), losses := [] }

theorem u7420 : Upper (D 8) (R 8) [6,40,48,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7420 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7421 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 11, targets := 64 }], pairs := [(0,6)], upper := (rows 7 42 52 41 273 224 192 192 448), lower := (rows 7 42 52 41 273 32 64 128 256), losses := [] }

theorem u7421 : Upper (D 8) (R 8) [6,40,48,33,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7421 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7422 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 11, targets := 64 }], pairs := [(0,6)], upper := (rows 7 42 52 41 336 225 193 193 449), lower := (rows 7 42 52 41 336 32 64 128 256), losses := [] }

theorem u7422 : Upper (D 8) (R 8) [6,40,48,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7422 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7423 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 7 42 52 73 81 416 480 416 416), lower := (rows 7 42 52 73 81 32 64 128 256), losses := [] }

theorem u7423 : Upper (D 8) (R 8) [6,40,48,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7423 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7424 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 15, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 52 73 112 417 449 385 385), lower := (rows 7 42 52 73 112 32 64 128 256), losses := [] }

theorem u7424 : Upper (D 8) (R 8) [6,40,48,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7424 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7425 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 418, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 52 73 145 480 480 480 480), lower := (rows 7 42 52 73 145 32 64 128 256), losses := [] }

theorem u7425 : Upper (D 8) (R 8) [6,40,48,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7425 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7426 : PairBound 9 := { available := 449, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 7 42 52 73 176 481 449 449 449), lower := (rows 7 42 52 73 176 32 64 128 256), losses := [] }

theorem u7426 : Upper (D 8) (R 8) [6,40,48,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7426 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7427 : PairBound 9 := { available := 417, camps := [{ cop := 3, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 7 42 52 73 208 417 481 417 417), lower := (rows 7 42 52 73 208 32 64 128 256), losses := [] }

theorem u7427 : Upper (D 8) (R 8) [6,40,48,65,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7427 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7428 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 162, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 52 73 273 224 224 224 480), lower := (rows 7 42 52 73 273 32 64 128 256), losses := [] }

theorem u7428 : Upper (D 8) (R 8) [6,40,48,65,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7428 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7429 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 7 42 52 73 304 225 193 193 449), lower := (rows 7 42 52 73 304 32 64 128 256), losses := [] }

theorem u7429 : Upper (D 8) (R 8) [6,40,48,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7429 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7430 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 7 42 52 73 336 161 225 161 417), lower := (rows 7 42 52 73 336 32 64 128 256), losses := [] }

theorem u7430 : Upper (D 8) (R 8) [6,40,48,65,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7430 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7431 : Route 9 := (fun mask => (mask,id))

def c7431 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7431 : Upper (D 8) (R 8) [6,40,48,65,384] 13 := by
  apply FastRouting.sound _ _ [6,40,48,65,384] 13 (by decide) (choices 1) [1,64,128] r7431 c7431
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1119
  · exact u1120
  · exact u1121

def b7432 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 52 104 208 417 449 385 385), lower := (rows 7 42 52 104 208 32 64 128 256), losses := [] }

theorem u7432 : Upper (D 8) (R 8) [6,40,48,96,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7432 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7433 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 52 104 273 225 193 193 449), lower := (rows 7 42 52 104 273 32 64 128 256), losses := [] }

theorem u7433 : Upper (D 8) (R 8) [6,40,48,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7433 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7434 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 52 104 336 161 193 129 385), lower := (rows 7 42 52 104 336 32 64 128 256), losses := [] }

theorem u7434 : Upper (D 8) (R 8) [6,40,48,96,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7434 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7435 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 52 104 400 225 193 193 449), lower := (rows 7 42 52 104 400 32 64 128 256), losses := [] }

theorem u7435 : Upper (D 8) (R 8) [6,40,48,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7435 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7436 : PairBound 9 := { available := 289, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 42 52 200 208 289 353 417 289), lower := (rows 7 42 52 200 208 32 64 128 256), losses := [] }

theorem u7436 : Upper (D 8) (R 8) [6,40,48,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7436 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7437 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7437 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7437 : Upper (D 8) (R 8) [6,40,48,192,257] 13 := by
  apply FastRouting.sound _ _ [6,40,48,192,257] 13 (by decide) (choices 1) [1,64] r7437 c7437
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1122
  · exact u1123

def b7438 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 7 42 52 200 304 225 193 193 449), lower := (rows 7 42 52 200 304 32 64 128 256), losses := [] }

theorem u7438 : Upper (D 8) (R 8) [6,40,48,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7438 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7439 : Route 9 := (fun mask => (mask,id))

def c7439 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7439 : Upper (D 8) (R 8) [6,40,48,192,320] 13 := by
  apply FastRouting.sound _ _ [6,40,48,192,320] 13 (by decide) (choices 1) [1,128] r7439 c7439
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1124
  · exact u1125

#print axioms u7439
end Delivery.IrregularNine14.P08

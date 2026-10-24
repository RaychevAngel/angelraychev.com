import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0040

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b9480 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 35 259 13 200 52 240 240 240 496), lower := (rows 35 259 13 200 52 32 64 128 256), losses := [] }

theorem u9480 : Upper (D 8) (R 8) [34,257,9,192,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9480 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9481 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 35 259 13 200 84 176 240 176 432), lower := (rows 35 259 13 200 84 32 64 128 256), losses := [] }

theorem u9481 : Upper (D 8) (R 8) [34,257,9,192,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9481 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9482 : PairBound 9 := { available := 180, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 35 259 13 200 112 180 244 180 436), lower := (rows 35 259 13 200 112 32 64 128 256), losses := [] }

theorem u9482 : Upper (D 8) (R 8) [34,257,9,192,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9482 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9483 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 28, targets := 64 }], pairs := [(2,6)], upper := (rows 35 259 28 41 52 224 192 192 448), lower := (rows 35 259 28 41 52 32 64 128 256), losses := [] }

theorem u9483 : Upper (D 8) (R 8) [34,257,24,33,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9483 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9484 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 259 28 41 84 224 224 224 480), lower := (rows 35 259 28 41 84 32 64 128 256), losses := [] }

theorem u9484 : Upper (D 8) (R 8) [34,257,24,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9484 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9485 : PairBound 9 := { available := 196, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 259 28 41 112 228 196 196 452), lower := (rows 35 259 28 41 112 32 64 128 256), losses := [] }

theorem u9485 : Upper (D 8) (R 8) [34,257,24,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9485 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9486 : PairBound 9 := { available := 228, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 259 28 41 208 228 228 228 484), lower := (rows 35 259 28 41 208 32 64 128 256), losses := [] }

theorem u9486 : Upper (D 8) (R 8) [34,257,24,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9486 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9487 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 172, targets := 1 }], pairs := [(2,0)], upper := (rows 35 259 28 44 81 224 224 224 480), lower := (rows 35 259 28 44 81 32 64 128 256), losses := [] }

theorem u9487 : Upper (D 8) (R 8) [34,257,24,36,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9487 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9488 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 35 259 28 44 112 225 193 193 449), lower := (rows 35 259 28 44 112 32 64 128 256), losses := [] }

theorem u9488 : Upper (D 8) (R 8) [34,257,24,36,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9488 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9489 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9489 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u9489 : Upper (D 8) (R 8) [34,257,24,36,192] 13 := by
  apply FastRouting.sound _ _ [34,257,24,36,192] 13 (by decide) (choices 1) [1,64] r9489 c9489
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2427
  · exact u2428

def b9490 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 35 259 28 73 84 160 224 160 416), lower := (rows 35 259 28 73 84 32 64 128 256), losses := [] }

theorem u9490 : Upper (D 8) (R 8) [34,257,24,65,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9490 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9491 : PairBound 9 := { available := 164, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 28 73 112 164 228 164 420), lower := (rows 35 259 28 73 112 32 64 128 256), losses := [] }

theorem u9491 : Upper (D 8) (R 8) [34,257,24,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9491 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9492 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 180, targets := 1 }], pairs := [(2,0)], upper := (rows 35 259 28 73 148 224 224 224 480), lower := (rows 35 259 28 73 148 32 64 128 256), losses := [] }

theorem u9492 : Upper (D 8) (R 8) [34,257,24,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9492 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9493 : PairBound 9 := { available := 228, camps := [{ cop := 3, region := 180, targets := 1 }], pairs := [(2,0)], upper := (rows 35 259 28 73 176 228 228 228 484), lower := (rows 35 259 28 73 176 32 64 128 256), losses := [] }

theorem u9493 : Upper (D 8) (R 8) [34,257,24,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9493 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9494 : PairBound 9 := { available := 164, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 28 73 208 164 228 164 420), lower := (rows 35 259 28 73 208 32 64 128 256), losses := [] }

theorem u9494 : Upper (D 8) (R 8) [34,257,24,65,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9494 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9495 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 35 259 28 76 112 161 225 161 417), lower := (rows 35 259 28 76 112 32 64 128 256), losses := [] }

theorem u9495 : Upper (D 8) (R 8) [34,257,24,68,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9495 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9496 : Route 9 := (fun mask => (mask,id))

def c9496 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u9496 : Upper (D 8) (R 8) [34,257,24,68,160] 13 := by
  apply FastRouting.sound _ _ [34,257,24,68,160] 13 (by decide) (choices 1) [1,64,128] r9496 c9496
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2429
  · exact u2430
  · exact u2431

def b9497 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 35 259 28 76 208 161 225 161 417), lower := (rows 35 259 28 76 208 32 64 128 256), losses := [] }

theorem u9497 : Upper (D 8) (R 8) [34,257,24,68,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9497 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9498 : PairBound 9 := { available := 133, camps := [{ cop := 3, region := 20, targets := 1 }], pairs := [(2,0)], upper := (rows 35 259 28 104 112 165 197 133 389), lower := (rows 35 259 28 104 112 32 64 128 256), losses := [] }

theorem u9498 : Upper (D 8) (R 8) [34,257,24,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9498 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m9499_128 : Upper (D 8) (R 8) [34,257,24,96,160,128] 13 :=
  permutation_upper _ _ _ [34,257,24,96,160,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2434

def r9499 : Route 9 := (fun mask => (mask,id))

def c9499 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u9499 : Upper (D 8) (R 8) [34,257,24,96,160] 13 := by
  apply FastRouting.sound _ _ [34,257,24,96,160] 13 (by decide) (choices 1) [1,4,64,128] r9499 c9499
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2432
  · exact u2433
  · exact u2434
  · exact m9499_128

def b9500 : PairBound 9 := { available := 165, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 28 104 208 165 229 165 421), lower := (rows 35 259 28 104 208 32 64 128 256), losses := [] }

theorem u9500 : Upper (D 8) (R 8) [34,257,24,96,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9500 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9501 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 20, targets := 1 }], pairs := [(2,0)], upper := (rows 35 259 28 200 208 37 101 165 293), lower := (rows 35 259 28 200 208 32 64 128 256), losses := [] }

theorem u9501 : Upper (D 8) (R 8) [34,257,24,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9501 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9502 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 259 37 44 88 240 208 208 464), lower := (rows 35 259 37 44 88 32 64 128 256), losses := [] }

theorem u9502 : Upper (D 8) (R 8) [34,257,33,36,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9502 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9503 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 259 37 44 208 248 216 216 472), lower := (rows 35 259 37 44 208 32 64 128 256), losses := [] }

theorem u9503 : Upper (D 8) (R 8) [34,257,33,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9503 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9504 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 259 37 56 84 232 200 200 456), lower := (rows 35 259 37 56 84 32 64 128 256), losses := [] }

theorem u9504 : Upper (D 8) (R 8) [34,257,33,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9504 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9505 : PairBound 9 := { available := 196, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 259 37 56 88 228 196 196 452), lower := (rows 35 259 37 56 88 32 64 128 256), losses := [] }

theorem u9505 : Upper (D 8) (R 8) [34,257,33,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9505 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9506 : PairBound 9 := { available := 204, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 259 37 56 208 236 204 204 460), lower := (rows 35 259 37 56 208 32 64 128 256), losses := [] }

theorem u9506 : Upper (D 8) (R 8) [34,257,33,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9506 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9507 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 259 37 76 112 184 216 152 408), lower := (rows 35 259 37 76 112 32 64 128 256), losses := [] }

theorem u9507 : Upper (D 8) (R 8) [34,257,33,68,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9507 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9508 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 259 37 76 152 240 240 240 496), lower := (rows 35 259 37 76 152 32 64 128 256), losses := [] }

theorem u9508 : Upper (D 8) (R 8) [34,257,33,68,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9508 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9509 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 259 37 76 176 248 216 216 472), lower := (rows 35 259 37 76 176 32 64 128 256), losses := [] }

theorem u9509 : Upper (D 8) (R 8) [34,257,33,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9509 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9510 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 259 37 76 208 184 248 184 440), lower := (rows 35 259 37 76 208 32 64 128 256), losses := [] }

theorem u9510 : Upper (D 8) (R 8) [34,257,33,68,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9510 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9511 : PairBound 9 := { available := 228, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 259 37 88 152 228 228 228 484), lower := (rows 35 259 37 88 152 32 64 128 256), losses := [] }

theorem u9511 : Upper (D 8) (R 8) [34,257,33,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9511 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9512 : PairBound 9 := { available := 204, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 259 37 88 176 236 204 204 460), lower := (rows 35 259 37 88 176 32 64 128 256), losses := [] }

theorem u9512 : Upper (D 8) (R 8) [34,257,33,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9512 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9513 : PairBound 9 := { available := 156, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 259 37 104 208 188 220 156 412), lower := (rows 35 259 37 104 208 32 64 128 256), losses := [] }

theorem u9513 : Upper (D 8) (R 8) [34,257,33,96,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9513 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9514 : PairBound 9 := { available := 209, camps := [{ cop := 5, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 35 259 44 44 208 241 209 209 465), lower := (rows 35 259 44 44 208 32 64 128 256), losses := [] }

theorem u9514 : Upper (D 8) (R 8) [34,257,40,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9514 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9515 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 35 259 44 56 84 225 193 193 449), lower := (rows 35 259 44 56 84 32 64 128 256), losses := [] }

theorem u9515 : Upper (D 8) (R 8) [34,257,40,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9515 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9516 : PairBound 9 := { available := 197, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 35 259 44 56 208 229 197 197 453), lower := (rows 35 259 44 56 208 32 64 128 256), losses := [] }

theorem u9516 : Upper (D 8) (R 8) [34,257,40,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9516 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9517 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 180, targets := 1 }], pairs := [(2,0)], upper := (rows 35 259 44 73 84 176 240 176 432), lower := (rows 35 259 44 73 84 32 64 128 256), losses := [] }

theorem u9517 : Upper (D 8) (R 8) [34,257,40,65,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9517 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9518 : PairBound 9 := { available := 148, camps := [{ cop := 3, region := 180, targets := 1 }], pairs := [(2,0)], upper := (rows 35 259 44 73 112 180 212 148 404), lower := (rows 35 259 44 73 112 32 64 128 256), losses := [] }

theorem u9518 : Upper (D 8) (R 8) [34,257,40,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9518 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9519 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 180, targets := 1 }], pairs := [(2,0)], upper := (rows 35 259 44 73 148 240 240 240 496), lower := (rows 35 259 44 73 148 32 64 128 256), losses := [] }

theorem u9519 : Upper (D 8) (R 8) [34,257,40,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9519 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9520 : PairBound 9 := { available := 212, camps := [{ cop := 3, region := 180, targets := 1 }], pairs := [(2,0)], upper := (rows 35 259 44 73 176 244 212 212 468), lower := (rows 35 259 44 73 176 32 64 128 256), losses := [] }

theorem u9520 : Upper (D 8) (R 8) [34,257,40,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9520 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9521 : PairBound 9 := { available := 180, camps := [{ cop := 3, region := 180, targets := 1 }], pairs := [(2,0)], upper := (rows 35 259 44 73 208 180 244 180 436), lower := (rows 35 259 44 73 208 32 64 128 256), losses := [] }

theorem u9521 : Upper (D 8) (R 8) [34,257,40,65,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9521 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9522 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 172, targets := 1 }], pairs := [(2,0)], upper := (rows 35 259 44 76 81 176 240 176 432), lower := (rows 35 259 44 76 81 32 64 128 256), losses := [] }

theorem u9522 : Upper (D 8) (R 8) [34,257,40,68,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9522 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9523 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 35 259 44 76 112 177 209 145 401), lower := (rows 35 259 44 76 112 32 64 128 256), losses := [] }

theorem u9523 : Upper (D 8) (R 8) [34,257,40,68,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9523 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9524 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 108, targets := 1 }], pairs := [(2,0)], upper := (rows 35 259 44 76 145 240 240 240 496), lower := (rows 35 259 44 76 145 32 64 128 256), losses := [] }

theorem u9524 : Upper (D 8) (R 8) [34,257,40,68,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9524 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9525 : Route 9 := (fun mask => (mask,id))

def c9525 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u9525 : Upper (D 8) (R 8) [34,257,40,68,160] 13 := by
  apply FastRouting.sound _ _ [34,257,40,68,160] 13 (by decide) (choices 1) [1,16,64,128] r9525 c9525
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2435
  · exact u2436
  · exact u2437
  · exact u2438

def b9526 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 291, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 44 76 208 177 241 177 433), lower := (rows 35 259 44 76 208 32 64 128 256), losses := [] }

theorem u9526 : Upper (D 8) (R 8) [34,257,40,68,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9526 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9527 : PairBound 9 := { available := 164, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 44 88 81 164 228 164 420), lower := (rows 35 259 44 88 81 32 64 128 256), losses := [] }

theorem u9527 : Upper (D 8) (R 8) [34,257,40,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9527 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9528 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 44 88 84 161 225 161 417), lower := (rows 35 259 44 88 84 32 64 128 256), losses := [] }

theorem u9528 : Upper (D 8) (R 8) [34,257,40,80,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9528 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9529 : PairBound 9 := { available := 133, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 35 259 44 88 112 165 197 133 389), lower := (rows 35 259 44 88 112 32 64 128 256), losses := [] }

theorem u9529 : Upper (D 8) (R 8) [34,257,40,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9529 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9530 : PairBound 9 := { available := 228, camps := [{ cop := 4, region := 108, targets := 1 }], pairs := [(2,0)], upper := (rows 35 259 44 88 145 228 228 228 484), lower := (rows 35 259 44 88 145 32 64 128 256), losses := [] }

theorem u9530 : Upper (D 8) (R 8) [34,257,40,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9530 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9531 : Route 9 := (fun mask => (mask,id))

def c9531 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u9531 : Upper (D 8) (R 8) [34,257,40,80,132] 13 := by
  apply FastRouting.sound _ _ [34,257,40,80,132] 13 (by decide) (choices 1) [1,64,128] r9531 c9531
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2439
  · exact u2440
  · exact u2441

def r9532 : Route 9 := (fun mask => (mask,id))

def c9532 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u9532 : Upper (D 8) (R 8) [34,257,40,80,160] 13 := by
  apply FastRouting.sound _ _ [34,257,40,80,160] 13 (by decide) (choices 1) [1,4,64,128] r9532 c9532
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2442
  · exact u2443
  · exact u2444
  · exact u2445

def b9533 : PairBound 9 := { available := 165, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 44 88 208 165 229 165 421), lower := (rows 35 259 44 88 208 32 64 128 256), losses := [] }

theorem u9533 : Upper (D 8) (R 8) [34,257,40,80,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9533 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9534 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 35 259 44 104 84 177 209 145 401), lower := (rows 35 259 44 104 84 32 64 128 256), losses := [] }

theorem u9534 : Upper (D 8) (R 8) [34,257,40,96,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9534 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9535 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 35 259 44 104 148 241 209 209 465), lower := (rows 35 259 44 104 148 32 64 128 256), losses := [] }

theorem u9535 : Upper (D 8) (R 8) [34,257,40,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9535 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9536 : PairBound 9 := { available := 149, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 35 259 44 104 208 181 213 149 405), lower := (rows 35 259 44 104 208 32 64 128 256), losses := [] }

theorem u9536 : Upper (D 8) (R 8) [34,257,40,96,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9536 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9537 : PairBound 9 := { available := 180, camps := [{ cop := 4, region := 172, targets := 1 }], pairs := [(2,0)], upper := (rows 35 259 44 200 81 180 244 180 436), lower := (rows 35 259 44 200 81 32 64 128 256), losses := [] }

theorem u9537 : Upper (D 8) (R 8) [34,257,40,192,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9537 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9538 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 44 200 84 177 241 177 433), lower := (rows 35 259 44 200 84 32 64 128 256), losses := [] }

theorem u9538 : Upper (D 8) (R 8) [34,257,40,192,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9538 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9539 : Route 9 := (fun mask => (mask,id))

def c9539 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9539 : Upper (D 8) (R 8) [34,257,40,192,96] 13 := by
  apply FastRouting.sound _ _ [34,257,40,192,96] 13 (by decide) (choices 1) [1,4,16,128] r9539 c9539
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2446
  · exact u2447
  · exact u2448
  · exact u2449

#print axioms u9539
end Delivery.IrregularNine14.P08

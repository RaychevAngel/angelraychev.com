import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0040
import IrregularNine14P08C0041

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b9540 : PairBound 9 := { available := 53, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 259 44 200 208 53 117 181 309), lower := (rows 35 259 44 200 208 32 64 128 256), losses := [] }

theorem u9540 : Upper (D 8) (R 8) [34,257,40,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9540 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9541 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 69 76 152 176 240 176 432), lower := (rows 35 259 69 76 152 32 64 128 256), losses := [] }

theorem u9541 : Upper (D 8) (R 8) [34,257,65,68,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9541 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9542 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 69 76 176 184 248 184 440), lower := (rows 35 259 69 76 176 32 64 128 256), losses := [] }

theorem u9542 : Upper (D 8) (R 8) [34,257,65,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9542 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9543 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 184, targets := 1 }], pairs := [(3,0)], upper := (rows 35 259 69 88 148 168 232 168 424), lower := (rows 35 259 69 88 148 32 64 128 256), losses := [] }

theorem u9543 : Upper (D 8) (R 8) [34,257,65,80,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9543 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9544 : PairBound 9 := { available := 164, camps := [{ cop := 2, region := 184, targets := 1 }], pairs := [(3,0)], upper := (rows 35 259 69 88 152 164 228 164 420), lower := (rows 35 259 69 88 152 32 64 128 256), losses := [] }

theorem u9544 : Upper (D 8) (R 8) [34,257,65,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9544 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9545 : PairBound 9 := { available := 172, camps := [{ cop := 2, region := 184, targets := 1 }], pairs := [(3,0)], upper := (rows 35 259 69 88 176 172 236 172 428), lower := (rows 35 259 69 88 176 32 64 128 256), losses := [] }

theorem u9545 : Upper (D 8) (R 8) [34,257,65,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9545 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9546 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 184, targets := 1 }], pairs := [(3,0)], upper := (rows 35 259 69 104 148 184 248 184 440), lower := (rows 35 259 69 104 148 32 64 128 256), losses := [] }

theorem u9546 : Upper (D 8) (R 8) [34,257,65,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9546 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9547 : PairBound 9 := { available := 180, camps := [{ cop := 2, region := 184, targets := 1 }], pairs := [(3,0)], upper := (rows 35 259 69 104 152 180 244 180 436), lower := (rows 35 259 69 104 152 32 64 128 256), losses := [] }

theorem u9547 : Upper (D 8) (R 8) [34,257,65,96,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9547 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9548 : PairBound 9 := { available := 156, camps := [{ cop := 2, region := 184, targets := 1 }], pairs := [(3,0)], upper := (rows 35 259 69 104 176 188 220 156 412), lower := (rows 35 259 69 104 176 32 64 128 256), losses := [] }

theorem u9548 : Upper (D 8) (R 8) [34,257,65,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9548 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9549 : PairBound 9 := { available := 120, camps := [{ cop := 2, region := 184, targets := 1 }], pairs := [(3,0)], upper := (rows 35 259 69 140 176 120 120 248 376), lower := (rows 35 259 69 140 176 32 64 128 256), losses := [] }

theorem u9549 : Upper (D 8) (R 8) [34,257,65,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9549 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9550 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 184, targets := 1 }], pairs := [(3,0)], upper := (rows 35 259 69 140 208 56 120 184 312), lower := (rows 35 259 69 140 208 32 64 128 256), losses := [] }

theorem u9550 : Upper (D 8) (R 8) [34,257,65,132,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9550 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9551 : PairBound 9 := { available := 60, camps := [{ cop := 2, region := 184, targets := 1 }], pairs := [(3,0)], upper := (rows 35 259 69 168 208 60 124 188 316), lower := (rows 35 259 69 168 208 32 64 128 256), losses := [] }

theorem u9551 : Upper (D 8) (R 8) [34,257,65,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9551 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9552 : PairBound 9 := { available := 177, camps := [{ cop := 6, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 35 259 76 76 176 177 241 177 433), lower := (rows 35 259 76 76 176 32 64 128 256), losses := [] }

theorem u9552 : Upper (D 8) (R 8) [34,257,72,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9552 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9553 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 76 88 148 161 225 161 417), lower := (rows 35 259 76 88 148 32 64 128 256), losses := [] }

theorem u9553 : Upper (D 8) (R 8) [34,257,72,80,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9553 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9554 : PairBound 9 := { available := 165, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 76 88 176 165 229 165 421), lower := (rows 35 259 76 88 176 32 64 128 256), losses := [] }

theorem u9554 : Upper (D 8) (R 8) [34,257,72,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9554 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9555 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 76 104 148 177 241 177 433), lower := (rows 35 259 76 104 148 32 64 128 256), losses := [] }

theorem u9555 : Upper (D 8) (R 8) [34,257,72,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9555 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9556 : PairBound 9 := { available := 149, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 76 104 176 181 213 149 405), lower := (rows 35 259 76 104 176 32 64 128 256), losses := [] }

theorem u9556 : Upper (D 8) (R 8) [34,257,72,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9556 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9557 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 387, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 76 140 112 177 241 177 433), lower := (rows 35 259 76 140 112 32 64 128 256), losses := [] }

theorem u9557 : Upper (D 8) (R 8) [34,257,72,132,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9557 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9558 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 35 259 76 140 208 49 113 177 305), lower := (rows 35 259 76 140 208 32 64 128 256), losses := [] }

theorem u9558 : Upper (D 8) (R 8) [34,257,72,132,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9558 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9559 : PairBound 9 := { available := 165, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 76 152 112 165 229 165 421), lower := (rows 35 259 76 152 112 32 64 128 256), losses := [] }

theorem u9559 : Upper (D 8) (R 8) [34,257,72,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9559 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9560 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 35 259 76 152 208 37 101 165 293), lower := (rows 35 259 76 152 208 32 64 128 256), losses := [] }

theorem u9560 : Upper (D 8) (R 8) [34,257,72,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9560 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9561 : Route 9 := (fun mask => (mask,id))

def c9561 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9561 : Upper (D 8) (R 8) [34,257,72,160,96] 13 := by
  apply FastRouting.sound _ _ [34,257,72,160,96] 13 (by decide) (choices 1) [1,4,16,128] r9561 c9561
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2450
  · exact u2451
  · exact u2452
  · exact u2453

def b9562 : PairBound 9 := { available := 85, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 259 76 168 176 117 85 213 341), lower := (rows 35 259 76 168 176 32 64 128 256), losses := [] }

theorem u9562 : Upper (D 8) (R 8) [34,257,72,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9562 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9563 : Route 9 := (fun mask => (mask,id))

def c9563 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9563 : Upper (D 8) (R 8) [34,257,72,160,192] 13 := by
  apply FastRouting.sound _ _ [34,257,72,160,192] 13 (by decide) (choices 1) [1,4,16] r9563 c9563
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2454
  · exact u2455
  · exact u2456

def b9564 : PairBound 9 := { available := 53, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 76 200 176 53 117 181 309), lower := (rows 35 259 76 200 176 32 64 128 256), losses := [] }

theorem u9564 : Upper (D 8) (R 8) [34,257,72,192,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9564 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m9565_8 : Upper (D 8) (R 8) [34,257,96,160,192,8] 13 :=
  permutation_upper _ _ _ [34,257,96,160,192,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2458

def r9565 : Route 9 := (fun mask => (mask,id))

def c9565 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9565 : Upper (D 8) (R 8) [34,257,96,160,192] 13 := by
  apply FastRouting.sound _ _ [34,257,96,160,192] 13 (by decide) (choices 1) [1,4,8,16] r9565 c9565
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2457
  · exact u2458
  · exact m9565_8
  · exact u2459

def b9566 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 28, targets := 64 }], pairs := [(2,6)], upper := (rows 35 262 13 56 49 224 192 192 448), lower := (rows 35 262 13 56 49 32 64 128 256), losses := [] }

theorem u9566 : Upper (D 8) (R 8) [34,260,9,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9566 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9567 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 482, targets := 1 }], pairs := [(1,0)], upper := (rows 35 262 13 56 81 224 224 224 480), lower := (rows 35 262 13 56 81 32 64 128 256), losses := [] }

theorem u9567 : Upper (D 8) (R 8) [34,260,9,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9567 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9568 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 262 13 56 112 225 193 193 449), lower := (rows 35 262 13 56 112 32 64 128 256), losses := [] }

theorem u9568 : Upper (D 8) (R 8) [34,260,9,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9568 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9569 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9569 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u9569 : Upper (D 8) (R 8) [34,260,9,48,192] 13 := by
  apply FastRouting.sound _ _ [34,260,9,48,192] 13 (by decide) (choices 1) [1,64] r9569 c9569
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2460
  · exact u2461

def b9570 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 35 262 13 88 49 224 224 224 480), lower := (rows 35 262 13 88 49 32 64 128 256), losses := [] }

theorem u9570 : Upper (D 8) (R 8) [34,260,9,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9570 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9571 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 262 13 88 81 160 224 160 416), lower := (rows 35 262 13 88 81 32 64 128 256), losses := [] }

theorem u9571 : Upper (D 8) (R 8) [34,260,9,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9571 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9572 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 13 88 112 161 225 161 417), lower := (rows 35 262 13 88 112 32 64 128 256), losses := [] }

theorem u9572 : Upper (D 8) (R 8) [34,260,9,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9572 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9573 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 482, targets := 1 }], pairs := [(1,0)], upper := (rows 35 262 13 88 145 224 224 224 480), lower := (rows 35 262 13 88 145 32 64 128 256), losses := [] }

theorem u9573 : Upper (D 8) (R 8) [34,260,9,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9573 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9574 : Route 9 := (fun mask => (mask,id))

def c9574 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u9574 : Upper (D 8) (R 8) [34,260,9,80,160] 13 := by
  apply FastRouting.sound _ _ [34,260,9,80,160] 13 (by decide) (choices 1) [1,64,128] r9574 c9574
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2462
  · exact u2463
  · exact u2464

def b9575 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 13 88 208 161 225 161 417), lower := (rows 35 262 13 88 208 32 64 128 256), losses := [] }

theorem u9575 : Upper (D 8) (R 8) [34,260,9,80,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9575 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9576 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 35 262 13 104 49 240 208 208 464), lower := (rows 35 262 13 104 49 32 64 128 256), losses := [] }

theorem u9576 : Upper (D 8) (R 8) [34,260,9,96,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9576 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9577 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 168, targets := 1 }], pairs := [(3,0)], upper := (rows 35 262 13 104 81 176 240 176 432), lower := (rows 35 262 13 104 81 32 64 128 256), losses := [] }

theorem u9577 : Upper (D 8) (R 8) [34,260,9,96,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9577 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9578 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 262 13 104 112 177 209 145 401), lower := (rows 35 262 13 104 112 32 64 128 256), losses := [] }

theorem u9578 : Upper (D 8) (R 8) [34,260,9,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9578 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9579 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 104, targets := 1 }], pairs := [(3,0)], upper := (rows 35 262 13 104 145 240 240 240 496), lower := (rows 35 262 13 104 145 32 64 128 256), losses := [] }

theorem u9579 : Upper (D 8) (R 8) [34,260,9,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9579 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9580 : Route 9 := (fun mask => (mask,id))

def c9580 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u9580 : Upper (D 8) (R 8) [34,260,9,96,160] 13 := by
  apply FastRouting.sound _ _ [34,260,9,96,160] 13 (by decide) (choices 1) [1,16,64,128] r9580 c9580
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2465
  · exact u2466
  · exact u2467
  · exact u2468

def r9581 : Route 9 := (fun mask => (mask,id))

def c9581 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9581 : Upper (D 8) (R 8) [34,260,9,96,192] 13 := by
  apply FastRouting.sound _ _ [34,260,9,96,192] 13 (by decide) (choices 1) [1,16,128] r9581 c9581
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2469
  · exact u2470
  · exact u2471

def b9582 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 35 262 13 200 49 240 240 240 496), lower := (rows 35 262 13 200 49 32 64 128 256), losses := [] }

theorem u9582 : Upper (D 8) (R 8) [34,260,9,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9582 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9583 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 168, targets := 1 }], pairs := [(3,0)], upper := (rows 35 262 13 200 81 176 240 176 432), lower := (rows 35 262 13 200 81 32 64 128 256), losses := [] }

theorem u9583 : Upper (D 8) (R 8) [34,260,9,192,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9583 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9584 : Route 9 := (fun mask => (mask,id))

def c9584 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9584 : Upper (D 8) (R 8) [34,260,9,192,96] 13 := by
  apply FastRouting.sound _ _ [34,260,9,192,96] 13 (by decide) (choices 1) [1,16,128] r9584 c9584
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2472
  · exact u2473
  · exact u2474

def b9585 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 262 13 200 208 49 113 177 305), lower := (rows 35 262 13 200 208 32 64 128 256), losses := [] }

theorem u9585 : Upper (D 8) (R 8) [34,260,9,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9585 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9586 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 262 28 41 81 224 224 224 480), lower := (rows 35 262 28 41 81 32 64 128 256), losses := [] }

theorem u9586 : Upper (D 8) (R 8) [34,260,24,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9586 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9587 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 262 28 41 112 225 193 193 449), lower := (rows 35 262 28 41 112 32 64 128 256), losses := [] }

theorem u9587 : Upper (D 8) (R 8) [34,260,24,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9587 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9588 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 262 28 41 208 225 225 225 481), lower := (rows 35 262 28 41 208 32 64 128 256), losses := [] }

theorem u9588 : Upper (D 8) (R 8) [34,260,24,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9588 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9589 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 35 262 28 73 81 160 224 160 416), lower := (rows 35 262 28 73 81 32 64 128 256), losses := [] }

theorem u9589 : Upper (D 8) (R 8) [34,260,24,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9589 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9590 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 28 73 112 161 225 161 417), lower := (rows 35 262 28 73 112 32 64 128 256), losses := [] }

theorem u9590 : Upper (D 8) (R 8) [34,260,24,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9590 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9591 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 482, targets := 1 }], pairs := [(1,0)], upper := (rows 35 262 28 73 145 224 224 224 480), lower := (rows 35 262 28 73 145 32 64 128 256), losses := [] }

theorem u9591 : Upper (D 8) (R 8) [34,260,24,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9591 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9592 : Route 9 := (fun mask => (mask,id))

def c9592 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u9592 : Upper (D 8) (R 8) [34,260,24,65,160] 13 := by
  apply FastRouting.sound _ _ [34,260,24,65,160] 13 (by decide) (choices 1) [1,64,128] r9592 c9592
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2475
  · exact u2476
  · exact u2477

def b9593 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 28 73 208 161 225 161 417), lower := (rows 35 262 28 73 208 32 64 128 256), losses := [] }

theorem u9593 : Upper (D 8) (R 8) [34,260,24,65,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9593 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9594 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 20, targets := 1 }], pairs := [(2,0)], upper := (rows 35 262 28 104 112 161 193 129 385), lower := (rows 35 262 28 104 112 32 64 128 256), losses := [] }

theorem u9594 : Upper (D 8) (R 8) [34,260,24,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9594 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m9595_128 : Upper (D 8) (R 8) [34,260,24,96,160,128] 13 :=
  permutation_upper _ _ _ [34,260,24,96,160,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2479

def r9595 : Route 9 := (fun mask => (mask,id))

def c9595 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u9595 : Upper (D 8) (R 8) [34,260,24,96,160] 13 := by
  apply FastRouting.sound _ _ [34,260,24,96,160] 13 (by decide) (choices 1) [1,64,128] r9595 c9595
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2478
  · exact u2479
  · exact m9595_128

def b9596 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 28 104 208 161 225 161 417), lower := (rows 35 262 28 104 208 32 64 128 256), losses := [] }

theorem u9596 : Upper (D 8) (R 8) [34,260,24,96,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9596 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9597 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 20, targets := 1 }], pairs := [(2,0)], upper := (rows 35 262 28 200 208 33 97 161 289), lower := (rows 35 262 28 200 208 32 64 128 256), losses := [] }

theorem u9597 : Upper (D 8) (R 8) [34,260,24,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9597 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9598 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 28, targets := 64 }], pairs := [(2,6)], upper := (rows 35 262 44 25 49 224 192 192 448), lower := (rows 35 262 44 25 49 32 64 128 256), losses := [] }

theorem u9598 : Upper (D 8) (R 8) [34,260,40,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9598 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9599 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 262 44 25 81 224 224 224 480), lower := (rows 35 262 44 25 81 32 64 128 256), losses := [] }

theorem u9599 : Upper (D 8) (R 8) [34,260,40,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9599 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u9599
end Delivery.IrregularNine14.P08

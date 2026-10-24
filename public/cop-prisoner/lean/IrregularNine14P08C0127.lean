import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0021

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7620 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 7 67 140 280 208 33 97 161 289), lower := (rows 7 67 140 280 208 32 64 128 256), losses := [] }

theorem u7620 : Upper (D 8) (R 8) [6,65,136,272,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7620 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7621 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 140 296 49 240 240 240 496), lower := (rows 7 67 140 296 49 32 64 128 256), losses := [] }

theorem u7621 : Upper (D 8) (R 8) [6,65,136,288,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7621 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7622 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 7 67 140 296 81 176 240 176 432), lower := (rows 7 67 140 296 81 32 64 128 256), losses := [] }

theorem u7622 : Upper (D 8) (R 8) [6,65,136,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7622 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7623 : Route 9 := (fun mask => (mask,id))

def c7623 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7623 : Upper (D 8) (R 8) [6,65,136,288,96] 13 := by
  apply FastRouting.sound _ _ [6,65,136,288,96] 13 (by decide) (choices 1) [1,16,128] r7623 c7623
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1281
  · exact u1282
  · exact u1283

def b7624 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 140 296 145 112 112 240 368), lower := (rows 7 67 140 296 145 32 64 128 256), losses := [] }

theorem u7624 : Upper (D 8) (R 8) [6,65,136,288,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7624 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7625 : Route 9 := (fun mask => (mask,id))

def c7625 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7625 : Upper (D 8) (R 8) [6,65,136,288,160] 13 := by
  apply FastRouting.sound _ _ [6,65,136,288,160] 13 (by decide) (choices 1) [1,16,64] r7625 c7625
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1284
  · exact u1285
  · exact u1286

def r7626 : Route 9 := (fun mask => (mask,id))

def c7626 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7626 : Upper (D 8) (R 8) [6,65,136,288,192] 13 := by
  apply FastRouting.sound _ _ [6,65,136,288,192] 13 (by decide) (choices 1) [1,16] r7626 c7626
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1287
  · exact u1288

def b7627 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 484, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 164 25 56 480 480 480 480), lower := (rows 7 67 164 25 56 32 64 128 256), losses := [] }

theorem u7627 : Upper (D 8) (R 8) [6,65,160,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7627 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7628 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 7 67 164 25 88 416 480 416 416), lower := (rows 7 67 164 25 88 32 64 128 256), losses := [] }

theorem u7628 : Upper (D 8) (R 8) [6,65,160,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7628 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7629 : PairBound 9 := { available := 424, camps := [{ cop := 3, region := 420, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 164 25 112 424 488 424 424), lower := (rows 7 67 164 25 112 32 64 128 256), losses := [] }

theorem u7629 : Upper (D 8) (R 8) [6,65,160,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7629 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7630 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 7 67 164 25 152 352 352 480 352), lower := (rows 7 67 164 25 152 32 64 128 256), losses := [] }

theorem u7630 : Upper (D 8) (R 8) [6,65,160,17,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7630 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7631 : PairBound 9 := { available := 296, camps := [{ cop := 3, region := 420, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 164 25 208 296 360 424 296), lower := (rows 7 67 164 25 208 32 64 128 256), losses := [] }

theorem u7631 : Upper (D 8) (R 8) [6,65,160,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7631 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7632 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 228, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 164 25 280 224 224 224 480), lower := (rows 7 67 164 25 280 32 64 128 256), losses := [] }

theorem u7632 : Upper (D 8) (R 8) [6,65,160,17,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7632 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7633 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 228, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 164 25 304 232 232 232 488), lower := (rows 7 67 164 25 304 32 64 128 256), losses := [] }

theorem u7633 : Upper (D 8) (R 8) [6,65,160,17,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7633 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7634 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 164, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 164 25 336 168 232 168 424), lower := (rows 7 67 164 25 336 32 64 128 256), losses := [] }

theorem u7634 : Upper (D 8) (R 8) [6,65,160,17,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7634 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7635 : PairBound 9 := { available := 104, camps := [{ cop := 3, region := 228, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 164 25 400 104 104 232 360), lower := (rows 7 67 164 25 400 32 64 128 256), losses := [] }

theorem u7635 : Upper (D 8) (R 8) [6,65,160,17,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7635 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7636 : PairBound 9 := { available := 464, camps := [{ cop := 3, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 164 41 56 496 464 464 464), lower := (rows 7 67 164 41 56 32 64 128 256), losses := [] }

theorem u7636 : Upper (D 8) (R 8) [6,65,160,33,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7636 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7637 : PairBound 9 := { available := 432, camps := [{ cop := 3, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 164 41 88 432 496 432 432), lower := (rows 7 67 164 41 88 32 64 128 256), losses := [] }

theorem u7637 : Upper (D 8) (R 8) [6,65,160,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7637 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7638 : PairBound 9 := { available := 408, camps := [{ cop := 3, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 164 41 112 440 472 408 408), lower := (rows 7 67 164 41 112 32 64 128 256), losses := [] }

theorem u7638 : Upper (D 8) (R 8) [6,65,160,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7638 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7639 : PairBound 9 := { available := 368, camps := [{ cop := 3, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 164 41 152 368 368 496 368), lower := (rows 7 67 164 41 152 32 64 128 256), losses := [] }

theorem u7639 : Upper (D 8) (R 8) [6,65,160,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7639 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7640 : PairBound 9 := { available := 312, camps := [{ cop := 3, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 164 41 208 312 376 440 312), lower := (rows 7 67 164 41 208 32 64 128 256), losses := [] }

theorem u7640 : Upper (D 8) (R 8) [6,65,160,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7640 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7641 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 164 41 280 240 240 240 496), lower := (rows 7 67 164 41 280 32 64 128 256), losses := [] }

theorem u7641 : Upper (D 8) (R 8) [6,65,160,33,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7641 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7642 : PairBound 9 := { available := 216, camps := [{ cop := 3, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 164 41 304 248 216 216 472), lower := (rows 7 67 164 41 304 32 64 128 256), losses := [] }

theorem u7642 : Upper (D 8) (R 8) [6,65,160,33,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7642 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7643 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 164 41 336 184 248 184 440), lower := (rows 7 67 164 41 336 32 64 128 256), losses := [] }

theorem u7643 : Upper (D 8) (R 8) [6,65,160,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7643 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7644 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 164 41 400 120 120 248 376), lower := (rows 7 67 164 41 400 32 64 128 256), losses := [] }

theorem u7644 : Upper (D 8) (R 8) [6,65,160,33,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7644 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7645 : PairBound 9 := { available := 449, camps := [{ cop := 2, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 7 67 164 56 56 481 449 449 449), lower := (rows 7 67 164 56 56 32 64 128 256), losses := [] }

theorem u7645 : Upper (D 8) (R 8) [6,65,160,48,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7645 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7646 : PairBound 9 := { available := 424, camps := [{ cop := 1, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 7 67 164 56 81 424 488 424 424), lower := (rows 7 67 164 56 81 32 64 128 256), losses := [] }

theorem u7646 : Upper (D 8) (R 8) [6,65,160,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7646 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7647 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6)], upper := (rows 7 67 164 56 88 417 481 417 417), lower := (rows 7 67 164 56 88 32 64 128 256), losses := [] }

theorem u7647 : Upper (D 8) (R 8) [6,65,160,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7647 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7648 : PairBound 9 := { available := 393, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 67 164 56 112 425 457 393 393), lower := (rows 7 67 164 56 112 32 64 128 256), losses := [] }

theorem u7648 : Upper (D 8) (R 8) [6,65,160,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7648 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7649 : PairBound 9 := { available := 360, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 164 56 145 360 360 488 360), lower := (rows 7 67 164 56 145 32 64 128 256), losses := [] }

theorem u7649 : Upper (D 8) (R 8) [6,65,160,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7649 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7650 : PairBound 9 := { available := 353, camps := [{ cop := 2, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 7 67 164 56 152 353 353 481 353), lower := (rows 7 67 164 56 152 32 64 128 256), losses := [] }

theorem u7650 : Upper (D 8) (R 8) [6,65,160,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7650 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7651 : PairBound 9 := { available := 329, camps := [{ cop := 2, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 7 67 164 56 176 361 329 457 329), lower := (rows 7 67 164 56 176 32 64 128 256), losses := [] }

theorem u7651 : Upper (D 8) (R 8) [6,65,160,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7651 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7652 : Route 9 := (fun mask => (mask,id))

def c7652 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7652 : Upper (D 8) (R 8) [6,65,160,48,192] 13 := by
  apply FastRouting.sound _ _ [6,65,160,48,192] 13 (by decide) (choices 1) [1,8,256] r7652 c7652
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1289
  · exact u1290
  · exact u1291

def b7653 : PairBound 9 := { available := 232, camps := [{ cop := 4, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 164 56 273 232 232 232 488), lower := (rows 7 67 164 56 273 32 64 128 256), losses := [] }

theorem u7653 : Upper (D 8) (R 8) [6,65,160,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7653 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7654 : Route 9 := (fun mask => (mask,id))

def c7654 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7654 : Upper (D 8) (R 8) [6,65,160,48,264] 13 := by
  apply FastRouting.sound _ _ [6,65,160,48,264] 13 (by decide) (choices 1) [1,64,128] r7654 c7654
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1292
  · exact u1293
  · exact u1294

def b7655 : PairBound 9 := { available := 201, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 67 164 56 304 233 201 201 457), lower := (rows 7 67 164 56 304 32 64 128 256), losses := [] }

theorem u7655 : Upper (D 8) (R 8) [6,65,160,48,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7655 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7656 : Route 9 := (fun mask => (mask,id))

def c7656 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7656 : Upper (D 8) (R 8) [6,65,160,48,320] 13 := by
  apply FastRouting.sound _ _ [6,65,160,48,320] 13 (by decide) (choices 1) [1,8,128] r7656 c7656
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1295
  · exact u1296
  · exact u1297

def r7657 : Route 9 := (fun mask => (mask,id))

def c7657 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7657 : Upper (D 8) (R 8) [6,65,160,48,384] 13 := by
  apply FastRouting.sound _ _ [6,65,160,48,384] 13 (by decide) (choices 1) [1,8,64] r7657 c7657
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1298
  · exact u1299
  · exact u1300

def b7658 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 7 67 164 73 152 304 368 432 304), lower := (rows 7 67 164 73 152 32 64 128 256), losses := [] }

theorem u7658 : Upper (D 8) (R 8) [6,65,160,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7658 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7659 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 7 67 164 73 280 176 240 176 432), lower := (rows 7 67 164 73 280 32 64 128 256), losses := [] }

theorem u7659 : Upper (D 8) (R 8) [6,65,160,65,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7659 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7660 : PairBound 9 := { available := 184, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 7 67 164 73 304 184 248 184 440), lower := (rows 7 67 164 73 304 32 64 128 256), losses := [] }

theorem u7660 : Upper (D 8) (R 8) [6,65,160,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7660 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7661 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 7 67 164 73 400 56 120 184 312), lower := (rows 7 67 164 73 400 32 64 128 256), losses := [] }

theorem u7661 : Upper (D 8) (R 8) [6,65,160,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7661 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7662 : PairBound 9 := { available := 296, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 164 88 145 296 360 424 296), lower := (rows 7 67 164 88 145 32 64 128 256), losses := [] }

theorem u7662 : Upper (D 8) (R 8) [6,65,160,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7662 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7663 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6)], upper := (rows 7 67 164 88 152 289 353 417 289), lower := (rows 7 67 164 88 152 32 64 128 256), losses := [] }

theorem u7663 : Upper (D 8) (R 8) [6,65,160,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7663 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7664 : PairBound 9 := { available := 297, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 67 164 88 176 297 361 425 297), lower := (rows 7 67 164 88 176 32 64 128 256), losses := [] }

theorem u7664 : Upper (D 8) (R 8) [6,65,160,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7664 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7665 : PairBound 9 := { available := 168, camps := [{ cop := 4, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 164 88 273 168 232 168 424), lower := (rows 7 67 164 88 273 32 64 128 256), losses := [] }

theorem u7665 : Upper (D 8) (R 8) [6,65,160,80,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7665 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7666 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6)], upper := (rows 7 67 164 88 280 161 225 161 417), lower := (rows 7 67 164 88 280 32 64 128 256), losses := [] }

theorem u7666 : Upper (D 8) (R 8) [6,65,160,80,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7666 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7667 : Route 9 := (fun mask => (mask,id))

def c7667 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7667 : Upper (D 8) (R 8) [6,65,160,80,288] 13 := by
  apply FastRouting.sound _ _ [6,65,160,80,288] 13 (by decide) (choices 1) [1,8,128] r7667 c7667
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1301
  · exact u1302
  · exact u1303

def r7668 : Route 9 := (fun mask => (mask,id))

def c7668 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7668 : Upper (D 8) (R 8) [6,65,160,80,384] 13 := by
  apply FastRouting.sound _ _ [6,65,160,80,384] 13 (by decide) (choices 1) [1,8] r7668 c7668
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1304
  · exact u1305

def b7669 : PairBound 9 := { available := 312, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 164 104 145 312 376 440 312), lower := (rows 7 67 164 104 145 32 64 128 256), losses := [] }

theorem u7669 : Upper (D 8) (R 8) [6,65,160,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7669 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7670 : Route 9 := (fun mask => (mask,id))

def c7670 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7670 : Upper (D 8) (R 8) [6,65,160,96,136] 13 := by
  apply FastRouting.sound _ _ [6,65,160,96,136] 13 (by decide) (choices 1) [1,16,256] r7670 c7670
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1306
  · exact u1307
  · exact u1308

def b7671 : PairBound 9 := { available := 281, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 67 164 104 176 313 345 409 281), lower := (rows 7 67 164 104 176 32 64 128 256), losses := [] }

theorem u7671 : Upper (D 8) (R 8) [6,65,160,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7671 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7672 : PairBound 9 := { available := 184, camps := [{ cop := 4, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 164 104 273 184 248 184 440), lower := (rows 7 67 164 104 273 32 64 128 256), losses := [] }

theorem u7672 : Upper (D 8) (R 8) [6,65,160,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7672 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7673 : Route 9 := (fun mask => (mask,id))

def c7673 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7673 : Upper (D 8) (R 8) [6,65,160,96,264] 13 := by
  apply FastRouting.sound _ _ [6,65,160,96,264] 13 (by decide) (choices 1) [1,16,128] r7673 c7673
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1309
  · exact u1310
  · exact u1311

def r7674 : Route 9 := (fun mask => (mask,id))

def c7674 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7674 : Upper (D 8) (R 8) [6,65,160,96,288] 13 := by
  apply FastRouting.sound _ _ [6,65,160,96,288] 13 (by decide) (choices 1) [1,8,16,128] r7674 c7674
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1312
  · exact u1313
  · exact u1314
  · exact u1315

def r7675 : Route 9 := (fun mask => (mask,id))

def c7675 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7675 : Upper (D 8) (R 8) [6,65,160,96,384] 13 := by
  apply FastRouting.sound _ _ [6,65,160,96,384] 13 (by decide) (choices 1) [1,8,16] r7675 c7675
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1316
  · exact u1317
  · exact u1318

def b7676 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 164 137 280 112 112 240 368), lower := (rows 7 67 164 137 280 32 64 128 256), losses := [] }

theorem u7676 : Upper (D 8) (R 8) [6,65,160,129,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7676 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7677 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 164 137 304 120 120 248 376), lower := (rows 7 67 164 137 304 32 64 128 256), losses := [] }

theorem u7677 : Upper (D 8) (R 8) [6,65,160,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7677 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7678 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 164 137 336 56 120 184 312), lower := (rows 7 67 164 137 336 32 64 128 256), losses := [] }

theorem u7678 : Upper (D 8) (R 8) [6,65,160,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7678 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7679 : PairBound 9 := { available := 104, camps := [{ cop := 4, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 164 152 273 104 104 232 360), lower := (rows 7 67 164 152 273 32 64 128 256), losses := [] }

theorem u7679 : Upper (D 8) (R 8) [6,65,160,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7679 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u7679
end Delivery.IrregularNine14.P08

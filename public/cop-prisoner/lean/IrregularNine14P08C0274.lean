import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0099

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b16440 : PairBound 9 := { available := 184, camps := [{ cop := 4, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 259 38 196 41 81 184 248 184 440), lower := (rows 259 38 196 41 81 32 64 128 256), losses := [] }

theorem u16440 : Upper (D 8) (R 8) [258,36,192,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16440 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16441 : Route 9 := (fun mask => (mask,id))

def c16441 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u16441 : Upper (D 8) (R 8) [258,36,192,33,72] 13 := by
  apply FastRouting.sound _ _ [258,36,192,33,72] 13 (by decide) (choices 1) [1,16,128] r16441 c16441
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5960
  · exact u5961
  · exact u5962

def r16442 : Route 9 := (fun mask => (mask,id))

def c16442 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u16442 : Upper (D 8) (R 8) [258,36,192,33,96] 13 := by
  apply FastRouting.sound _ _ [258,36,192,33,96] 13 (by decide) (choices 1) [1,8,16,128] r16442 c16442
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5963
  · exact u5964
  · exact u5965
  · exact u5966

def b16443 : PairBound 9 := { available := 57, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 38 196 41 208 57 121 185 313), lower := (rows 259 38 196 41 208 32 64 128 256), losses := [] }

theorem u16443 : Upper (D 8) (R 8) [258,36,192,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16443 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16444 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 259 38 196 56 56 225 193 193 449), lower := (rows 259 38 196 56 56 32 64 128 256), losses := [] }

theorem u16444 : Upper (D 8) (R 8) [258,36,192,48,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16444 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16445 : PairBound 9 := { available := 169, camps := [{ cop := 4, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 259 38 196 56 81 169 233 169 425), lower := (rows 259 38 196 56 81 32 64 128 256), losses := [] }

theorem u16445 : Upper (D 8) (R 8) [258,36,192,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16445 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16446 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 291, targets := 64 }], pairs := [(0,6)], upper := (rows 259 38 196 56 88 161 225 161 417), lower := (rows 259 38 196 56 88 32 64 128 256), losses := [] }

theorem u16446 : Upper (D 8) (R 8) [258,36,192,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16446 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16447 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 38 196 56 112 169 201 137 393), lower := (rows 259 38 196 56 112 32 64 128 256), losses := [] }

theorem u16447 : Upper (D 8) (R 8) [258,36,192,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16447 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16448 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 38 196 56 208 41 105 169 297), lower := (rows 259 38 196 56 208 32 64 128 256), losses := [] }

theorem u16448 : Upper (D 8) (R 8) [258,36,192,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16448 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16449 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 259 38 196 73 152 49 113 177 305), lower := (rows 259 38 196 73 152 32 64 128 256), losses := [] }

theorem u16449 : Upper (D 8) (R 8) [258,36,192,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16449 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16450 : PairBound 9 := { available := 57, camps := [{ cop := 3, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 259 38 196 73 176 57 121 185 313), lower := (rows 259 38 196 73 176 32 64 128 256), losses := [] }

theorem u16450 : Upper (D 8) (R 8) [258,36,192,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16450 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16451 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 259 38 196 88 152 33 97 161 289), lower := (rows 259 38 196 88 152 32 64 128 256), losses := [] }

theorem u16451 : Upper (D 8) (R 8) [258,36,192,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16451 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16452 : Route 9 := (fun mask => (mask,id))

def c16452 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16452 : Upper (D 8) (R 8) [258,36,192,80,160] 13 := by
  apply FastRouting.sound _ _ [258,36,192,80,160] 13 (by decide) (choices 1) [1,8] r16452 c16452
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5967
  · exact u5968

theorem m16453_16 : Upper (D 8) (R 8) [258,36,192,96,160,16] 13 :=
  permutation_upper _ _ _ [258,36,192,96,160,8] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5970

def r16453 : Route 9 := (fun mask => (mask,id))

def c16453 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16453 : Upper (D 8) (R 8) [258,36,192,96,160] 13 := by
  apply FastRouting.sound _ _ [258,36,192,96,160] 13 (by decide) (choices 1) [1,8,16] r16453 c16453
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5969
  · exact u5970
  · exact m16453_16

def b16454 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 13 28 112 160 224 160 416), lower := (rows 259 67 13 28 112 32 64 128 256), losses := [] }

theorem u16454 : Upper (D 8) (R 8) [258,65,9,20,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16454 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16455 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 13 28 176 224 224 224 480), lower := (rows 259 67 13 28 176 32 64 128 256), losses := [] }

theorem u16455 : Upper (D 8) (R 8) [258,65,9,20,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16455 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16456 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 13 28 208 160 224 160 416), lower := (rows 259 67 13 28 208 32 64 128 256), losses := [] }

theorem u16456 : Upper (D 8) (R 8) [258,65,9,20,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16456 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16457 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 13 44 112 176 240 176 432), lower := (rows 259 67 13 44 112 32 64 128 256), losses := [] }

theorem u16457 : Upper (D 8) (R 8) [258,65,9,36,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16457 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16458 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 13 44 176 240 240 240 496), lower := (rows 259 67 13 44 176 32 64 128 256), losses := [] }

theorem u16458 : Upper (D 8) (R 8) [258,65,9,36,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16458 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16459 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 13 44 208 176 240 176 432), lower := (rows 259 67 13 44 208 32 64 128 256), losses := [] }

theorem u16459 : Upper (D 8) (R 8) [258,65,9,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16459 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16460 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 13 56 84 160 224 160 416), lower := (rows 259 67 13 56 84 32 64 128 256), losses := [] }

theorem u16460 : Upper (D 8) (R 8) [258,65,9,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16460 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16461 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 13 56 148 224 224 224 480), lower := (rows 259 67 13 56 148 32 64 128 256), losses := [] }

theorem u16461 : Upper (D 8) (R 8) [258,65,9,48,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16461 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16462 : PairBound 9 := { available := 164, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 13 56 208 164 228 164 420), lower := (rows 259 67 13 56 208 32 64 128 256), losses := [] }

theorem u16462 : Upper (D 8) (R 8) [258,65,9,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16462 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16463 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 259 67 13 76 176 176 240 176 432), lower := (rows 259 67 13 76 176 32 64 128 256), losses := [] }

theorem u16463 : Upper (D 8) (R 8) [258,65,9,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16463 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16464 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 13 88 52 160 224 160 416), lower := (rows 259 67 13 88 52 32 64 128 256), losses := [] }

theorem u16464 : Upper (D 8) (R 8) [258,65,9,80,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16464 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16465 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 13 88 148 160 224 160 416), lower := (rows 259 67 13 88 148 32 64 128 256), losses := [] }

theorem u16465 : Upper (D 8) (R 8) [258,65,9,80,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16465 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16466 : PairBound 9 := { available := 164, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 13 88 176 164 228 164 420), lower := (rows 259 67 13 88 176 32 64 128 256), losses := [] }

theorem u16466 : Upper (D 8) (R 8) [258,65,9,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16466 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16467 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 13 104 52 176 240 176 432), lower := (rows 259 67 13 104 52 32 64 128 256), losses := [] }

theorem u16467 : Upper (D 8) (R 8) [258,65,9,96,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16467 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16468 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 13 104 148 176 240 176 432), lower := (rows 259 67 13 104 148 32 64 128 256), losses := [] }

theorem u16468 : Upper (D 8) (R 8) [258,65,9,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16468 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16469 : PairBound 9 := { available := 180, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 13 104 176 180 244 180 436), lower := (rows 259 67 13 104 176 32 64 128 256), losses := [] }

theorem u16469 : Upper (D 8) (R 8) [258,65,9,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16469 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16470 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 13 140 112 176 240 176 432), lower := (rows 259 67 13 140 112 32 64 128 256), losses := [] }

theorem u16470 : Upper (D 8) (R 8) [258,65,9,132,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16470 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16471 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 13 140 176 112 112 240 368), lower := (rows 259 67 13 140 176 32 64 128 256), losses := [] }

theorem u16471 : Upper (D 8) (R 8) [258,65,9,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16471 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16472 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 13 140 208 48 112 176 304), lower := (rows 259 67 13 140 208 32 64 128 256), losses := [] }

theorem u16472 : Upper (D 8) (R 8) [258,65,9,132,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16472 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16473 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 13 152 52 224 224 224 480), lower := (rows 259 67 13 152 52 32 64 128 256), losses := [] }

theorem u16473 : Upper (D 8) (R 8) [258,65,9,144,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16473 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16474 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 13 152 84 160 224 160 416), lower := (rows 259 67 13 152 84 32 64 128 256), losses := [] }

theorem u16474 : Upper (D 8) (R 8) [258,65,9,144,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16474 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16475 : PairBound 9 := { available := 164, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 13 152 112 164 228 164 420), lower := (rows 259 67 13 152 112 32 64 128 256), losses := [] }

theorem u16475 : Upper (D 8) (R 8) [258,65,9,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16475 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16476 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 13 168 52 240 240 240 496), lower := (rows 259 67 13 168 52 32 64 128 256), losses := [] }

theorem u16476 : Upper (D 8) (R 8) [258,65,9,160,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16476 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16477 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 13 168 84 176 240 176 432), lower := (rows 259 67 13 168 84 32 64 128 256), losses := [] }

theorem u16477 : Upper (D 8) (R 8) [258,65,9,160,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16477 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16478 : PairBound 9 := { available := 180, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 13 168 112 180 244 180 436), lower := (rows 259 67 13 168 112 32 64 128 256), losses := [] }

theorem u16478 : Upper (D 8) (R 8) [258,65,9,160,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16478 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16479 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 13 168 148 112 112 240 368), lower := (rows 259 67 13 168 148 32 64 128 256), losses := [] }

theorem u16479 : Upper (D 8) (R 8) [258,65,9,160,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16479 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16480 : PairBound 9 := { available := 52, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 13 168 208 52 116 180 308), lower := (rows 259 67 13 168 208 32 64 128 256), losses := [] }

theorem u16480 : Upper (D 8) (R 8) [258,65,9,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16480 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16481 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 13 200 52 176 240 176 432), lower := (rows 259 67 13 200 52 32 64 128 256), losses := [] }

theorem u16481 : Upper (D 8) (R 8) [258,65,9,192,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16481 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16482 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 13 200 148 48 112 176 304), lower := (rows 259 67 13 200 148 32 64 128 256), losses := [] }

theorem u16482 : Upper (D 8) (R 8) [258,65,9,192,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16482 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16483 : PairBound 9 := { available := 52, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 13 200 176 52 116 180 308), lower := (rows 259 67 13 200 176 32 64 128 256), losses := [] }

theorem u16483 : Upper (D 8) (R 8) [258,65,9,192,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16483 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16484 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 20, targets := 64 }], pairs := [(2,6)], upper := (rows 259 67 28 41 52 224 224 224 480), lower := (rows 259 67 28 41 52 32 64 128 256), losses := [] }

theorem u16484 : Upper (D 8) (R 8) [258,65,24,33,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16484 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16485 : PairBound 9 := { available := 164, camps := [{ cop := 3, region := 212, targets := 1 }], pairs := [(2,0)], upper := (rows 259 67 28 41 112 164 228 164 420), lower := (rows 259 67 28 41 112 32 64 128 256), losses := [] }

theorem u16485 : Upper (D 8) (R 8) [258,65,24,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16485 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16486 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 212, targets := 1 }], pairs := [(2,0)], upper := (rows 259 67 28 41 148 224 224 224 480), lower := (rows 259 67 28 41 148 32 64 128 256), losses := [] }

theorem u16486 : Upper (D 8) (R 8) [258,65,24,33,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16486 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16487 : PairBound 9 := { available := 228, camps := [{ cop := 3, region := 212, targets := 1 }], pairs := [(2,0)], upper := (rows 259 67 28 41 176 228 228 228 484), lower := (rows 259 67 28 41 176 32 64 128 256), losses := [] }

theorem u16487 : Upper (D 8) (R 8) [258,65,24,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16487 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16488 : PairBound 9 := { available := 164, camps := [{ cop := 3, region := 212, targets := 1 }], pairs := [(2,0)], upper := (rows 259 67 28 41 208 164 228 164 420), lower := (rows 259 67 28 41 208 32 64 128 256), losses := [] }

theorem u16488 : Upper (D 8) (R 8) [258,65,24,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16488 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16489 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 259 67 28 44 81 160 224 160 416), lower := (rows 259 67 28 44 81 32 64 128 256), losses := [] }

theorem u16489 : Upper (D 8) (R 8) [258,65,24,36,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16489 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16490 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 259 67 28 44 112 161 225 161 417), lower := (rows 259 67 28 44 112 32 64 128 256), losses := [] }

theorem u16490 : Upper (D 8) (R 8) [258,65,24,36,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16490 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16491 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 108, targets := 1 }], pairs := [(2,0)], upper := (rows 259 67 28 44 145 224 224 224 480), lower := (rows 259 67 28 44 145 32 64 128 256), losses := [] }

theorem u16491 : Upper (D 8) (R 8) [258,65,24,36,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16491 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16492 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 259 67 28 44 176 225 225 225 481), lower := (rows 259 67 28 44 176 32 64 128 256), losses := [] }

theorem u16492 : Upper (D 8) (R 8) [258,65,24,36,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16492 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16493 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 259 67 28 44 208 161 225 161 417), lower := (rows 259 67 28 44 208 32 64 128 256), losses := [] }

theorem u16493 : Upper (D 8) (R 8) [258,65,24,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16493 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16494 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 259 67 28 73 148 160 224 160 416), lower := (rows 259 67 28 73 148 32 64 128 256), losses := [] }

theorem u16494 : Upper (D 8) (R 8) [258,65,24,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16494 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16495 : PairBound 9 := { available := 164, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 259 67 28 73 176 164 228 164 420), lower := (rows 259 67 28 73 176 32 64 128 256), losses := [] }

theorem u16495 : Upper (D 8) (R 8) [258,65,24,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16495 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16496 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 259 67 28 76 176 161 225 161 417), lower := (rows 259 67 28 76 176 32 64 128 256), losses := [] }

theorem u16496 : Upper (D 8) (R 8) [258,65,24,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16496 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16497 : PairBound 9 := { available := 164, camps := [{ cop := 4, region := 108, targets := 1 }], pairs := [(2,0)], upper := (rows 259 67 28 104 145 164 228 164 420), lower := (rows 259 67 28 104 145 32 64 128 256), losses := [] }

theorem u16497 : Upper (D 8) (R 8) [258,65,24,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16497 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16498 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 259 67 28 104 148 161 225 161 417), lower := (rows 259 67 28 104 148 32 64 128 256), losses := [] }

theorem u16498 : Upper (D 8) (R 8) [258,65,24,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16498 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16499 : Route 9 := (fun mask => (mask,id))

def c16499 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u16499 : Upper (D 8) (R 8) [258,65,24,96,160] 13 := by
  apply FastRouting.sound _ _ [258,65,24,96,160] 13 (by decide) (choices 1) [1,4,128] r16499 c16499
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5971
  · exact u5972
  · exact u5973

#print axioms u16499
end Delivery.IrregularNine14.P08

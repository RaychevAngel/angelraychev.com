import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0092
import IrregularNine14P09C0093

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b8100 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 6, targets := 384 },{ cop := 1, region := 408, targets := 32 }], pairs := [(1,7),(1,8),(2,7),(2,8),(3,5)], upper := (rows 97 7 100 152 280 419 451 387 387), lower := (rows 97 7 100 152 280 32 64 128 256), losses := [] }

theorem u8100 : Upper (D 9) (R 9) [96,5,96,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8100 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8101 : PairBound 9 := { available := 448, camps := [{ cop := 2, region := 2, targets := 448 },{ cop := 0, region := 390, targets := 32 }], pairs := [(1,5),(1,6),(1,7),(1,8),(2,5)], upper := (rows 97 7 133 26 56 480 448 448 448), lower := (rows 97 7 133 26 56 32 64 128 256), losses := [] }

theorem u8101 : Upper (D 9) (R 9) [96,5,129,18,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8101 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8102 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 26, targets := 352 }], pairs := [(1,5),(1,6),(1,8),(3,5),(3,6)], upper := (rows 97 7 133 26 152 352 352 480 352), lower := (rows 97 7 133 26 152 32 64 128 256), losses := [] }

theorem u8102 : Upper (D 9) (R 9) [96,5,129,18,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8102 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8103 : PairBound 9 := { available := 328, camps := [{ cop := 2, region := 2, targets := 480 },{ cop := 1, region := 504, targets := 1 }], pairs := [(1,5),(1,6),(1,7),(1,8),(3,0)], upper := (rows 97 7 133 26 176 360 328 456 328), lower := (rows 97 7 133 26 176 32 64 128 256), losses := [] }

theorem u8103 : Upper (D 9) (R 9) [96,5,129,18,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8103 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8104 : PairBound 9 := { available := 480, camps := [{ cop := 2, region := 2, targets := 480 },{ cop := 1, region := 504, targets := 1 }], pairs := [(1,5),(1,6),(1,7),(1,8),(3,0)], upper := (rows 97 7 133 26 280 480 480 480 480), lower := (rows 97 7 133 26 280 32 64 128 256), losses := [] }

theorem u8104 : Upper (D 9) (R 9) [96,5,129,18,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8104 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8105 : PairBound 9 := { available := 456, camps := [{ cop := 2, region := 2, targets := 480 },{ cop := 1, region := 504, targets := 1 }], pairs := [(1,5),(1,6),(1,7),(1,8),(3,0)], upper := (rows 97 7 133 26 304 488 456 456 456), lower := (rows 97 7 133 26 304 32 64 128 256), losses := [] }

theorem u8105 : Upper (D 9) (R 9) [96,5,129,18,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8105 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8106 : PairBound 9 := { available := 360, camps := [{ cop := 2, region := 2, targets := 480 },{ cop := 1, region := 504, targets := 1 }], pairs := [(1,5),(1,6),(1,7),(1,8),(3,0)], upper := (rows 97 7 133 26 400 360 360 488 360), lower := (rows 97 7 133 26 400 32 64 128 256), losses := [] }

theorem u8106 : Upper (D 9) (R 9) [96,5,129,18,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8106 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8107 : PairBound 9 := { available := 400, camps := [{ cop := 2, region := 2, targets := 480 },{ cop := 1, region := 504, targets := 1 }], pairs := [(1,5),(1,6),(1,7),(1,8),(3,0)], upper := (rows 97 7 133 42 88 432 464 400 400), lower := (rows 97 7 133 42 88 32 64 128 256), losses := [] }

theorem u8107 : Upper (D 9) (R 9) [96,5,129,34,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8107 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8108 : PairBound 9 := { available := 336, camps := [{ cop := 2, region := 2, targets := 480 },{ cop := 1, region := 504, targets := 1 }], pairs := [(1,5),(1,6),(1,7),(1,8),(3,0)], upper := (rows 97 7 133 42 152 368 336 464 336), lower := (rows 97 7 133 42 152 32 64 128 256), losses := [] }

theorem u8108 : Upper (D 9) (R 9) [96,5,129,34,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8108 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8109 : PairBound 9 := { available := 280, camps := [{ cop := 2, region := 2, targets := 480 },{ cop := 1, region := 504, targets := 1 }], pairs := [(1,5),(1,6),(1,7),(1,8),(3,0)], upper := (rows 97 7 133 42 208 312 344 408 280), lower := (rows 97 7 133 42 208 32 64 128 256), losses := [] }

theorem u8109 : Upper (D 9) (R 9) [96,5,129,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8109 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8110 : PairBound 9 := { available := 464, camps := [{ cop := 2, region := 2, targets := 480 },{ cop := 1, region := 504, targets := 1 }], pairs := [(1,5),(1,6),(1,7),(1,8),(3,0)], upper := (rows 97 7 133 42 280 496 464 464 464), lower := (rows 97 7 133 42 280 32 64 128 256), losses := [] }

theorem u8110 : Upper (D 9) (R 9) [96,5,129,34,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8110 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8111 : PairBound 9 := { available := 408, camps := [{ cop := 2, region := 2, targets := 480 },{ cop := 1, region := 504, targets := 1 }], pairs := [(1,5),(1,6),(1,7),(1,8),(3,0)], upper := (rows 97 7 133 42 336 440 472 408 408), lower := (rows 97 7 133 42 336 32 64 128 256), losses := [] }

theorem u8111 : Upper (D 9) (R 9) [96,5,129,34,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8111 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8112 : PairBound 9 := { available := 344, camps := [{ cop := 2, region := 2, targets := 480 },{ cop := 1, region := 504, targets := 1 }], pairs := [(1,5),(1,6),(1,7),(1,8),(3,0)], upper := (rows 97 7 133 42 400 376 344 472 344), lower := (rows 97 7 133 42 400 32 64 128 256), losses := [] }

theorem u8112 : Upper (D 9) (R 9) [96,5,129,34,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8112 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8113 : PairBound 9 := { available := 328, camps := [{ cop := 2, region := 18, targets := 352 }], pairs := [(1,5),(1,6),(1,8),(4,5),(4,6)], upper := (rows 97 7 133 56 146 360 328 456 328), lower := (rows 97 7 133 56 146 32 64 128 256), losses := [] }

theorem u8113 : Upper (D 9) (R 9) [96,5,129,48,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8113 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8114 : PairBound 9 := { available := 322, camps := [{ cop := 0, region := 390, targets := 32 },{ cop := 1, region := 504, targets := 1 },{ cop := 2, region := 2, targets := 64 }], pairs := [(1,5),(1,6),(2,5),(3,0),(4,0)], upper := (rows 97 7 133 56 152 354 322 450 322), lower := (rows 97 7 133 56 152 32 64 128 256), losses := [] }

theorem u8114 : Upper (D 9) (R 9) [96,5,129,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8114 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8115 : PairBound 9 := { available := 266, camps := [{ cop := 2, region := 2, targets := 480 },{ cop := 1, region := 504, targets := 1 }], pairs := [(1,5),(1,6),(1,7),(1,8),(3,0)], upper := (rows 97 7 133 56 208 298 330 394 266), lower := (rows 97 7 133 56 208 32 64 128 256), losses := [] }

theorem u8115 : Upper (D 9) (R 9) [96,5,129,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8115 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8116 : PairBound 9 := { available := 456, camps := [{ cop := 2, region := 2, targets := 480 },{ cop := 1, region := 504, targets := 1 }], pairs := [(1,5),(1,6),(1,7),(1,8),(3,0)], upper := (rows 97 7 133 56 274 488 456 456 456), lower := (rows 97 7 133 56 274 32 64 128 256), losses := [] }

theorem u8116 : Upper (D 9) (R 9) [96,5,129,48,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8116 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8117 : PairBound 9 := { available := 450, camps := [{ cop := 2, region := 2, targets := 448 },{ cop := 0, region := 390, targets := 32 }], pairs := [(1,5),(1,6),(1,7),(1,8),(2,5)], upper := (rows 97 7 133 56 280 482 450 450 450), lower := (rows 97 7 133 56 280 32 64 128 256), losses := [] }

theorem u8117 : Upper (D 9) (R 9) [96,5,129,48,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8117 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8118 : PairBound 9 := { available := 394, camps := [{ cop := 2, region := 2, targets := 480 },{ cop := 1, region := 504, targets := 1 }], pairs := [(1,5),(1,6),(1,7),(1,8),(3,0)], upper := (rows 97 7 133 56 336 426 458 394 394), lower := (rows 97 7 133 56 336 32 64 128 256), losses := [] }

theorem u8118 : Upper (D 9) (R 9) [96,5,129,48,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8118 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8119 : PairBound 9 := { available := 330, camps := [{ cop := 2, region := 2, targets := 480 },{ cop := 1, region := 504, targets := 1 }], pairs := [(1,5),(1,6),(1,7),(1,8),(3,0)], upper := (rows 97 7 133 56 400 362 330 458 330), lower := (rows 97 7 133 56 400 32 64 128 256), losses := [] }

theorem u8119 : Upper (D 9) (R 9) [96,5,129,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8119 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8120 : PairBound 9 := { available := 368, camps := [{ cop := 2, region := 10, targets := 352 }], pairs := [(1,5),(1,6),(1,8),(3,5),(3,6)], upper := (rows 97 7 133 138 280 368 368 496 368), lower := (rows 97 7 133 138 280 32 64 128 256), losses := [] }

theorem u8120 : Upper (D 9) (R 9) [96,5,129,130,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8120 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8121 : PairBound 9 := { available := 344, camps := [{ cop := 2, region := 10, targets := 352 }], pairs := [(1,5),(1,6),(1,8),(3,5),(3,6)], upper := (rows 97 7 133 138 304 376 344 472 344), lower := (rows 97 7 133 138 304 32 64 128 256), losses := [] }

theorem u8121 : Upper (D 9) (R 9) [96,5,129,130,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8121 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8122 : PairBound 9 := { available := 360, camps := [{ cop := 2, region := 2, targets := 480 },{ cop := 1, region := 504, targets := 1 }], pairs := [(1,5),(1,6),(1,7),(1,8),(3,0)], upper := (rows 97 7 133 152 274 360 360 488 360), lower := (rows 97 7 133 152 274 32 64 128 256), losses := [] }

theorem u8122 : Upper (D 9) (R 9) [96,5,129,144,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8122 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8123 : PairBound 9 := { available := 354, camps := [{ cop := 2, region := 2, targets := 352 },{ cop := 1, region := 504, targets := 1 }], pairs := [(1,5),(1,6),(1,8),(3,0),(4,0)], upper := (rows 97 7 133 152 280 354 354 482 354), lower := (rows 97 7 133 152 280 32 64 128 256), losses := [] }

theorem u8123 : Upper (D 9) (R 9) [96,5,129,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8123 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8124 : PairBound 9 := { available := 330, camps := [{ cop := 2, region := 2, targets := 480 },{ cop := 1, region := 504, targets := 1 }], pairs := [(1,5),(1,6),(1,7),(1,8),(3,0)], upper := (rows 97 7 133 152 304 362 330 458 330), lower := (rows 97 7 133 152 304 32 64 128 256), losses := [] }

theorem u8124 : Upper (D 9) (R 9) [96,5,129,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8124 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8125 : PairBound 9 := { available := 344, camps := [{ cop := 2, region := 2, targets := 480 },{ cop := 1, region := 504, targets := 1 }], pairs := [(1,5),(1,6),(1,7),(1,8),(3,0)], upper := (rows 97 7 133 168 274 376 344 472 344), lower := (rows 97 7 133 168 274 32 64 128 256), losses := [] }

theorem u8125 : Upper (D 9) (R 9) [96,5,129,160,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8125 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8126 : PairBound 9 := { available := 338, camps := [{ cop := 2, region := 2, targets := 480 },{ cop := 1, region := 504, targets := 1 }], pairs := [(1,5),(1,6),(1,7),(1,8),(3,0)], upper := (rows 97 7 133 168 280 370 338 466 338), lower := (rows 97 7 133 168 280 32 64 128 256), losses := [] }

theorem u8126 : Upper (D 9) (R 9) [96,5,129,160,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8126 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8127 : PairBound 9 := { available := 282, camps := [{ cop := 2, region := 2, targets := 480 },{ cop := 1, region := 504, targets := 1 }], pairs := [(1,5),(1,6),(1,7),(1,8),(3,0)], upper := (rows 97 7 133 168 336 314 346 410 282), lower := (rows 97 7 133 168 336 32 64 128 256), losses := [] }

theorem u8127 : Upper (D 9) (R 9) [96,5,129,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8127 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8128 : PairBound 9 := { available := 216, camps := [{ cop := 2, region := 2, targets := 480 },{ cop := 1, region := 504, targets := 1 }], pairs := [(1,5),(1,6),(1,7),(1,8),(3,0)], upper := (rows 97 7 133 266 304 248 216 216 472), lower := (rows 97 7 133 266 304 32 64 128 256), losses := [] }

theorem u8128 : Upper (D 9) (R 9) [96,5,129,258,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8128 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8129 : PairBound 9 := { available := 120, camps := [{ cop := 2, region := 2, targets := 480 },{ cop := 1, region := 504, targets := 1 }], pairs := [(1,5),(1,6),(1,7),(1,8),(3,0)], upper := (rows 97 7 133 266 400 120 120 248 376), lower := (rows 97 7 133 266 400 32 64 128 256), losses := [] }

theorem u8129 : Upper (D 9) (R 9) [96,5,129,258,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8129 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8130 : PairBound 9 := { available := 154, camps := [{ cop := 2, region := 2, targets := 480 },{ cop := 1, region := 504, targets := 1 }], pairs := [(1,5),(1,6),(1,7),(1,8),(3,0)], upper := (rows 97 7 133 296 336 186 218 154 410), lower := (rows 97 7 133 296 336 32 64 128 256), losses := [] }

theorem u8130 : Upper (D 9) (R 9) [96,5,129,288,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8130 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8131 : PairBound 9 := { available := 90, camps := [{ cop := 2, region := 2, targets := 480 },{ cop := 1, region := 504, targets := 1 }], pairs := [(1,5),(1,6),(1,7),(1,8),(3,0)], upper := (rows 97 7 133 296 400 122 90 218 346), lower := (rows 97 7 133 296 400 32 64 128 256), losses := [] }

theorem u8131 : Upper (D 9) (R 9) [96,5,129,288,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8131 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8132 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 1, region := 484, targets := 1 },{ cop := 3, region := 496, targets := 1 },{ cop := 4, region := 361, targets := 128 }], pairs := [(0,7),(1,7),(2,0),(3,7),(4,0)], upper := (rows 97 7 134 25 152 352 352 480 352), lower := (rows 97 7 134 25 152 32 64 128 256), losses := [] }

theorem u8132 : Upper (D 9) (R 9) [96,5,130,17,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8132 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8133 : PairBound 9 := { available := 328, camps := [{ cop := 3, region := 454, targets := 32 },{ cop := 4, region := 329, targets := 128 },{ cop := 3, region := 496, targets := 1 }], pairs := [(0,7),(1,5),(2,5),(3,7),(4,0)], upper := (rows 97 7 134 25 176 360 328 456 328), lower := (rows 97 7 134 25 176 32 64 128 256), losses := [] }

theorem u8133 : Upper (D 9) (R 9) [96,5,130,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8133 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m8134_256 : Upper (D 9) (R 9) [96,5,130,17,264,256] 13 :=
  permutation_upper _ _ _ [96,5,130,17,264,128] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5551

def r8134 : Route 9 := (fun mask => (mask,id))

def c8134 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u8134 : Upper (D 9) (R 9) [96,5,130,17,264] 13 := by
  apply FastRouting.sound _ _ [96,5,130,17,264] 13 (by decide) (choices 1) [64,128,256] r8134 c8134
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5550
  · exact u5551
  · exact m8134_256

def r8135 : Route 9 := (fun mask => (mask,id))

def c8135 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | _ => 0)

theorem u8135 : Upper (D 9) (R 9) [96,5,130,17,288] 13 := by
  apply FastRouting.sound _ _ [96,5,130,17,288] 13 (by decide) (choices 1) [8,64,128,256] r8135 c8135
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5552
  · exact u5553
  · exact u5554
  · exact u5555

def r8136 : Route 9 := (fun mask => (mask,id))

def c8136 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u8136 : Upper (D 9) (R 9) [96,5,130,17,384] 13 := by
  apply FastRouting.sound _ _ [96,5,130,17,384] 13 (by decide) (choices 1) [8,64,256] r8136 c8136
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5556
  · exact u5557
  · exact u5558

def b8137 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 24, targets := 384 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,7),(3,8),(4,7),(4,8)], upper := (rows 97 7 134 41 88 432 464 400 400), lower := (rows 97 7 134 41 88 32 64 128 256), losses := [] }

theorem u8137 : Upper (D 9) (R 9) [96,5,130,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8137 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8138 : PairBound 9 := { available := 336, camps := [{ cop := 0, region := 8, targets := 448 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(3,6),(3,7),(3,8)], upper := (rows 97 7 134 41 152 368 336 464 336), lower := (rows 97 7 134 41 152 32 64 128 256), losses := [] }

theorem u8138 : Upper (D 9) (R 9) [96,5,130,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8138 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8139 : PairBound 9 := { available := 280, camps := [{ cop := 0, region := 8, targets := 448 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(3,6),(3,7),(3,8)], upper := (rows 97 7 134 41 208 312 344 408 280), lower := (rows 97 7 134 41 208 32 64 128 256), losses := [] }

theorem u8139 : Upper (D 9) (R 9) [96,5,130,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8139 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8140 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 8, targets := 448 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(3,6),(3,7),(3,8)], upper := (rows 97 7 134 41 280 496 464 464 464), lower := (rows 97 7 134 41 280 32 64 128 256), losses := [] }

theorem u8140 : Upper (D 9) (R 9) [96,5,130,33,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8140 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8141 : PairBound 9 := { available := 408, camps := [{ cop := 0, region := 8, targets := 448 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(3,6),(3,7),(3,8)], upper := (rows 97 7 134 41 336 440 472 408 408), lower := (rows 97 7 134 41 336 32 64 128 256), losses := [] }

theorem u8141 : Upper (D 9) (R 9) [96,5,130,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8141 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8142 : PairBound 9 := { available := 344, camps := [{ cop := 0, region := 8, targets := 448 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(3,6),(3,7),(3,8)], upper := (rows 97 7 134 41 400 376 344 472 344), lower := (rows 97 7 134 41 400 32 64 128 256), losses := [] }

theorem u8142 : Upper (D 9) (R 9) [96,5,130,33,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8142 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8143 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 24, targets := 384 },{ cop := 0, region := 24, targets := 1 }], pairs := [(3,0),(3,7),(3,8),(4,7),(4,8)], upper := (rows 97 7 134 56 88 417 449 385 385), lower := (rows 97 7 134 56 88 32 64 128 256), losses := [] }

theorem u8143 : Upper (D 9) (R 9) [96,5,130,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8143 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8144 : PairBound 9 := { available := 328, camps := [{ cop := 4, region := 6, targets := 352 }], pairs := [(1,5),(1,6),(1,8),(2,5),(2,6)], upper := (rows 97 7 134 56 145 360 328 456 328), lower := (rows 97 7 134 56 145 32 64 128 256), losses := [] }

theorem u8144 : Upper (D 9) (R 9) [96,5,130,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8144 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8145 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 390, targets := 32 },{ cop := 2, region := 355, targets := 128 },{ cop := 4, region := 361, targets := 128 }], pairs := [(0,7),(1,5),(1,7),(2,5),(3,7)], upper := (rows 97 7 134 56 152 353 321 449 321), lower := (rows 97 7 134 56 152 32 64 128 256), losses := [] }

theorem u8145 : Upper (D 9) (R 9) [96,5,130,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8145 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8146 : Route 9 := (fun mask => (mask,id))

def c8146 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8146 : Upper (D 9) (R 9) [96,5,130,48,192] 13 := by
  apply FastRouting.sound _ _ [96,5,130,48,192] 13 (by decide) (choices 1) [1,8,256] r8146 c8146
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5559
  · exact u5560
  · exact u5561

def r8147 : Route 9 := (fun mask => (mask,id))

def c8147 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | _ => 0)

theorem u8147 : Upper (D 9) (R 9) [96,5,130,48,257] 13 := by
  apply FastRouting.sound _ _ [96,5,130,48,257] 13 (by decide) (choices 1) [8,64,128,256] r8147 c8147
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5562
  · exact u5563
  · exact u5564
  · exact u5565

def r8148 : Route 9 := (fun mask => (mask,id))

def c8148 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u8148 : Upper (D 9) (R 9) [96,5,130,48,264] 13 := by
  apply FastRouting.sound _ _ [96,5,130,48,264] 13 (by decide) (choices 1) [1,64,128,256] r8148 c8148
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5566
  · exact u5567
  · exact u5568
  · exact u5569

def r8149 : Route 9 := (fun mask => (mask,id))

def c8149 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u8149 : Upper (D 9) (R 9) [96,5,130,48,320] 13 := by
  apply FastRouting.sound _ _ [96,5,130,48,320] 13 (by decide) (choices 1) [1,8,128,256] r8149 c8149
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5570
  · exact u5571
  · exact u5572
  · exact u5573

def r8150 : Route 9 := (fun mask => (mask,id))

def c8150 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u8150 : Upper (D 9) (R 9) [96,5,130,48,384] 13 := by
  apply FastRouting.sound _ _ [96,5,130,48,384] 13 (by decide) (choices 1) [1,8,64,256] r8150 c8150
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5574
  · exact u5575
  · exact u5576
  · exact u5577

def b8151 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 8, targets := 384 },{ cop := 3, region := 1, targets := 384 },{ cop := 0, region := 8, targets := 1 }], pairs := [(0,7),(0,8),(3,0),(3,7),(3,8)], upper := (rows 97 7 134 104 152 305 337 401 273), lower := (rows 97 7 134 104 152 32 64 128 256), losses := [] }

theorem u8151 : Upper (D 9) (R 9) [96,5,130,96,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8151 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8152 : PairBound 9 := { available := 408, camps := [{ cop := 0, region := 8, targets := 384 },{ cop := 3, region := 1, targets := 384 },{ cop := 0, region := 8, targets := 1 }], pairs := [(0,7),(0,8),(3,0),(3,7),(3,8)], upper := (rows 97 7 134 104 273 440 472 408 408), lower := (rows 97 7 134 104 273 32 64 128 256), losses := [] }

theorem u8152 : Upper (D 9) (R 9) [96,5,130,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8152 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8153 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 8, targets := 384 },{ cop := 3, region := 1, targets := 384 },{ cop := 0, region := 8, targets := 1 }], pairs := [(0,7),(0,8),(3,0),(3,7),(3,8)], upper := (rows 97 7 134 104 280 433 465 401 401), lower := (rows 97 7 134 104 280 32 64 128 256), losses := [] }

theorem u8153 : Upper (D 9) (R 9) [96,5,130,96,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8153 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8154 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 8, targets := 384 },{ cop := 3, region := 1, targets := 384 },{ cop := 0, region := 8, targets := 1 }], pairs := [(0,7),(0,8),(3,0),(3,7),(3,8)], upper := (rows 97 7 134 104 400 313 345 409 281), lower := (rows 97 7 134 104 400 32 64 128 256), losses := [] }

theorem u8154 : Upper (D 9) (R 9) [96,5,130,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8154 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8155 : PairBound 9 := { available := 368, camps := [{ cop := 3, region := 6, targets := 352 }], pairs := [(1,5),(1,6),(1,8),(2,5),(2,6)], upper := (rows 97 7 134 137 280 368 368 496 368), lower := (rows 97 7 134 137 280 32 64 128 256), losses := [] }

theorem u8155 : Upper (D 9) (R 9) [96,5,130,129,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8155 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8156 : PairBound 9 := { available := 344, camps := [{ cop := 3, region := 6, targets := 352 }], pairs := [(1,5),(1,6),(1,8),(2,5),(2,6)], upper := (rows 97 7 134 137 304 376 344 472 344), lower := (rows 97 7 134 137 304 32 64 128 256), losses := [] }

theorem u8156 : Upper (D 9) (R 9) [96,5,130,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8156 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8157 : Route 9 := (fun mask => (mask,id))

def c8157 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u8157 : Upper (D 9) (R 9) [96,5,130,144,257] 13 := by
  apply FastRouting.sound _ _ [96,5,130,144,257] 13 (by decide) (choices 1) [8,64,256] r8157 c8157
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5578
  · exact u5579
  · exact u5580

def r8158 : Route 9 := (fun mask => (mask,id))

def c8158 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u8158 : Upper (D 9) (R 9) [96,5,130,144,264] 13 := by
  apply FastRouting.sound _ _ [96,5,130,144,264] 13 (by decide) (choices 1) [1,64,256] r8158 c8158
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5581
  · exact u5582
  · exact u5583

def r8159 : Route 9 := (fun mask => (mask,id))

def c8159 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u8159 : Upper (D 9) (R 9) [96,5,130,144,288] 13 := by
  apply FastRouting.sound _ _ [96,5,130,144,288] 13 (by decide) (choices 1) [1,8,64,256] r8159 c8159
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5584
  · exact u5585
  · exact u5586
  · exact u5587

#print axioms u8159
end Delivery.IrregularNine14.P09

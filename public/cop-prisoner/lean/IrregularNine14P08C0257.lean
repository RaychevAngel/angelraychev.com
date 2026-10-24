import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0089

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b15420 : PairBound 9 := { available := 51, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 100 168 280 51 115 179 307), lower := (rows 193 7 100 168 280 32 64 128 256), losses := [] }

theorem u15420 : Upper (D 8) (R 8) [192,5,96,160,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15420 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15421 : PairBound 9 := { available := 27, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 100 168 304 59 91 155 283), lower := (rows 193 7 100 168 304 32 64 128 256), losses := [] }

theorem u15421 : Upper (D 8) (R 8) [192,5,96,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15421 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15422 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 196 25 304 42 106 170 298), lower := (rows 193 7 196 25 304 32 64 128 256), losses := [] }

theorem u15422 : Upper (D 8) (R 8) [192,5,192,17,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15422 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15423 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 196 26 56 289 353 417 289), lower := (rows 193 7 196 26 56 32 64 128 256), losses := [] }

theorem u15423 : Upper (D 8) (R 8) [192,5,192,18,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15423 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15424 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 196 26 280 33 97 161 289), lower := (rows 193 7 196 26 280 32 64 128 256), losses := [] }

theorem u15424 : Upper (D 8) (R 8) [192,5,192,18,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15424 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15425 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 196 26 304 41 105 169 297), lower := (rows 193 7 196 26 304 32 64 128 256), losses := [] }

theorem u15425 : Upper (D 8) (R 8) [192,5,192,18,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15425 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15426 : PairBound 9 := { available := 312, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 196 41 50 312 376 440 312), lower := (rows 193 7 196 41 50 32 64 128 256), losses := [] }

theorem u15426 : Upper (D 8) (R 8) [192,5,192,33,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15426 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15427 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 196 41 274 56 120 184 312), lower := (rows 193 7 196 41 274 32 64 128 256), losses := [] }

theorem u15427 : Upper (D 8) (R 8) [192,5,192,33,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15427 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15428 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 196 41 280 50 114 178 306), lower := (rows 193 7 196 41 280 32 64 128 256), losses := [] }

theorem u15428 : Upper (D 8) (R 8) [192,5,192,33,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15428 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15429 : PairBound 9 := { available := 58, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 196 41 304 58 122 186 314), lower := (rows 193 7 196 41 304 32 64 128 256), losses := [] }

theorem u15429 : Upper (D 8) (R 8) [192,5,192,33,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15429 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15430 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 196 42 273 56 120 184 312), lower := (rows 193 7 196 42 273 32 64 128 256), losses := [] }

theorem u15430 : Upper (D 8) (R 8) [192,5,192,34,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15430 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15431 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 196 42 280 49 113 177 305), lower := (rows 193 7 196 42 280 32 64 128 256), losses := [] }

theorem u15431 : Upper (D 8) (R 8) [192,5,192,34,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15431 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15432 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 196 42 304 57 121 185 313), lower := (rows 193 7 196 42 304 32 64 128 256), losses := [] }

theorem u15432 : Upper (D 8) (R 8) [192,5,192,34,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15432 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15433 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 196 56 273 42 106 170 298), lower := (rows 193 7 196 56 273 32 64 128 256), losses := [] }

theorem u15433 : Upper (D 8) (R 8) [192,5,192,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15433 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15434 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 196 56 274 41 105 169 297), lower := (rows 193 7 196 56 274 32 64 128 256), losses := [] }

theorem u15434 : Upper (D 8) (R 8) [192,5,192,48,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15434 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15435 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 196 56 280 35 99 163 291), lower := (rows 193 7 196 56 280 32 64 128 256), losses := [] }

theorem u15435 : Upper (D 8) (R 8) [192,5,192,48,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15435 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15436 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 261 26 56 224 224 224 480), lower := (rows 193 7 261 26 56 32 64 128 256), losses := [] }

theorem u15436 : Upper (D 8) (R 8) [192,5,257,18,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15436 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15437 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 261 26 112 168 232 168 424), lower := (rows 193 7 261 26 112 32 64 128 256), losses := [] }

theorem u15437 : Upper (D 8) (R 8) [192,5,257,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15437 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15438 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 261 42 88 176 240 176 432), lower := (rows 193 7 261 42 88 32 64 128 256), losses := [] }

theorem u15438 : Upper (D 8) (R 8) [192,5,257,34,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15438 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15439 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 261 42 112 184 248 184 440), lower := (rows 193 7 261 42 112 32 64 128 256), losses := [] }

theorem u15439 : Upper (D 8) (R 8) [192,5,257,34,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15439 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15440 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 261 56 82 168 232 168 424), lower := (rows 193 7 261 56 82 32 64 128 256), losses := [] }

theorem u15440 : Upper (D 8) (R 8) [192,5,257,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15440 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15441 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 261 74 152 48 112 176 304), lower := (rows 193 7 261 74 152 32 64 128 256), losses := [] }

theorem u15441 : Upper (D 8) (R 8) [192,5,257,66,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15441 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15442 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 261 74 176 56 120 184 312), lower := (rows 193 7 261 74 176 32 64 128 256), losses := [] }

theorem u15442 : Upper (D 8) (R 8) [192,5,257,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15442 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15443 : PairBound 9 := { available := 42, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 261 88 176 42 106 170 298), lower := (rows 193 7 261 88 176 32 64 128 256), losses := [] }

theorem u15443 : Upper (D 8) (R 8) [192,5,257,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15443 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15444 : PairBound 9 := { available := 58, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 261 104 176 58 122 186 314), lower := (rows 193 7 261 104 176 32 64 128 256), losses := [] }

theorem u15444 : Upper (D 8) (R 8) [192,5,257,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15444 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15445 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 193 7 262 41 56 240 240 240 496), lower := (rows 193 7 262 41 56 32 64 128 256), losses := [] }

theorem u15445 : Upper (D 8) (R 8) [192,5,258,33,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15445 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15446 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 208, targets := 1 }], pairs := [(4,0)], upper := (rows 193 7 262 41 88 176 240 176 432), lower := (rows 193 7 262 41 88 32 64 128 256), losses := [] }

theorem u15446 : Upper (D 8) (R 8) [192,5,258,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15446 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15447 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 208, targets := 1 }], pairs := [(4,0)], upper := (rows 193 7 262 41 112 184 248 184 440), lower := (rows 193 7 262 41 112 32 64 128 256), losses := [] }

theorem u15447 : Upper (D 8) (R 8) [192,5,258,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15447 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15448 : PairBound 9 := { available := 225, camps := [{ cop := 5, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 262 56 56 225 225 225 481), lower := (rows 193 7 262 56 56 32 64 128 256), losses := [] }

theorem u15448 : Upper (D 8) (R 8) [192,5,258,48,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15448 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15449 : PairBound 9 := { available := 168, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 262 56 81 168 232 168 424), lower := (rows 193 7 262 56 81 32 64 128 256), losses := [] }

theorem u15449 : Upper (D 8) (R 8) [192,5,258,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15449 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15450 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 294, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 262 56 88 161 225 161 417), lower := (rows 193 7 262 56 88 32 64 128 256), losses := [] }

theorem u15450 : Upper (D 8) (R 8) [192,5,258,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15450 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15451 : PairBound 9 := { available := 169, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 262 56 112 169 233 169 425), lower := (rows 193 7 262 56 112 32 64 128 256), losses := [] }

theorem u15451 : Upper (D 8) (R 8) [192,5,258,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15451 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15452 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 193 7 262 56 208 41 105 169 297), lower := (rows 193 7 262 56 208 32 64 128 256), losses := [] }

theorem u15452 : Upper (D 8) (R 8) [192,5,258,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15452 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15453 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 262 73 152 48 112 176 304), lower := (rows 193 7 262 73 152 32 64 128 256), losses := [] }

theorem u15453 : Upper (D 8) (R 8) [192,5,258,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15453 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15454 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 262 73 176 56 120 184 312), lower := (rows 193 7 262 73 176 32 64 128 256), losses := [] }

theorem u15454 : Upper (D 8) (R 8) [192,5,258,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15454 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15455 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 262 88 152 33 97 161 289), lower := (rows 193 7 262 88 152 32 64 128 256), losses := [] }

theorem u15455 : Upper (D 8) (R 8) [192,5,258,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15455 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15456 : Route 9 := (fun mask => (mask,id))

def c15456 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15456 : Upper (D 8) (R 8) [192,5,258,80,160] 13 := by
  apply FastRouting.sound _ _ [192,5,258,80,160] 13 (by decide) (choices 1) [1,8] r15456 c15456
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5377
  · exact u5378

theorem m15457_16 : Upper (D 8) (R 8) [192,5,258,96,160,16] 13 :=
  permutation_upper _ _ _ [192,5,258,96,160,8] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5380

def r15457 : Route 9 := (fun mask => (mask,id))

def c15457 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15457 : Upper (D 8) (R 8) [192,5,258,96,160] 13 := by
  apply FastRouting.sound _ _ [192,5,258,96,160] 13 (by decide) (choices 1) [1,8,16] r15457 c15457
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5379
  · exact u5380
  · exact m15457_16

def b15458 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 484, targets := 1 }], pairs := [(2,0)], upper := (rows 193 7 268 26 49 224 224 224 480), lower := (rows 193 7 268 26 49 32 64 128 256), losses := [] }

theorem u15458 : Upper (D 8) (R 8) [192,5,264,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15458 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15459 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 268 26 81 160 224 160 416), lower := (rows 193 7 268 26 81 32 64 128 256), losses := [] }

theorem u15459 : Upper (D 8) (R 8) [192,5,264,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15459 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15460 : PairBound 9 := { available := 161, camps := [], pairs := [(2,6)], upper := (rows 193 7 268 26 112 161 225 161 417), lower := (rows 193 7 268 26 112 32 64 128 256), losses := [{ target := 6, region := (rows 1 2 12 8 16 35 0 131 259), good := (rows 417 423 268 446 48 32 0 128 256) }] }

theorem u15460 : Upper (D 8) (R 8) [192,5,264,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15460 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15461 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 193 7 268 26 208 33 97 161 289), lower := (rows 193 7 268 26 208 32 64 128 256), losses := [] }

theorem u15461 : Upper (D 8) (R 8) [192,5,264,18,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15461 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15462 : PairBound 9 := { available := 240, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 193 7 268 41 50 240 240 240 496), lower := (rows 193 7 268 41 50 32 64 128 256), losses := [] }

theorem u15462 : Upper (D 8) (R 8) [192,5,264,33,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15462 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15463 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 193 7 268 41 82 176 240 176 432), lower := (rows 193 7 268 41 82 32 64 128 256), losses := [] }

theorem u15463 : Upper (D 8) (R 8) [192,5,264,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15463 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15464 : PairBound 9 := { available := 178, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 193 7 268 41 112 178 242 178 434), lower := (rows 193 7 268 41 112 32 64 128 256), losses := [] }

theorem u15464 : Upper (D 8) (R 8) [192,5,264,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15464 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15465 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c15465 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u15465 : Upper (D 8) (R 8) [192,5,264,34,33] 13 := by
  apply FastRouting.sound _ _ [192,5,264,34,33] 13 (by decide) (choices 1) [16,64] r15465 c15465
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5381
  · exact u5382

def b15466 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 268 42 81 176 240 176 432), lower := (rows 193 7 268 42 81 32 64 128 256), losses := [] }

theorem u15466 : Upper (D 8) (R 8) [192,5,264,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15466 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15467 : Route 9 := (fun mask => (mask,id))

def c15467 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u15467 : Upper (D 8) (R 8) [192,5,264,34,96] 13 := by
  apply FastRouting.sound _ _ [192,5,264,34,96] 13 (by decide) (choices 1) [1,16,128] r15467 c15467
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5383
  · exact u5384
  · exact u5385

def b15468 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 193 7 268 42 208 49 113 177 305), lower := (rows 193 7 268 42 208 32 64 128 256), losses := [] }

theorem u15468 : Upper (D 8) (R 8) [192,5,264,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15468 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15469 : PairBound 9 := { available := 226, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 268 56 49 226 226 226 482), lower := (rows 193 7 268 56 49 32 64 128 256), losses := [] }

theorem u15469 : Upper (D 8) (R 8) [192,5,264,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15469 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15470 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 268 56 50 225 225 225 481), lower := (rows 193 7 268 56 50 32 64 128 256), losses := [] }

theorem u15470 : Upper (D 8) (R 8) [192,5,264,48,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15470 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15471 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 268 56 81 162 226 162 418), lower := (rows 193 7 268 56 81 32 64 128 256), losses := [] }

theorem u15471 : Upper (D 8) (R 8) [192,5,264,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15471 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15472 : PairBound 9 := { available := 161, camps := [], pairs := [(2,6)], upper := (rows 193 7 268 56 82 161 225 161 417), lower := (rows 193 7 268 56 82 32 64 128 256), losses := [{ target := 6, region := (rows 1 2 20 24 16 35 0 131 259), good := (rows 417 423 268 60 446 32 0 128 256) }] }

theorem u15472 : Upper (D 8) (R 8) [192,5,264,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15472 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15473 : PairBound 9 := { available := 163, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 268 56 112 163 227 163 419), lower := (rows 193 7 268 56 112 32 64 128 256), losses := [] }

theorem u15473 : Upper (D 8) (R 8) [192,5,264,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15473 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15474 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 193 7 268 56 208 35 99 163 291), lower := (rows 193 7 268 56 208 32 64 128 256), losses := [] }

theorem u15474 : Upper (D 8) (R 8) [192,5,264,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15474 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15475 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 268 73 50 176 240 176 432), lower := (rows 193 7 268 73 50 32 64 128 256), losses := [] }

theorem u15475 : Upper (D 8) (R 8) [192,5,264,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15475 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15476 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 268 73 146 48 112 176 304), lower := (rows 193 7 268 73 146 32 64 128 256), losses := [] }

theorem u15476 : Upper (D 8) (R 8) [192,5,264,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15476 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15477 : PairBound 9 := { available := 50, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 268 73 176 50 114 178 306), lower := (rows 193 7 268 73 176 32 64 128 256), losses := [] }

theorem u15477 : Upper (D 8) (R 8) [192,5,264,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15477 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15478 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 193 7 268 74 49 176 240 176 432), lower := (rows 193 7 268 74 49 32 64 128 256), losses := [] }

theorem u15478 : Upper (D 8) (R 8) [192,5,264,66,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15478 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15479 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 193 7 268 74 176 49 113 177 305), lower := (rows 193 7 268 74 176 32 64 128 256), losses := [] }

theorem u15479 : Upper (D 8) (R 8) [192,5,264,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15479 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u15479
end Delivery.IrregularNine14.P08

import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0000

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b660 : PairBound 9 := { available := 272, camps := [{ cop := 3, region := 70, targets := 288 },{ cop := 2, region := 307, targets := 128 }], pairs := [(0,7),(1,5),(1,8),(2,5),(2,8)], upper := (rows 35 7 76 137 112 288 192 400 272), lower := (rows 35 7 76 137 112 288 192 128 256), losses := [] }

theorem u660 : Upper (D 9) (R 9) [34,5,72,129,96,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b660 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b661 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 143, targets := 256 },{ cop := 3, region := 372, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(2,8),(3,8)], upper := (rows 35 7 76 137 112 288 320 144 400), lower := (rows 35 7 76 137 112 288 320 128 256), losses := [] }

theorem u661 : Upper (D 9) (R 9) [34,5,72,129,96,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b661 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b662 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 79, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 7 76 137 176 288 80 448 320), lower := (rows 35 7 76 137 176 288 80 128 256), losses := [] }

theorem u662 : Upper (D 9) (R 9) [34,5,72,129,160,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b662 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b663 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(0,6),(0,7),(1,6),(2,0),(4,0)], upper := (rows 35 7 76 137 176 288 320 208 336), lower := (rows 35 7 76 137 176 288 320 128 256), losses := [{ target := 6, region := (rows 5 6 4 8 16 352 0 128 256), good := (rows 35 7 47 137 176 288 288 128 288) },{ target := 7, region := (rows 5 6 4 8 16 368 368 0 272), good := (rows 99 7 111 9 368 352 352 0 352) }] }

theorem u663 : Upper (D 9) (R 9) [34,5,72,129,160,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b663 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b664 : PairBound 9 := { available := 288, camps := [{ cop := 3, region := 86, targets := 288 }], pairs := [(1,5),(1,8),(2,5),(2,8)], upper := (rows 35 7 76 137 208 288 80 416 288), lower := (rows 35 7 76 137 208 288 80 128 256), losses := [] }

theorem u664 : Upper (D 9) (R 9) [34,5,72,129,192,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b664 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b665 : PairBound 9 := { available := 272, camps := [{ cop := 3, region := 372, targets := 1 },{ cop := 2, region := 400, targets := 32 }], pairs := [(1,7),(2,0),(3,5),(4,0),(4,5)], upper := (rows 35 7 76 137 208 288 96 400 272), lower := (rows 35 7 76 137 208 288 96 128 256), losses := [{ target := 5, region := (rows 1 2 4 11 84 0 64 214 342), good := (rows 395 415 476 137 464 256 464 128 256) },{ target := 7, region := (rows 1 10 12 8 16 304 369 0 272), good := (rows 99 71 78 79 368 352 96 0 352) }] }

theorem u665 : Upper (D 9) (R 9) [34,5,72,129,192,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b665 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b666 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(0,6),(0,7),(1,6),(2,0),(4,0)], upper := (rows 35 7 76 137 208 288 320 176 304), lower := (rows 35 7 76 137 208 288 320 128 256), losses := [{ target := 6, region := (rows 5 6 4 8 16 368 0 144 272), good := (rows 35 7 47 137 432 288 288 128 288) },{ target := 7, region := (rows 5 6 4 8 16 368 368 0 272), good := (rows 99 7 111 9 368 352 352 0 352) }] }

theorem u666 : Upper (D 9) (R 9) [34,5,72,129,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b666 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b667 : PairBound 9 := { available := 384, camps := [{ cop := 0, region := 392, targets := 96 },{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0),(3,5),(3,6),(4,0)], upper := (rows 35 7 76 137 336 48 96 384 384), lower := (rows 35 7 76 137 336 48 96 128 256), losses := [] }

theorem u667 : Upper (D 9) (R 9) [34,5,72,129,320,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b667 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b668 : PairBound 9 := { available := 288, camps := [{ cop := 3, region := 70, targets := 288 }], pairs := [(1,5),(1,8),(2,5),(2,8)], upper := (rows 35 7 76 137 336 48 192 416 288), lower := (rows 35 7 76 137 336 48 192 128 256), losses := [] }

theorem u668 : Upper (D 9) (R 9) [34,5,72,129,320,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b668 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b669 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 175, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 7 76 137 336 48 320 160 416), lower := (rows 35 7 76 137 336 48 320 128 256), losses := [] }

theorem u669 : Upper (D 9) (R 9) [34,5,72,129,320,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b669 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b670 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 427, targets := 64 },{ cop := 3, region := 372, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(3,6)], upper := (rows 35 7 76 137 336 288 80 160 416), lower := (rows 35 7 76 137 336 288 80 128 256), losses := [] }

theorem u670 : Upper (D 9) (R 9) [34,5,72,129,320,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b670 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b671 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 372, targets := 1 },{ cop := 2, region := 400, targets := 32 },{ cop := 5, region := 80, targets := 128 }], pairs := [(2,0),(3,5),(4,0),(4,5),(4,7)], upper := (rows 35 7 76 137 336 288 96 144 400), lower := (rows 35 7 76 137 336 288 96 128 256), losses := [{ target := 5, region := (rows 1 2 4 11 84 0 64 214 342), good := (rows 395 415 476 137 464 256 464 128 256) }] }

theorem u671 : Upper (D 9) (R 9) [34,5,72,129,320,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b671 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b672 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 70, targets := 288 },{ cop := 2, region := 307, targets := 128 }], pairs := [(0,7),(1,5),(1,8),(2,5),(2,8)], upper := (rows 35 7 76 137 336 288 192 176 304), lower := (rows 35 7 76 137 336 288 192 128 256), losses := [] }

theorem u672 : Upper (D 9) (R 9) [34,5,72,129,320,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b672 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b673 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 291, targets := 128 },{ cop := 3, region := 372, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,0)], upper := (rows 35 7 76 137 400 288 80 224 352), lower := (rows 35 7 76 137 400 288 80 128 256), losses := [] }

theorem u673 : Upper (D 9) (R 9) [34,5,72,129,384,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b673 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b674 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 372, targets := 1 },{ cop := 2, region := 400, targets := 32 }], pairs := [(1,7),(2,0),(3,5),(4,0),(4,5)], upper := (rows 35 7 76 137 400 288 96 208 336), lower := (rows 35 7 76 137 400 288 96 128 256), losses := [{ target := 5, region := (rows 1 2 4 10 86 0 64 196 324), good := (rows 27 415 476 137 400 256 464 128 256) },{ target := 7, region := (rows 1 10 12 8 16 304 369 0 272), good := (rows 99 71 78 79 368 352 96 0 352) }] }

theorem u674 : Upper (D 9) (R 9) [34,5,72,129,384,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b674 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b675 : PairBound 9 := { available := 384, camps := [{ cop := 6, region := 444, targets := 1 },{ cop := 0, region := 80, targets := 384 }], pairs := [(2,0),(3,0),(4,0),(4,7),(4,8)], upper := (rows 35 7 76 152 112 288 65 384 384), lower := (rows 35 7 76 152 112 288 65 128 256), losses := [] }

theorem u675 : Upper (D 9) (R 9) [34,5,72,144,96,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b675 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b676 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 307, targets := 128 },{ cop := 3, region := 68, targets := 33 }], pairs := [(0,7),(1,7),(2,0),(2,5),(4,7)], upper := (rows 35 7 76 152 112 288 192 385 257), lower := (rows 35 7 76 152 112 288 192 128 256), losses := [] }

theorem u676 : Upper (D 9) (R 9) [34,5,72,144,96,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b676 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b677 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 143, targets := 256 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 7 76 152 112 288 320 129 385), lower := (rows 35 7 76 152 112 288 320 128 256), losses := [] }

theorem u677 : Upper (D 9) (R 9) [34,5,72,144,96,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b677 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b678 : PairBound 9 := { available := 160, camps := [{ cop := 6, region := 444, targets := 1 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,6),(2,0),(3,0),(4,0)], upper := (rows 35 7 76 152 336 288 65 160 416), lower := (rows 35 7 76 152 336 288 65 128 256), losses := [] }

theorem u678 : Upper (D 9) (R 9) [34,5,72,144,320,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b678 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b679 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 5, region := 80, targets := 129 }], pairs := [(0,6),(1,6),(2,0),(4,0),(4,7)], upper := (rows 35 7 76 152 336 288 96 129 385), lower := (rows 35 7 76 152 336 288 96 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 304 304 377 128 256), good := (rows 114 70 76 252 368 368 112 128 368) }] }

theorem u679 : Upper (D 9) (R 9) [34,5,72,144,320,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b679 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b680 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 307, targets := 128 },{ cop := 3, region := 68, targets := 33 }], pairs := [(0,7),(1,7),(2,0),(2,5),(4,7)], upper := (rows 35 7 76 152 336 288 192 161 289), lower := (rows 35 7 76 152 336 288 192 128 256), losses := [] }

theorem u680 : Upper (D 9) (R 9) [34,5,72,144,320,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b680 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b681 : PairBound 9 := { available := 384, camps := [{ cop := 3, region := 87, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 7 76 168 81 288 80 384 384), lower := (rows 35 7 76 168 81 288 80 128 256), losses := [] }

theorem u681 : Upper (D 9) (R 9) [34,5,72,160,65,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b681 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b682 : PairBound 9 := { available := 272, camps := [{ cop := 3, region := 87, targets := 256 },{ cop := 2, region := 307, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8),(4,8)], upper := (rows 35 7 76 168 81 288 192 400 272), lower := (rows 35 7 76 168 81 288 192 128 256), losses := [] }

theorem u682 : Upper (D 9) (R 9) [34,5,72,160,65,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b682 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b683 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 428, targets := 1 },{ cop := 0, region := 464, targets := 32 },{ cop := 4, region := 424, targets := 64 }], pairs := [(2,0),(2,5),(3,0),(3,6),(4,5)], upper := (rows 35 7 76 168 81 288 320 144 400), lower := (rows 35 7 76 168 81 288 320 128 256), losses := [{ target := 5, region := (rows 1 2 12 8 19 0 371 147 275), good := (rows 467 471 76 204 465 320 320 128 320) }] }

theorem u683 : Upper (D 9) (R 9) [34,5,72,160,65,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b683 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b684 : PairBound 9 := { available := 320, camps := [{ cop := 3, region := 87, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(4,8)], upper := (rows 35 7 76 168 145 288 80 448 320), lower := (rows 35 7 76 168 145 288 80 128 256), losses := [] }

theorem u684 : Upper (D 9) (R 9) [34,5,72,160,129,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b684 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b685 : PairBound 9 := { available := 80, camps := [{ cop := 4, region := 364, targets := 1 },{ cop := 0, region := 464, targets := 32 }], pairs := [(0,6),(2,0),(2,5),(3,0),(4,5)], upper := (rows 35 7 76 168 145 288 320 208 336), lower := (rows 35 7 76 168 145 288 320 128 256), losses := [{ target := 5, region := (rows 1 2 12 8 19 0 371 147 275), good := (rows 467 471 76 204 465 320 320 128 320) },{ target := 6, region := (rows 5 6 4 8 16 352 0 128 256), good := (rows 35 7 47 168 145 288 288 128 288) }] }

theorem u685 : Upper (D 9) (R 9) [34,5,72,160,129,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b685 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b686 : PairBound 9 := { available := 272, camps := [{ cop := 3, region := 87, targets := 256 },{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8),(4,8)], upper := (rows 35 7 76 168 208 288 65 400 272), lower := (rows 35 7 76 168 208 288 65 128 256), losses := [] }

theorem u686 : Upper (D 9) (R 9) [34,5,72,160,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b686 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b687 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 84, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 35 7 76 168 208 288 80 385 257), lower := (rows 35 7 76 168 208 288 80 128 256), losses := [] }

theorem u687 : Upper (D 9) (R 9) [34,5,72,160,192,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b687 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b688 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 464, targets := 32 }], pairs := [(2,0),(2,5),(3,0),(4,0),(4,5)], upper := (rows 35 7 76 168 208 288 320 145 273), lower := (rows 35 7 76 168 208 288 320 128 256), losses := [{ target := 0, region := (rows 0 2 28 24 24 352 352 128 256), good := (rows 98 6 124 252 252 352 352 128 352) },{ target := 5, region := (rows 1 2 12 8 27 0 355 131 259), good := (rows 467 471 92 220 208 320 320 128 320) }] }

theorem u688 : Upper (D 9) (R 9) [34,5,72,160,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b688 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r689 : Route 9 := (fun mask => (mask,id))

def c689 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u689 : Upper (D 9) (R 9) [34,5,72,160,257,256,16] 13 := by
  apply FastRouting.sound _ _ [34,5,72,160,257,256,16] 13 (by decide) (choices 1) [64] r689 c689
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u33

def b690 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 307, targets := 128 },{ cop := 3, region := 71, targets := 256 }], pairs := [(0,7),(0,8),(1,7),(1,8),(4,7)], upper := (rows 35 7 76 168 273 288 192 208 336), lower := (rows 35 7 76 168 273 288 192 128 256), losses := [] }

theorem u690 : Upper (D 9) (R 9) [34,5,72,160,257,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b690 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b691 : PairBound 9 := { available := 384, camps := [{ cop := 3, region := 71, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 7 76 168 336 48 65 384 384), lower := (rows 35 7 76 168 336 48 65 128 256), losses := [] }

theorem u691 : Upper (D 9) (R 9) [34,5,72,160,320,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b691 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b692 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 307, targets := 128 },{ cop := 3, region := 71, targets := 256 }], pairs := [(0,7),(0,8),(1,7),(4,7)], upper := (rows 35 7 76 168 336 48 192 385 257), lower := (rows 35 7 76 168 336 48 192 128 256), losses := [] }

theorem u692 : Upper (D 9) (R 9) [34,5,72,160,320,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b692 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b693 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 175, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 7 76 168 336 48 320 129 385), lower := (rows 35 7 76 168 336 48 320 128 256), losses := [] }

theorem u693 : Upper (D 9) (R 9) [34,5,72,160,320,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b693 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b694 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 71, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 35 7 76 168 336 288 65 144 400), lower := (rows 35 7 76 168 336 288 65 128 256), losses := [] }

theorem u694 : Upper (D 9) (R 9) [34,5,72,160,320,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b694 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b695 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 427, targets := 64 },{ cop := 5, region := 80, targets := 1 }], pairs := [(0,6),(1,6),(3,6),(4,0)], upper := (rows 35 7 76 168 336 288 80 129 385), lower := (rows 35 7 76 168 336 288 80 128 256), losses := [] }

theorem u695 : Upper (D 9) (R 9) [34,5,72,160,320,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b695 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b696 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 307, targets := 128 },{ cop := 3, region := 71, targets := 256 }], pairs := [(0,7),(0,8),(1,7),(1,8),(4,7)], upper := (rows 35 7 76 168 336 288 192 145 273), lower := (rows 35 7 76 168 336 288 192 128 256), losses := [] }

theorem u696 : Upper (D 9) (R 9) [34,5,72,160,320,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b696 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b697 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 71, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 35 7 76 168 400 288 65 208 336), lower := (rows 35 7 76 168 400 288 65 128 256), losses := [] }

theorem u697 : Upper (D 9) (R 9) [34,5,72,160,384,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b697 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b698 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 291, targets := 128 },{ cop := 4, region := 108, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,0)], upper := (rows 35 7 76 168 400 288 80 193 321), lower := (rows 35 7 76 168 400 288 80 128 256), losses := [] }

theorem u698 : Upper (D 9) (R 9) [34,5,72,160,384,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b698 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b699 : PairBound 9 := { available := 320, camps := [{ cop := 3, region := 119, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(4,8)], upper := (rows 35 7 76 392 145 48 96 448 320), lower := (rows 35 7 76 392 145 48 96 128 256), losses := [] }

theorem u699 : Upper (D 9) (R 9) [34,5,72,384,129,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b699 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b700 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 179, targets := 256 },{ cop := 3, region := 68, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(4,8)], upper := (rows 35 7 76 392 145 48 320 224 352), lower := (rows 35 7 76 392 145 48 320 128 256), losses := [] }

theorem u700 : Upper (D 9) (R 9) [34,5,72,384,129,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b700 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b701 : PairBound 9 := { available := 288, camps := [{ cop := 3, region := 119, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(4,8)], upper := (rows 35 7 76 392 208 48 65 416 288), lower := (rows 35 7 76 392 208 48 65 128 256), losses := [] }

theorem u701 : Upper (D 9) (R 9) [34,5,72,384,192,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b701 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b702 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 119, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(4,8)], upper := (rows 35 7 76 392 208 48 96 385 257), lower := (rows 35 7 76 392 208 48 96 128 256), losses := [] }

theorem u702 : Upper (D 9) (R 9) [34,5,72,384,192,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b702 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b703 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 179, targets := 256 },{ cop := 3, region := 68, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(4,8)], upper := (rows 35 7 76 392 208 48 320 161 289), lower := (rows 35 7 76 392 208 48 320 128 256), losses := [] }

theorem u703 : Upper (D 9) (R 9) [34,5,72,384,192,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b703 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b704 : PairBound 9 := { available := 384, camps := [{ cop := 0, region := 88, targets := 384 },{ cop := 2, region := 291, targets := 64 }], pairs := [(0,6),(3,7),(3,8),(4,7),(4,8)], upper := (rows 35 7 196 25 88 288 96 384 384), lower := (rows 35 7 196 25 88 288 96 128 256), losses := [] }

theorem u704 : Upper (D 9) (R 9) [34,5,192,17,72,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b704 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b705 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 315, targets := 128 },{ cop := 2, region := 291, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(3,7),(4,7)], upper := (rows 35 7 196 25 88 288 192 416 288), lower := (rows 35 7 196 25 88 288 192 128 256), losses := [] }

theorem u705 : Upper (D 9) (R 9) [34,5,192,17,72,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b705 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b706 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 291, targets := 64 },{ cop := 3, region := 500, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(3,5),(4,0)], upper := (rows 35 7 196 25 88 288 320 160 416), lower := (rows 35 7 196 25 88 288 320 128 256), losses := [{ target := 5, region := (rows 1 2 4 11 17 0 352 128 256), good := (rows 91 31 196 25 88 320 320 128 320) }] }

theorem u706 : Upper (D 9) (R 9) [34,5,192,17,72,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b706 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b707 : PairBound 9 := { available := 384, camps := [{ cop := 0, region := 88, targets := 384 }], pairs := [(3,7),(3,8),(4,7),(4,8)], upper := (rows 35 7 196 25 112 288 72 384 384), lower := (rows 35 7 196 25 112 288 72 128 256), losses := [] }

theorem u707 : Upper (D 9) (R 9) [34,5,192,17,96,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b707 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b708 : PairBound 9 := { available := 264, camps := [{ cop := 2, region := 315, targets := 128 },{ cop := 6, region := 4, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7),(4,7)], upper := (rows 35 7 196 25 112 288 192 392 264), lower := (rows 35 7 196 25 112 288 192 128 256), losses := [] }

theorem u708 : Upper (D 9) (R 9) [34,5,192,17,96,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b708 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b709 : PairBound 9 := { available := 136, camps := [{ cop := 4, region := 143, targets := 256 },{ cop := 3, region := 452, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(2,8),(3,8)], upper := (rows 35 7 196 25 112 288 320 136 392), lower := (rows 35 7 196 25 112 288 320 128 256), losses := [] }

theorem u709 : Upper (D 9) (R 9) [34,5,192,17,96,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b709 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b710 : PairBound 9 := { available := 384, camps := [{ cop := 6, region := 404, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 35 7 196 25 336 40 96 384 384), lower := (rows 35 7 196 25 336 40 96 128 256), losses := [] }

theorem u710 : Upper (D 9) (R 9) [34,5,192,17,320,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b710 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b711 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 35 7 196 25 336 40 192 416 288), lower := (rows 35 7 196 25 336 40 192 128 256), losses := [] }

theorem u711 : Upper (D 9) (R 9) [34,5,192,17,320,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b711 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b712 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 175, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 7 196 25 336 40 320 160 416), lower := (rows 35 7 196 25 336 40 320 128 256), losses := [] }

theorem u712 : Upper (D 9) (R 9) [34,5,192,17,320,8,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b712 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b713 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 291, targets := 64 },{ cop := 3, region := 500, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(4,0)], upper := (rows 35 7 196 25 336 288 72 160 416), lower := (rows 35 7 196 25 336 288 72 128 256), losses := [] }

theorem u713 : Upper (D 9) (R 9) [34,5,192,17,320,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b713 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b714 : PairBound 9 := { available := 136, camps := [{ cop := 3, region := 500, targets := 1 },{ cop := 5, region := 80, targets := 128 }], pairs := [(1,8),(2,0),(3,7),(4,0),(4,7)], upper := (rows 35 7 196 25 336 288 96 136 392), lower := (rows 35 7 196 25 336 288 96 128 256), losses := [{ target := 7, region := (rows 1 2 4 9 304 304 377 0 256), good := (rows 123 79 68 121 368 368 112 0 368) },{ target := 8, region := (rows 1 10 12 8 16 32 97 136 0), good := (rows 99 71 196 223 80 96 96 128 0) }] }

theorem u714 : Upper (D 9) (R 9) [34,5,192,17,320,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b714 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b715 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 315, targets := 128 },{ cop := 6, region := 4, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7),(4,7)], upper := (rows 35 7 196 25 336 288 192 168 296), lower := (rows 35 7 196 25 336 288 192 128 256), losses := [] }

theorem u715 : Upper (D 9) (R 9) [34,5,192,17,320,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b715 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b716 : PairBound 9 := { available := 384, camps := [{ cop := 0, region := 88, targets := 384 }], pairs := [(3,7),(3,8),(4,7),(4,8)], upper := (rows 35 7 196 56 81 288 72 384 384), lower := (rows 35 7 196 56 81 288 72 128 256), losses := [] }

theorem u716 : Upper (D 9) (R 9) [34,5,192,48,65,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b716 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b717 : PairBound 9 := { available := 264, camps := [{ cop := 2, region := 315, targets := 128 },{ cop := 6, region := 4, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7),(4,7)], upper := (rows 35 7 196 56 81 288 192 392 264), lower := (rows 35 7 196 56 81 288 192 128 256), losses := [] }

theorem u717 : Upper (D 9) (R 9) [34,5,192,48,65,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b717 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b718 : PairBound 9 := { available := 136, camps := [{ cop := 4, region := 428, targets := 1 },{ cop := 3, region := 452, targets := 32 },{ cop := 4, region := 424, targets := 64 }], pairs := [(2,0),(2,5),(3,0),(3,6),(4,5)], upper := (rows 35 7 196 56 81 288 320 136 392), lower := (rows 35 7 196 56 81 288 320 128 256), losses := [{ target := 5, region := (rows 1 2 12 8 17 0 360 136 264), good := (rows 83 23 196 476 81 320 320 128 320) }] }

theorem u718 : Upper (D 9) (R 9) [34,5,192,48,65,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b718 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b719 : PairBound 9 := { available := 384, camps := [{ cop := 0, region := 88, targets := 384 },{ cop := 6, region := 388, targets := 1 }], pairs := [(2,0),(3,7),(3,8),(4,7),(4,8)], upper := (rows 35 7 196 56 88 288 65 384 384), lower := (rows 35 7 196 56 88 288 65 128 256), losses := [] }

theorem u719 : Upper (D 9) (R 9) [34,5,192,48,72,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b719 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u719
end Delivery.IrregularNine14.P09

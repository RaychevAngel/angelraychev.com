import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0055
import IrregularNine14P07C0056

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b15660 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 1, region := 200, targets := 32 }], pairs := [(2,0),(3,0),(3,5),(4,0)], upper := (rows 13 35 52 200 336 33 194 130 386), lower := (rows 13 35 52 200 336 33 64 128 256), losses := [] }

theorem u15660 : Upper (D 7) (R 7) [12,33,48,192,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15660 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15661 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 0, region := 34, targets := 64 },{ cop := 0, region := 34, targets := 128 }], pairs := [(1,6),(1,7),(3,5),(4,5)], upper := (rows 13 35 52 200 336 34 195 131 387), lower := (rows 13 35 52 200 336 34 64 128 256), losses := [] }

theorem u15661 : Upper (D 7) (R 7) [12,33,48,192,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15661 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15662 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 1, region := 340, targets := 128 }], pairs := [(2,7),(3,5),(4,5),(4,7)], upper := (rows 13 35 52 200 336 160 67 131 259), lower := (rows 13 35 52 200 336 160 64 128 256), losses := [] }

theorem u15662 : Upper (D 7) (R 7) [12,33,48,192,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15662 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15663 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 38, targets := 192 }], pairs := [(1,6),(1,7),(2,6),(2,7)], upper := (rows 13 35 52 266 81 34 192 192 448), lower := (rows 13 35 52 266 81 34 64 128 256), losses := [] }

theorem u15663 : Upper (D 7) (R 7) [12,33,48,258,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15663 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15664 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 395, targets := 64 },{ cop := 1, region := 392, targets := 32 }], pairs := [(0,6),(1,6),(3,5),(3,6)], upper := (rows 13 35 52 266 81 96 194 130 386), lower := (rows 13 35 52 266 81 96 64 128 256), losses := [] }

theorem u15664 : Upper (D 7) (R 7) [12,33,48,258,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15664 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15665 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 1, region := 456, targets := 1 }], pairs := [(2,0),(3,0),(3,5),(4,5)], upper := (rows 13 35 52 266 81 160 194 194 450), lower := (rows 13 35 52 266 81 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 10 16 171 74 138 266), good := (rows 492 490 52 490 116 160 64 160 256) }] }

theorem u15665 : Upper (D 7) (R 7) [12,33,48,258,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15665 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15666 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(4,0)], upper := (rows 13 35 52 266 208 33 194 194 450), lower := (rows 13 35 52 266 208 33 64 128 256), losses := [] }

theorem u15666 : Upper (D 7) (R 7) [12,33,48,258,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15666 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15667 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 208, targets := 34 },{ cop := 0, region := 34, targets := 192 }], pairs := [(1,6),(1,7),(4,1),(4,5)], upper := (rows 13 35 52 266 208 34 193 193 449), lower := (rows 13 35 52 266 208 34 64 128 256), losses := [] }

theorem u15667 : Upper (D 7) (R 7) [12,33,48,258,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15667 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15668 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 395, targets := 64 },{ cop := 4, region := 36, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(3,6)], upper := (rows 13 35 52 266 208 96 195 131 387), lower := (rows 13 35 52 266 208 96 64 128 256), losses := [] }

theorem u15668 : Upper (D 7) (R 7) [12,33,48,258,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15668 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15669 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 38, targets := 192 }], pairs := [(1,6),(1,7),(2,6),(2,7)], upper := (rows 13 35 52 328 145 34 194 194 450), lower := (rows 13 35 52 328 145 34 64 128 256), losses := [] }

theorem u15669 : Upper (D 7) (R 7) [12,33,48,320,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15669 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15670 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 1, region := 148, targets := 64 }], pairs := [(2,6),(3,5),(4,5),(4,6)], upper := (rows 13 35 52 328 145 96 194 130 386), lower := (rows 13 35 52 328 145 96 64 128 256), losses := [] }

theorem u15670 : Upper (D 7) (R 7) [12,33,48,320,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15670 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15671 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 331, targets := 128 },{ cop := 1, region := 328, targets := 32 }], pairs := [(0,7),(1,7),(3,5),(3,7)], upper := (rows 13 35 52 328 145 160 66 194 322), lower := (rows 13 35 52 328 145 160 64 128 256), losses := [] }

theorem u15671 : Upper (D 7) (R 7) [12,33,48,320,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15671 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15672 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(4,0)], upper := (rows 13 35 52 328 146 33 194 194 450), lower := (rows 13 35 52 328 146 33 64 128 256), losses := [] }

theorem u15672 : Upper (D 7) (R 7) [12,33,48,320,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15672 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15673 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 457, targets := 34 }], pairs := [(0,1),(0,5),(3,1),(3,5)], upper := (rows 13 35 52 328 146 34 193 193 449), lower := (rows 13 35 52 328 146 34 64 128 256), losses := [] }

theorem u15673 : Upper (D 7) (R 7) [12,33,48,320,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15673 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15674 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 1, region := 148, targets := 64 }], pairs := [(2,6),(3,5),(4,5),(4,6)], upper := (rows 13 35 52 328 146 96 195 131 387), lower := (rows 13 35 52 328 146 96 64 128 256), losses := [] }

theorem u15674 : Upper (D 7) (R 7) [12,33,48,320,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15674 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15675 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 331, targets := 128 },{ cop := 4, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 13 35 52 328 146 160 67 195 323), lower := (rows 13 35 52 328 146 160 64 128 256), losses := [] }

theorem u15675 : Upper (D 7) (R 7) [12,33,48,320,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15675 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15676 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 1, region := 456, targets := 32 }], pairs := [(2,0),(3,0),(3,5),(4,0)], upper := (rows 13 35 52 328 208 33 194 130 386), lower := (rows 13 35 52 328 208 33 64 128 256), losses := [] }

theorem u15676 : Upper (D 7) (R 7) [12,33,48,320,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15676 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15677 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 0, region := 34, targets := 64 },{ cop := 0, region := 34, targets := 128 }], pairs := [(1,6),(1,7),(3,5),(4,5)], upper := (rows 13 35 52 328 208 34 195 131 387), lower := (rows 13 35 52 328 208 34 64 128 256), losses := [] }

theorem u15677 : Upper (D 7) (R 7) [12,33,48,320,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15677 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15678 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 331, targets := 128 },{ cop := 4, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 13 35 52 328 208 160 67 131 259), lower := (rows 13 35 52 328 208 160 64 128 256), losses := [] }

theorem u15678 : Upper (D 7) (R 7) [12,33,48,320,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15678 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15679 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 2, region := 50, targets := 128 }], pairs := [(1,7),(3,0),(4,0)], upper := (rows 13 35 69 138 82 48 480 416 416), lower := (rows 13 35 69 138 82 48 64 128 256), losses := [] }

theorem u15679 : Upper (D 7) (R 7) [12,33,65,130,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15679 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15680 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 1, region := 340, targets := 128 }], pairs := [(2,7),(3,0),(4,0),(4,7)], upper := (rows 13 35 69 138 82 160 368 432 304), lower := (rows 13 35 69 138 82 160 64 128 256), losses := [] }

theorem u15680 : Upper (D 7) (R 7) [12,33,65,130,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15680 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15681 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 216, targets := 1 },{ cop := 4, region := 424, targets := 64 }], pairs := [(3,0),(3,6),(4,0)], upper := (rows 13 35 69 138 82 288 240 176 432), lower := (rows 13 35 69 138 82 288 64 128 256), losses := [] }

theorem u15681 : Upper (D 7) (R 7) [12,33,65,130,66,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15681 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15682 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 34, targets := 192 },{ cop := 1, region := 472, targets := 1 }], pairs := [(1,6),(1,7),(3,0),(4,0)], upper := (rows 13 35 69 138 112 34 464 400 400), lower := (rows 13 35 69 138 112 34 64 128 256), losses := [] }

theorem u15682 : Upper (D 7) (R 7) [12,33,65,130,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15682 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15683 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 13 35 69 138 112 48 450 386 386), lower := (rows 13 35 69 138 112 48 64 128 256), losses := [] }

theorem u15683 : Upper (D 7) (R 7) [12,33,65,130,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15683 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15684 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 1, region := 340, targets := 128 }], pairs := [(2,7),(3,0),(4,0),(4,7)], upper := (rows 13 35 69 138 112 160 338 402 274), lower := (rows 13 35 69 138 112 160 64 128 256), losses := [] }

theorem u15684 : Upper (D 7) (R 7) [12,33,65,130,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15684 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15685 : Route 9 := (fun mask => (mask,id))

def c15685 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15685 : Upper (D 7) (R 7) [12,33,65,130,96,256] 13 := by
  apply FastRouting.sound _ _ [12,33,65,130,96,256] 13 (by decide) (choices 1) [2,16,128] r15685 c15685
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3348
  · exact u3349
  · exact u3350

def b15686 : PairBound 9 := { available := 336, camps := [{ cop := 0, region := 34, targets := 192 },{ cop := 1, region := 472, targets := 1 }], pairs := [(1,6),(1,7),(3,0),(4,0)], upper := (rows 13 35 69 138 176 34 336 464 336), lower := (rows 13 35 69 138 176 34 64 128 256), losses := [] }

theorem u15686 : Upper (D 7) (R 7) [12,33,65,130,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15686 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15687 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 13 35 69 138 176 48 322 450 322), lower := (rows 13 35 69 138 176 48 64 128 256), losses := [] }

theorem u15687 : Upper (D 7) (R 7) [12,33,65,130,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15687 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15688 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 408, targets := 1 },{ cop := 1, region := 408, targets := 64 }], pairs := [(3,0),(3,6),(4,0),(4,6)], upper := (rows 13 35 69 138 176 96 338 402 274), lower := (rows 13 35 69 138 176 96 64 128 256), losses := [] }

theorem u15688 : Upper (D 7) (R 7) [12,33,65,130,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15688 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15689 : Route 9 := (fun mask => (mask,id))

def c15689 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15689 : Upper (D 7) (R 7) [12,33,65,130,160,256] 13 := by
  apply FastRouting.sound _ _ [12,33,65,130,160,256] 13 (by decide) (choices 1) [2,16] r15689 c15689
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3351
  · exact u3352

def b15690 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 34, targets := 192 },{ cop := 1, region := 472, targets := 1 }], pairs := [(1,6),(1,7),(3,0),(4,0)], upper := (rows 13 35 69 138 208 34 368 432 304), lower := (rows 13 35 69 138 208 34 64 128 256), losses := [] }

theorem u15690 : Upper (D 7) (R 7) [12,33,65,130,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15690 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15691 : PairBound 9 := { available := 290, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 1, region := 392, targets := 64 }], pairs := [(3,0),(3,6),(4,0)], upper := (rows 13 35 69 138 208 48 354 418 290), lower := (rows 13 35 69 138 208 48 64 128 256), losses := [] }

theorem u15691 : Upper (D 7) (R 7) [12,33,65,130,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15691 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15692 : Route 9 := (fun mask => (mask,id))

def c15692 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15692 : Upper (D 7) (R 7) [12,33,65,130,192,256] 13 := by
  apply FastRouting.sound _ _ [12,33,65,130,192,256] 13 (by decide) (choices 1) [2,16,32] r15692 c15692
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3353
  · exact u3354
  · exact u3355

def b15693 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 1, region := 196, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 13 35 69 138 274 48 224 224 480), lower := (rows 13 35 69 138 274 48 64 128 256), losses := [] }

theorem u15693 : Upper (D 7) (R 7) [12,33,65,130,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15693 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15694 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 408, targets := 1 },{ cop := 1, region := 408, targets := 64 }], pairs := [(3,0),(3,6),(4,0),(4,6)], upper := (rows 13 35 69 138 274 96 240 176 432), lower := (rows 13 35 69 138 274 96 64 128 256), losses := [] }

theorem u15694 : Upper (D 7) (R 7) [12,33,65,130,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15694 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15695 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 1, region := 340, targets := 128 }], pairs := [(2,7),(3,0),(4,0),(4,7)], upper := (rows 13 35 69 138 274 160 112 240 368), lower := (rows 13 35 69 138 274 160 64 128 256), losses := [] }

theorem u15695 : Upper (D 7) (R 7) [12,33,65,130,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15695 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15696 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 34, targets := 192 },{ cop := 1, region := 472, targets := 1 }], pairs := [(1,6),(1,7),(3,0),(4,0)], upper := (rows 13 35 69 138 304 34 208 208 464), lower := (rows 13 35 69 138 304 34 64 128 256), losses := [] }

theorem u15696 : Upper (D 7) (R 7) [12,33,65,130,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15696 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15697 : PairBound 9 := { available := 194, camps := [{ cop := 8, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 13 35 69 138 304 48 194 194 450), lower := (rows 13 35 69 138 304 48 64 128 256), losses := [] }

theorem u15697 : Upper (D 7) (R 7) [12,33,65,130,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15697 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15698 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 408, targets := 1 },{ cop := 1, region := 408, targets := 64 }], pairs := [(3,0),(3,6),(4,0),(4,6)], upper := (rows 13 35 69 138 304 96 210 146 402), lower := (rows 13 35 69 138 304 96 64 128 256), losses := [] }

theorem u15698 : Upper (D 7) (R 7) [12,33,65,130,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15698 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15699 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 1, region := 340, targets := 128 }], pairs := [(2,7),(3,0),(4,0),(4,7)], upper := (rows 13 35 69 138 304 160 82 210 338), lower := (rows 13 35 69 138 304 160 64 128 256), losses := [] }

theorem u15699 : Upper (D 7) (R 7) [12,33,65,130,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15699 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15700 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 34, targets := 192 },{ cop := 1, region := 472, targets := 1 }], pairs := [(1,6),(1,7),(3,0),(4,0)], upper := (rows 13 35 69 138 336 34 240 176 432), lower := (rows 13 35 69 138 336 34 64 128 256), losses := [] }

theorem u15700 : Upper (D 7) (R 7) [12,33,65,130,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15700 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15701 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 1, region := 136, targets := 64 }], pairs := [(3,0),(3,6),(4,0)], upper := (rows 13 35 69 138 336 48 226 162 418), lower := (rows 13 35 69 138 336 48 64 128 256), losses := [] }

theorem u15701 : Upper (D 7) (R 7) [12,33,65,130,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15701 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15702 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 1, region := 340, targets := 128 }], pairs := [(2,7),(3,0),(4,0),(4,7)], upper := (rows 13 35 69 138 336 160 114 178 306), lower := (rows 13 35 69 138 336 160 64 128 256), losses := [] }

theorem u15702 : Upper (D 7) (R 7) [12,33,65,130,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15702 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15703 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 34, targets := 192 },{ cop := 1, region := 472, targets := 1 }], pairs := [(1,6),(1,7),(3,0),(4,0)], upper := (rows 13 35 69 138 400 34 112 240 368), lower := (rows 13 35 69 138 400 34 64 128 256), losses := [] }

theorem u15703 : Upper (D 7) (R 7) [12,33,65,130,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15703 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15704 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 1, region := 68, targets := 128 }], pairs := [(2,7),(3,0),(4,0)], upper := (rows 13 35 69 138 400 48 98 226 354), lower := (rows 13 35 69 138 400 48 64 128 256), losses := [] }

theorem u15704 : Upper (D 7) (R 7) [12,33,65,130,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15704 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15705 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 408, targets := 1 },{ cop := 1, region := 408, targets := 64 }], pairs := [(3,0),(3,6),(4,0),(4,6)], upper := (rows 13 35 69 138 400 96 114 178 306), lower := (rows 13 35 69 138 400 96 64 128 256), losses := [] }

theorem u15705 : Upper (D 7) (R 7) [12,33,65,130,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15705 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15706 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 34, targets := 192 },{ cop := 1, region := 472, targets := 1 }], pairs := [(1,6),(1,7),(3,0),(4,0)], upper := (rows 13 35 69 152 274 34 224 224 480), lower := (rows 13 35 69 152 274 34 64 128 256), losses := [] }

theorem u15706 : Upper (D 7) (R 7) [12,33,65,144,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15706 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15707 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 408, targets := 1 },{ cop := 1, region := 408, targets := 64 }], pairs := [(3,0),(3,6),(4,0),(4,6)], upper := (rows 13 35 69 152 274 96 226 162 418), lower := (rows 13 35 69 152 274 96 64 128 256), losses := [] }

theorem u15707 : Upper (D 7) (R 7) [12,33,65,144,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15707 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15708 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 1, region := 340, targets := 128 }], pairs := [(2,7),(3,0),(4,0),(4,7)], upper := (rows 13 35 69 152 274 160 98 226 354), lower := (rows 13 35 69 152 274 160 64 128 256), losses := [] }

theorem u15708 : Upper (D 7) (R 7) [12,33,65,144,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15708 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15709 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 34, targets := 192 },{ cop := 1, region := 472, targets := 1 }], pairs := [(1,6),(1,7),(3,0),(4,0)], upper := (rows 13 35 69 152 304 34 194 194 450), lower := (rows 13 35 69 152 304 34 64 128 256), losses := [] }

theorem u15709 : Upper (D 7) (R 7) [12,33,65,144,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15709 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15710 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 408, targets := 1 },{ cop := 1, region := 408, targets := 64 }], pairs := [(3,0),(3,6),(4,0),(4,6)], upper := (rows 13 35 69 152 304 96 194 130 386), lower := (rows 13 35 69 152 304 96 64 128 256), losses := [] }

theorem u15710 : Upper (D 7) (R 7) [12,33,65,144,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15710 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15711 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 1, region := 340, targets := 128 }], pairs := [(2,7),(3,0),(4,0),(4,7)], upper := (rows 13 35 69 152 304 160 66 194 322), lower := (rows 13 35 69 152 304 160 64 128 256), losses := [] }

theorem u15711 : Upper (D 7) (R 7) [12,33,65,144,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15711 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15712 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 0, region := 34, targets := 64 },{ cop := 0, region := 34, targets := 128 }], pairs := [(1,6),(1,7),(3,0),(4,0)], upper := (rows 13 35 69 152 336 34 226 162 418), lower := (rows 13 35 69 152 336 34 64 128 256), losses := [] }

theorem u15712 : Upper (D 7) (R 7) [12,33,65,144,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15712 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15713 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 1, region := 340, targets := 128 }], pairs := [(2,7),(3,0),(4,0),(4,7)], upper := (rows 13 35 69 152 336 160 98 162 290), lower := (rows 13 35 69 152 336 160 64 128 256), losses := [] }

theorem u15713 : Upper (D 7) (R 7) [12,33,65,144,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15713 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15714 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 2, region := 50, targets := 128 }], pairs := [(1,7),(3,0),(4,0)], upper := (rows 13 35 69 266 82 48 224 160 416), lower := (rows 13 35 69 266 82 48 64 128 256), losses := [] }

theorem u15714 : Upper (D 7) (R 7) [12,33,65,258,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15714 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15715 : Route 9 := (fun mask => (mask,id))

def c15715 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u15715 : Upper (D 7) (R 7) [12,33,65,258,66,128] 13 := by
  apply FastRouting.sound _ _ [12,33,65,258,66,128] 13 (by decide) (choices 1) [16,32,128] r15715 c15715
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3356
  · exact u3357
  · exact u3358

def b15716 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 34, targets := 192 },{ cop := 1, region := 472, targets := 1 }], pairs := [(1,6),(1,7),(3,0),(4,0)], upper := (rows 13 35 69 266 112 34 208 144 400), lower := (rows 13 35 69 266 112 34 64 128 256), losses := [] }

theorem u15716 : Upper (D 7) (R 7) [12,33,65,258,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15716 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15717 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 13 35 69 266 112 48 194 130 386), lower := (rows 13 35 69 266 112 48 64 128 256), losses := [] }

theorem u15717 : Upper (D 7) (R 7) [12,33,65,258,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15717 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15718 : Route 9 := (fun mask => (mask,id))

def c15718 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15718 : Upper (D 7) (R 7) [12,33,65,258,96,128] 13 := by
  apply FastRouting.sound _ _ [12,33,65,258,96,128] 13 (by decide) (choices 1) [2,16,128] r15718 c15718
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3359
  · exact u3360
  · exact u3361

def b15719 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 1, region := 196, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 13 35 69 266 146 48 224 224 480), lower := (rows 13 35 69 266 146 48 64 128 256), losses := [] }

theorem u15719 : Upper (D 7) (R 7) [12,33,65,258,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15719 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u15719
end Delivery.IrregularNine14.P07

import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0000

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b660 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 97 14 84 296 145 160 66 161 289), lower := (rows 97 14 84 296 145 160 66 128 256), losses := [] }

theorem u660 : Upper (D 8) (R 8) [96,12,80,288,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b660 [(6,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b661 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 84 296 145 160 96 131 259), lower := (rows 97 14 84 296 145 160 96 128 256), losses := [] }

theorem u661 : Upper (D 8) (R 8) [96,12,80,288,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b661 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b662 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 424, targets := 1 }], pairs := [(3,0)], upper := (rows 97 14 133 296 82 160 65 176 304), lower := (rows 97 14 133 296 82 160 65 128 256), losses := [] }

theorem u662 : Upper (D 8) (R 8) [96,12,129,288,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b662 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b663 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 97 14 133 296 82 160 80 161 289), lower := (rows 97 14 133 296 82 160 80 128 256), losses := [] }

theorem u663 : Upper (D 8) (R 8) [96,12,129,288,66,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b663 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b664 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 133 296 82 160 96 145 273), lower := (rows 97 14 133 296 82 160 96 128 256), losses := [] }

theorem u664 : Upper (D 8) (R 8) [96,12,129,288,66,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b664 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b665 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 56 273 160 65 130 386), lower := (rows 97 38 76 56 273 160 65 128 256), losses := [] }

theorem u665 : Upper (D 8) (R 8) [96,36,72,48,257,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b665 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b666 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 97 38 76 56 273 160 66 129 385), lower := (rows 97 38 76 56 273 160 66 128 256), losses := [] }

theorem u666 : Upper (D 8) (R 8) [96,36,72,48,257,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b666 [(6,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b667 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 286, targets := 128 }], pairs := [(1,7)], upper := (rows 97 38 76 56 273 160 192 131 259), lower := (rows 97 38 76 56 273 160 192 128 256), losses := [] }

theorem u667 : Upper (D 8) (R 8) [96,36,72,48,257,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b667 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b668 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 56 274 160 65 129 385), lower := (rows 97 38 76 56 274 160 65 128 256), losses := [] }

theorem u668 : Upper (D 8) (R 8) [96,36,72,48,258,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b668 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b669 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 286, targets := 128 }], pairs := [(1,7)], upper := (rows 97 38 76 56 274 160 192 129 257), lower := (rows 97 38 76 56 274 160 192 128 256), losses := [] }

theorem u669 : Upper (D 8) (R 8) [96,36,72,48,258,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b669 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b670 : PairBound 9 := { available := 48, camps := [], pairs := [], upper := (rows 97 38 76 265 145 160 66 176 304), lower := (rows 97 38 76 265 145 160 66 128 256), losses := [] }

theorem u670 : Upper (D 8) (R 8) [96,36,72,257,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b670 [(6,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b671 : PairBound 9 := { available := 34, camps := [], pairs := [], upper := (rows 97 38 76 265 145 160 80 162 290), lower := (rows 97 38 76 265 145 160 80 128 256), losses := [] }

theorem u671 : Upper (D 8) (R 8) [96,36,72,257,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b671 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b672 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 265 145 160 96 146 274), lower := (rows 97 38 76 265 145 160 96 128 256), losses := [] }

theorem u672 : Upper (D 8) (R 8) [96,36,72,257,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b672 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b673 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 178, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 76 265 146 160 65 176 304), lower := (rows 97 38 76 265 146 160 65 128 256), losses := [] }

theorem u673 : Upper (D 8) (R 8) [96,36,72,257,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b673 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b674 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 97 38 76 265 146 160 80 161 289), lower := (rows 97 38 76 265 146 160 80 128 256), losses := [] }

theorem u674 : Upper (D 8) (R 8) [96,36,72,257,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b674 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b675 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 265 146 160 96 145 273), lower := (rows 97 38 76 265 146 160 96 128 256), losses := [] }

theorem u675 : Upper (D 8) (R 8) [96,36,72,257,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b675 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b676 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 296 145 160 65 146 274), lower := (rows 97 38 76 296 145 160 65 128 256), losses := [] }

theorem u676 : Upper (D 8) (R 8) [96,36,72,288,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b676 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b677 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 97 38 76 296 145 160 66 145 273), lower := (rows 97 38 76 296 145 160 66 128 256), losses := [] }

theorem u677 : Upper (D 8) (R 8) [96,36,72,288,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b677 [(6,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b678 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 97 38 76 296 145 160 80 131 259), lower := (rows 97 38 76 296 145 160 80 128 256), losses := [] }

theorem u678 : Upper (D 8) (R 8) [96,36,72,288,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b678 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b679 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 296 146 160 65 145 273), lower := (rows 97 38 76 296 146 160 65 128 256), losses := [] }

theorem u679 : Upper (D 8) (R 8) [96,36,72,288,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b679 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b680 : PairBound 9 := { available := 1, camps := [], pairs := [], upper := (rows 97 38 76 296 146 160 80 129 257), lower := (rows 97 38 76 296 146 160 80 128 256), losses := [] }

theorem u680 : Upper (D 8) (R 8) [96,36,72,288,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b680 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b681 : PairBound 9 := { available := 48, camps := [], pairs := [], upper := (rows 97 38 261 74 145 160 72 176 304), lower := (rows 97 38 261 74 145 160 72 128 256), losses := [] }

theorem u681 : Upper (D 8) (R 8) [96,36,257,66,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b681 [(6,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b682 : PairBound 9 := { available := 40, camps := [], pairs := [], upper := (rows 97 38 261 74 145 160 80 168 296), lower := (rows 97 38 261 74 145 160 80 128 256), losses := [] }

theorem u682 : Upper (D 8) (R 8) [96,36,257,66,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b682 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b683 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 261 74 145 160 96 152 280), lower := (rows 97 38 261 74 145 160 96 128 256), losses := [] }

theorem u683 : Upper (D 8) (R 8) [96,36,257,66,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b683 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b684 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 261 74 152 160 65 176 304), lower := (rows 97 38 261 74 152 160 65 128 256), losses := [] }

theorem u684 : Upper (D 8) (R 8) [96,36,257,66,136,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b684 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b685 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 97 38 261 74 152 160 80 161 289), lower := (rows 97 38 261 74 152 160 80 128 256), losses := [] }

theorem u685 : Upper (D 8) (R 8) [96,36,257,66,136,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b685 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b686 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 261 74 152 160 96 145 273), lower := (rows 97 38 261 74 152 160 96 128 256), losses := [] }

theorem u686 : Upper (D 8) (R 8) [96,36,257,66,136,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b686 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b687 : PairBound 9 := { available := 40, camps := [], pairs := [], upper := (rows 97 38 261 88 145 160 66 168 296), lower := (rows 97 38 261 88 145 160 66 128 256), losses := [] }

theorem u687 : Upper (D 8) (R 8) [96,36,257,80,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b687 [(6,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b688 : PairBound 9 := { available := 34, camps := [], pairs := [], upper := (rows 97 38 261 88 145 160 72 162 290), lower := (rows 97 38 261 88 145 160 72 128 256), losses := [] }

theorem u688 : Upper (D 8) (R 8) [96,36,257,80,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b688 [(6,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b689 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 261 88 145 160 96 138 266), lower := (rows 97 38 261 88 145 160 96 128 256), losses := [] }

theorem u689 : Upper (D 8) (R 8) [96,36,257,80,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b689 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b690 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 261 88 146 160 65 168 296), lower := (rows 97 38 261 88 146 160 65 128 256), losses := [] }

theorem u690 : Upper (D 8) (R 8) [96,36,257,80,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b690 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b691 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 97 38 261 88 146 160 72 161 289), lower := (rows 97 38 261 88 146 160 72 128 256), losses := [] }

theorem u691 : Upper (D 8) (R 8) [96,36,257,80,130,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b691 [(6,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b692 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 261 88 146 160 96 137 265), lower := (rows 97 38 261 88 146 160 96 128 256), losses := [] }

theorem u692 : Upper (D 8) (R 8) [96,36,257,80,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b692 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b693 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 422, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 262 88 145 160 65 168 296), lower := (rows 97 38 262 88 145 160 65 128 256), losses := [] }

theorem u693 : Upper (D 8) (R 8) [96,36,258,80,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b693 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b694 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 97 38 262 88 145 160 72 161 289), lower := (rows 97 38 262 88 145 160 72 128 256), losses := [] }

theorem u694 : Upper (D 8) (R 8) [96,36,258,80,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b694 [(6,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b695 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 152, targets := 32 }], pairs := [(3,5)], upper := (rows 97 38 262 88 145 160 96 137 265), lower := (rows 97 38 262 88 145 160 96 128 256), losses := [] }

theorem u695 : Upper (D 8) (R 8) [96,36,258,80,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b695 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b696 : PairBound 9 := { available := 32, camps := [{ cop := 0, region := 312, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 14 56 336 160 65 160 288), lower := (rows 193 7 14 56 336 160 65 128 256), losses := [] }

theorem u696 : Upper (D 8) (R 8) [192,5,10,48,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b696 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r697 : Route 9 := (fun mask => (mask,id))

def c697 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u697 : Upper (D 8) (R 8) [192,5,10,48,320,128,32] 13 := by
  apply FastRouting.sound _ _ [192,5,10,48,320,128,32] 13 (by decide) (choices 1) [1,32] r697 c697
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4
  · exact u5

def b698 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 400, targets := 1 }], pairs := [(4,0)], upper := (rows 193 7 44 26 304 96 65 160 416), lower := (rows 193 7 44 26 304 96 65 128 256), losses := [] }

theorem u698 : Upper (D 8) (R 8) [192,5,40,18,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b698 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b699 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 100, targets := 1 }], pairs := [(2,0)], upper := (rows 193 7 44 26 304 96 96 129 385), lower := (rows 193 7 44 26 304 96 96 128 256), losses := [] }

theorem u699 : Upper (D 8) (R 8) [192,5,40,18,288,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b699 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b700 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 318, targets := 128 }], pairs := [(1,7)], upper := (rows 193 7 44 26 304 96 192 161 289), lower := (rows 193 7 44 26 304 96 192 128 256), losses := [] }

theorem u700 : Upper (D 8) (R 8) [192,5,40,18,288,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b700 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b701 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 428, targets := 1 }], pairs := [(2,0)], upper := (rows 193 7 292 56 82 160 65 168 296), lower := (rows 193 7 292 56 82 160 65 128 256), losses := [] }

theorem u701 : Upper (D 8) (R 8) [192,5,288,48,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b701 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b702 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 193 7 292 56 82 160 72 161 289), lower := (rows 193 7 292 56 82 160 72 128 256), losses := [] }

theorem u702 : Upper (D 8) (R 8) [192,5,288,48,66,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b702 [(6,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b703 : PairBound 9 := { available := 9, camps := [], pairs := [(3,0)], upper := (rows 193 7 292 56 82 160 96 137 265), lower := (rows 193 7 292 56 82 160 96 128 256), losses := [{ target := 0, region := (rows 0 2 4 10 18 161 239 128 256), good := (rows 224 126 356 120 90 224 96 224 256) }] }

theorem u703 : Upper (D 8) (R 8) [192,5,288,48,66,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b703 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b704 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 65, targets := 32 }], pairs := [(0,5)], upper := (rows 193 38 76 56 274 160 65 161 289), lower := (rows 193 38 76 56 274 160 65 128 256), losses := [] }

theorem u704 : Upper (D 8) (R 8) [192,36,72,48,258,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b704 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b705 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 70, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 76 56 274 160 96 129 257), lower := (rows 193 38 76 56 274 160 96 128 256), losses := [] }

theorem u705 : Upper (D 8) (R 8) [192,36,72,48,258,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b705 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b706 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 408, targets := 1 }], pairs := [(3,0)], upper := (rows 193 38 76 56 400 33 65 162 290), lower := (rows 193 38 76 56 400 33 65 128 256), losses := [] }

theorem u706 : Upper (D 8) (R 8) [192,36,72,48,384,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b706 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b707 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 193 38 76 56 400 33 66 161 289), lower := (rows 193 38 76 56 400 33 66 128 256), losses := [] }

theorem u707 : Upper (D 8) (R 8) [192,36,72,48,384,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b707 [(6,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b708 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 70, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 76 56 400 33 96 131 259), lower := (rows 193 38 76 56 400 33 96 128 256), losses := [] }

theorem u708 : Upper (D 8) (R 8) [192,36,72,48,384,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b708 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b709 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 408, targets := 1 }], pairs := [(3,0)], upper := (rows 193 38 76 152 304 33 65 162 290), lower := (rows 193 38 76 152 304 33 65 128 256), losses := [] }

theorem u709 : Upper (D 8) (R 8) [192,36,72,144,288,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b709 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b710 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 193 38 76 152 304 33 66 161 289), lower := (rows 193 38 76 152 304 33 66 128 256), losses := [] }

theorem u710 : Upper (D 8) (R 8) [192,36,72,144,288,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b710 [(6,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b711 : PairBound 9 := { available := 3, camps := [], pairs := [(2,0)], upper := (rows 193 38 76 152 304 33 96 131 259), lower := (rows 193 38 76 152 304 33 96 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 32 114 128 256), good := (rows 192 102 76 220 368 96 96 128 256) }] }

theorem u711 : Upper (D 8) (R 8) [192,36,72,144,288,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b711 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b712 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 408, targets := 1 }], pairs := [(3,0)], upper := (rows 193 38 76 296 146 33 65 176 304), lower := (rows 193 38 76 296 146 33 65 128 256), losses := [] }

theorem u712 : Upper (D 8) (R 8) [192,36,72,288,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b712 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b713 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 193 38 76 296 146 33 80 161 289), lower := (rows 193 38 76 296 146 33 80 128 256), losses := [] }

theorem u713 : Upper (D 8) (R 8) [192,36,72,288,130,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b713 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b714 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 70, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 76 296 146 33 96 145 273), lower := (rows 193 38 76 296 146 33 96 128 256), losses := [] }

theorem u714 : Upper (D 8) (R 8) [192,36,72,288,130,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b714 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b715 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 154, targets := 1 }], pairs := [(1,0)], upper := (rows 259 14 100 168 208 33 65 176 304), lower := (rows 259 14 100 168 208 33 65 128 256), losses := [] }

theorem u715 : Upper (D 8) (R 8) [258,12,96,160,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b715 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b716 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 259 14 100 168 208 33 80 161 289), lower := (rows 259 14 100 168 208 33 80 128 256), losses := [] }

theorem u716 : Upper (D 8) (R 8) [258,12,96,160,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b716 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b717 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 70, targets := 1 }], pairs := [(1,0)], upper := (rows 259 14 100 168 208 33 96 145 273), lower := (rows 259 14 100 168 208 33 96 128 256), losses := [] }

theorem u717 : Upper (D 8) (R 8) [258,12,96,160,192,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b717 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b718 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 186, targets := 1 }], pairs := [(1,0)], upper := (rows 259 38 69 104 152 160 65 176 304), lower := (rows 259 38 69 104 152 160 65 128 256), losses := [] }

theorem u718 : Upper (D 8) (R 8) [258,36,65,96,136,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b718 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b719 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 259 38 69 104 152 160 80 161 289), lower := (rows 259 38 69 104 152 160 80 128 256), losses := [] }

theorem u719 : Upper (D 8) (R 8) [258,36,65,96,136,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b719 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u719
end Delivery.IrregularNine14.P08

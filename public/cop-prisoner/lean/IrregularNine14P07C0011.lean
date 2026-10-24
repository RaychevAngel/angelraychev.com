import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b660 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 324, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 37 98 268 138 19 48 192 129 320), lower := (rows 37 98 268 138 19 48 192 129 256), losses := [] }

theorem u660 : Upper (D 7) (R 7) [36,96,264,130,3,16,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b660 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b661 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 309, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 37 98 268 138 19 48 192 192 257), lower := (rows 37 98 268 138 19 48 192 192 256), losses := [] }

theorem u661 : Upper (D 7) (R 7) [36,96,264,130,3,16,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b661 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b662 : PairBound 9 := { available := 8, camps := [{ cop := 3, region := 324, targets := 162 },{ cop := 1, region := 144, targets := 1 }], pairs := [(2,1),(2,5),(2,7),(4,0)], upper := (rows 37 98 324 25 146 160 65 130 264), lower := (rows 37 98 324 25 146 160 65 130 256), losses := [] }

theorem u662 : Upper (D 7) (R 7) [36,96,320,17,130,128,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b662 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b663 : PairBound 9 := { available := 2, camps := [{ cop := 5, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 98 324 25 146 160 65 136 258), lower := (rows 37 98 324 25 146 160 65 136 256), losses := [] }

theorem u663 : Upper (D 7) (R 7) [36,96,320,17,130,128,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b663 [(7,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b664 : PairBound 9 := { available := 2, camps := [{ cop := 5, region := 327, targets := 128 },{ cop := 1, region := 260, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(2,7)], upper := (rows 37 98 324 26 152 160 65 129 258), lower := (rows 37 98 324 26 152 160 65 129 256), losses := [] }

theorem u664 : Upper (D 7) (R 7) [36,96,320,18,136,128,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b664 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b665 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 152, targets := 65 }], pairs := [(3,0),(3,6),(4,0),(4,6)], upper := (rows 37 98 324 26 152 160 65 130 257), lower := (rows 37 98 324 26 152 160 65 130 256), losses := [] }

theorem u665 : Upper (D 7) (R 7) [36,96,320,18,136,128,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b665 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b666 : PairBound 9 := { available := 8, camps := [{ cop := 3, region := 324, targets := 162 }], pairs := [(2,1),(2,5),(2,7)], upper := (rows 37 98 324 137 146 48 65 130 264), lower := (rows 37 98 324 137 146 48 65 130 256), losses := [] }

theorem u666 : Upper (D 7) (R 7) [36,96,320,129,130,16,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b666 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b667 : PairBound 9 := { available := 2, camps := [{ cop := 4, region := 359, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 37 98 324 137 146 48 65 136 258), lower := (rows 37 98 324 137 146 48 65 136 256), losses := [] }

theorem u667 : Upper (D 7) (R 7) [36,96,320,129,130,16,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b667 [(5,4),(7,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b668 : PairBound 9 := { available := 2, camps := [{ cop := 7, region := 378, targets := 1 },{ cop := 1, region := 280, targets := 32 }], pairs := [(1,0),(3,0),(3,5),(4,0)], upper := (rows 37 194 13 88 400 34 96 129 258), lower := (rows 37 194 13 88 400 34 96 129 256), losses := [] }

theorem u668 : Upper (D 7) (R 7) [36,192,9,80,384,2,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b668 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b669 : PairBound 9 := { available := 1, camps := [{ cop := 8, region := 250, targets := 1 },{ cop := 3, region := 130, targets := 32 }], pairs := [(1,0),(1,5),(3,0),(4,0)], upper := (rows 37 194 13 88 400 34 96 130 257), lower := (rows 37 194 13 88 400 34 96 130 256), losses := [] }

theorem u669 : Upper (D 7) (R 7) [36,192,9,80,384,2,32,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b669 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b670 : PairBound 9 := { available := 16, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 3, region := 130, targets := 32 }], pairs := [(0,1),(1,0),(1,5),(3,0)], upper := (rows 37 194 13 328 145 34 96 130 272), lower := (rows 37 194 13 328 145 34 96 130 256), losses := [{ target := 1, region := (rows 97 0 127 123 18 32 97 128 434), good := (rows 365 477 77 333 477 381 365 412 256) }] }

theorem u670 : Upper (D 7) (R 7) [36,192,9,320,129,2,32,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b670 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b671 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 301, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 13 328 145 34 96 144 258), lower := (rows 37 194 13 328 145 34 96 144 256), losses := [] }

theorem u671 : Upper (D 7) (R 7) [36,192,9,320,129,2,32,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b671 [(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b672 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 272, targets := 160 },{ cop := 5, region := 338, targets := 1 }], pairs := [(1,0),(4,0),(4,5),(4,7)], upper := (rows 37 194 14 25 336 160 96 129 258), lower := (rows 37 194 14 25 336 160 96 129 256), losses := [] }

theorem u672 : Upper (D 7) (R 7) [36,192,10,17,320,128,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b672 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b673 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 344, targets := 130 }], pairs := [(3,1),(3,7),(4,1),(4,7)], upper := (rows 37 194 14 25 336 160 96 130 257), lower := (rows 37 194 14 25 336 160 96 130 256), losses := [] }

theorem u673 : Upper (D 7) (R 7) [36,192,10,17,320,128,32,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b673 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b674 : PairBound 9 := { available := 32, camps := [{ cop := 1, region := 316, targets := 1 },{ cop := 2, region := 161, targets := 64 }], pairs := [(0,6),(2,0),(3,0),(4,0)], upper := (rows 37 194 14 88 274 160 65 129 288), lower := (rows 37 194 14 88 274 160 65 129 256), losses := [] }

theorem u674 : Upper (D 7) (R 7) [36,192,10,80,258,128,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b674 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b675 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 433, targets := 64 },{ cop := 3, region := 166, targets := 1 }], pairs := [(0,6),(1,0),(2,0),(4,6)], upper := (rows 37 194 14 88 274 160 65 160 257), lower := (rows 37 194 14 88 274 160 65 160 256), losses := [] }

theorem u675 : Upper (D 7) (R 7) [36,192,10,80,258,128,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b675 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b676 : PairBound 9 := { available := 32, camps := [{ cop := 4, region := 142, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 194 28 11 81 160 320 130 288), lower := (rows 37 194 28 11 81 160 320 130 256), losses := [] }

theorem u676 : Upper (D 7) (R 7) [36,192,24,3,65,128,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b676 [(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b677 : PairBound 9 := { available := 2, camps := [{ cop := 3, region := 340, targets := 160 }], pairs := [(2,5),(2,7),(4,5)], upper := (rows 37 194 28 11 81 160 320 160 258), lower := (rows 37 194 28 11 81 160 320 160 256), losses := [] }

theorem u677 : Upper (D 7) (R 7) [36,192,24,3,65,128,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b677 [(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b678 : PairBound 9 := { available := 2, camps := [{ cop := 0, region := 202, targets := 32 },{ cop := 2, region := 161, targets := 66 }], pairs := [(0,1),(0,6),(1,5),(3,5)], upper := (rows 37 194 28 73 304 160 66 129 258), lower := (rows 37 194 28 73 304 160 66 129 256), losses := [] }

theorem u678 : Upper (D 7) (R 7) [36,192,24,65,288,128,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b678 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b679 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 317, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 37 194 28 73 304 160 66 130 257), lower := (rows 37 194 28 73 304 160 66 130 256), losses := [] }

theorem u679 : Upper (D 7) (R 7) [36,192,24,65,288,128,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b679 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b680 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 316, targets := 1 },{ cop := 1, region := 312, targets := 64 }], pairs := [(2,0),(3,0),(3,6),(4,0)], upper := (rows 37 194 76 26 304 160 65 129 258), lower := (rows 37 194 76 26 304 160 65 129 256), losses := [] }

theorem u680 : Upper (D 7) (R 7) [36,192,72,18,288,128,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b680 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b681 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 272, targets := 130 },{ cop := 0, region := 194, targets := 32 },{ cop := 0, region := 272, targets := 64 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 194 76 26 304 160 65 130 257), lower := (rows 37 194 76 26 304 160 65 130 256), losses := [] }

theorem u681 : Upper (D 7) (R 7) [36,192,72,18,288,128,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b681 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b682 : PairBound 9 := { available := 32, camps := [{ cop := 3, region := 358, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 37 194 76 137 19 34 320 144 288), lower := (rows 37 194 76 137 19 34 320 144 256), losses := [] }

theorem u682 : Upper (D 7) (R 7) [36,192,72,129,3,2,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b682 [(6,8),(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b683 : PairBound 9 := { available := 16, camps := [{ cop := 3, region := 342, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 37 194 76 137 19 34 320 160 272), lower := (rows 37 194 76 137 19 34 320 160 256), losses := [] }

theorem u683 : Upper (D 7) (R 7) [36,192,72,129,3,2,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b683 [(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b684 : PairBound 9 := { available := 2, camps := [{ cop := 0, region := 136, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 37 194 76 137 50 288 80 129 258), lower := (rows 37 194 76 137 50 288 80 129 256), losses := [] }

theorem u684 : Upper (D 7) (R 7) [36,192,72,129,34,256,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b684 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b685 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 301, targets := 2 }], pairs := [(0,1),(2,1)], upper := (rows 37 194 76 137 50 288 80 130 257), lower := (rows 37 194 76 137 50 288 80 130 256), losses := [] }

theorem u685 : Upper (D 7) (R 7) [36,192,72,129,34,256,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b685 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b686 : PairBound 9 := { available := 32, camps := [{ cop := 3, region := 374, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 37 194 76 137 274 34 80 129 288), lower := (rows 37 194 76 137 274 34 80 129 256), losses := [] }

theorem u686 : Upper (D 7) (R 7) [36,192,72,129,258,2,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b686 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b687 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 342, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 37 194 76 137 274 34 80 160 257), lower := (rows 37 194 76 137 274 34 80 160 256), losses := [] }

theorem u687 : Upper (D 7) (R 7) [36,192,72,129,258,2,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b687 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b688 : PairBound 9 := { available := 2, camps := [{ cop := 0, region := 136, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 37 194 76 137 304 34 80 129 258), lower := (rows 37 194 76 137 304 34 80 129 256), losses := [] }

theorem u688 : Upper (D 7) (R 7) [36,192,72,129,288,2,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b688 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b689 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 272, targets := 130 },{ cop := 8, region := 242, targets := 1 }], pairs := [(1,0),(4,1),(4,7)], upper := (rows 37 194 76 137 304 34 80 130 257), lower := (rows 37 194 76 137 304 34 80 130 256), losses := [] }

theorem u689 : Upper (D 7) (R 7) [36,192,72,129,288,2,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b689 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b690 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 316, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 37 194 76 152 50 288 65 129 258), lower := (rows 37 194 76 152 50 288 65 129 256), losses := [] }

theorem u690 : Upper (D 7) (R 7) [36,192,72,144,34,256,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b690 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b691 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 357, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 194 76 152 50 288 65 130 257), lower := (rows 37 194 76 152 50 288 65 130 256), losses := [] }

theorem u691 : Upper (D 7) (R 7) [36,192,72,144,34,256,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b691 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b692 : PairBound 9 := { available := 2, camps := [{ cop := 4, region := 136, targets := 98 },{ cop := 3, region := 98, targets := 1 }], pairs := [(1,0),(3,1),(3,5),(3,6)], upper := (rows 37 194 76 152 273 34 96 129 258), lower := (rows 37 194 76 152 273 34 96 129 256), losses := [] }

theorem u692 : Upper (D 7) (R 7) [36,192,72,144,257,2,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b692 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b693 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 238, targets := 1 },{ cop := 0, region := 272, targets := 2 }], pairs := [(1,0),(2,0),(3,0),(4,1)], upper := (rows 37 194 76 152 273 34 96 130 257), lower := (rows 37 194 76 152 273 34 96 130 256), losses := [] }

theorem u693 : Upper (D 7) (R 7) [36,192,72,144,257,2,32,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b693 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b694 : PairBound 9 := { available := 32, camps := [{ cop := 1, region := 316, targets := 1 },{ cop := 1, region := 312, targets := 64 }], pairs := [(2,0),(3,0),(3,6),(4,0)], upper := (rows 37 194 76 152 274 34 65 129 288), lower := (rows 37 194 76 152 274 34 65 129 256), losses := [] }

theorem u694 : Upper (D 7) (R 7) [36,192,72,144,258,2,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b694 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b695 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 168, targets := 65 },{ cop := 2, region := 162, targets := 1 }], pairs := [(1,0),(2,5),(3,0),(3,6)], upper := (rows 37 194 76 152 274 34 65 160 257), lower := (rows 37 194 76 152 274 34 65 160 256), losses := [{ target := 5, region := (rows 1 2 6 10 18 0 65 128 321), good := (rows 325 478 332 152 286 30 321 128 256) }] }

theorem u695 : Upper (D 7) (R 7) [36,192,72,144,258,2,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b695 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b696 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 316, targets := 1 },{ cop := 4, region := 205, targets := 2 }], pairs := [(0,1),(2,0),(3,0),(4,0)], upper := (rows 37 194 76 152 304 34 65 129 258), lower := (rows 37 194 76 152 304 34 65 129 256), losses := [] }

theorem u696 : Upper (D 7) (R 7) [36,192,72,144,288,2,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b696 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b697 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 272, targets := 130 },{ cop := 0, region := 194, targets := 32 },{ cop := 0, region := 272, targets := 64 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 194 76 152 304 34 65 130 257), lower := (rows 37 194 76 152 304 34 65 130 256), losses := [] }

theorem u697 : Upper (D 7) (R 7) [36,192,72,144,288,2,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b697 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b698 : PairBound 9 := { available := 32, camps := [{ cop := 0, region := 210, targets := 32 },{ cop := 2, region := 130, targets := 1 }], pairs := [(1,0),(1,5),(4,5)], upper := (rows 37 194 76 266 145 48 65 130 288), lower := (rows 37 194 76 266 145 48 65 130 256), losses := [] }

theorem u698 : Upper (D 7) (R 7) [36,192,72,258,129,16,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b698 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b699 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 268, targets := 161 }], pairs := [(2,0),(2,5),(2,7)], upper := (rows 37 194 76 266 145 48 65 160 258), lower := (rows 37 194 76 266 145 48 65 160 256), losses := [] }

theorem u699 : Upper (D 7) (R 7) [36,192,72,258,129,16,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b699 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b700 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 268, targets := 161 }], pairs := [(2,0),(2,5),(2,7)], upper := (rows 37 194 76 266 145 48 96 129 258), lower := (rows 37 194 76 266 145 48 96 129 256), losses := [] }

theorem u700 : Upper (D 7) (R 7) [36,192,72,258,129,16,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b700 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b701 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 130, targets := 33 }], pairs := [(1,0),(1,5),(3,5)], upper := (rows 37 194 76 266 145 48 96 130 257), lower := (rows 37 194 76 266 145 48 96 130 256), losses := [{ target := 5, region := (rows 1 70 4 9 17 0 64 207 273), good := (rows 415 194 206 394 409 272 194 130 256) }] }

theorem u701 : Upper (D 7) (R 7) [36,192,72,258,129,16,32,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b701 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b702 : PairBound 9 := { available := 2, camps := [{ cop := 4, region := 366, targets := 1 },{ cop := 7, region := 16, targets := 2 }], pairs := [(1,0),(2,0),(3,0),(4,1)], upper := (rows 37 194 76 280 145 34 96 129 258), lower := (rows 37 194 76 280 145 34 96 129 256), losses := [] }

theorem u702 : Upper (D 7) (R 7) [36,192,72,272,129,2,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b702 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b703 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 264, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 37 194 76 280 145 34 96 130 257), lower := (rows 37 194 76 280 145 34 96 130 256), losses := [] }

theorem u703 : Upper (D 7) (R 7) [36,192,72,272,129,2,32,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b703 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b704 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 316, targets := 1 },{ cop := 1, region := 312, targets := 64 }], pairs := [(2,0),(3,0),(3,6),(4,0)], upper := (rows 37 194 76 280 176 34 65 129 258), lower := (rows 37 194 76 280 176 34 65 129 256), losses := [] }

theorem u704 : Upper (D 7) (R 7) [36,192,72,272,160,2,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b704 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b705 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 333, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 194 76 280 176 34 65 130 257), lower := (rows 37 194 76 280 176 34 65 130 256), losses := [] }

theorem u705 : Upper (D 7) (R 7) [36,192,72,272,160,2,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b705 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b706 : PairBound 9 := { available := 32, camps := [{ cop := 0, region := 210, targets := 32 },{ cop := 1, region := 300, targets := 1 }], pairs := [(1,5),(2,0),(4,5)], upper := (rows 37 194 76 392 19 34 65 144 288), lower := (rows 37 194 76 392 19 34 65 144 256), losses := [] }

theorem u706 : Upper (D 7) (R 7) [36,192,72,384,3,2,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b706 [(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b707 : PairBound 9 := { available := 16, camps := [{ cop := 4, region := 424, targets := 65 },{ cop := 2, region := 162, targets := 1 }], pairs := [(1,0),(2,1),(3,0),(3,6)], upper := (rows 37 194 76 392 19 34 65 160 272), lower := (rows 37 194 76 392 19 34 65 160 256), losses := [{ target := 1, region := (rows 1 0 20 24 16 32 81 161 272), good := (rows 229 192 76 392 477 160 193 160 256) }] }

theorem u707 : Upper (D 7) (R 7) [36,192,72,384,3,2,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b707 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b708 : PairBound 9 := { available := 32, camps := [{ cop := 0, region := 210, targets := 32 },{ cop := 4, region := 424, targets := 1 }], pairs := [(1,5),(3,0),(4,5)], upper := (rows 37 194 76 392 19 48 65 130 288), lower := (rows 37 194 76 392 19 48 65 130 256), losses := [] }

theorem u708 : Upper (D 7) (R 7) [36,192,72,384,3,16,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b708 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b709 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 268, targets := 33 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 37 194 76 392 19 48 65 160 258), lower := (rows 37 194 76 392 19 48 65 160 256), losses := [] }

theorem u709 : Upper (D 7) (R 7) [36,192,72,384,3,16,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b709 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b710 : PairBound 9 := { available := 16, camps := [{ cop := 4, region := 325, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 194 324 11 176 34 65 136 272), lower := (rows 37 194 324 11 176 34 65 136 256), losses := [] }

theorem u710 : Upper (D 7) (R 7) [36,192,320,3,160,2,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b710 [(7,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b711 : PairBound 9 := { available := 8, camps := [{ cop := 1, region := 301, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 324 11 176 34 65 144 264), lower := (rows 37 194 324 11 176 34 65 144 256), losses := [] }

theorem u711 : Upper (D 7) (R 7) [36,192,320,3,160,2,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b711 [(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b712 : PairBound 9 := { available := 128, camps := [{ cop := 5, region := 453, targets := 2 },{ cop := 7, region := 358, targets := 1 }], pairs := [(0,1),(1,0),(2,0),(2,1)], upper := (rows 37 194 324 25 26 34 96 129 384), lower := (rows 37 194 324 25 26 34 96 129 256), losses := [] }

theorem u712 : Upper (D 7) (R 7) [36,192,320,17,10,2,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b712 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b713 : PairBound 9 := { available := 32, camps := [{ cop := 5, region := 325, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 194 324 25 26 160 65 130 288), lower := (rows 37 194 324 25 26 160 65 130 256), losses := [] }

theorem u713 : Upper (D 7) (R 7) [36,192,320,17,10,128,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b713 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b714 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 260, targets := 160 },{ cop := 6, region := 422, targets := 1 }], pairs := [(1,0),(2,0),(2,5),(2,7)], upper := (rows 37 194 324 25 26 160 65 160 258), lower := (rows 37 194 324 25 26 160 65 160 256), losses := [] }

theorem u714 : Upper (D 7) (R 7) [36,192,320,17,10,128,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b714 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b715 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 260, targets := 160 },{ cop := 5, region := 326, targets := 1 }], pairs := [(1,0),(2,0),(2,5),(2,7)], upper := (rows 37 194 324 25 26 160 96 129 258), lower := (rows 37 194 324 25 26 160 96 129 256), losses := [] }

theorem u715 : Upper (D 7) (R 7) [36,192,320,17,10,128,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b715 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b716 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 325, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 194 324 25 26 160 96 130 257), lower := (rows 37 194 324 25 26 160 96 130 256), losses := [] }

theorem u716 : Upper (D 7) (R 7) [36,192,320,17,10,128,32,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b716 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b717 : PairBound 9 := { available := 2, camps := [{ cop := 7, region := 24, targets := 98 }], pairs := [(3,1),(3,5),(3,6),(4,1)], upper := (rows 37 194 324 25 152 34 96 129 258), lower := (rows 37 194 324 25 152 34 96 129 256), losses := [] }

theorem u717 : Upper (D 7) (R 7) [36,192,320,17,136,2,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b717 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b718 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 325, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 194 324 25 152 34 96 130 257), lower := (rows 37 194 324 25 152 34 96 130 256), losses := [] }

theorem u718 : Upper (D 7) (R 7) [36,192,320,17,136,2,32,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b718 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b719 : PairBound 9 := { available := 8, camps := [{ cop := 3, region := 325, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 194 324 56 145 34 65 130 264), lower := (rows 37 194 324 56 145 34 65 130 256), losses := [] }

theorem u719 : Upper (D 7) (R 7) [36,192,320,48,129,2,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b719 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u719
end Delivery.IrregularNine14.P07

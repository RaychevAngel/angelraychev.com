import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0000

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b660 : PairBound 9 := { available := 8, camps := [{ cop := 1, region := 300, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 97 131 261 42 84 36 66 144 264), lower := (rows 97 131 261 42 84 36 66 144 256), losses := [] }

theorem u660 : Upper (D 6) (R 6) [96,129,257,34,68,4,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b660 [(7,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b661 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 324, targets := 33 },{ cop := 6, region := 33, targets := 2 }], pairs := [(0,1),(2,0),(2,5)], upper := (rows 97 134 268 26 52 33 66 129 320), lower := (rows 97 134 268 26 52 33 66 129 256), losses := [] }

theorem u661 : Upper (D 6) (R 6) [96,132,264,18,36,1,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b661 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b662 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 202, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 97 134 268 26 52 33 66 192 257), lower := (rows 97 134 268 26 52 33 66 192 256), losses := [] }

theorem u662 : Upper (D 6) (R 6) [96,132,264,18,36,1,2,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b662 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b663 : PairBound 9 := { available := 64, camps := [{ cop := 5, region := 325, targets := 2 },{ cop := 7, region := 358, targets := 1 }], pairs := [(0,1),(1,0),(2,1)], upper := (rows 97 134 292 25 26 34 68 129 320), lower := (rows 97 134 292 25 26 34 68 129 256), losses := [] }

theorem u663 : Upper (D 6) (R 6) [96,132,288,17,10,2,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b663 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b664 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 325, targets := 2 },{ cop := 8, region := 230, targets := 1 }], pairs := [(0,1),(1,0),(2,1)], upper := (rows 97 134 292 25 26 34 68 192 257), lower := (rows 97 134 292 25 26 34 68 192 256), losses := [] }

theorem u664 : Upper (D 6) (R 6) [96,132,288,17,10,2,4,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b664 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b665 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 400, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 7 11 21 104 400 34 68 224 352), lower := (rows 7 11 21 104 400 34 68 128 256), losses := [] }

theorem u665 : Upper (D 6) (R 6) [6,9,17,96,384,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b665 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b666 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 407, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 7 11 21 104 400 36 96 194 322), lower := (rows 7 11 21 104 400 36 96 128 256), losses := [] }

theorem u666 : Upper (D 6) (R 6) [6,9,17,96,384,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b666 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r667 : Route 9 := (fun mask => (mask,id))

def c667 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u667 : Upper (D 6) (R 6) [6,9,17,160,288,64,2] 13 := by
  apply FastRouting.sound _ _ [6,9,17,160,288,64,2] 13 (by decide) (choices 1) [4,64] r667 c667
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u0
  · exact u1

def b668 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 7 11 21 168 336 34 96 196 324), lower := (rows 7 11 21 168 336 34 96 128 256), losses := [{ target := 1, region := (rows 1 0 7 104 122 32 104 162 290), good := (rows 405 477 21 504 344 508 504 128 256) }] }

theorem u668 : Upper (D 6) (R 6) [6,9,17,160,320,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b668 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r669 : Route 9 := (fun mask => (mask,id))

def c669 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u669 : Upper (D 6) (R 6) [6,9,17,160,320,4,2] 13 := by
  apply FastRouting.sound _ _ [6,9,17,160,320,4,2] 13 (by decide) (choices 1) [32,64] r669 c669
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2
  · exact u3

def b670 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0),(4,0),(4,2)], upper := (rows 7 11 21 168 336 36 96 194 322), lower := (rows 7 11 21 168 336 36 96 128 256), losses := [{ target := 2, region := (rows 1 2 0 8 18 32 104 130 258), good := (rows 403 475 17 232 336 96 96 128 256) }] }

theorem u670 : Upper (D 6) (R 6) [6,9,17,160,320,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b670 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b671 : PairBound 9 := { available := 6, camps := [{ cop := 7, region := 104, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 11 21 168 336 96 96 134 262), lower := (rows 7 11 21 168 336 96 96 128 256), losses := [] }

theorem u671 : Upper (D 6) (R 6) [6,9,17,160,320,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b671 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b672 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 424, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 11 37 152 84 96 66 416 288), lower := (rows 7 11 37 152 84 96 66 128 256), losses := [] }

theorem u672 : Upper (D 6) (R 6) [6,9,33,144,68,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b672 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b673 : PairBound 9 := { available := 258, camps := [{ cop := 4, region := 395, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 11 37 152 84 96 96 386 258), lower := (rows 7 11 37 152 84 96 96 128 256), losses := [] }

theorem u673 : Upper (D 6) (R 6) [6,9,33,144,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b673 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b674 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 11 37 152 84 96 320 162 290), lower := (rows 7 11 37 152 84 96 320 128 256), losses := [] }

theorem u674 : Upper (D 6) (R 6) [6,9,33,144,68,64,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b674 [(6,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b675 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 7 11 37 152 276 96 66 224 352), lower := (rows 7 11 37 152 276 96 66 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 20 96 64 224 352), good := (rows 29 9 445 152 284 480 480 128 256) }] }

theorem u675 : Upper (D 6) (R 6) [6,9,33,144,260,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b675 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b676 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 0, region := 100, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 7 11 37 152 276 96 96 194 322), lower := (rows 7 11 37 152 276 96 96 128 256), losses := [] }

theorem u676 : Upper (D 6) (R 6) [6,9,33,144,260,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b676 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r677 : Route 9 := (fun mask => (mask,id))

def c677 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u677 : Upper (D 6) (R 6) [6,9,33,144,288,64,2] 13 := by
  apply FastRouting.sound _ _ [6,9,33,144,288,64,2] 13 (by decide) (choices 1) [4,64] r677 c677
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4
  · exact u5

def b678 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 0, region := 100, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 7 11 37 152 304 96 68 194 322), lower := (rows 7 11 37 152 304 96 68 128 256), losses := [] }

theorem u678 : Upper (D 6) (R 6) [6,9,33,144,288,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b678 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r679 : Route 9 := (fun mask => (mask,id))

def c679 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u679 : Upper (D 6) (R 6) [6,9,33,144,320,64,2] 13 := by
  apply FastRouting.sound _ _ [6,9,33,144,320,64,2] 13 (by decide) (choices 1) [4,32] r679 c679
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6
  · exact u7

def b680 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 0, region := 100, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 7 11 37 152 336 96 68 162 290), lower := (rows 7 11 37 152 336 96 68 128 256), losses := [] }

theorem u680 : Upper (D 6) (R 6) [6,9,33,144,320,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b680 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b681 : PairBound 9 := { available := 6, camps := [{ cop := 8, region := 112, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 7 11 37 152 336 96 96 134 262), lower := (rows 7 11 37 152 336 96 96 128 256), losses := [] }

theorem u681 : Upper (D 6) (R 6) [6,9,33,144,320,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b681 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b682 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 424, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 11 37 392 82 96 68 176 304), lower := (rows 7 11 37 392 82 96 68 128 256), losses := [] }

theorem u682 : Upper (D 6) (R 6) [6,9,33,384,66,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b682 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b683 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 11 37 392 82 96 80 164 292), lower := (rows 7 11 37 392 82 96 80 128 256), losses := [] }

theorem u683 : Upper (D 6) (R 6) [6,9,33,384,66,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b683 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b684 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 0, region := 100, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 7 11 37 392 82 96 96 148 276), lower := (rows 7 11 37 392 82 96 96 128 256), losses := [] }

theorem u684 : Upper (D 6) (R 6) [6,9,33,384,66,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b684 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b685 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 424, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 11 37 392 84 96 66 176 304), lower := (rows 7 11 37 392 84 96 66 128 256), losses := [] }

theorem u685 : Upper (D 6) (R 6) [6,9,33,384,68,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b685 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b686 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 11 37 392 84 96 80 162 290), lower := (rows 7 11 37 392 84 96 80 128 256), losses := [] }

theorem u686 : Upper (D 6) (R 6) [6,9,33,384,68,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b686 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b687 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 395, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 11 37 392 84 96 96 146 274), lower := (rows 7 11 37 392 84 96 96 128 256), losses := [] }

theorem u687 : Upper (D 6) (R 6) [6,9,33,384,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b687 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b688 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 404, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 11 52 74 400 96 65 164 292), lower := (rows 7 11 52 74 400 96 65 128 256), losses := [] }

theorem u688 : Upper (D 6) (R 6) [6,9,48,66,384,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b688 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b689 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 75, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 11 52 74 400 96 68 161 289), lower := (rows 7 11 52 74 400 96 68 128 256), losses := [] }

theorem u689 : Upper (D 6) (R 6) [6,9,48,66,384,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b689 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b690 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 106, targets := 4 }], pairs := [(1,2),(2,1),(4,1)], upper := (rows 7 11 52 74 400 96 96 133 261), lower := (rows 7 11 52 74 400 96 96 128 256), losses := [] }

theorem u690 : Upper (D 6) (R 6) [6,9,48,66,384,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b690 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b691 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(2,0),(4,5)], upper := (rows 7 11 52 104 208 288 65 134 262), lower := (rows 7 11 52 104 208 288 65 128 256), losses := [{ target := 0, region := (rows 0 2 92 88 80 355 64 131 259), good := (rows 422 430 60 124 252 288 508 128 288) }] }

theorem u691 : Upper (D 6) (R 6) [6,9,48,96,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b691 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b692 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(2,1),(4,5)], upper := (rows 7 11 52 104 208 288 66 133 261), lower := (rows 7 11 52 104 208 288 66 128 256), losses := [{ target := 1, region := (rows 1 0 92 88 80 355 64 131 259), good := (rows 421 429 60 124 252 288 508 128 288) }] }

theorem u692 : Upper (D 6) (R 6) [6,9,48,96,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b692 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b693 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 11 52 104 208 288 68 131 259), lower := (rows 7 11 52 104 208 288 68 128 256), losses := [] }

theorem u693 : Upper (D 6) (R 6) [6,9,48,96,192,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b693 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b694 : PairBound 9 := { available := 288, camps := [{ cop := 0, region := 490, targets := 4 },{ cop := 0, region := 80, targets := 1 }], pairs := [(1,2),(3,2),(4,0)], upper := (rows 7 11 52 200 84 33 66 416 288), lower := (rows 7 11 52 200 84 33 66 128 256), losses := [] }

theorem u694 : Upper (D 6) (R 6) [6,9,48,192,68,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b694 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b695 : PairBound 9 := { available := 258, camps := [{ cop := 5, region := 84, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 11 52 200 84 33 96 386 258), lower := (rows 7 11 52 200 84 33 96 128 256), losses := [] }

theorem u695 : Upper (D 6) (R 6) [6,9,48,192,68,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b695 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b696 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 490, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 11 52 200 84 33 320 162 290), lower := (rows 7 11 52 200 84 33 320 128 256), losses := [] }

theorem u696 : Upper (D 6) (R 6) [6,9,48,192,68,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b696 [(6,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b697 : PairBound 9 := { available := 288, camps := [{ cop := 0, region := 80, targets := 34 },{ cop := 0, region := 490, targets := 4 }], pairs := [(1,2),(4,1),(4,5)], upper := (rows 7 11 52 200 84 34 65 416 288), lower := (rows 7 11 52 200 84 34 65 128 256), losses := [] }

theorem u697 : Upper (D 6) (R 6) [6,9,48,192,68,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b697 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b698 : PairBound 9 := { available := 257, camps := [{ cop := 5, region := 84, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 11 52 200 84 34 96 385 257), lower := (rows 7 11 52 200 84 34 96 128 256), losses := [] }

theorem u698 : Upper (D 6) (R 6) [6,9,48,192,68,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b698 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b699 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 490, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 11 52 200 84 34 320 161 289), lower := (rows 7 11 52 200 84 34 320 128 256), losses := [] }

theorem u699 : Upper (D 6) (R 6) [6,9,48,192,68,2,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b699 [(6,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b700 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 232, targets := 1 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 11 52 200 273 96 66 164 292), lower := (rows 7 11 52 200 273 96 66 128 256), losses := [{ target := 0, region := (rows 0 2 20 27 16 123 67 149 277), good := (rows 494 490 444 232 508 96 106 128 256) },{ target := 1, region := (rows 1 0 70 104 19 104 64 238 366), good := (rows 405 445 444 492 273 492 508 128 256) }] }

theorem u700 : Upper (D 6) (R 6) [6,9,48,192,257,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b700 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b701 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 100, targets := 3 },{ cop := 0, region := 232, targets := 1 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 11 52 200 273 96 68 162 290), lower := (rows 7 11 52 200 273 96 68 128 256), losses := [] }

theorem u701 : Upper (D 6) (R 6) [6,9,48,192,257,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b701 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b702 : PairBound 9 := { available := 6, camps := [{ cop := 7, region := 104, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 11 52 200 273 96 96 134 262), lower := (rows 7 11 52 200 273 96 96 128 256), losses := [] }

theorem u702 : Upper (D 6) (R 6) [6,9,48,192,257,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b702 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b703 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 232, targets := 2 }], pairs := [(2,0),(3,0),(3,1)], upper := (rows 7 11 52 200 274 96 65 164 292), lower := (rows 7 11 52 200 274 96 65 128 256), losses := [{ target := 0, region := (rows 0 2 70 104 19 104 64 238 366), good := (rows 406 446 444 492 406 492 508 128 256) }] }

theorem u703 : Upper (D 6) (R 6) [6,9,48,192,258,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b703 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b704 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 100, targets := 3 },{ cop := 0, region := 232, targets := 2 }], pairs := [(2,0),(2,1),(3,1)], upper := (rows 7 11 52 200 274 96 68 161 289), lower := (rows 7 11 52 200 274 96 68 128 256), losses := [] }

theorem u704 : Upper (D 6) (R 6) [6,9,48,192,258,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b704 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b705 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 104, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 11 52 200 274 96 96 133 261), lower := (rows 7 11 52 200 274 96 96 128 256), losses := [] }

theorem u705 : Upper (D 6) (R 6) [6,9,48,192,258,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b705 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b706 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 234, targets := 4 }], pairs := [(1,2),(2,0),(3,2)], upper := (rows 7 11 52 200 276 33 66 224 352), lower := (rows 7 11 52 200 276 33 66 128 256), losses := [{ target := 0, region := (rows 0 2 36 40 52 32 67 160 288), good := (rows 86 74 444 200 276 508 66 128 256) }] }

theorem u706 : Upper (D 6) (R 6) [6,9,48,192,260,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b706 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b707 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 234, targets := 4 }], pairs := [(1,2),(2,0),(3,2)], upper := (rows 7 11 52 200 276 33 96 194 322), lower := (rows 7 11 52 200 276 33 96 128 256), losses := [{ target := 0, region := (rows 0 2 100 41 49 32 100 129 257), good := (rows 478 410 124 204 340 508 124 128 256) }] }

theorem u707 : Upper (D 6) (R 6) [6,9,48,192,260,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b707 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b708 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 234, targets := 4 }], pairs := [(1,2),(2,0),(3,2)], upper := (rows 7 11 52 200 276 34 65 224 352), lower := (rows 7 11 52 200 276 34 65 128 256), losses := [{ target := 0, region := (rows 0 2 70 72 88 35 64 192 320), good := (rows 38 62 52 476 276 38 508 128 256) }] }

theorem u708 : Upper (D 6) (R 6) [6,9,48,192,260,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b708 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b709 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 234, targets := 4 }], pairs := [(1,2),(3,1),(3,2)], upper := (rows 7 11 52 200 276 34 96 193 321), lower := (rows 7 11 52 200 276 34 96 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 17 32 100 129 257), good := (rows 477 409 116 200 340 96 96 128 256) }] }

theorem u709 : Upper (D 6) (R 6) [6,9,48,192,260,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b709 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b710 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 234, targets := 4 }], pairs := [(1,2),(2,0),(3,2)], upper := (rows 7 11 52 200 276 96 65 162 290), lower := (rows 7 11 52 200 276 96 65 128 256), losses := [{ target := 0, region := (rows 0 2 70 8 19 104 64 130 258), good := (rows 406 446 52 236 276 100 116 128 256) }] }

theorem u710 : Upper (D 6) (R 6) [6,9,48,192,260,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b710 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b711 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 234, targets := 4 }], pairs := [(1,2),(2,1),(3,2)], upper := (rows 7 11 52 200 276 96 66 161 289), lower := (rows 7 11 52 200 276 96 66 128 256), losses := [{ target := 1, region := (rows 1 0 110 72 83 104 64 130 258), good := (rows 405 445 52 252 276 124 508 128 256) }] }

theorem u711 : Upper (D 6) (R 6) [6,9,48,192,260,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b711 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b712 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 116, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 11 52 200 276 96 96 131 259), lower := (rows 7 11 52 200 276 96 96 128 256), losses := [] }

theorem u712 : Upper (D 6) (R 6) [6,9,48,192,260,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b712 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b713 : PairBound 9 := { available := 36, camps := [], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 11 52 200 336 33 66 164 292), lower := (rows 7 11 52 200 336 33 66 128 256), losses := [{ target := 0, region := (rows 0 2 36 41 49 32 67 164 292), good := (rows 478 90 444 200 336 508 66 128 256) }] }

theorem u713 : Upper (D 6) (R 6) [6,9,48,192,320,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b713 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r714 : Route 9 := (fun mask => (mask,id))

def c714 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u714 : Upper (D 6) (R 6) [6,9,48,192,320,1,4] 13 := by
  apply FastRouting.sound _ _ [6,9,48,192,320,1,4] 13 (by decide) (choices 1) [2,32] r714 c714
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8
  · exact u9

def b715 : PairBound 9 := { available := 6, camps := [], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 11 52 200 336 33 96 134 262), lower := (rows 7 11 52 200 336 33 96 128 256), losses := [{ target := 0, region := (rows 0 2 100 41 49 32 100 129 257), good := (rows 478 410 124 204 340 508 124 128 256) }] }

theorem u715 : Upper (D 6) (R 6) [6,9,48,192,320,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b715 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b716 : PairBound 9 := { available := 36, camps := [], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 11 52 200 336 34 65 164 292), lower := (rows 7 11 52 200 336 34 65 128 256), losses := [{ target := 0, region := (rows 0 2 70 88 88 35 64 231 359), good := (rows 422 446 444 476 476 422 508 128 256) }] }

theorem u716 : Upper (D 6) (R 6) [6,9,48,192,320,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b716 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r717 : Route 9 := (fun mask => (mask,id))

def c717 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u717 : Upper (D 6) (R 6) [6,9,48,192,320,2,4] 13 := by
  apply FastRouting.sound _ _ [6,9,48,192,320,2,4] 13 (by decide) (choices 1) [1,32] r717 c717
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10
  · exact u11

def r718 : Route 9 := (fun mask => (mask,id))

def c718 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u718 : Upper (D 6) (R 6) [6,9,48,192,320,2,32] 13 := by
  apply FastRouting.sound _ _ [6,9,48,192,320,2,32] 13 (by decide) (choices 1) [1,4] r718 c718
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u12
  · exact u13

def b719 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 490, targets := 4 },{ cop := 0, region := 80, targets := 1 }], pairs := [(1,2),(3,2),(4,0)], upper := (rows 7 11 52 392 84 33 66 224 352), lower := (rows 7 11 52 392 84 33 66 128 256), losses := [] }

theorem u719 : Upper (D 6) (R 6) [6,9,48,384,68,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b719 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u719
end Delivery.IrregularNine14.P06

import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0004

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3660 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 163, targets := 64 }], pairs := [(0,6),(1,6),(2,0)], upper := (rows 11 131 52 76 336 33 66 164 292), lower := (rows 11 131 52 76 336 33 66 128 256), losses := [{ target := 0, region := (rows 0 2 36 40 56 32 67 164 292), good := (rows 90 194 444 476 336 508 66 128 256) }] }

theorem u3660 : Upper (D 6) (R 6) [10,129,48,68,320,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3660 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3661 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 72, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 131 52 76 336 33 68 162 290), lower := (rows 11 131 52 76 336 33 68 128 256), losses := [] }

theorem u3661 : Upper (D 6) (R 6) [10,129,48,68,320,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3661 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3662 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 403, targets := 32 }], pairs := [(0,5),(1,5),(4,5)], upper := (rows 11 131 52 76 336 33 96 134 262), lower := (rows 11 131 52 76 336 33 96 128 256), losses := [] }

theorem u3662 : Upper (D 6) (R 6) [10,129,48,68,320,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3662 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3663 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 163, targets := 64 }], pairs := [(0,6),(1,6),(2,0)], upper := (rows 11 131 52 76 336 34 65 164 292), lower := (rows 11 131 52 76 336 34 65 128 256), losses := [{ target := 0, region := (rows 0 2 69 88 88 35 64 199 327), good := (rows 446 422 444 476 476 418 508 128 256) }] }

theorem u3663 : Upper (D 6) (R 6) [10,129,48,68,320,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3663 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3664 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 72, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 131 52 76 336 34 68 161 289), lower := (rows 11 131 52 76 336 34 68 128 256), losses := [] }

theorem u3664 : Upper (D 6) (R 6) [10,129,48,68,320,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3664 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3665 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 403, targets := 32 }], pairs := [(0,5),(1,5),(4,5)], upper := (rows 11 131 52 76 336 34 96 133 261), lower := (rows 11 131 52 76 336 34 96 128 256), losses := [] }

theorem u3665 : Upper (D 6) (R 6) [10,129,48,68,320,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3665 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3666 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 194, targets := 32 }], pairs := [(1,5),(2,0)], upper := (rows 11 131 52 104 21 288 66 196 324), lower := (rows 11 131 52 104 21 288 66 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 308 67 144 272), good := (rows 74 194 444 104 508 288 66 128 288) }] }

theorem u3666 : Upper (D 6) (R 6) [10,129,48,96,5,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3666 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3667 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 427, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 11 131 52 104 21 288 68 194 322), lower := (rows 11 131 52 104 21 288 68 128 256), losses := [] }

theorem u3667 : Upper (D 6) (R 6) [10,129,48,96,5,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3667 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3668 : PairBound 9 := { available := 68, camps := [], pairs := [(2,0),(3,0)], upper := (rows 11 131 52 104 22 288 65 196 324), lower := (rows 11 131 52 104 22 288 65 128 256), losses := [{ target := 0, region := (rows 0 2 71 72 19 361 64 200 328), good := (rows 446 182 52 492 22 288 508 128 288) }] }

theorem u3668 : Upper (D 6) (R 6) [10,129,48,96,6,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3668 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3669 : PairBound 9 := { available := 65, camps := [{ cop := 6, region := 427, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 11 131 52 104 22 288 68 193 321), lower := (rows 11 131 52 104 22 288 68 128 256), losses := [] }

theorem u3669 : Upper (D 6) (R 6) [10,129,48,96,6,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3669 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3670 : PairBound 9 := { available := 4, camps := [{ cop := 4, region := 292, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 11 131 52 104 82 288 65 132 260), lower := (rows 11 131 52 104 82 288 65 128 256), losses := [] }

theorem u3670 : Upper (D 6) (R 6) [10,129,48,96,66,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3670 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3671 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 131 52 104 82 288 68 133 261), lower := (rows 11 131 52 104 82 288 68 128 256), losses := [] }

theorem u3671 : Upper (D 6) (R 6) [10,129,48,96,66,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3671 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3672 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 276, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 52 104 276 34 65 196 324), lower := (rows 11 131 52 104 276 34 65 128 256), losses := [] }

theorem u3672 : Upper (D 6) (R 6) [10,129,48,96,260,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3672 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3673 : PairBound 9 := { available := 65, camps := [{ cop := 6, region := 171, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 131 52 104 276 34 68 193 321), lower := (rows 11 131 52 104 276 34 68 128 256), losses := [] }

theorem u3673 : Upper (D 6) (R 6) [10,129,48,96,260,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3673 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3674 : PairBound 9 := { available := 4, camps := [{ cop := 3, region := 276, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 52 104 336 34 65 132 260), lower := (rows 11 131 52 104 336 34 65 128 256), losses := [] }

theorem u3674 : Upper (D 6) (R 6) [10,129,48,96,320,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3674 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r3675 : Route 9 := (fun mask => (mask,id))

def c3675 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3675 : Upper (D 6) (R 6) [10,129,48,96,320,2,4] 13 := by
  apply FastRouting.sound _ _ [10,129,48,96,320,2,4] 13 (by decide) (choices 1) [1,4] r3675 c3675
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u264
  · exact u265

def b3676 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 227, targets := 4 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 11 131 52 268 84 33 66 224 352), lower := (rows 11 131 52 268 84 33 66 128 256), losses := [{ target := 0, region := (rows 0 2 36 44 48 32 67 160 288), good := (rows 74 194 444 268 92 508 66 128 256) }] }

theorem u3676 : Upper (D 6) (R 6) [10,129,48,260,68,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3676 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3677 : PairBound 9 := { available := 66, camps := [{ cop := 5, region := 84, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 52 268 84 33 96 194 322), lower := (rows 11 131 52 268 84 33 96 128 256), losses := [] }

theorem u3677 : Upper (D 6) (R 6) [10,129,48,260,68,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3677 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3678 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 227, targets := 4 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 11 131 52 268 84 34 65 224 352), lower := (rows 11 131 52 268 84 34 65 128 256), losses := [{ target := 0, region := (rows 0 2 68 88 80 35 64 192 320), good := (rows 42 162 60 268 476 34 508 128 256) }] }

theorem u3678 : Upper (D 6) (R 6) [10,129,48,260,68,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3678 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3679 : PairBound 9 := { available := 65, camps := [{ cop := 5, region := 84, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 52 268 84 34 96 193 321), lower := (rows 11 131 52 268 84 34 96 128 256), losses := [] }

theorem u3679 : Upper (D 6) (R 6) [10,129,48,260,68,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3679 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3680 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 194, targets := 32 }], pairs := [(1,5),(2,0),(3,0)], upper := (rows 11 131 52 296 21 96 66 196 324), lower := (rows 11 131 52 296 21 96 66 128 256), losses := [{ target := 0, region := (rows 0 2 20 28 16 115 67 144 272), good := (rows 106 226 444 296 508 96 98 128 256) }] }

theorem u3680 : Upper (D 6) (R 6) [10,129,48,288,5,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3680 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3681 : PairBound 9 := { available := 66, camps := [{ cop := 5, region := 395, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 131 52 296 21 96 68 194 322), lower := (rows 11 131 52 296 21 96 68 128 256), losses := [] }

theorem u3681 : Upper (D 6) (R 6) [10,129,48,288,5,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3681 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r3682 : Route 9 := (fun mask => (mask,id))

def c3682 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3682 : Upper (D 6) (R 6) [10,129,48,288,6,64,1] 13 := by
  apply FastRouting.sound _ _ [10,129,48,288,6,64,1] 13 (by decide) (choices 1) [4,64] r3682 c3682
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u266
  · exact u267

def b3683 : PairBound 9 := { available := 65, camps := [{ cop := 5, region := 395, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 131 52 296 22 96 68 193 321), lower := (rows 11 131 52 296 22 96 68 128 256), losses := [] }

theorem u3683 : Upper (D 6) (R 6) [10,129,48,288,6,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3683 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3684 : PairBound 9 := { available := 68, camps := [], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 131 52 296 84 34 65 196 324), lower := (rows 11 131 52 296 84 34 65 128 256), losses := [{ target := 0, region := (rows 0 2 68 76 80 35 64 208 336), good := (rows 42 162 444 296 476 34 508 128 256) }] }

theorem u3684 : Upper (D 6) (R 6) [10,129,48,288,68,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3684 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3685 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 84, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 52 296 84 34 68 193 321), lower := (rows 11 131 52 296 84 34 68 128 256), losses := [] }

theorem u3685 : Upper (D 6) (R 6) [10,129,48,288,68,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3685 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3686 : PairBound 9 := { available := 36, camps := [], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 131 52 328 22 96 65 164 292), lower := (rows 11 131 52 328 22 96 65 128 256), losses := [{ target := 0, region := (rows 0 2 69 104 19 104 64 237 365), good := (rows 446 406 444 492 406 492 508 128 256) }] }

theorem u3686 : Upper (D 6) (R 6) [10,129,48,320,6,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3686 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3687 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 395, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 131 52 328 22 96 68 161 289), lower := (rows 11 131 52 328 22 96 68 128 256), losses := [] }

theorem u3687 : Upper (D 6) (R 6) [10,129,48,320,6,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3687 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3688 : PairBound 9 := { available := 5, camps := [{ cop := 8, region := 104, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 131 52 328 22 96 96 133 261), lower := (rows 11 131 52 328 22 96 96 128 256), losses := [] }

theorem u3688 : Upper (D 6) (R 6) [10,129,48,320,6,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3688 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3689 : PairBound 9 := { available := 36, camps := [], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 131 52 328 84 33 66 164 292), lower := (rows 11 131 52 328 84 33 66 128 256), losses := [{ target := 0, region := (rows 0 2 36 56 48 32 67 164 292), good := (rows 74 194 444 328 476 508 66 128 256) }] }

theorem u3689 : Upper (D 6) (R 6) [10,129,48,320,68,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3689 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3690 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 163, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 131 52 328 84 33 68 162 290), lower := (rows 11 131 52 328 84 33 68 128 256), losses := [] }

theorem u3690 : Upper (D 6) (R 6) [10,129,48,320,68,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3690 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3691 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 84, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 52 328 84 33 96 134 262), lower := (rows 11 131 52 328 84 33 96 128 256), losses := [] }

theorem u3691 : Upper (D 6) (R 6) [10,129,48,320,68,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3691 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3692 : PairBound 9 := { available := 36, camps := [], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 131 52 328 84 34 65 164 292), lower := (rows 11 131 52 328 84 34 65 128 256), losses := [{ target := 0, region := (rows 0 2 69 88 88 35 64 199 327), good := (rows 446 422 444 476 476 418 508 128 256) }] }

theorem u3692 : Upper (D 6) (R 6) [10,129,48,320,68,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3692 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3693 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 163, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 131 52 328 84 34 68 161 289), lower := (rows 11 131 52 328 84 34 68 128 256), losses := [] }

theorem u3693 : Upper (D 6) (R 6) [10,129,48,320,68,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3693 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3694 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 84, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 52 328 84 34 96 133 261), lower := (rows 11 131 52 328 84 34 96 128 256), losses := [] }

theorem u3694 : Upper (D 6) (R 6) [10,129,48,320,68,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3694 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3695 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 280, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 100 28 304 33 66 196 324), lower := (rows 11 131 100 28 304 33 66 128 256), losses := [] }

theorem u3695 : Upper (D 6) (R 6) [10,129,96,20,288,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3695 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3696 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 76, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 100 28 304 33 68 194 322), lower := (rows 11 131 100 28 304 33 68 128 256), losses := [] }

theorem u3696 : Upper (D 6) (R 6) [10,129,96,20,288,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3696 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3697 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 280, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 100 28 304 34 65 196 324), lower := (rows 11 131 100 28 304 34 65 128 256), losses := [] }

theorem u3697 : Upper (D 6) (R 6) [10,129,96,20,288,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3697 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3698 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 76, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 100 28 304 34 68 193 321), lower := (rows 11 131 100 28 304 34 68 128 256), losses := [] }

theorem u3698 : Upper (D 6) (R 6) [10,129,96,20,288,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3698 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3699 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 280, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 100 56 276 33 66 196 324), lower := (rows 11 131 100 56 276 33 66 128 256), losses := [] }

theorem u3699 : Upper (D 6) (R 6) [10,129,96,48,260,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3699 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3700 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 68, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 100 56 276 33 68 194 322), lower := (rows 11 131 100 56 276 33 68 128 256), losses := [{ target := 0, region := (rows 0 2 44 44 49 32 125 131 259), good := (rows 478 466 124 124 348 508 76 128 256) }] }

theorem u3700 : Upper (D 6) (R 6) [10,129,96,48,260,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3700 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3701 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 280, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 100 56 276 34 65 196 324), lower := (rows 11 131 100 56 276 34 65 128 256), losses := [] }

theorem u3701 : Upper (D 6) (R 6) [10,129,96,48,260,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3701 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3702 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 68, targets := 3 }], pairs := [(2,0),(2,1),(3,1)], upper := (rows 11 131 100 56 276 34 68 193 321), lower := (rows 11 131 100 56 276 34 68 128 256), losses := [{ target := 1, region := (rows 1 0 44 44 49 32 125 131 259), good := (rows 477 465 124 124 348 508 76 128 256) }] }

theorem u3702 : Upper (D 6) (R 6) [10,129,96,48,260,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3702 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3703 : PairBound 9 := { available := 4, camps := [{ cop := 2, region := 280, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 100 56 336 33 66 132 260), lower := (rows 11 131 100 56 336 33 66 128 256), losses := [] }

theorem u3703 : Upper (D 6) (R 6) [10,129,96,48,320,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3703 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3704 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 68, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 100 56 336 33 68 134 262), lower := (rows 11 131 100 56 336 33 68 128 256), losses := [{ target := 0, region := (rows 0 2 44 44 51 32 109 129 257), good := (rows 478 466 124 124 336 508 76 128 256) }] }

theorem u3704 : Upper (D 6) (R 6) [10,129,96,48,320,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3704 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3705 : PairBound 9 := { available := 4, camps := [{ cop := 2, region := 280, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 100 56 336 34 65 132 260), lower := (rows 11 131 100 56 336 34 65 128 256), losses := [] }

theorem u3705 : Upper (D 6) (R 6) [10,129,96,48,320,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3705 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3706 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 68, targets := 3 }], pairs := [(2,0),(2,1),(3,1)], upper := (rows 11 131 100 56 336 34 68 133 261), lower := (rows 11 131 100 56 336 34 68 128 256), losses := [{ target := 1, region := (rows 1 0 44 40 19 32 109 129 257), good := (rows 477 465 108 124 336 124 68 128 256) }] }

theorem u3706 : Upper (D 6) (R 6) [10,129,96,48,320,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3706 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3707 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 264, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 131 100 268 21 34 80 224 352), lower := (rows 11 131 100 268 21 34 80 128 256), losses := [] }

theorem u3707 : Upper (D 6) (R 6) [10,129,96,260,5,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3707 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3708 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 395, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 131 100 268 21 48 96 194 322), lower := (rows 11 131 100 268 21 48 96 128 256), losses := [] }

theorem u3708 : Upper (D 6) (R 6) [10,129,96,260,5,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3708 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3709 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 264, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 131 100 268 22 33 80 224 352), lower := (rows 11 131 100 268 22 33 80 128 256), losses := [] }

theorem u3709 : Upper (D 6) (R 6) [10,129,96,260,6,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3709 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3710 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 411, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 131 100 268 22 33 96 208 336), lower := (rows 11 131 100 268 22 33 96 128 256), losses := [] }

theorem u3710 : Upper (D 6) (R 6) [10,129,96,260,6,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3710 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3711 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 395, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 131 100 268 22 48 96 193 321), lower := (rows 11 131 100 268 22 48 96 128 256), losses := [] }

theorem u3711 : Upper (D 6) (R 6) [10,129,96,260,6,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3711 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3712 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 264, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 131 100 296 21 48 66 196 324), lower := (rows 11 131 100 296 21 48 66 128 256), losses := [] }

theorem u3712 : Upper (D 6) (R 6) [10,129,96,288,5,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3712 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3713 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 395, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 11 131 100 296 21 48 68 194 322), lower := (rows 11 131 100 296 21 48 68 128 256), losses := [] }

theorem u3713 : Upper (D 6) (R 6) [10,129,96,288,5,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3713 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3714 : PairBound 9 := { available := 80, camps := [{ cop := 6, region := 36, targets := 3 }], pairs := [(2,0),(2,1),(3,1)], upper := (rows 11 131 100 296 22 36 65 208 336), lower := (rows 11 131 100 296 22 36 65 128 256), losses := [{ target := 1, region := (rows 1 0 87 24 16 119 67 144 272), good := (rows 109 229 100 296 508 36 101 128 256) }] }

theorem u3714 : Upper (D 6) (R 6) [10,129,96,288,6,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3714 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3715 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 395, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 11 131 100 296 22 36 80 193 321), lower := (rows 11 131 100 296 22 36 80 128 256), losses := [] }

theorem u3715 : Upper (D 6) (R 6) [10,129,96,288,6,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3715 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3716 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 264, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 131 100 296 22 48 65 196 324), lower := (rows 11 131 100 296 22 48 65 128 256), losses := [] }

theorem u3716 : Upper (D 6) (R 6) [10,129,96,288,6,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3716 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3717 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 395, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 11 131 100 296 22 48 68 193 321), lower := (rows 11 131 100 296 22 48 68 128 256), losses := [] }

theorem u3717 : Upper (D 6) (R 6) [10,129,96,288,6,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3717 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3718 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 300, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 100 296 81 36 66 148 276), lower := (rows 11 131 100 296 81 36 66 128 256), losses := [] }

theorem u3718 : Upper (D 6) (R 6) [10,129,96,288,65,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3718 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3719 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 411, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 131 100 296 81 36 68 146 274), lower := (rows 11 131 100 296 81 36 68 128 256), losses := [] }

theorem u3719 : Upper (D 6) (R 6) [10,129,96,288,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3719 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u3719
end Delivery.IrregularNine14.P06

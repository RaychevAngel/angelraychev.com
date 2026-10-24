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

def b3720 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 131 100 296 81 36 80 134 262), lower := (rows 11 131 100 296 81 36 80 128 256), losses := [] }

theorem u3720 : Upper (D 6) (R 6) [10,129,96,288,65,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3720 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3721 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 300, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 100 296 82 36 65 148 276), lower := (rows 11 131 100 296 82 36 65 128 256), losses := [] }

theorem u3721 : Upper (D 6) (R 6) [10,129,96,288,66,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3721 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3722 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 411, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 131 100 296 82 36 68 145 273), lower := (rows 11 131 100 296 82 36 68 128 256), losses := [] }

theorem u3722 : Upper (D 6) (R 6) [10,129,96,288,66,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3722 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3723 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 131 100 296 82 36 80 133 261), lower := (rows 11 131 100 296 82 36 80 128 256), losses := [] }

theorem u3723 : Upper (D 6) (R 6) [10,129,96,288,66,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3723 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3724 : PairBound 9 := { available := 96, camps := [], pairs := [(0,2),(3,0),(4,0)], upper := (rows 11 131 261 28 112 34 68 224 352), lower := (rows 11 131 261 28 112 34 68 128 256), losses := [{ target := 0, region := (rows 0 2 4 76 21 35 76 149 277), good := (rows 506 434 508 476 504 34 476 128 256) },{ target := 2, region := (rows 9 10 0 8 16 43 64 144 272), good := (rows 43 163 289 443 496 34 64 128 256) }] }

theorem u3724 : Upper (D 6) (R 6) [10,129,257,20,96,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3724 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3725 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 399, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 11 131 261 28 112 34 96 196 324), lower := (rows 11 131 261 28 112 34 96 128 256), losses := [] }

theorem u3725 : Upper (D 6) (R 6) [10,129,257,20,96,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3725 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3726 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 120, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 261 28 112 36 96 194 322), lower := (rows 11 131 261 28 112 36 96 128 256), losses := [] }

theorem u3726 : Upper (D 6) (R 6) [10,129,257,20,96,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3726 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3727 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 104, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 131 261 44 22 96 80 224 352), lower := (rows 11 131 261 44 22 96 80 128 256), losses := [] }

theorem u3727 : Upper (D 6) (R 6) [10,129,257,36,6,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3727 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r3728 : Route 9 := (fun mask => (mask,id))

def c3728 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3728 : Upper (D 6) (R 6) [10,129,257,36,6,64,32] 13 := by
  apply FastRouting.sound _ _ [10,129,257,36,6,64,32] 13 (by decide) (choices 1) [16,64] r3728 c3728
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u268
  · exact u269

def b3729 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 104, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 261 44 50 96 68 208 336), lower := (rows 11 131 261 44 50 96 68 128 256), losses := [{ target := 0, region := (rows 0 2 4 76 19 109 76 133 261), good := (rows 506 434 508 492 50 104 492 128 256) }] }

theorem u3729 : Upper (D 6) (R 6) [10,129,257,36,34,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3729 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3730 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 112, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 11 131 261 44 50 96 80 196 324), lower := (rows 11 131 261 44 50 96 80 128 256), losses := [] }

theorem u3730 : Upper (D 6) (R 6) [10,129,257,36,34,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3730 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3731 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 104, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 261 44 82 96 68 176 304), lower := (rows 11 131 261 44 82 96 68 128 256), losses := [{ target := 0, region := (rows 0 2 4 76 17 125 76 151 279), good := (rows 506 434 508 492 506 104 492 128 256) }] }

theorem u3731 : Upper (D 6) (R 6) [10,129,257,36,66,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3731 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3732 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 131 261 44 82 96 80 164 292), lower := (rows 11 131 261 44 82 96 80 128 256), losses := [] }

theorem u3732 : Upper (D 6) (R 6) [10,129,257,36,66,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3732 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3733 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 112, targets := 5 },{ cop := 2, region := 104, targets := 1 }], pairs := [(3,0),(4,0),(4,2)], upper := (rows 11 131 261 44 82 96 96 148 276), lower := (rows 11 131 261 44 82 96 96 128 256), losses := [] }

theorem u3733 : Upper (D 6) (R 6) [10,129,257,36,66,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3733 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3734 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 261 44 84 96 66 176 304), lower := (rows 11 131 261 44 84 96 66 128 256), losses := [{ target := 0, region := (rows 0 2 4 28 20 119 67 156 284), good := (rows 490 226 508 444 508 96 98 128 256) }] }

theorem u3734 : Upper (D 6) (R 6) [10,129,257,36,68,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3734 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3735 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 120, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 131 261 44 84 96 80 162 290), lower := (rows 11 131 261 44 84 96 80 128 256), losses := [] }

theorem u3735 : Upper (D 6) (R 6) [10,129,257,36,68,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3735 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3736 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 120, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 261 44 84 96 96 146 274), lower := (rows 11 131 261 44 84 96 96 128 256), losses := [] }

theorem u3736 : Upper (D 6) (R 6) [10,129,257,36,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3736 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3737 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 356, targets := 2 }], pairs := [(2,1),(3,0),(3,1)], upper := (rows 11 131 261 56 82 36 68 224 352), lower := (rows 11 131 261 56 82 36 68 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 100 100 252 380), good := (rows 394 130 484 504 506 484 484 128 256) },{ target := 1, region := (rows 1 0 7 24 16 119 119 255 383), good := (rows 493 485 485 504 508 484 484 128 256) }] }

theorem u3737 : Upper (D 6) (R 6) [10,129,257,48,66,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3737 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3738 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 356, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 11 131 261 56 82 36 96 196 324), lower := (rows 11 131 261 56 82 36 96 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 17 36 108 164 292), good := (rows 90 146 508 504 82 492 480 128 256) }] }

theorem u3738 : Upper (D 6) (R 6) [10,129,257,48,66,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3738 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3739 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 80, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 131 261 56 84 34 68 224 352), lower := (rows 11 131 261 56 84 34 68 128 256), losses := [] }

theorem u3739 : Upper (D 6) (R 6) [10,129,257,48,68,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3739 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3740 : PairBound 9 := { available := 68, camps := [], pairs := [(2,1),(3,0),(4,0)], upper := (rows 11 131 261 56 84 34 96 196 324), lower := (rows 11 131 261 56 84 34 96 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 20 35 111 148 276), good := (rows 106 226 508 504 476 98 96 128 256) },{ target := 1, region := (rows 1 0 7 104 49 32 104 177 305), good := (rows 477 405 405 504 476 508 504 128 256) }] }

theorem u3740 : Upper (D 6) (R 6) [10,129,257,48,68,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3740 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3741 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 131, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 11 131 261 104 22 36 80 224 352), lower := (rows 11 131 261 104 22 36 80 128 256), losses := [] }

theorem u3741 : Upper (D 6) (R 6) [10,129,257,96,6,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3741 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3742 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 407, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 11 131 261 104 22 36 96 208 336), lower := (rows 11 131 261 104 22 36 96 128 256), losses := [] }

theorem u3742 : Upper (D 6) (R 6) [10,129,257,96,6,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3742 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3743 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 147, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 131 261 104 50 36 68 208 336), lower := (rows 11 131 261 104 50 36 68 128 256), losses := [] }

theorem u3743 : Upper (D 6) (R 6) [10,129,257,96,34,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3743 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3744 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 391, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 131 261 104 50 36 80 196 324), lower := (rows 11 131 261 104 50 36 80 128 256), losses := [] }

theorem u3744 : Upper (D 6) (R 6) [10,129,257,96,34,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3744 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3745 : PairBound 9 := { available := 96, camps := [], pairs := [(0,2),(3,1),(4,1)], upper := (rows 11 131 262 28 112 33 68 224 352), lower := (rows 11 131 262 28 112 33 68 128 256), losses := [{ target := 1, region := (rows 1 0 4 76 21 35 76 149 277), good := (rows 505 433 508 476 504 433 476 128 256) },{ target := 2, region := (rows 9 10 0 8 16 43 64 144 272), good := (rows 43 163 290 443 496 33 64 128 256) }] }

theorem u3745 : Upper (D 6) (R 6) [10,129,258,20,96,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3745 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3746 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 399, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 11 131 262 28 112 33 96 196 324), lower := (rows 11 131 262 28 112 33 96 128 256), losses := [] }

theorem u3746 : Upper (D 6) (R 6) [10,129,258,20,96,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3746 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3747 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 120, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 262 28 112 36 96 193 321), lower := (rows 11 131 262 28 112 36 96 128 256), losses := [] }

theorem u3747 : Upper (D 6) (R 6) [10,129,258,20,96,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3747 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3748 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 104, targets := 3 },{ cop := 4, region := 454, targets := 32 }], pairs := [(1,5),(3,0),(3,1)], upper := (rows 11 131 262 44 49 96 68 208 336), lower := (rows 11 131 262 44 49 96 68 128 256), losses := [] }

theorem u3748 : Upper (D 6) (R 6) [10,129,258,36,33,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3748 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3749 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 112, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 131 262 44 49 96 80 196 324), lower := (rows 11 131 262 44 49 96 80 128 256), losses := [] }

theorem u3749 : Upper (D 6) (R 6) [10,129,258,36,33,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3749 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3750 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 104, targets := 3 },{ cop := 4, region := 162, targets := 4 }], pairs := [(1,2),(3,0),(3,1)], upper := (rows 11 131 262 44 81 96 68 176 304), lower := (rows 11 131 262 44 81 96 68 128 256), losses := [] }

theorem u3750 : Upper (D 6) (R 6) [10,129,258,36,65,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3750 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3751 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 131 262 44 81 96 80 164 292), lower := (rows 11 131 262 44 81 96 80 128 256), losses := [] }

theorem u3751 : Upper (D 6) (R 6) [10,129,258,36,65,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3751 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3752 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 390, targets := 96 }], pairs := [(1,5),(1,6),(2,5)], upper := (rows 11 131 262 44 81 96 96 148 276), lower := (rows 11 131 262 44 81 96 96 128 256), losses := [] }

theorem u3752 : Upper (D 6) (R 6) [10,129,258,36,65,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3752 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3753 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1),(4,1)], upper := (rows 11 131 262 44 84 96 65 176 304), lower := (rows 11 131 262 44 84 96 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 28 20 119 67 156 284), good := (rows 489 225 508 444 508 96 97 128 256) }] }

theorem u3753 : Upper (D 6) (R 6) [10,129,258,36,68,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3753 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3754 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 120, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 131 262 44 84 96 80 161 289), lower := (rows 11 131 262 44 84 96 80 128 256), losses := [] }

theorem u3754 : Upper (D 6) (R 6) [10,129,258,36,68,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3754 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3755 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 120, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 262 44 84 96 96 145 273), lower := (rows 11 131 262 44 84 96 96 128 256), losses := [] }

theorem u3755 : Upper (D 6) (R 6) [10,129,258,36,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3755 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3756 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 356, targets := 1 }], pairs := [(2,0),(3,0),(3,1)], upper := (rows 11 131 262 56 81 36 68 224 352), lower := (rows 11 131 262 56 81 36 68 128 256), losses := [{ target := 0, region := (rows 0 2 7 24 16 119 119 255 383), good := (rows 494 486 486 504 508 484 484 128 256) },{ target := 1, region := (rows 1 0 4 24 16 100 100 252 380), good := (rows 393 129 484 504 505 484 484 128 256) }] }

theorem u3756 : Upper (D 6) (R 6) [10,129,258,48,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3756 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3757 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 390, targets := 32 },{ cop := 0, region := 356, targets := 1 }], pairs := [(1,5),(2,0),(2,5)], upper := (rows 11 131 262 56 81 36 96 196 324), lower := (rows 11 131 262 56 81 36 96 128 256), losses := [] }

theorem u3757 : Upper (D 6) (R 6) [10,129,258,48,65,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3757 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3758 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 80, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 131 262 56 84 33 68 224 352), lower := (rows 11 131 262 56 84 33 68 128 256), losses := [] }

theorem u3758 : Upper (D 6) (R 6) [10,129,258,48,68,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3758 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3759 : PairBound 9 := { available := 68, camps := [], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 131 262 56 84 33 96 196 324), lower := (rows 11 131 262 56 84 33 96 128 256), losses := [{ target := 0, region := (rows 0 2 7 104 49 32 104 177 305), good := (rows 478 406 262 504 476 508 504 128 256) }] }

theorem u3759 : Upper (D 6) (R 6) [10,129,258,48,68,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3759 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3760 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 131, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 11 131 262 104 21 36 80 224 352), lower := (rows 11 131 262 104 21 36 80 128 256), losses := [] }

theorem u3760 : Upper (D 6) (R 6) [10,129,258,96,5,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3760 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3761 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 407, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 11 131 262 104 21 36 96 208 336), lower := (rows 11 131 262 104 21 36 96 128 256), losses := [] }

theorem u3761 : Upper (D 6) (R 6) [10,129,258,96,5,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3761 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3762 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 147, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 131 262 104 49 36 68 208 336), lower := (rows 11 131 262 104 49 36 68 128 256), losses := [] }

theorem u3762 : Upper (D 6) (R 6) [10,129,258,96,33,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3762 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3763 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 391, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 131 262 104 49 36 80 196 324), lower := (rows 11 131 262 104 49 36 80 128 256), losses := [] }

theorem u3763 : Upper (D 6) (R 6) [10,129,258,96,33,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3763 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3764 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 340, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 276 13 112 34 68 224 352), lower := (rows 11 131 276 13 112 34 68 128 256), losses := [] }

theorem u3764 : Upper (D 6) (R 6) [10,129,272,5,96,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3764 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3765 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 399, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 11 131 276 13 112 36 96 194 322), lower := (rows 11 131 276 13 112 36 96 128 256), losses := [] }

theorem u3765 : Upper (D 6) (R 6) [10,129,272,5,96,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3765 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3766 : PairBound 9 := { available := 68, camps := [{ cop := 5, region := 276, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 276 41 52 96 66 196 324), lower := (rows 11 131 276 41 52 96 66 128 256), losses := [] }

theorem u3766 : Upper (D 6) (R 6) [10,129,272,33,36,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3766 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3767 : PairBound 9 := { available := 66, camps := [{ cop := 8, region := 116, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 276 41 52 96 68 194 322), lower := (rows 11 131 276 41 52 96 68 128 256), losses := [] }

theorem u3767 : Upper (D 6) (R 6) [10,129,272,33,36,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3767 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3768 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 276, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 276 41 84 96 66 164 292), lower := (rows 11 131 276 41 84 96 66 128 256), losses := [] }

theorem u3768 : Upper (D 6) (R 6) [10,129,272,33,68,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3768 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3769 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 139, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 131 276 41 84 96 68 162 290), lower := (rows 11 131 276 41 84 96 68 128 256), losses := [] }

theorem u3769 : Upper (D 6) (R 6) [10,129,272,33,68,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3769 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3770 : PairBound 9 := { available := 6, camps := [{ cop := 8, region := 116, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 276 41 84 96 96 134 262), lower := (rows 11 131 276 41 84 96 96 128 256), losses := [] }

theorem u3770 : Upper (D 6) (R 6) [10,129,272,33,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3770 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3771 : PairBound 9 := { available := 68, camps := [{ cop := 6, region := 308, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 276 41 112 36 66 196 324), lower := (rows 11 131 276 41 112 36 66 128 256), losses := [] }

theorem u3771 : Upper (D 6) (R 6) [10,129,272,33,96,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3771 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3772 : PairBound 9 := { available := 66, camps := [{ cop := 8, region := 116, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 276 41 112 36 68 194 322), lower := (rows 11 131 276 41 112 36 68 128 256), losses := [] }

theorem u3772 : Upper (D 6) (R 6) [10,129,272,33,96,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3772 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3773 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 195, targets := 32 },{ cop := 0, region := 112, targets := 4 }], pairs := [(0,5),(1,5),(4,2)], upper := (rows 11 131 276 44 50 96 65 196 324), lower := (rows 11 131 276 44 50 96 65 128 256), losses := [] }

theorem u3773 : Upper (D 6) (R 6) [10,129,272,36,34,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3773 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3774 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 104, targets := 3 },{ cop := 3, region := 195, targets := 32 }], pairs := [(0,5),(3,0),(3,1)], upper := (rows 11 131 276 44 50 96 68 193 321), lower := (rows 11 131 276 44 50 96 68 128 256), losses := [] }

theorem u3774 : Upper (D 6) (R 6) [10,129,272,36,34,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3774 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3775 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 195, targets := 4 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 11 131 276 44 84 33 66 224 352), lower := (rows 11 131 276 44 84 33 66 128 256), losses := [{ target := 0, region := (rows 0 2 44 40 49 32 67 160 288), good := (rows 94 210 276 444 84 508 66 128 256) }] }

theorem u3775 : Upper (D 6) (R 6) [10,129,272,36,68,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3775 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3776 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 80, targets := 3 },{ cop := 3, region := 195, targets := 4 }], pairs := [(0,2),(4,0),(4,1)], upper := (rows 11 131 276 44 84 33 96 194 322), lower := (rows 11 131 276 44 84 33 96 128 256), losses := [] }

theorem u3776 : Upper (D 6) (R 6) [10,129,272,36,68,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3776 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3777 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 195, targets := 4 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 11 131 276 44 84 34 65 224 352), lower := (rows 11 131 276 44 84 34 65 128 256), losses := [{ target := 0, region := (rows 0 2 84 72 80 35 64 192 320), good := (rows 42 162 276 44 476 34 508 128 256) }] }

theorem u3777 : Upper (D 6) (R 6) [10,129,272,36,68,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3777 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3778 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 80, targets := 3 },{ cop := 3, region := 195, targets := 4 }], pairs := [(0,2),(4,0),(4,1)], upper := (rows 11 131 276 44 84 34 96 193 321), lower := (rows 11 131 276 44 84 34 96 128 256), losses := [] }

theorem u3778 : Upper (D 6) (R 6) [10,129,272,36,68,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3778 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3779 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 268, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 276 44 112 33 66 196 324), lower := (rows 11 131 276 44 112 33 66 128 256), losses := [] }

theorem u3779 : Upper (D 6) (R 6) [10,129,272,36,96,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3779 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u3779
end Delivery.IrregularNine14.P06

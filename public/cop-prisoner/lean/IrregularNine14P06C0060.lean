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

def b3600 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 131, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 11 131 38 104 276 48 68 193 321), lower := (rows 11 131 38 104 276 48 68 128 256), losses := [] }

theorem u3600 : Upper (D 6) (R 6) [10,129,34,96,260,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3600 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3601 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 36, targets := 65 },{ cop := 2, region := 73, targets := 4 }], pairs := [(0,2),(2,0),(2,6)], upper := (rows 11 131 38 104 336 36 65 148 276), lower := (rows 11 131 38 104 336 36 65 128 256), losses := [] }

theorem u3601 : Upper (D 6) (R 6) [10,129,34,96,320,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3601 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3602 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 403, targets := 36 }], pairs := [(0,2),(0,5),(1,2)], upper := (rows 11 131 38 104 336 36 68 145 273), lower := (rows 11 131 38 104 336 36 68 128 256), losses := [] }

theorem u3602 : Upper (D 6) (R 6) [10,129,34,96,320,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3602 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3603 : PairBound 9 := { available := 5, camps := [{ cop := 8, region := 80, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 11 131 38 104 336 36 80 133 261), lower := (rows 11 131 38 104 336 36 80 128 256), losses := [] }

theorem u3603 : Upper (D 6) (R 6) [10,129,34,96,320,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3603 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3604 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 100, targets := 1 }], pairs := [(2,0),(3,0),(3,1)], upper := (rows 11 131 38 268 49 96 68 208 336), lower := (rows 11 131 38 268 49 96 68 128 256), losses := [{ target := 0, region := (rows 0 2 7 24 16 127 95 144 272), good := (rows 110 230 102 364 508 96 100 128 256) },{ target := 1, region := (rows 1 0 4 76 19 109 76 133 261), good := (rows 505 433 508 492 433 104 492 128 256) }] }

theorem u3604 : Upper (D 6) (R 6) [10,129,34,260,33,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3604 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3605 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 112, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 131 38 268 49 96 80 196 324), lower := (rows 11 131 38 268 49 96 80 128 256), losses := [] }

theorem u3605 : Upper (D 6) (R 6) [10,129,34,260,33,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3605 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3606 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 100, targets := 1 },{ cop := 4, region := 162, targets := 4 }], pairs := [(1,2),(2,0),(3,0)], upper := (rows 11 131 38 268 81 96 68 176 304), lower := (rows 11 131 38 268 81 96 68 128 256), losses := [{ target := 0, region := (rows 0 2 7 24 16 127 95 144 272), good := (rows 110 230 102 364 508 96 100 128 256) }] }

theorem u3606 : Upper (D 6) (R 6) [10,129,34,260,65,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3606 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3607 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 131 38 268 81 96 80 164 292), lower := (rows 11 131 38 268 81 96 80 128 256), losses := [] }

theorem u3607 : Upper (D 6) (R 6) [10,129,34,260,65,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3607 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3608 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 112, targets := 6 },{ cop := 0, region := 100, targets := 1 }], pairs := [(2,0),(4,1),(4,2)], upper := (rows 11 131 38 268 81 96 96 148 276), lower := (rows 11 131 38 268 81 96 96 128 256), losses := [] }

theorem u3608 : Upper (D 6) (R 6) [10,129,34,260,65,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3608 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3609 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 296, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 131 38 268 84 48 65 224 352), lower := (rows 11 131 38 268 84 48 65 128 256), losses := [] }

theorem u3609 : Upper (D 6) (R 6) [10,129,34,260,68,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3609 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3610 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 395, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 131 38 268 84 48 96 193 321), lower := (rows 11 131 38 268 84 48 96 128 256), losses := [] }

theorem u3610 : Upper (D 6) (R 6) [10,129,34,260,68,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3610 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3611 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 296, targets := 3 }], pairs := [(3,0),(3,1),(4,1)], upper := (rows 11 131 38 268 84 96 65 176 304), lower := (rows 11 131 38 268 84 96 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 28 20 119 67 156 284), good := (rows 489 225 508 444 508 96 97 128 256) }] }

theorem u3611 : Upper (D 6) (R 6) [10,129,34,260,68,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3611 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3612 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 131 38 268 84 96 80 161 289), lower := (rows 11 131 38 268 84 96 80 128 256), losses := [] }

theorem u3612 : Upper (D 6) (R 6) [10,129,34,260,68,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3612 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3613 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 395, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 11 131 38 268 84 96 96 145 273), lower := (rows 11 131 38 268 84 96 96 128 256), losses := [] }

theorem u3613 : Upper (D 6) (R 6) [10,129,34,260,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3613 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r3614 : Route 9 := (fun mask => (mask,id))

def c3614 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3614 : Upper (D 6) (R 6) [10,129,34,272,33,64,4] 13 := by
  apply FastRouting.sound _ _ [10,129,34,272,33,64,4] 13 (by decide) (choices 1) [4,64] r3614 c3614
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u260
  · exact u261

def b3615 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 100, targets := 1 }], pairs := [(2,0),(3,0),(3,1)], upper := (rows 11 131 38 280 81 96 68 164 292), lower := (rows 11 131 38 280 81 96 68 128 256), losses := [{ target := 0, region := (rows 0 2 7 24 16 127 87 215 343), good := (rows 494 486 486 504 508 480 484 128 256) },{ target := 1, region := (rows 1 0 4 24 16 116 68 196 324), good := (rows 9 129 484 312 505 480 484 128 256) }] }

theorem u3615 : Upper (D 6) (R 6) [10,129,34,272,65,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3615 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3616 : PairBound 9 := { available := 4, camps := [{ cop := 0, region := 112, targets := 6 },{ cop := 0, region := 100, targets := 1 }], pairs := [(2,0),(4,1),(4,2)], upper := (rows 11 131 38 280 81 96 96 132 260), lower := (rows 11 131 38 280 81 96 96 128 256), losses := [] }

theorem u3616 : Upper (D 6) (R 6) [10,129,34,272,65,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3616 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3617 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 36, targets := 65 },{ cop := 4, region := 296, targets := 1 }], pairs := [(2,0),(2,6),(3,0)], upper := (rows 11 131 38 280 84 36 65 224 352), lower := (rows 11 131 38 280 84 36 65 128 256), losses := [] }

theorem u3617 : Upper (D 6) (R 6) [10,129,34,272,68,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3617 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3618 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 395, targets := 36 }], pairs := [(0,2),(0,5),(1,2)], upper := (rows 11 131 38 280 84 36 96 193 321), lower := (rows 11 131 38 280 84 36 96 128 256), losses := [] }

theorem u3618 : Upper (D 6) (R 6) [10,129,34,272,68,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3618 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3619 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 296, targets := 3 }], pairs := [(3,0),(3,1),(4,1)], upper := (rows 11 131 38 280 84 96 65 164 292), lower := (rows 11 131 38 280 84 96 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 28 20 119 67 148 276), good := (rows 105 225 508 440 508 96 97 128 256) }] }

theorem u3619 : Upper (D 6) (R 6) [10,129,34,272,68,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3619 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3620 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 427, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 131 38 280 84 96 68 161 289), lower := (rows 11 131 38 280 84 96 68 128 256), losses := [] }

theorem u3620 : Upper (D 6) (R 6) [10,129,34,272,68,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3620 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3621 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 395, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 11 131 38 280 84 96 96 133 261), lower := (rows 11 131 38 280 84 96 96 128 256), losses := [] }

theorem u3621 : Upper (D 6) (R 6) [10,129,34,272,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3621 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3622 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 36, targets := 65 }], pairs := [(2,0),(2,6),(3,0)], upper := (rows 11 131 38 280 112 36 65 196 324), lower := (rows 11 131 38 280 112 36 65 128 256), losses := [{ target := 0, region := (rows 0 2 7 88 80 103 64 192 320), good := (rows 46 166 38 280 504 36 508 128 256) }] }

theorem u3622 : Upper (D 6) (R 6) [10,129,34,272,96,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3622 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3623 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 395, targets := 36 }], pairs := [(0,2),(0,5),(1,2)], upper := (rows 11 131 38 280 112 36 68 193 321), lower := (rows 11 131 38 280 112 36 68 128 256), losses := [] }

theorem u3623 : Upper (D 6) (R 6) [10,129,34,272,96,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3623 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r3624 : Route 9 := (fun mask => (mask,id))

def c3624 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3624 : Upper (D 6) (R 6) [10,129,34,288,65,64,4] 13 := by
  apply FastRouting.sound _ _ [10,129,34,288,65,64,4] 13 (by decide) (choices 1) [4,16] r3624 c3624
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u262
  · exact u263

def b3625 : PairBound 9 := { available := 4, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 131 38 296 81 96 80 132 260), lower := (rows 11 131 38 296 81 96 80 128 256), losses := [] }

theorem u3625 : Upper (D 6) (R 6) [10,129,34,288,65,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3625 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3626 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 36, targets := 65 },{ cop := 4, region := 296, targets := 1 }], pairs := [(2,0),(2,6),(3,0)], upper := (rows 11 131 38 296 84 36 65 208 336), lower := (rows 11 131 38 296 84 36 65 128 256), losses := [] }

theorem u3626 : Upper (D 6) (R 6) [10,129,34,288,68,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3626 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3627 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 116, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 11 131 38 296 84 36 80 193 321), lower := (rows 11 131 38 296 84 36 80 128 256), losses := [] }

theorem u3627 : Upper (D 6) (R 6) [10,129,34,288,68,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3627 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3628 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 296, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 131 38 296 84 48 65 196 324), lower := (rows 11 131 38 296 84 48 65 128 256), losses := [] }

theorem u3628 : Upper (D 6) (R 6) [10,129,34,288,68,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3628 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3629 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 427, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 11 131 38 296 84 48 68 193 321), lower := (rows 11 131 38 296 84 48 68 128 256), losses := [] }

theorem u3629 : Upper (D 6) (R 6) [10,129,34,288,68,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3629 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3630 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 296, targets := 3 }], pairs := [(3,0),(3,1),(4,1)], upper := (rows 11 131 38 296 84 96 65 148 276), lower := (rows 11 131 38 296 84 96 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 28 20 119 67 148 276), good := (rows 105 225 508 296 508 96 97 128 256) }] }

theorem u3630 : Upper (D 6) (R 6) [10,129,34,288,68,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3630 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3631 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 427, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 131 38 296 84 96 68 145 273), lower := (rows 11 131 38 296 84 96 68 128 256), losses := [] }

theorem u3631 : Upper (D 6) (R 6) [10,129,34,288,68,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3631 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3632 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 131 38 296 84 96 80 133 261), lower := (rows 11 131 38 296 84 96 80 128 256), losses := [] }

theorem u3632 : Upper (D 6) (R 6) [10,129,34,288,68,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3632 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3633 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 36, targets := 65 },{ cop := 4, region := 296, targets := 1 }], pairs := [(2,0),(2,6),(3,0)], upper := (rows 11 131 38 328 84 36 65 176 304), lower := (rows 11 131 38 328 84 36 65 128 256), losses := [] }

theorem u3633 : Upper (D 6) (R 6) [10,129,34,320,68,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3633 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3634 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 167, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 131 38 328 84 36 80 161 289), lower := (rows 11 131 38 328 84 36 80 128 256), losses := [] }

theorem u3634 : Upper (D 6) (R 6) [10,129,34,320,68,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3634 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3635 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 395, targets := 36 }], pairs := [(0,2),(0,5),(1,2)], upper := (rows 11 131 38 328 84 36 96 145 273), lower := (rows 11 131 38 328 84 36 96 128 256), losses := [] }

theorem u3635 : Upper (D 6) (R 6) [10,129,34,320,68,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3635 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3636 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 296, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 131 38 328 84 48 65 164 292), lower := (rows 11 131 38 328 84 48 65 128 256), losses := [] }

theorem u3636 : Upper (D 6) (R 6) [10,129,34,320,68,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3636 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3637 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 427, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 11 131 38 328 84 48 68 161 289), lower := (rows 11 131 38 328 84 48 68 128 256), losses := [] }

theorem u3637 : Upper (D 6) (R 6) [10,129,34,320,68,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3637 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3638 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 395, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 131 38 328 84 48 96 133 261), lower := (rows 11 131 38 328 84 48 96 128 256), losses := [] }

theorem u3638 : Upper (D 6) (R 6) [10,129,34,320,68,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3638 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3639 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 36, targets := 65 }], pairs := [(2,0),(2,6),(3,0)], upper := (rows 11 131 38 328 112 36 65 148 276), lower := (rows 11 131 38 328 112 36 65 128 256), losses := [{ target := 0, region := (rows 0 2 7 88 88 103 64 193 321), good := (rows 446 422 38 504 504 36 508 128 256) }] }

theorem u3639 : Upper (D 6) (R 6) [10,129,34,320,96,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3639 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3640 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 395, targets := 36 }], pairs := [(0,2),(0,5),(1,2)], upper := (rows 11 131 38 328 112 36 68 145 273), lower := (rows 11 131 38 328 112 36 68 128 256), losses := [] }

theorem u3640 : Upper (D 6) (R 6) [10,129,34,320,96,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3640 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3641 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 167, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 131 38 328 112 36 80 133 261), lower := (rows 11 131 38 328 112 36 80 128 256), losses := [] }

theorem u3641 : Upper (D 6) (R 6) [10,129,34,320,96,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3641 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3642 : PairBound 9 := { available := 68, camps := [{ cop := 5, region := 276, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 52 41 276 96 66 196 324), lower := (rows 11 131 52 41 276 96 66 128 256), losses := [] }

theorem u3642 : Upper (D 6) (R 6) [10,129,48,33,260,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3642 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3643 : PairBound 9 := { available := 66, camps := [{ cop := 8, region := 116, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 52 41 276 96 68 194 322), lower := (rows 11 131 52 41 276 96 68 128 256), losses := [] }

theorem u3643 : Upper (D 6) (R 6) [10,129,48,33,260,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3643 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3644 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 276, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 131 52 73 276 96 66 164 292), lower := (rows 11 131 52 73 276 96 66 128 256), losses := [] }

theorem u3644 : Upper (D 6) (R 6) [10,129,48,65,260,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3644 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3645 : PairBound 9 := { available := 34, camps := [{ cop := 8, region := 116, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 52 73 276 96 68 162 290), lower := (rows 11 131 52 73 276 96 68 128 256), losses := [] }

theorem u3645 : Upper (D 6) (R 6) [10,129,48,65,260,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3645 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3646 : PairBound 9 := { available := 6, camps := [{ cop := 8, region := 116, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 52 73 276 96 96 134 262), lower := (rows 11 131 52 73 276 96 96 128 256), losses := [] }

theorem u3646 : Upper (D 6) (R 6) [10,129,48,65,260,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3646 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3647 : PairBound 9 := { available := 36, camps := [], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 52 76 273 96 66 164 292), lower := (rows 11 131 52 76 273 96 66 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 123 67 156 284), good := (rows 490 226 444 492 508 96 98 128 256) },{ target := 1, region := (rows 1 0 69 104 19 104 64 237 365), good := (rows 445 405 444 492 405 492 508 128 256) }] }

theorem u3647 : Upper (D 6) (R 6) [10,129,48,68,257,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3647 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3648 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 108, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 52 76 273 96 68 162 290), lower := (rows 11 131 52 76 273 96 68 128 256), losses := [] }

theorem u3648 : Upper (D 6) (R 6) [10,129,48,68,257,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3648 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3649 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 131, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 11 131 52 76 273 96 96 134 262), lower := (rows 11 131 52 76 273 96 96 128 256), losses := [] }

theorem u3649 : Upper (D 6) (R 6) [10,129,48,68,257,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3649 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3650 : PairBound 9 := { available := 36, camps := [], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 131 52 76 274 96 65 164 292), lower := (rows 11 131 52 76 274 96 65 128 256), losses := [{ target := 0, region := (rows 0 2 69 104 19 104 64 237 365), good := (rows 446 406 444 492 274 492 508 128 256) }] }

theorem u3650 : Upper (D 6) (R 6) [10,129,48,68,258,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3650 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3651 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 108, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 52 76 274 96 68 161 289), lower := (rows 11 131 52 76 274 96 68 128 256), losses := [] }

theorem u3651 : Upper (D 6) (R 6) [10,129,48,68,258,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3651 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3652 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 131, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 11 131 52 76 274 96 96 133 261), lower := (rows 11 131 52 76 274 96 96 128 256), losses := [] }

theorem u3652 : Upper (D 6) (R 6) [10,129,48,68,258,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3652 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3653 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 163, targets := 4 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 11 131 52 76 276 33 66 224 352), lower := (rows 11 131 52 76 276 33 66 128 256), losses := [{ target := 0, region := (rows 0 2 36 40 52 32 67 160 288), good := (rows 74 194 444 92 276 508 66 128 256) }] }

theorem u3653 : Upper (D 6) (R 6) [10,129,48,68,260,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3653 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3654 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 403, targets := 32 }], pairs := [(0,5),(1,5),(4,5)], upper := (rows 11 131 52 76 276 33 96 194 322), lower := (rows 11 131 52 76 276 33 96 128 256), losses := [] }

theorem u3654 : Upper (D 6) (R 6) [10,129,48,68,260,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3654 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3655 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 163, targets := 4 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 11 131 52 76 276 34 65 224 352), lower := (rows 11 131 52 76 276 34 65 128 256), losses := [{ target := 0, region := (rows 0 2 69 72 88 35 64 192 320), good := (rows 62 166 52 476 276 34 508 128 256) }] }

theorem u3655 : Upper (D 6) (R 6) [10,129,48,68,260,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3655 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3656 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 403, targets := 32 }], pairs := [(0,5),(1,5),(4,5)], upper := (rows 11 131 52 76 276 34 96 193 321), lower := (rows 11 131 52 76 276 34 96 128 256), losses := [] }

theorem u3656 : Upper (D 6) (R 6) [10,129,48,68,260,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3656 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3657 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 163, targets := 4 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 11 131 52 76 276 96 65 162 290), lower := (rows 11 131 52 76 276 96 65 128 256), losses := [{ target := 0, region := (rows 0 2 109 104 83 104 64 129 257), good := (rows 446 406 60 124 276 124 508 128 256) }] }

theorem u3657 : Upper (D 6) (R 6) [10,129,48,68,260,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3657 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3658 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 163, targets := 4 }], pairs := [(0,2),(1,2),(2,1)], upper := (rows 11 131 52 76 276 96 66 161 289), lower := (rows 11 131 52 76 276 96 66 128 256), losses := [{ target := 1, region := (rows 1 0 69 104 19 104 64 129 257), good := (rows 445 405 60 108 276 108 124 128 256) }] }

theorem u3658 : Upper (D 6) (R 6) [10,129,48,68,260,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3658 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3659 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 131, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 11 131 52 76 276 96 96 131 259), lower := (rows 11 131 52 76 276 96 96 128 256), losses := [] }

theorem u3659 : Upper (D 6) (R 6) [10,129,48,68,260,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3659 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u3659
end Delivery.IrregularNine14.P06

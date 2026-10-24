import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0050

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b10620 : PairBound 9 := { available := 116, camps := [{ cop := 2, region := 376, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 133 168 280 116 116 244 372), lower := (rows 67 35 133 168 280 32 64 128 256), losses := [] }

theorem u10620 : Upper (D 8) (R 8) [66,33,129,160,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10620 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10621 : PairBound 9 := { available := 92, camps := [{ cop := 2, region := 376, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 133 168 304 124 92 220 348), lower := (rows 67 35 133 168 304 32 64 128 256), losses := [] }

theorem u10621 : Upper (D 8) (R 8) [66,33,129,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10621 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10622 : PairBound 9 := { available := 60, camps := [{ cop := 2, region := 376, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 133 168 336 60 124 188 316), lower := (rows 67 35 133 168 336 32 64 128 256), losses := [] }

theorem u10622 : Upper (D 8) (R 8) [66,33,129,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10622 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10623 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 376, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 133 200 276 56 120 184 312), lower := (rows 67 35 133 200 276 32 64 128 256), losses := [] }

theorem u10623 : Upper (D 8) (R 8) [66,33,129,192,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10623 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10624 : PairBound 9 := { available := 52, camps := [{ cop := 2, region := 376, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 133 200 280 52 116 180 308), lower := (rows 67 35 133 200 280 32 64 128 256), losses := [] }

theorem u10624 : Upper (D 8) (R 8) [66,33,129,192,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10624 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10625 : PairBound 9 := { available := 60, camps := [{ cop := 2, region := 376, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 133 200 304 60 124 188 316), lower := (rows 67 35 133 200 304 32 64 128 256), losses := [] }

theorem u10625 : Upper (D 8) (R 8) [66,33,129,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10625 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10626 : PairBound 9 := { available := 113, camps := [{ cop := 7, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 140 140 304 113 113 241 369), lower := (rows 67 35 140 140 304 32 64 128 256), losses := [] }

theorem u10626 : Upper (D 8) (R 8) [66,33,136,132,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10626 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10627 : PairBound 9 := { available := 49, camps := [{ cop := 7, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 140 140 336 49 113 177 305), lower := (rows 67 35 140 140 336 32 64 128 256), losses := [] }

theorem u10627 : Upper (D 8) (R 8) [66,33,136,132,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10627 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10628 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 140 152 276 97 97 225 353), lower := (rows 67 35 140 152 276 32 64 128 256), losses := [] }

theorem u10628 : Upper (D 8) (R 8) [66,33,136,144,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10628 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10629 : PairBound 9 := { available := 101, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 140 152 304 101 101 229 357), lower := (rows 67 35 140 152 304 32 64 128 256), losses := [] }

theorem u10629 : Upper (D 8) (R 8) [66,33,136,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10629 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10630 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 140 152 336 37 101 165 293), lower := (rows 67 35 140 152 336 32 64 128 256), losses := [] }

theorem u10630 : Upper (D 8) (R 8) [66,33,136,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10630 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10631 : PairBound 9 := { available := 113, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 140 168 276 113 113 241 369), lower := (rows 67 35 140 168 276 32 64 128 256), losses := [] }

theorem u10631 : Upper (D 8) (R 8) [66,33,136,160,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10631 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10632 : PairBound 9 := { available := 85, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 140 168 304 117 85 213 341), lower := (rows 67 35 140 168 304 32 64 128 256), losses := [] }

theorem u10632 : Upper (D 8) (R 8) [66,33,136,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10632 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10633 : PairBound 9 := { available := 53, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 140 168 336 53 117 181 309), lower := (rows 67 35 140 168 336 32 64 128 256), losses := [] }

theorem u10633 : Upper (D 8) (R 8) [66,33,136,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10633 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10634 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 140 200 276 49 113 177 305), lower := (rows 67 35 140 200 276 32 64 128 256), losses := [] }

theorem u10634 : Upper (D 8) (R 8) [66,33,136,192,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10634 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10635 : PairBound 9 := { available := 53, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 140 200 304 53 117 181 309), lower := (rows 67 35 140 200 304 32 64 128 256), losses := [] }

theorem u10635 : Upper (D 8) (R 8) [66,33,136,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10635 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10636 : PairBound 9 := { available := 116, camps := [{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 140 265 176 116 116 244 372), lower := (rows 67 35 140 265 176 32 64 128 256), losses := [] }

theorem u10636 : Upper (D 8) (R 8) [66,33,136,257,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10636 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10637 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 140 265 208 52 116 180 308), lower := (rows 67 35 140 265 208 32 64 128 256), losses := [] }

theorem u10637 : Upper (D 8) (R 8) [66,33,136,257,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10637 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10638 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 140 268 176 113 113 241 369), lower := (rows 67 35 140 268 176 32 64 128 256), losses := [] }

theorem u10638 : Upper (D 8) (R 8) [66,33,136,260,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10638 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10639 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 35, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 140 268 208 49 113 177 305), lower := (rows 67 35 140 268 208 32 64 128 256), losses := [] }

theorem u10639 : Upper (D 8) (R 8) [66,33,136,260,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10639 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10640 : PairBound 9 := { available := 101, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 140 280 176 101 101 229 357), lower := (rows 67 35 140 280 176 32 64 128 256), losses := [] }

theorem u10640 : Upper (D 8) (R 8) [66,33,136,272,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10640 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10641 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 140 280 208 37 101 165 293), lower := (rows 67 35 140 280 208 32 64 128 256), losses := [] }

theorem u10641 : Upper (D 8) (R 8) [66,33,136,272,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10641 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10642 : Route 9 := (fun mask => (mask,id))

def c10642 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10642 : Upper (D 8) (R 8) [66,33,136,288,160] 13 := by
  apply FastRouting.sound _ _ [66,33,136,288,160] 13 (by decide) (choices 1) [1,4,16,64] r10642 c10642
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3002
  · exact u3003
  · exact u3004
  · exact u3005

def r10643 : Route 9 := (fun mask => (mask,id))

def c10643 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10643 : Upper (D 8) (R 8) [66,33,136,288,192] 13 := by
  apply FastRouting.sound _ _ [66,33,136,288,192] 13 (by decide) (choices 1) [1,4,16] r10643 c10643
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3006
  · exact u3007
  · exact u3008

def r10644 : Route 9 := (fun mask => (mask,id))

def c10644 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10644 : Upper (D 8) (R 8) [66,33,136,320,160] 13 := by
  apply FastRouting.sound _ _ [66,33,136,320,160] 13 (by decide) (choices 1) [1,4,16] r10644 c10644
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3009
  · exact u3010
  · exact u3011

def b10645 : PairBound 9 := { available := 89, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 164 168 276 121 89 217 345), lower := (rows 67 35 164 168 276 32 64 128 256), losses := [] }

theorem u10645 : Upper (D 8) (R 8) [66,33,160,160,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10645 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10646 : PairBound 9 := { available := 29, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 164 168 336 61 93 157 285), lower := (rows 67 35 164 168 336 32 64 128 256), losses := [] }

theorem u10646 : Upper (D 8) (R 8) [66,33,160,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10646 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10647 : PairBound 9 := { available := 60, camps := [{ cop := 4, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 164 200 273 60 124 188 316), lower := (rows 67 35 164 200 273 32 64 128 256), losses := [] }

theorem u10647 : Upper (D 8) (R 8) [66,33,160,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10647 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10648 : Route 9 := (fun mask => (mask,id))

def c10648 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10648 : Upper (D 8) (R 8) [66,33,160,192,260] 13 := by
  apply FastRouting.sound _ _ [66,33,160,192,260] 13 (by decide) (choices 1) [1,8,16] r10648 c10648
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3012
  · exact u3013
  · exact u3014

def r10649 : Route 9 := (fun mask => (mask,id))

def c10649 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10649 : Upper (D 8) (R 8) [66,33,160,192,264] 13 := by
  apply FastRouting.sound _ _ [66,33,160,192,264] 13 (by decide) (choices 1) [1,4,16] r10649 c10649
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3015
  · exact u3016
  · exact u3017

def r10650 : Route 9 := (fun mask => (mask,id))

def c10650 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10650 : Upper (D 8) (R 8) [66,33,160,192,288] 13 := by
  apply FastRouting.sound _ _ [66,33,160,192,288] 13 (by decide) (choices 1) [1,4,8,16] r10650 c10650
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3018
  · exact u3019
  · exact u3020
  · exact u3021

def b10651 : PairBound 9 := { available := 448, camps := [{ cop := 4, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 13 56 49 480 448 448 448), lower := (rows 67 38 13 56 49 32 64 128 256), losses := [] }

theorem u10651 : Upper (D 8) (R 8) [66,36,9,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10651 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10652 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 13 56 81 416 480 416 416), lower := (rows 67 38 13 56 81 32 64 128 256), losses := [] }

theorem u10652 : Upper (D 8) (R 8) [66,36,9,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10652 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10653 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 15, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 13 56 112 417 449 385 385), lower := (rows 67 38 13 56 112 32 64 128 256), losses := [] }

theorem u10653 : Upper (D 8) (R 8) [66,36,9,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10653 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10654 : PairBound 9 := { available := 480, camps := [{ cop := 2, region := 482, targets := 1 }], pairs := [(1,0)], upper := (rows 67 38 13 56 145 480 480 480 480), lower := (rows 67 38 13 56 145 32 64 128 256), losses := [] }

theorem u10654 : Upper (D 8) (R 8) [66,36,9,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10654 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10655 : PairBound 9 := { available := 449, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 13 56 176 481 449 449 449), lower := (rows 67 38 13 56 176 32 64 128 256), losses := [] }

theorem u10655 : Upper (D 8) (R 8) [66,36,9,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10655 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10656 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 13 56 208 417 481 417 417), lower := (rows 67 38 13 56 208 32 64 128 256), losses := [] }

theorem u10656 : Upper (D 8) (R 8) [66,36,9,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10656 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10657 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 226, targets := 1 }], pairs := [(1,0)], upper := (rows 67 38 13 56 273 224 224 224 480), lower := (rows 67 38 13 56 273 32 64 128 256), losses := [] }

theorem u10657 : Upper (D 8) (R 8) [66,36,9,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10657 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10658 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 13 56 304 225 193 193 449), lower := (rows 67 38 13 56 304 32 64 128 256), losses := [] }

theorem u10658 : Upper (D 8) (R 8) [66,36,9,48,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10658 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10659 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 13 56 336 161 225 161 417), lower := (rows 67 38 13 56 336 32 64 128 256), losses := [] }

theorem u10659 : Upper (D 8) (R 8) [66,36,9,48,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10659 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10660 : Route 9 := (fun mask => (mask,id))

def c10660 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u10660 : Upper (D 8) (R 8) [66,36,9,48,384] 13 := by
  apply FastRouting.sound _ _ [66,36,9,48,384] 13 (by decide) (choices 1) [1,64,128] r10660 c10660
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3022
  · exact u3023
  · exact u3024

def b10661 : PairBound 9 := { available := 480, camps := [{ cop := 2, region := 482, targets := 1 }], pairs := [(1,0)], upper := (rows 67 38 13 152 49 480 480 480 480), lower := (rows 67 38 13 152 49 32 64 128 256), losses := [] }

theorem u10661 : Upper (D 8) (R 8) [66,36,9,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10661 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10662 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 13 152 81 416 480 416 416), lower := (rows 67 38 13 152 81 32 64 128 256), losses := [] }

theorem u10662 : Upper (D 8) (R 8) [66,36,9,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10662 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10663 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 13 152 112 417 481 417 417), lower := (rows 67 38 13 152 112 32 64 128 256), losses := [] }

theorem u10663 : Upper (D 8) (R 8) [66,36,9,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10663 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10664 : PairBound 9 := { available := 352, camps := [{ cop := 4, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 67 38 13 152 145 352 352 480 352), lower := (rows 67 38 13 152 145 32 64 128 256), losses := [] }

theorem u10664 : Upper (D 8) (R 8) [66,36,9,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10664 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10665 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 13 152 176 353 353 481 353), lower := (rows 67 38 13 152 176 32 64 128 256), losses := [] }

theorem u10665 : Upper (D 8) (R 8) [66,36,9,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10665 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10666 : PairBound 9 := { available := 289, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 13 152 208 289 353 417 289), lower := (rows 67 38 13 152 208 32 64 128 256), losses := [] }

theorem u10666 : Upper (D 8) (R 8) [66,36,9,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10666 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10667 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 226, targets := 1 }], pairs := [(1,0)], upper := (rows 67 38 13 152 273 224 224 224 480), lower := (rows 67 38 13 152 273 32 64 128 256), losses := [] }

theorem u10667 : Upper (D 8) (R 8) [66,36,9,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10667 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10668 : Route 9 := (fun mask => (mask,id))

def c10668 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u10668 : Upper (D 8) (R 8) [66,36,9,144,288] 13 := by
  apply FastRouting.sound _ _ [66,36,9,144,288] 13 (by decide) (choices 1) [1,64,128] r10668 c10668
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3025
  · exact u3026
  · exact u3027

def b10669 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 13 152 336 161 225 161 417), lower := (rows 67 38 13 152 336 32 64 128 256), losses := [] }

theorem u10669 : Upper (D 8) (R 8) [66,36,9,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10669 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10670 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 103, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 13 152 400 97 97 225 353), lower := (rows 67 38 13 152 400 32 64 128 256), losses := [] }

theorem u10670 : Upper (D 8) (R 8) [66,36,9,144,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10670 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10671 : PairBound 9 := { available := 464, camps := [{ cop := 4, region := 456, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 13 168 49 496 464 464 464), lower := (rows 67 38 13 168 49 32 64 128 256), losses := [] }

theorem u10671 : Upper (D 8) (R 8) [66,36,9,160,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10671 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10672 : PairBound 9 := { available := 432, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 13 168 81 432 496 432 432), lower := (rows 67 38 13 168 81 32 64 128 256), losses := [] }

theorem u10672 : Upper (D 8) (R 8) [66,36,9,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10672 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10673 : Route 9 := (fun mask => (mask,id))

def c10673 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u10673 : Upper (D 8) (R 8) [66,36,9,160,96] 13 := by
  apply FastRouting.sound _ _ [66,36,9,160,96] 13 (by decide) (choices 1) [1,16,128,256] r10673 c10673
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3028
  · exact u3029
  · exact u3030
  · exact u3031

def b10674 : PairBound 9 := { available := 368, camps := [{ cop := 4, region := 360, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 13 168 145 368 368 496 368), lower := (rows 67 38 13 168 145 32 64 128 256), losses := [] }

theorem u10674 : Upper (D 8) (R 8) [66,36,9,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10674 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10675 : PairBound 9 := { available := 337, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 67 38 13 168 176 369 337 465 337), lower := (rows 67 38 13 168 176 32 64 128 256), losses := [] }

theorem u10675 : Upper (D 8) (R 8) [66,36,9,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10675 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10676 : Route 9 := (fun mask => (mask,id))

def c10676 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u10676 : Upper (D 8) (R 8) [66,36,9,160,192] 13 := by
  apply FastRouting.sound _ _ [66,36,9,160,192] 13 (by decide) (choices 1) [1,16,256] r10676 c10676
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3032
  · exact u3033
  · exact u3034

def b10677 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 13 168 273 240 240 240 496), lower := (rows 67 38 13 168 273 32 64 128 256), losses := [] }

theorem u10677 : Upper (D 8) (R 8) [66,36,9,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10677 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10678 : Route 9 := (fun mask => (mask,id))

def c10678 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u10678 : Upper (D 8) (R 8) [66,36,9,160,288] 13 := by
  apply FastRouting.sound _ _ [66,36,9,160,288] 13 (by decide) (choices 1) [1,16,64,128] r10678 c10678
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3035
  · exact u3036
  · exact u3037
  · exact u3038

def r10679 : Route 9 := (fun mask => (mask,id))

def c10679 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10679 : Upper (D 8) (R 8) [66,36,9,160,320] 13 := by
  apply FastRouting.sound _ _ [66,36,9,160,320] 13 (by decide) (choices 1) [1,16,128] r10679 c10679
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3039
  · exact u3040
  · exact u3041

#print axioms u10679
end Delivery.IrregularNine14.P08

import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0098

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b19680 : PairBound 9 := { available := 50, camps := [{ cop := 5, region := 339, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 67 140 13 336 36 114 178 306), lower := (rows 35 67 140 13 336 36 64 128 256), losses := [] }

theorem u19680 : Upper (D 6) (R 6) [34,65,136,5,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19680 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19681 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 140, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 67 140 13 336 48 102 166 294), lower := (rows 35 67 140 13 336 48 64 128 256), losses := [] }

theorem u19681 : Upper (D 6) (R 6) [34,65,136,5,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19681 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19682 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 484, targets := 3 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,0),(2,1)], upper := (rows 35 67 140 25 22 36 352 480 352), lower := (rows 35 67 140 25 22 36 64 128 256), losses := [] }

theorem u19682 : Upper (D 6) (R 6) [34,65,136,17,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19682 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19683 : PairBound 9 := { available := 292, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 140 25 22 96 356 420 292), lower := (rows 35 67 140 25 22 96 64 128 256), losses := [] }

theorem u19683 : Upper (D 6) (R 6) [34,65,136,17,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19683 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19684 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 484, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 67 140 25 22 288 100 228 356), lower := (rows 35 67 140 25 22 288 64 128 256), losses := [] }

theorem u19684 : Upper (D 6) (R 6) [34,65,136,17,6,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19684 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19685 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 140 25 52 34 324 452 324), lower := (rows 35 67 140 25 52 34 64 128 256), losses := [] }

theorem u19685 : Upper (D 6) (R 6) [34,65,136,17,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19685 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19686 : PairBound 9 := { available := 322, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 67 140 25 52 36 322 450 322), lower := (rows 35 67 140 25 52 36 64 128 256), losses := [] }

theorem u19686 : Upper (D 6) (R 6) [34,65,136,17,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19686 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19687 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 140 25 52 96 326 390 262), lower := (rows 35 67 140 25 52 96 64 128 256), losses := [] }

theorem u19687 : Upper (D 6) (R 6) [34,65,136,17,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19687 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19688 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 198, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 67 140 25 52 288 70 198 326), lower := (rows 35 67 140 25 52 288 64 128 256), losses := [] }

theorem u19688 : Upper (D 6) (R 6) [34,65,136,17,36,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19688 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19689 : PairBound 9 := { available := 292, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 140 25 84 34 356 420 292), lower := (rows 35 67 140 25 84 34 64 128 256), losses := [] }

theorem u19689 : Upper (D 6) (R 6) [34,65,136,17,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19689 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19690 : PairBound 9 := { available := 290, camps := [{ cop := 5, region := 323, targets := 4 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 35 67 140 25 84 36 354 418 290), lower := (rows 35 67 140 25 84 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 24 60 65 129 257), good := (rows 482 450 188 508 116 36 64 128 256) }] }

theorem u19690 : Upper (D 6) (R 6) [34,65,136,17,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19690 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19691 : Route 9 := (fun mask => (mask,id))

def c19691 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19691 : Upper (D 6) (R 6) [34,65,136,17,68,256] 13 := by
  apply FastRouting.sound _ _ [34,65,136,17,68,256] 13 (by decide) (choices 1) [2,4,32] r19691 c19691
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5906
  · exact u5907
  · exact u5908

def b19692 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 228, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 67 140 25 274 36 100 228 356), lower := (rows 35 67 140 25 274 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 17 44 108 172 300), good := (rows 498 82 492 508 274 484 64 128 256) }] }

theorem u19692 : Upper (D 6) (R 6) [34,65,136,17,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19692 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19693 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 140 25 274 96 100 164 292), lower := (rows 35 67 140 25 274 96 64 128 256), losses := [] }

theorem u19693 : Upper (D 6) (R 6) [34,65,136,17,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19693 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19694 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 140 25 276 34 100 228 356), lower := (rows 35 67 140 25 276 34 64 128 256), losses := [] }

theorem u19694 : Upper (D 6) (R 6) [34,65,136,17,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19694 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19695 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 67, targets := 4 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 35 67 140 25 276 36 98 226 354), lower := (rows 35 67 140 25 276 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 24 60 65 129 257), good := (rows 482 450 188 508 308 36 64 128 256) }] }

theorem u19695 : Upper (D 6) (R 6) [34,65,136,17,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19695 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19696 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 140 25 276 96 102 166 294), lower := (rows 35 67 140 25 276 96 64 128 256), losses := [] }

theorem u19696 : Upper (D 6) (R 6) [34,65,136,17,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19696 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19697 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 140 25 304 34 68 196 324), lower := (rows 35 67 140 25 304 34 64 128 256), losses := [] }

theorem u19697 : Upper (D 6) (R 6) [34,65,136,17,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19697 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19698 : Route 9 := (fun mask => (mask,id))

def c19698 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19698 : Upper (D 6) (R 6) [34,65,136,17,288,4] 13 := by
  apply FastRouting.sound _ _ [34,65,136,17,288,4] 13 (by decide) (choices 1) [2,4] r19698 c19698
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5909
  · exact u5910

def b19699 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 140 25 304 96 70 134 262), lower := (rows 35 67 140 25 304 96 64 128 256), losses := [] }

theorem u19699 : Upper (D 6) (R 6) [34,65,136,17,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19699 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19700 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 140 25 336 34 100 164 292), lower := (rows 35 67 140 25 336 34 64 128 256), losses := [] }

theorem u19700 : Upper (D 6) (R 6) [34,65,136,17,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19700 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19701 : Route 9 := (fun mask => (mask,id))

def c19701 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19701 : Upper (D 6) (R 6) [34,65,136,17,320,4] 13 := by
  apply FastRouting.sound _ _ [34,65,136,17,320,4] 13 (by decide) (choices 1) [2,4,32] r19701 c19701
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5911
  · exact u5912
  · exact u5913

def b19702 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 140 28 112 33 326 390 262), lower := (rows 35 67 140 28 112 33 64 128 256), losses := [] }

theorem u19702 : Upper (D 6) (R 6) [34,65,136,20,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19702 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19703 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 140 28 112 34 325 389 261), lower := (rows 35 67 140 28 112 34 64 128 256), losses := [] }

theorem u19703 : Upper (D 6) (R 6) [34,65,136,20,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19703 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19704 : PairBound 9 := { available := 259, camps := [{ cop := 5, region := 339, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 67 140 28 112 36 323 387 259), lower := (rows 35 67 140 28 112 36 64 128 256), losses := [] }

theorem u19704 : Upper (D 6) (R 6) [34,65,136,20,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19704 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19705 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 3, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 67 140 28 112 288 71 135 263), lower := (rows 35 67 140 28 112 288 64 128 256), losses := [] }

theorem u19705 : Upper (D 6) (R 6) [34,65,136,20,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19705 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19706 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 140 28 273 34 100 228 356), lower := (rows 35 67 140 28 273 34 64 128 256), losses := [] }

theorem u19706 : Upper (D 6) (R 6) [34,65,136,20,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19706 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19707 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 339, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 67 140 28 273 36 98 226 354), lower := (rows 35 67 140 28 273 36 64 128 256), losses := [] }

theorem u19707 : Upper (D 6) (R 6) [34,65,136,20,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19707 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19708 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 140 28 273 96 102 166 294), lower := (rows 35 67 140 28 273 96 64 128 256), losses := [] }

theorem u19708 : Upper (D 6) (R 6) [34,65,136,20,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19708 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19709 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 140 28 304 33 70 198 326), lower := (rows 35 67 140 28 304 33 64 128 256), losses := [] }

theorem u19709 : Upper (D 6) (R 6) [34,65,136,20,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19709 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19710 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 140 28 304 34 69 197 325), lower := (rows 35 67 140 28 304 34 64 128 256), losses := [] }

theorem u19710 : Upper (D 6) (R 6) [34,65,136,20,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19710 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19711 : PairBound 9 := { available := 67, camps := [{ cop := 5, region := 339, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 67 140 28 304 36 67 195 323), lower := (rows 35 67 140 28 304 36 64 128 256), losses := [] }

theorem u19711 : Upper (D 6) (R 6) [34,65,136,20,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19711 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19712 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 140 28 304 96 71 135 263), lower := (rows 35 67 140 28 304 96 64 128 256), losses := [] }

theorem u19712 : Upper (D 6) (R 6) [34,65,136,20,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19712 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19713 : PairBound 9 := { available := 336, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 140 44 22 33 336 464 336), lower := (rows 35 67 140 44 22 33 64 128 256), losses := [] }

theorem u19713 : Upper (D 6) (R 6) [34,65,136,36,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19713 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19714 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 67 140 44 22 48 321 449 321), lower := (rows 35 67 140 44 22 48 64 128 256), losses := [] }

theorem u19714 : Upper (D 6) (R 6) [34,65,136,36,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19714 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19715 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 140 44 22 96 337 401 273), lower := (rows 35 67 140 44 22 96 64 128 256), losses := [] }

theorem u19715 : Upper (D 6) (R 6) [34,65,136,36,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19715 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19716 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 355, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 67 140 44 22 288 81 209 337), lower := (rows 35 67 140 44 22 288 64 128 256), losses := [] }

theorem u19716 : Upper (D 6) (R 6) [34,65,136,36,6,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19716 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19717 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 140 44 84 33 338 402 274), lower := (rows 35 67 140 44 84 33 64 128 256), losses := [] }

theorem u19717 : Upper (D 6) (R 6) [34,65,136,36,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19717 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19718 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 140 44 84 34 337 401 273), lower := (rows 35 67 140 44 84 34 64 128 256), losses := [] }

theorem u19718 : Upper (D 6) (R 6) [34,65,136,36,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19718 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19719 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 67 140 44 84 48 323 387 259), lower := (rows 35 67 140 44 84 48 64 128 256), losses := [] }

theorem u19719 : Upper (D 6) (R 6) [34,65,136,36,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19719 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19720 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 291, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 67 140 44 84 288 83 147 275), lower := (rows 35 67 140 44 84 288 64 128 256), losses := [] }

theorem u19720 : Upper (D 6) (R 6) [34,65,136,36,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19720 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19721 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 140 44 273 34 84 212 340), lower := (rows 35 67 140 44 273 34 64 128 256), losses := [] }

theorem u19721 : Upper (D 6) (R 6) [34,65,136,36,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19721 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19722 : PairBound 9 := { available := 82, camps := [{ cop := 7, region := 44, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 140 44 273 36 82 210 338), lower := (rows 35 67 140 44 273 36 64 128 256), losses := [] }

theorem u19722 : Upper (D 6) (R 6) [34,65,136,36,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19722 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19723 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 204, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 67 140 44 273 48 70 198 326), lower := (rows 35 67 140 44 273 48 64 128 256), losses := [] }

theorem u19723 : Upper (D 6) (R 6) [34,65,136,36,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19723 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19724 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 140 44 273 96 86 150 278), lower := (rows 35 67 140 44 273 96 64 128 256), losses := [] }

theorem u19724 : Upper (D 6) (R 6) [34,65,136,36,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19724 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19725 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 140 44 274 33 84 212 340), lower := (rows 35 67 140 44 274 33 64 128 256), losses := [] }

theorem u19725 : Upper (D 6) (R 6) [34,65,136,36,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19725 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19726 : PairBound 9 := { available := 81, camps := [{ cop := 7, region := 44, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 140 44 274 36 81 209 337), lower := (rows 35 67 140 44 274 36 64 128 256), losses := [] }

theorem u19726 : Upper (D 6) (R 6) [34,65,136,36,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19726 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19727 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 67 140 44 274 48 69 197 325), lower := (rows 35 67 140 44 274 48 64 128 256), losses := [] }

theorem u19727 : Upper (D 6) (R 6) [34,65,136,36,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19727 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19728 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 140 44 274 96 85 149 277), lower := (rows 35 67 140 44 274 96 64 128 256), losses := [] }

theorem u19728 : Upper (D 6) (R 6) [34,65,136,36,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19728 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19729 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 140 44 276 33 82 210 338), lower := (rows 35 67 140 44 276 33 64 128 256), losses := [] }

theorem u19729 : Upper (D 6) (R 6) [34,65,136,36,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19729 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19730 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 140 44 276 34 81 209 337), lower := (rows 35 67 140 44 276 34 64 128 256), losses := [] }

theorem u19730 : Upper (D 6) (R 6) [34,65,136,36,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19730 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19731 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 67 140 44 276 48 67 195 323), lower := (rows 35 67 140 44 276 48 64 128 256), losses := [] }

theorem u19731 : Upper (D 6) (R 6) [34,65,136,36,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19731 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19732 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 140 44 276 96 83 147 275), lower := (rows 35 67 140 44 276 96 64 128 256), losses := [] }

theorem u19732 : Upper (D 6) (R 6) [34,65,136,36,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19732 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19733 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 140 44 336 33 86 150 278), lower := (rows 35 67 140 44 336 33 64 128 256), losses := [] }

theorem u19733 : Upper (D 6) (R 6) [34,65,136,36,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19733 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19734 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 140 44 336 34 85 149 277), lower := (rows 35 67 140 44 336 34 64 128 256), losses := [] }

theorem u19734 : Upper (D 6) (R 6) [34,65,136,36,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19734 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19735 : PairBound 9 := { available := 19, camps := [{ cop := 7, region := 44, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 140 44 336 36 83 147 275), lower := (rows 35 67 140 44 336 36 64 128 256), losses := [] }

theorem u19735 : Upper (D 6) (R 6) [34,65,136,36,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19735 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19736 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 140, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 67 140 44 336 48 71 135 263), lower := (rows 35 67 140 44 336 48 64 128 256), losses := [] }

theorem u19736 : Upper (D 6) (R 6) [34,65,136,36,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19736 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19737 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 140 56 21 34 324 452 324), lower := (rows 35 67 140 56 21 34 64 128 256), losses := [] }

theorem u19737 : Upper (D 6) (R 6) [34,65,136,48,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19737 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19738 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 67 140 56 21 36 322 450 322), lower := (rows 35 67 140 56 21 36 64 128 256), losses := [] }

theorem u19738 : Upper (D 6) (R 6) [34,65,136,48,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19738 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19739 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 140 56 21 96 326 390 262), lower := (rows 35 67 140 56 21 96 64 128 256), losses := [] }

theorem u19739 : Upper (D 6) (R 6) [34,65,136,48,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19739 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u19739
end Delivery.IrregularNine14.P06

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

def b720 : PairBound 9 := { available := 66, camps := [{ cop := 5, region := 84, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 11 52 392 84 33 96 194 322), lower := (rows 7 11 52 392 84 33 96 128 256), losses := [] }

theorem u720 : Upper (D 6) (R 6) [6,9,48,384,68,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b720 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b721 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 80, targets := 34 },{ cop := 0, region := 490, targets := 4 }], pairs := [(1,2),(4,1),(4,5)], upper := (rows 7 11 52 392 84 34 65 224 352), lower := (rows 7 11 52 392 84 34 65 128 256), losses := [] }

theorem u721 : Upper (D 6) (R 6) [6,9,48,384,68,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b721 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b722 : PairBound 9 := { available := 65, camps := [{ cop := 5, region := 84, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 11 52 392 84 34 96 193 321), lower := (rows 7 11 52 392 84 34 96 128 256), losses := [] }

theorem u722 : Upper (D 6) (R 6) [6,9,48,384,68,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b722 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r723 : Route 9 := (fun mask => (mask,id))

def c723 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u723 : Upper (D 6) (R 6) [6,9,96,48,132,256,1] 13 := by
  apply FastRouting.sound _ _ [6,9,96,48,132,256,1] 13 (by decide) (choices 1) [2,64] r723 c723
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u14
  · exact u15

def r724 : Route 9 := (fun mask => (mask,id))

def c724 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u724 : Upper (D 6) (R 6) [6,9,96,48,132,256,2] 13 := by
  apply FastRouting.sound _ _ [6,9,96,48,132,256,2] 13 (by decide) (choices 1) [1,64] r724 c724
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16
  · exact u17

def b725 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(2,0),(4,5)], upper := (rows 7 11 100 56 208 288 65 134 262), lower := (rows 7 11 100 56 208 288 65 128 256), losses := [{ target := 0, region := (rows 0 2 84 92 80 355 64 129 257), good := (rows 430 426 124 60 252 288 508 128 288) }] }

theorem u725 : Upper (D 6) (R 6) [6,9,96,48,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b725 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b726 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(2,1),(4,5)], upper := (rows 7 11 100 56 208 288 66 133 261), lower := (rows 7 11 100 56 208 288 66 128 256), losses := [{ target := 1, region := (rows 1 0 68 8 16 291 64 129 257), good := (rows 421 425 100 56 212 288 100 128 288) }] }

theorem u726 : Upper (D 6) (R 6) [6,9,96,48,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b726 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b727 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 68, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 11 100 56 208 288 68 131 259), lower := (rows 7 11 100 56 208 288 68 128 256), losses := [] }

theorem u727 : Upper (D 6) (R 6) [6,9,96,48,192,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b727 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b728 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 408, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 7 11 100 152 276 33 66 224 352), lower := (rows 7 11 100 152 276 33 66 128 256), losses := [] }

theorem u728 : Upper (D 6) (R 6) [6,9,96,144,260,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b728 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b729 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 411, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 11 100 152 276 33 96 194 322), lower := (rows 7 11 100 152 276 33 96 128 256), losses := [] }

theorem u729 : Upper (D 6) (R 6) [6,9,96,144,260,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b729 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b730 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 411, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 11 100 152 276 34 96 193 321), lower := (rows 7 11 100 152 276 34 96 128 256), losses := [] }

theorem u730 : Upper (D 6) (R 6) [6,9,96,144,260,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b730 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b731 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 408, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 7 11 100 152 304 34 65 196 324), lower := (rows 7 11 100 152 304 34 65 128 256), losses := [] }

theorem u731 : Upper (D 6) (R 6) [6,9,96,144,288,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b731 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b732 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 68, targets := 3 }], pairs := [(2,0),(2,1),(3,1)], upper := (rows 7 11 100 152 304 34 68 193 321), lower := (rows 7 11 100 152 304 34 68 128 256), losses := [{ target := 1, region := (rows 1 0 52 40 48 32 125 131 259), good := (rows 453 457 124 220 380 508 68 128 256) }] }

theorem u732 : Upper (D 6) (R 6) [6,9,96,144,288,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b732 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b733 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 36, targets := 3 }], pairs := [(1,2),(2,0),(2,1)], upper := (rows 7 11 100 152 304 36 65 194 322), lower := (rows 7 11 100 152 304 36 65 128 256), losses := [{ target := 2, region := (rows 1 67 0 45 52 32 67 199 327), good := (rows 475 459 506 152 312 440 459 128 256) }] }

theorem u733 : Upper (D 6) (R 6) [6,9,96,144,288,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b733 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r734 : Route 9 := (fun mask => (mask,id))

def c734 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u734 : Upper (D 6) (R 6) [6,9,96,144,288,4,2] 13 := by
  apply FastRouting.sound _ _ [6,9,96,144,288,4,2] 13 (by decide) (choices 1) [1,64] r734 c734
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18
  · exact u19

def b735 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 292, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 11 100 168 81 288 66 148 276), lower := (rows 7 11 100 168 81 288 66 128 256), losses := [] }

theorem u735 : Upper (D 6) (R 6) [6,9,96,160,65,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b735 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b736 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 426, targets := 68 }], pairs := [(1,2),(1,6)], upper := (rows 7 11 100 168 81 288 68 146 274), lower := (rows 7 11 100 168 81 288 68 128 256), losses := [] }

theorem u736 : Upper (D 6) (R 6) [6,9,96,160,65,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b736 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b737 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 139, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 100 168 81 288 80 134 262), lower := (rows 7 11 100 168 81 288 80 128 256), losses := [] }

theorem u737 : Upper (D 6) (R 6) [6,9,96,160,65,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b737 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b738 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 292, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 11 100 168 82 288 65 148 276), lower := (rows 7 11 100 168 82 288 65 128 256), losses := [] }

theorem u738 : Upper (D 6) (R 6) [6,9,96,160,66,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b738 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b739 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 68, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 11 100 168 82 288 68 145 273), lower := (rows 7 11 100 168 82 288 68 128 256), losses := [] }

theorem u739 : Upper (D 6) (R 6) [6,9,96,160,66,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b739 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b740 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 80, targets := 1 }], pairs := [(4,0)], upper := (rows 7 11 100 168 82 288 80 133 261), lower := (rows 7 11 100 168 82 288 80 128 256), losses := [] }

theorem u740 : Upper (D 6) (R 6) [6,9,96,160,66,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b740 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b741 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 136, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 11 100 168 274 48 65 196 324), lower := (rows 7 11 100 168 274 48 65 128 256), losses := [] }

theorem u741 : Upper (D 6) (R 6) [6,9,96,160,258,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b741 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b742 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 68, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 11 100 168 274 48 68 193 321), lower := (rows 7 11 100 168 274 48 68 128 256), losses := [] }

theorem u742 : Upper (D 6) (R 6) [6,9,96,160,258,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b742 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b743 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 336, targets := 32 }], pairs := [(1,2),(4,5)], upper := (rows 7 11 100 168 276 48 65 194 322), lower := (rows 7 11 100 168 276 48 65 128 256), losses := [{ target := 2, region := (rows 1 3 0 12 16 48 67 195 323), good := (rows 459 459 488 168 312 48 451 128 256) }] }

theorem u743 : Upper (D 6) (R 6) [6,9,96,160,260,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b743 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r744 : Route 9 := (fun mask => (mask,id))

def c744 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u744 : Upper (D 6) (R 6) [6,9,96,160,260,16,2] 13 := by
  apply FastRouting.sound _ _ [6,9,96,160,260,16,2] 13 (by decide) (choices 1) [1,64] r744 c744
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u20
  · exact u21

def b745 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 408, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 7 11 100 168 336 34 65 148 276), lower := (rows 7 11 100 168 336 34 65 128 256), losses := [] }

theorem u745 : Upper (D 6) (R 6) [6,9,96,160,320,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b745 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b746 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 336, targets := 34 },{ cop := 3, region := 68, targets := 1 }], pairs := [(2,0),(4,1),(4,5)], upper := (rows 7 11 100 168 336 34 68 145 273), lower := (rows 7 11 100 168 336 34 68 128 256), losses := [] }

theorem u746 : Upper (D 6) (R 6) [6,9,96,160,320,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b746 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b747 : PairBound 9 := { available := 5, camps := [{ cop := 8, region := 80, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 11 100 168 336 34 80 133 261), lower := (rows 7 11 100 168 336 34 80 128 256), losses := [] }

theorem u747 : Upper (D 6) (R 6) [6,9,96,160,320,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b747 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b748 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 376, targets := 1 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 7 11 133 56 336 34 68 224 352), lower := (rows 7 11 133 56 336 34 68 128 256), losses := [{ target := 1, region := (rows 1 0 6 40 58 32 103 168 296), good := (rows 85 477 197 504 336 508 68 128 256) }] }

theorem u748 : Upper (D 6) (R 6) [6,9,129,48,320,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b748 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b749 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 376, targets := 1 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 7 11 133 56 336 34 96 196 324), lower := (rows 7 11 133 56 336 34 96 128 256), losses := [{ target := 1, region := (rows 1 0 7 104 122 32 104 162 290), good := (rows 405 477 133 504 344 508 504 128 256) }] }

theorem u749 : Upper (D 6) (R 6) [6,9,129,48,320,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b749 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r750 : Route 9 := (fun mask => (mask,id))

def c750 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u750 : Upper (D 6) (R 6) [6,9,129,48,320,4,2] 13 := by
  apply FastRouting.sound _ _ [6,9,129,48,320,4,2] 13 (by decide) (choices 1) [32,64] r750 c750
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u22
  · exact u23

def b751 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 376, targets := 1 }], pairs := [(3,0),(4,0),(4,2)], upper := (rows 7 11 133 56 336 36 96 194 322), lower := (rows 7 11 133 56 336 36 96 128 256), losses := [{ target := 2, region := (rows 1 2 0 8 18 32 104 130 258), good := (rows 403 475 129 120 336 96 96 128 256) }] }

theorem u751 : Upper (D 6) (R 6) [6,9,129,48,320,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b751 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b752 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 376, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 11 133 104 274 36 80 224 352), lower := (rows 7 11 133 104 274 36 80 128 256), losses := [] }

theorem u752 : Upper (D 6) (R 6) [6,9,129,96,258,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b752 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b753 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 407, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 7 11 133 104 274 36 96 208 336), lower := (rows 7 11 133 104 274 36 96 128 256), losses := [] }

theorem u753 : Upper (D 6) (R 6) [6,9,129,96,258,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b753 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b754 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 272, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 7 11 133 104 304 36 66 208 336), lower := (rows 7 11 133 104 304 36 66 128 256), losses := [] }

theorem u754 : Upper (D 6) (R 6) [6,9,129,96,288,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b754 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b755 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 135, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 11 133 104 304 36 80 194 322), lower := (rows 7 11 133 104 304 36 80 128 256), losses := [] }

theorem u755 : Upper (D 6) (R 6) [6,9,129,96,288,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b755 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b756 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 376, targets := 1 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 7 11 133 280 52 96 66 224 352), lower := (rows 7 11 133 280 52 96 66 128 256), losses := [{ target := 1, region := (rows 1 0 4 24 16 96 64 224 352), good := (rows 5 9 133 280 444 480 480 128 256) }] }

theorem u756 : Upper (D 6) (R 6) [6,9,129,272,36,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b756 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b757 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 376, targets := 1 },{ cop := 0, region := 112, targets := 2 }], pairs := [(3,0),(4,0),(4,1)], upper := (rows 7 11 133 280 52 96 96 194 322), lower := (rows 7 11 133 280 52 96 96 128 256), losses := [] }

theorem u757 : Upper (D 6) (R 6) [6,9,129,272,36,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b757 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b758 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 264, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 11 133 280 112 34 68 224 352), lower := (rows 7 11 133 280 112 34 68 128 256), losses := [] }

theorem u758 : Upper (D 6) (R 6) [6,9,129,272,96,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b758 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b759 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 399, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 7 11 133 280 112 34 96 196 324), lower := (rows 7 11 133 280 112 34 96 128 256), losses := [] }

theorem u759 : Upper (D 6) (R 6) [6,9,129,272,96,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b759 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b760 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 399, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 7 11 133 280 112 36 96 194 322), lower := (rows 7 11 133 280 112 36 96 128 256), losses := [] }

theorem u760 : Upper (D 6) (R 6) [6,9,129,272,96,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b760 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r761 : Route 9 := (fun mask => (mask,id))

def c761 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u761 : Upper (D 6) (R 6) [6,9,129,288,36,64,2] 13 := by
  apply FastRouting.sound _ _ [6,9,129,288,36,64,2] 13 (by decide) (choices 1) [16,64] r761 c761
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u24
  · exact u25

def b762 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 376, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 11 133 296 52 96 80 194 322), lower := (rows 7 11 133 296 52 96 80 128 256), losses := [] }

theorem u762 : Upper (D 6) (R 6) [6,9,129,288,36,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b762 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b763 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 80, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 11 133 296 82 36 80 224 352), lower := (rows 7 11 133 296 82 36 80 128 256), losses := [] }

theorem u763 : Upper (D 6) (R 6) [6,9,129,288,66,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b763 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b764 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 376, targets := 1 },{ cop := 4, region := 133, targets := 32 }], pairs := [(0,5),(3,0),(4,0)], upper := (rows 7 11 133 296 82 36 96 208 336), lower := (rows 7 11 133 296 82 36 96 128 256), losses := [] }

theorem u764 : Upper (D 6) (R 6) [6,9,129,288,66,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b764 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b765 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 296, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 11 133 296 82 96 68 176 304), lower := (rows 7 11 133 296 82 96 68 128 256), losses := [] }

theorem u765 : Upper (D 6) (R 6) [6,9,129,288,66,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b765 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b766 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 11 133 296 82 96 80 164 292), lower := (rows 7 11 133 296 82 96 80 128 256), losses := [] }

theorem u766 : Upper (D 6) (R 6) [6,9,129,288,66,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b766 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b767 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 133, targets := 96 }], pairs := [(0,5),(0,6),(2,5)], upper := (rows 7 11 133 296 82 96 96 148 276), lower := (rows 7 11 133 296 82 96 96 128 256), losses := [] }

theorem u767 : Upper (D 6) (R 6) [6,9,129,288,66,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b767 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b768 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 296, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 11 133 296 84 96 66 176 304), lower := (rows 7 11 133 296 84 96 66 128 256), losses := [] }

theorem u768 : Upper (D 6) (R 6) [6,9,129,288,68,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b768 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b769 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 11 133 296 84 96 80 162 290), lower := (rows 7 11 133 296 84 96 80 128 256), losses := [] }

theorem u769 : Upper (D 6) (R 6) [6,9,129,288,68,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b769 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b770 : PairBound 9 := { available := 18, camps := [{ cop := 8, region := 104, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 11 133 296 84 96 96 146 274), lower := (rows 7 11 133 296 84 96 96 128 256), losses := [] }

theorem u770 : Upper (D 6) (R 6) [6,9,129,288,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b770 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b771 : PairBound 9 := { available := 80, camps := [{ cop := 4, region := 264, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 11 133 296 112 36 66 208 336), lower := (rows 7 11 133 296 112 36 66 128 256), losses := [] }

theorem u771 : Upper (D 6) (R 6) [6,9,129,288,96,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b771 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b772 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 80, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 11 133 296 112 36 80 194 322), lower := (rows 7 11 133 296 112 36 80 128 256), losses := [] }

theorem u772 : Upper (D 6) (R 6) [6,9,129,288,96,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b772 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b773 : PairBound 9 := { available := 68, camps := [{ cop := 5, region := 404, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 11 148 42 304 96 65 196 324), lower := (rows 7 11 148 42 304 96 65 128 256), losses := [] }

theorem u773 : Upper (D 6) (R 6) [6,9,144,34,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b773 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b774 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 104, targets := 1 }], pairs := [(2,1),(3,0),(4,1)], upper := (rows 7 11 148 42 304 96 68 193 321), lower := (rows 7 11 148 42 304 96 68 128 256), losses := [] }

theorem u774 : Upper (D 6) (R 6) [6,9,144,34,288,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b774 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b775 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 404, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 11 148 42 336 96 65 164 292), lower := (rows 7 11 148 42 336 96 65 128 256), losses := [] }

theorem u775 : Upper (D 6) (R 6) [6,9,144,34,320,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b775 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b776 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 104, targets := 1 }], pairs := [(2,1),(3,0),(4,1)], upper := (rows 7 11 148 42 336 96 68 161 289), lower := (rows 7 11 148 42 336 96 68 128 256), losses := [] }

theorem u776 : Upper (D 6) (R 6) [6,9,144,34,320,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b776 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b777 : PairBound 9 := { available := 5, camps := [{ cop := 8, region := 112, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 7 11 148 42 336 96 96 133 261), lower := (rows 7 11 148 42 336 96 96 128 256), losses := [] }

theorem u777 : Upper (D 6) (R 6) [6,9,144,34,320,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b777 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b778 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 104, targets := 1 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 11 148 104 273 34 68 224 352), lower := (rows 7 11 148 104 273 34 68 128 256), losses := [{ target := 0, region := (rows 0 2 20 27 16 35 85 155 283), good := (rows 494 490 476 488 508 426 68 128 256) },{ target := 1, region := (rows 1 0 38 40 18 32 111 168 296), good := (rows 85 477 212 492 337 508 68 128 256) }] }

theorem u778 : Upper (D 6) (R 6) [6,9,144,96,257,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b778 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b779 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 407, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 7 11 148 104 273 36 96 194 322), lower := (rows 7 11 148 104 273 36 96 128 256), losses := [] }

theorem u779 : Upper (D 6) (R 6) [6,9,144,96,257,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b779 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u779
end Delivery.IrregularNine14.P06

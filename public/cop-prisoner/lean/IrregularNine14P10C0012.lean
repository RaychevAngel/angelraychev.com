import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P10C0002
import IrregularNine14P10C0003

namespace Delivery.IrregularNine14.P10
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b720 : PairBound 9 := { available := 336, camps := [{ cop := 3, region := 36, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 44 392 176 36 336 464 336), lower := (rows 35 67 44 392 176 36 64 128 256), losses := [] }

theorem u720 : Upper (D 10) (R 10) [34,65,40,384,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b720 [(5,2)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b721 : PairBound 9 := { available := 324, camps := [{ cop := 3, region := 52, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 44 392 176 48 324 452 324), lower := (rows 35 67 44 392 176 48 64 128 256), losses := [] }

theorem u721 : Upper (D 10) (R 10) [34,65,40,384,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b721 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b722 : PairBound 9 := { available := 276, camps := [{ cop := 5, region := 3, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 35 67 44 392 176 96 340 404 276), lower := (rows 35 67 44 392 176 96 64 128 256), losses := [] }

theorem u722 : Upper (D 10) (R 10) [34,65,40,384,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b722 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b723 : PairBound 9 := { available := 84, camps := [{ cop := 2, region := 211, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 35 67 44 392 176 288 84 212 340), lower := (rows 35 67 44 392 176 288 64 128 256), losses := [] }

theorem u723 : Upper (D 10) (R 10) [34,65,40,384,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b723 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b724 : PairBound 9 := { available := 336, camps := [{ cop := 4, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 140 296 176 36 336 464 336), lower := (rows 35 67 140 296 176 36 64 128 256), losses := [] }

theorem u724 : Upper (D 10) (R 10) [34,65,136,288,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b724 [(5,2)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b725 : PairBound 9 := { available := 324, camps := [{ cop := 2, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 35 67 140 296 176 48 324 452 324), lower := (rows 35 67 140 296 176 48 64 128 256), losses := [] }

theorem u725 : Upper (D 10) (R 10) [34,65,136,288,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b725 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b726 : PairBound 9 := { available := 276, camps := [{ cop := 5, region := 3, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 35 67 140 296 176 96 340 404 276), lower := (rows 35 67 140 296 176 96 64 128 256), losses := [] }

theorem u726 : Upper (D 10) (R 10) [34,65,136,288,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b726 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b727 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 215, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 35 67 140 296 176 288 84 212 340), lower := (rows 35 67 140 296 176 288 64 128 256), losses := [] }

theorem u727 : Upper (D 10) (R 10) [34,65,136,288,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b727 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b728 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 44, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 140 296 400 36 112 240 368), lower := (rows 35 67 140 296 400 36 64 128 256), losses := [] }

theorem u728 : Upper (D 10) (R 10) [34,65,136,288,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b728 [(5,2)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b729 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 199, targets := 256 }], pairs := [(0,8)], upper := (rows 35 67 140 296 400 48 100 228 356), lower := (rows 35 67 140 296 400 48 64 128 256), losses := [] }

theorem u729 : Upper (D 10) (R 10) [34,65,136,288,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b729 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b730 : PairBound 9 := { available := 52, camps := [{ cop := 5, region := 3, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 35 67 140 296 400 96 116 180 308), lower := (rows 35 67 140 296 400 96 64 128 256), losses := [] }

theorem u730 : Upper (D 10) (R 10) [34,65,136,288,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b730 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b731 : PairBound 9 := { available := 88, camps := [{ cop := 4, region := 36, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 164 296 400 36 88 216 344), lower := (rows 35 67 164 296 400 36 64 128 256), losses := [] }

theorem u731 : Upper (D 10) (R 10) [34,65,160,288,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b731 [(5,2)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b732 : PairBound 9 := { available := 76, camps := [{ cop := 2, region := 331, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 164 296 400 48 76 204 332), lower := (rows 35 67 164 296 400 48 64 128 256), losses := [] }

theorem u732 : Upper (D 10) (R 10) [34,65,160,288,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b732 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b733 : PairBound 9 := { available := 28, camps := [{ cop := 5, region := 3, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 35 67 164 296 400 96 92 156 284), lower := (rows 35 67 164 296 400 96 64 128 256), losses := [] }

theorem u733 : Upper (D 10) (R 10) [34,65,160,288,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b733 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b734 : PairBound 9 := { available := 384, camps := [{ cop := 1, region := 49, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 44 137 112 48 448 384 384), lower := (rows 35 70 44 137 112 48 64 128 256), losses := [] }

theorem u734 : Upper (D 10) (R 10) [34,68,40,129,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b734 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b735 : PairBound 9 := { available := 272, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 70 44 137 112 160 336 400 272), lower := (rows 35 70 44 137 112 160 64 128 256), losses := [] }

theorem u735 : Upper (D 10) (R 10) [34,68,40,129,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b735 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r736 : Route 9 := (fun mask => (mask,id))

def c736 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | _ => 0)

theorem u736 : Upper (D 10) (R 10) [34,68,40,129,96,256] 13 := by
  apply FastRouting.sound _ _ [34,68,40,129,96,256] 13 (by decide) (choices 1) [16,128,256] r736 c736
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u169
  · exact u170
  · exact u171

def b737 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 47, targets := 256 }], pairs := [(0,8)], upper := (rows 35 70 44 137 208 48 352 416 288), lower := (rows 35 70 44 137 208 48 64 128 256), losses := [] }

theorem u737 : Upper (D 10) (R 10) [34,68,40,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b737 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r738 : Route 9 := (fun mask => (mask,id))

def c738 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u738 : Upper (D 10) (R 10) [34,68,40,129,192,256] 13 := by
  apply FastRouting.sound _ _ [34,68,40,129,192,256] 13 (by decide) (choices 1) [16,32,256] r738 c738
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u172
  · exact u173
  · exact u174

def b739 : PairBound 9 := { available := 448, camps := [{ cop := 8, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 35 70 44 137 304 48 448 448 448), lower := (rows 35 70 44 137 304 48 64 128 256), losses := [] }

theorem u739 : Upper (D 10) (R 10) [34,68,40,129,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b739 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b740 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 70 44 137 304 96 464 400 400), lower := (rows 35 70 44 137 304 96 64 128 256), losses := [] }

theorem u740 : Upper (D 10) (R 10) [34,68,40,129,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b740 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b741 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 207, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 35 70 44 137 304 288 208 208 464), lower := (rows 35 70 44 137 304 288 64 128 256), losses := [] }

theorem u741 : Upper (D 10) (R 10) [34,68,40,129,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b741 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b742 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 44 137 336 48 480 416 416), lower := (rows 35 70 44 137 336 48 64 128 256), losses := [] }

theorem u742 : Upper (D 10) (R 10) [34,68,40,129,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b742 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b743 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 70 44 137 336 160 368 432 304), lower := (rows 35 70 44 137 336 160 64 128 256), losses := [] }

theorem u743 : Upper (D 10) (R 10) [34,68,40,129,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b743 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r744 : Route 9 := (fun mask => (mask,id))

def c744 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u744 : Upper (D 10) (R 10) [34,68,40,129,320,256] 13 := by
  apply FastRouting.sound _ _ [34,68,40,129,320,256] 13 (by decide) (choices 1) [16,32,128] r744 c744
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u175
  · exact u176
  · exact u177

def b745 : PairBound 9 := { available := 384, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 44 152 112 33 448 384 384), lower := (rows 35 70 44 152 112 33 64 128 256), losses := [] }

theorem u745 : Upper (D 10) (R 10) [34,68,40,144,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b745 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b746 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 70 44 152 112 160 321 385 257), lower := (rows 35 70 44 152 112 160 64 128 256), losses := [] }

theorem u746 : Upper (D 10) (R 10) [34,68,40,144,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b746 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r747 : Route 9 := (fun mask => (mask,id))

def c747 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u747 : Upper (D 10) (R 10) [34,68,40,144,96,256] 13 := by
  apply FastRouting.sound _ _ [34,68,40,144,96,256] 13 (by decide) (choices 1) [1,128,256] r747 c747
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u178
  · exact u179
  · exact u180

def b748 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 70 44 152 273 96 480 416 416), lower := (rows 35 70 44 152 273 96 64 128 256), losses := [] }

theorem u748 : Upper (D 10) (R 10) [34,68,40,144,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b748 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b749 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 70 44 152 273 160 352 480 352), lower := (rows 35 70 44 152 273 160 64 128 256), losses := [] }

theorem u749 : Upper (D 10) (R 10) [34,68,40,144,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b749 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b750 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 195, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 35 70 44 152 273 288 224 224 480), lower := (rows 35 70 44 152 273 288 64 128 256), losses := [] }

theorem u750 : Upper (D 10) (R 10) [34,68,40,144,257,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b750 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b751 : PairBound 9 := { available := 448, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 44 152 304 33 448 448 448), lower := (rows 35 70 44 152 304 33 64 128 256), losses := [] }

theorem u751 : Upper (D 10) (R 10) [34,68,40,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b751 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b752 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 70 44 152 304 96 449 385 385), lower := (rows 35 70 44 152 304 96 64 128 256), losses := [] }

theorem u752 : Upper (D 10) (R 10) [34,68,40,144,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b752 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b753 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 70 44 152 304 160 321 449 321), lower := (rows 35 70 44 152 304 160 64 128 256), losses := [] }

theorem u753 : Upper (D 10) (R 10) [34,68,40,144,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b753 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b754 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 207, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 35 70 44 152 304 288 193 193 449), lower := (rows 35 70 44 152 304 288 64 128 256), losses := [] }

theorem u754 : Upper (D 10) (R 10) [34,68,40,144,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b754 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b755 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 44 152 336 33 480 416 416), lower := (rows 35 70 44 152 336 33 64 128 256), losses := [] }

theorem u755 : Upper (D 10) (R 10) [34,68,40,144,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b755 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b756 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 70 44 152 336 160 353 417 289), lower := (rows 35 70 44 152 336 160 64 128 256), losses := [] }

theorem u756 : Upper (D 10) (R 10) [34,68,40,144,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b756 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b757 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 195, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 35 70 44 152 336 288 225 161 417), lower := (rows 35 70 44 152 336 288 64 128 256), losses := [] }

theorem u757 : Upper (D 10) (R 10) [34,68,40,144,320,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b757 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b758 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 44 392 112 33 464 400 400), lower := (rows 35 70 44 392 112 33 64 128 256), losses := [] }

theorem u758 : Upper (D 10) (R 10) [34,68,40,384,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b758 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b759 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 49, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 44 392 112 48 449 385 385), lower := (rows 35 70 44 392 112 48 64 128 256), losses := [] }

theorem u759 : Upper (D 10) (R 10) [34,68,40,384,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b759 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b760 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 70 44 392 112 160 337 401 273), lower := (rows 35 70 44 392 112 160 64 128 256), losses := [] }

theorem u760 : Upper (D 10) (R 10) [34,68,40,384,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b760 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b761 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 44 392 145 48 352 480 352), lower := (rows 35 70 44 392 145 48 64 128 256), losses := [] }

theorem u761 : Upper (D 10) (R 10) [34,68,40,384,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b761 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b762 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 70 44 392 145 96 368 432 304), lower := (rows 35 70 44 392 145 96 64 128 256), losses := [] }

theorem u762 : Upper (D 10) (R 10) [34,68,40,384,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b762 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b763 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 211, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 35 70 44 392 145 288 112 240 368), lower := (rows 35 70 44 392 145 288 64 128 256), losses := [] }

theorem u763 : Upper (D 10) (R 10) [34,68,40,384,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b763 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b764 : PairBound 9 := { available := 336, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 44 392 176 33 336 464 336), lower := (rows 35 70 44 392 176 33 64 128 256), losses := [] }

theorem u764 : Upper (D 10) (R 10) [34,68,40,384,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b764 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b765 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 52, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 44 392 176 48 321 449 321), lower := (rows 35 70 44 392 176 48 64 128 256), losses := [] }

theorem u765 : Upper (D 10) (R 10) [34,68,40,384,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b765 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b766 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 70 44 392 176 96 337 401 273), lower := (rows 35 70 44 392 176 96 64 128 256), losses := [] }

theorem u766 : Upper (D 10) (R 10) [34,68,40,384,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b766 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b767 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 211, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 35 70 44 392 176 288 81 209 337), lower := (rows 35 70 44 392 176 288 64 128 256), losses := [] }

theorem u767 : Upper (D 10) (R 10) [34,68,40,384,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b767 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b768 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 44 392 208 33 368 432 304), lower := (rows 35 70 44 392 208 33 64 128 256), losses := [] }

theorem u768 : Upper (D 10) (R 10) [34,68,40,384,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b768 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b769 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 44 392 208 48 353 417 289), lower := (rows 35 70 44 392 208 48 64 128 256), losses := [] }

theorem u769 : Upper (D 10) (R 10) [34,68,40,384,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b769 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b770 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 211, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 35 70 44 392 208 288 113 177 305), lower := (rows 35 70 44 392 208 288 64 128 256), losses := [] }

theorem u770 : Upper (D 10) (R 10) [34,68,40,384,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b770 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b771 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 40, targets := 128 }], pairs := [(3,7)], upper := (rows 35 70 133 56 336 40 480 416 416), lower := (rows 35 70 133 56 336 40 64 128 256), losses := [] }

theorem u771 : Upper (D 10) (R 10) [34,68,129,48,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b771 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b772 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 344, targets := 128 }], pairs := [(3,7),(4,7)], upper := (rows 35 70 133 56 336 160 360 424 296), lower := (rows 35 70 133 56 336 160 64 128 256), losses := [] }

theorem u772 : Upper (D 10) (R 10) [34,68,129,48,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b772 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b773 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 199, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 35 70 133 56 336 288 232 168 424), lower := (rows 35 70 133 56 336 288 64 128 256), losses := [] }

theorem u773 : Upper (D 10) (R 10) [34,68,129,48,320,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b773 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b774 : PairBound 9 := { available := 352, camps := [{ cop := 4, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 133 56 400 40 352 480 352), lower := (rows 35 70 133 56 400 40 64 128 256), losses := [] }

theorem u774 : Upper (D 10) (R 10) [34,68,129,48,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b774 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b775 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 70 133 56 400 96 360 424 296), lower := (rows 35 70 133 56 400 96 64 128 256), losses := [] }

theorem u775 : Upper (D 10) (R 10) [34,68,129,48,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b775 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b776 : PairBound 9 := { available := 104, camps := [{ cop := 3, region := 199, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 35 70 133 56 400 288 104 232 360), lower := (rows 35 70 133 56 400 288 64 128 256), losses := [] }

theorem u776 : Upper (D 10) (R 10) [34,68,129,48,384,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b776 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b777 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 388, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 133 88 304 40 480 416 416), lower := (rows 35 70 133 88 304 40 64 128 256), losses := [] }

theorem u777 : Upper (D 10) (R 10) [34,68,129,80,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b777 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b778 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 344, targets := 128 }], pairs := [(3,7),(4,7)], upper := (rows 35 70 133 88 304 160 360 424 296), lower := (rows 35 70 133 88 304 160 64 128 256), losses := [] }

theorem u778 : Upper (D 10) (R 10) [34,68,129,80,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b778 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b779 : PairBound 9 := { available := 168, camps := [{ cop := 4, region := 207, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 35 70 133 88 304 288 232 168 424), lower := (rows 35 70 133 88 304 288 64 128 256), losses := [] }

theorem u779 : Upper (D 10) (R 10) [34,68,129,80,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b779 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

#print axioms u779
end Delivery.IrregularNine14.P10

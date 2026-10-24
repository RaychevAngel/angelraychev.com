import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0000

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b720 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 315, targets := 128 },{ cop := 6, region := 4, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7),(4,7)], upper := (rows 35 7 196 56 88 288 192 385 257), lower := (rows 35 7 196 56 88 288 192 128 256), losses := [] }

theorem u720 : Upper (D 9) (R 9) [34,5,192,48,72,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b720 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b721 : PairBound 9 := { available := 129, camps := [{ cop := 5, region := 88, targets := 129 },{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(3,0),(3,7),(4,0),(4,7)], upper := (rows 35 7 196 56 88 288 320 129 385), lower := (rows 35 7 196 56 88 288 320 128 256), losses := [] }

theorem u721 : Upper (D 9) (R 9) [34,5,192,48,72,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b721 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b722 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 299, targets := 128 },{ cop := 2, region := 291, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(3,7)], upper := (rows 35 7 196 73 152 288 80 416 288), lower := (rows 35 7 196 73 152 288 80 128 256), losses := [] }

theorem u722 : Upper (D 9) (R 9) [34,5,192,65,136,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b722 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b723 : PairBound 9 := { available := 272, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 0, region := 72, targets := 384 }], pairs := [(1,5),(2,5),(3,7),(3,8),(4,5)], upper := (rows 35 7 196 73 152 288 96 400 272), lower := (rows 35 7 196 73 152 288 96 128 256), losses := [] }

theorem u723 : Upper (D 9) (R 9) [34,5,192,65,136,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b723 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b724 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 436, targets := 1 },{ cop := 3, region := 432, targets := 64 }], pairs := [(0,6),(2,0),(3,5),(4,0),(4,6)], upper := (rows 35 7 196 73 152 288 320 176 304), lower := (rows 35 7 196 73 152 288 320 128 256), losses := [{ target := 5, region := (rows 1 2 4 9 16 0 352 128 256), good := (rows 75 15 196 73 152 320 320 128 320) },{ target := 6, region := (rows 5 6 4 8 24 376 0 152 280), good := (rows 35 7 167 441 440 288 288 128 288) }] }

theorem u724 : Upper (D 9) (R 9) [34,5,192,65,136,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b724 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b725 : PairBound 9 := { available := 272, camps := [{ cop := 4, region := 79, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 7 196 73 176 288 72 400 272), lower := (rows 35 7 196 73 176 288 72 128 256), losses := [] }

theorem u725 : Upper (D 9) (R 9) [34,5,192,65,160,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b725 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b726 : PairBound 9 := { available := 264, camps := [{ cop := 4, region := 79, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 7 196 73 176 288 80 392 264), lower := (rows 35 7 196 73 176 288 80 128 256), losses := [] }

theorem u726 : Upper (D 9) (R 9) [34,5,192,65,160,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b726 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b727 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 436, targets := 1 },{ cop := 3, region := 432, targets := 64 }], pairs := [(2,0),(2,5),(3,5),(4,0),(4,6)], upper := (rows 35 7 196 73 176 288 320 152 280), lower := (rows 35 7 196 73 176 288 320 128 256), losses := [{ target := 5, region := (rows 1 2 20 9 16 0 352 128 256), good := (rows 75 15 196 73 212 320 320 128 320) }] }

theorem u727 : Upper (D 9) (R 9) [34,5,192,65,160,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b727 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b728 : PairBound 9 := { available := 384, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 0, region := 72, targets := 128 }], pairs := [(1,5),(2,5),(3,7),(4,5)], upper := (rows 35 7 196 73 280 48 96 384 384), lower := (rows 35 7 196 73 280 48 96 128 256), losses := [] }

theorem u728 : Upper (D 9) (R 9) [34,5,192,65,264,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b728 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b729 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 35 7 196 73 280 48 192 416 288), lower := (rows 35 7 196 73 280 48 192 128 256), losses := [] }

theorem u729 : Upper (D 9) (R 9) [34,5,192,65,264,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b729 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b730 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 436, targets := 1 },{ cop := 3, region := 432, targets := 64 }], pairs := [(0,8),(2,0),(4,0),(4,6)], upper := (rows 35 7 196 73 280 48 320 160 416), lower := (rows 35 7 196 73 280 48 320 128 256), losses := [{ target := 8, region := (rows 49 26 12 8 16 48 64 177 0), good := (rows 163 135 196 207 191 179 64 128 0) }] }

theorem u730 : Upper (D 9) (R 9) [34,5,192,65,264,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b730 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b731 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 291, targets := 64 },{ cop := 3, region := 436, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(4,0)], upper := (rows 35 7 196 73 280 288 80 160 416), lower := (rows 35 7 196 73 280 288 80 128 256), losses := [] }

theorem u731 : Upper (D 9) (R 9) [34,5,192,65,264,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b731 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b732 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 0, region := 72, targets := 384 }], pairs := [(1,5),(2,5),(3,7),(3,8),(4,5)], upper := (rows 35 7 196 73 280 288 96 144 400), lower := (rows 35 7 196 73 280 288 96 128 256), losses := [] }

theorem u732 : Upper (D 9) (R 9) [34,5,192,65,264,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b732 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b733 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 315, targets := 128 },{ cop := 6, region := 4, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7),(4,7)], upper := (rows 35 7 196 73 280 288 192 176 304), lower := (rows 35 7 196 73 280 288 192 128 256), losses := [] }

theorem u733 : Upper (D 9) (R 9) [34,5,192,65,264,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b733 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b734 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 72, targets := 416 },{ cop := 2, region := 307, targets := 64 }], pairs := [(0,6),(3,5),(3,7),(3,8)], upper := (rows 35 7 196 73 400 288 72 176 304), lower := (rows 35 7 196 73 400 288 72 128 256), losses := [] }

theorem u734 : Upper (D 9) (R 9) [34,5,192,65,384,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b734 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b735 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 299, targets := 128 },{ cop := 3, region := 420, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 35 7 196 73 400 288 80 168 296), lower := (rows 35 7 196 73 400 288 80 128 256), losses := [] }

theorem u735 : Upper (D 9) (R 9) [34,5,192,65,384,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b735 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b736 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 0, region := 72, targets := 384 }], pairs := [(1,5),(2,5),(3,7),(3,8),(4,5)], upper := (rows 35 7 196 73 400 288 96 152 280), lower := (rows 35 7 196 73 400 288 96 128 256), losses := [] }

theorem u736 : Upper (D 9) (R 9) [34,5,192,65,384,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b736 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b737 : PairBound 9 := { available := 264, camps := [{ cop := 4, region := 79, targets := 256 },{ cop := 6, region := 444, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(2,8),(3,8)], upper := (rows 35 7 196 88 176 288 65 392 264), lower := (rows 35 7 196 88 176 288 65 128 256), losses := [] }

theorem u737 : Upper (D 9) (R 9) [34,5,192,80,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b737 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b738 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 76, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 35 7 196 88 176 288 72 385 257), lower := (rows 35 7 196 88 176 288 72 128 256), losses := [] }

theorem u738 : Upper (D 9) (R 9) [34,5,192,80,160,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b738 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b739 : PairBound 9 := { available := 9, camps := [], pairs := [(2,0),(2,5),(3,0),(3,5),(4,0)], upper := (rows 35 7 196 88 176 288 320 137 265), lower := (rows 35 7 196 88 176 288 320 128 256), losses := [{ target := 0, region := (rows 0 2 20 28 20 352 352 128 256), good := (rows 98 30 252 124 252 352 352 128 352) },{ target := 5, region := (rows 1 2 20 24 16 0 352 128 256), good := (rows 67 7 196 92 220 320 320 128 320) }] }

theorem u739 : Upper (D 9) (R 9) [34,5,192,80,160,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b739 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b740 : PairBound 9 := { available := 384, camps := [{ cop := 0, region := 400, targets := 96 },{ cop := 4, region := 236, targets := 1 }], pairs := [(2,0),(3,0),(4,5),(4,6)], upper := (rows 35 7 196 88 273 40 96 384 384), lower := (rows 35 7 196 88 273 40 96 128 256), losses := [] }

theorem u740 : Upper (D 9) (R 9) [34,5,192,80,257,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b740 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b741 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 35 7 196 88 273 40 192 416 288), lower := (rows 35 7 196 88 273 40 192 128 256), losses := [] }

theorem u741 : Upper (D 9) (R 9) [34,5,192,80,257,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b741 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b742 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 167, targets := 256 },{ cop := 4, region := 236, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(2,8)], upper := (rows 35 7 196 88 273 40 320 160 416), lower := (rows 35 7 196 88 273 40 320 128 256), losses := [] }

theorem u742 : Upper (D 9) (R 9) [34,5,192,80,257,8,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b742 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b743 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 307, targets := 64 },{ cop := 4, region := 236, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(4,6)], upper := (rows 35 7 196 88 273 288 72 160 416), lower := (rows 35 7 196 88 273 288 72 128 256), losses := [] }

theorem u743 : Upper (D 9) (R 9) [34,5,192,80,257,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b743 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b744 : PairBound 9 := { available := 136, camps := [{ cop := 4, region := 236, targets := 1 },{ cop := 3, region := 132, targets := 32 },{ cop := 3, region := 132, targets := 256 },{ cop := 4, region := 104, targets := 128 }], pairs := [(2,0),(2,5),(2,8),(3,0),(3,7)], upper := (rows 35 7 196 88 273 288 96 136 392), lower := (rows 35 7 196 88 273 288 96 128 256), losses := [] }

theorem u744 : Upper (D 9) (R 9) [34,5,192,80,257,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b744 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b745 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 315, targets := 128 },{ cop := 6, region := 4, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7),(4,7)], upper := (rows 35 7 196 88 273 288 192 168 296), lower := (rows 35 7 196 88 273 288 192 128 256), losses := [] }

theorem u745 : Upper (D 9) (R 9) [34,5,192,80,257,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b745 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b746 : PairBound 9 := { available := 384, camps := [{ cop := 6, region := 444, targets := 1 },{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,0),(3,0),(4,0)], upper := (rows 35 7 196 88 304 40 65 384 384), lower := (rows 35 7 196 88 304 40 65 128 256), losses := [] }

theorem u746 : Upper (D 9) (R 9) [34,5,192,80,288,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b746 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b747 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 35 7 196 88 304 40 192 385 257), lower := (rows 35 7 196 88 304 40 192 128 256), losses := [] }

theorem u747 : Upper (D 9) (R 9) [34,5,192,80,288,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b747 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b748 : PairBound 9 := { available := 129, camps := [{ cop := 6, region := 56, targets := 129 }], pairs := [(3,0),(3,7),(4,0),(4,7)], upper := (rows 35 7 196 88 304 40 320 129 385), lower := (rows 35 7 196 88 304 40 320 128 256), losses := [] }

theorem u748 : Upper (D 9) (R 9) [34,5,192,80,288,8,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b748 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b749 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 111, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 7 196 88 400 40 65 416 288), lower := (rows 35 7 196 88 400 40 65 128 256), losses := [] }

theorem u749 : Upper (D 9) (R 9) [34,5,192,80,384,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b749 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b750 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 111, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 7 196 88 400 40 96 385 257), lower := (rows 35 7 196 88 400 40 96 128 256), losses := [] }

theorem u750 : Upper (D 9) (R 9) [34,5,192,80,384,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b750 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b751 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 167, targets := 256 },{ cop := 4, region := 68, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(2,8)], upper := (rows 35 7 196 88 400 40 320 161 289), lower := (rows 35 7 196 88 400 40 320 128 256), losses := [] }

theorem u751 : Upper (D 9) (R 9) [34,5,192,80,384,8,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b751 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r752 : Route 9 := (fun mask => (mask,id))

def c752 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u752 : Upper (D 9) (R 9) [34,5,192,80,384,256,1] 13 := by
  apply FastRouting.sound _ _ [34,5,192,80,384,256,1] 13 (by decide) (choices 1) [8,32] r752 c752
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u34
  · exact u35

def b753 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 76, targets := 288 }], pairs := [(2,5),(2,8),(3,5),(3,8)], upper := (rows 35 7 196 88 400 288 72 161 289), lower := (rows 35 7 196 88 400 288 72 128 256), losses := [] }

theorem u753 : Upper (D 9) (R 9) [34,5,192,80,384,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b753 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r754 : Route 9 := (fun mask => (mask,id))

def c754 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u754 : Upper (D 9) (R 9) [34,5,192,80,384,256,32] 13 := by
  apply FastRouting.sound _ _ [34,5,192,80,384,256,32] 13 (by decide) (choices 1) [1,8] r754 c754
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u36
  · exact u37

def b755 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 307, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 7 196 104 273 48 72 384 384), lower := (rows 35 7 196 104 273 48 72 128 256), losses := [] }

theorem u755 : Upper (D 9) (R 9) [34,5,192,96,257,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b755 [(5,4),(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b756 : PairBound 9 := { available := 264, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 35 7 196 104 273 48 192 392 264), lower := (rows 35 7 196 104 273 48 192 128 256), losses := [] }

theorem u756 : Upper (D 9) (R 9) [34,5,192,96,257,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b756 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b757 : PairBound 9 := { available := 136, camps := [{ cop := 3, region := 135, targets := 256 },{ cop := 0, region := 460, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(2,8)], upper := (rows 35 7 196 104 273 48 320 136 392), lower := (rows 35 7 196 104 273 48 320 128 256), losses := [] }

theorem u757 : Upper (D 9) (R 9) [34,5,192,96,257,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b757 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b758 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 307, targets := 64 },{ cop := 5, region := 72, targets := 1 }], pairs := [(0,6),(1,6),(3,0),(4,6)], upper := (rows 35 7 196 104 273 288 72 144 400), lower := (rows 35 7 196 104 273 288 72 128 256), losses := [] }

theorem u758 : Upper (D 9) (R 9) [34,5,192,96,257,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b758 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b759 : PairBound 9 := { available := 136, camps := [{ cop := 3, region := 135, targets := 256 },{ cop := 4, region := 236, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(2,8)], upper := (rows 35 7 196 104 273 288 80 136 392), lower := (rows 35 7 196 104 273 288 80 128 256), losses := [] }

theorem u759 : Upper (D 9) (R 9) [34,5,192,96,257,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b759 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b760 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 315, targets := 128 },{ cop := 6, region := 4, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7),(4,7)], upper := (rows 35 7 196 104 273 288 192 152 280), lower := (rows 35 7 196 104 273 288 192 128 256), losses := [] }

theorem u760 : Upper (D 9) (R 9) [34,5,192,96,257,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b760 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b761 : PairBound 9 := { available := 384, camps := [{ cop := 6, region := 444, targets := 1 },{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,0),(3,0),(4,0)], upper := (rows 35 7 196 104 280 48 65 384 384), lower := (rows 35 7 196 104 280 48 65 128 256), losses := [] }

theorem u761 : Upper (D 9) (R 9) [34,5,192,96,264,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b761 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b762 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 35 7 196 104 280 48 192 385 257), lower := (rows 35 7 196 104 280 48 192 128 256), losses := [] }

theorem u762 : Upper (D 9) (R 9) [34,5,192,96,264,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b762 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b763 : PairBound 9 := { available := 129, camps := [{ cop := 6, region := 56, targets := 129 }], pairs := [(3,0),(3,7),(4,0),(4,7)], upper := (rows 35 7 196 104 280 48 320 129 385), lower := (rows 35 7 196 104 280 48 320 128 256), losses := [] }

theorem u763 : Upper (D 9) (R 9) [34,5,192,96,264,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b763 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b764 : PairBound 9 := { available := 144, camps := [{ cop := 6, region := 444, targets := 1 },{ cop := 0, region := 72, targets := 384 }], pairs := [(2,0),(3,0),(3,7),(3,8),(4,0)], upper := (rows 35 7 196 104 280 288 65 144 400), lower := (rows 35 7 196 104 280 288 65 128 256), losses := [] }

theorem u764 : Upper (D 9) (R 9) [34,5,192,96,264,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b764 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b765 : PairBound 9 := { available := 129, camps := [{ cop := 5, region := 88, targets := 129 }], pairs := [(3,0),(3,7),(4,0),(4,7)], upper := (rows 35 7 196 104 280 288 80 129 385), lower := (rows 35 7 196 104 280 288 80 128 256), losses := [] }

theorem u765 : Upper (D 9) (R 9) [34,5,192,96,264,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b765 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b766 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 315, targets := 128 },{ cop := 6, region := 4, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7),(4,7)], upper := (rows 35 7 196 104 280 288 192 145 273), lower := (rows 35 7 196 104 280 288 192 128 256), losses := [] }

theorem u766 : Upper (D 9) (R 9) [34,5,192,96,264,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b766 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b767 : PairBound 9 := { available := 264, camps := [{ cop := 4, region := 111, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 7 196 104 400 48 65 392 264), lower := (rows 35 7 196 104 400 48 65 128 256), losses := [] }

theorem u767 : Upper (D 9) (R 9) [34,5,192,96,384,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b767 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b768 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 111, targets := 256 }], pairs := [(0,8),(1,8),(2,8)], upper := (rows 35 7 196 104 400 48 72 385 257), lower := (rows 35 7 196 104 400 48 72 128 256), losses := [] }

theorem u768 : Upper (D 9) (R 9) [34,5,192,96,384,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b768 [(5,4),(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b769 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 135, targets := 256 },{ cop := 4, region := 68, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(2,8)], upper := (rows 35 7 196 104 400 48 320 137 265), lower := (rows 35 7 196 104 400 48 320 128 256), losses := [] }

theorem u769 : Upper (D 9) (R 9) [34,5,192,96,384,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b769 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b770 : PairBound 9 := { available := 24, camps := [{ cop := 6, region := 444, targets := 1 },{ cop := 0, region := 72, targets := 384 }], pairs := [(2,0),(3,0),(3,7),(3,8),(4,0)], upper := (rows 35 7 196 104 400 288 65 152 280), lower := (rows 35 7 196 104 400 288 65 128 256), losses := [] }

theorem u770 : Upper (D 9) (R 9) [34,5,192,96,384,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b770 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b771 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 307, targets := 64 },{ cop := 5, region := 72, targets := 1 }], pairs := [(0,6),(1,6),(3,0),(4,6)], upper := (rows 35 7 196 104 400 288 72 145 273), lower := (rows 35 7 196 104 400 288 72 128 256), losses := [] }

theorem u771 : Upper (D 9) (R 9) [34,5,192,96,384,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b771 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b772 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 299, targets := 128 },{ cop := 3, region := 135, targets := 256 }], pairs := [(0,7),(0,8),(1,7),(3,7)], upper := (rows 35 7 196 104 400 288 80 137 265), lower := (rows 35 7 196 104 400 288 80 128 256), losses := [] }

theorem u772 : Upper (D 9) (R 9) [34,5,192,96,384,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b772 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b773 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 299, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 7 196 265 336 40 80 160 416), lower := (rows 35 7 196 265 336 40 80 128 256), losses := [] }

theorem u773 : Upper (D 9) (R 9) [34,5,192,257,320,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b773 [(5,3),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b774 : PairBound 9 := { available := 144, camps := [{ cop := 6, region := 404, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 35 7 196 265 336 40 96 144 400), lower := (rows 35 7 196 265 336 40 96 128 256), losses := [] }

theorem u774 : Upper (D 9) (R 9) [34,5,192,257,320,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b774 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b775 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 35 7 196 265 336 40 192 176 304), lower := (rows 35 7 196 265 336 40 192 128 256), losses := [] }

theorem u775 : Upper (D 9) (R 9) [34,5,192,257,320,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b775 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b776 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 167, targets := 256 }], pairs := [(0,8),(1,8),(2,8)], upper := (rows 35 7 196 265 336 48 72 160 416), lower := (rows 35 7 196 265 336 48 72 128 256), losses := [] }

theorem u776 : Upper (D 9) (R 9) [34,5,192,257,320,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b776 [(5,4),(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b777 : PairBound 9 := { available := 136, camps := [{ cop := 0, region := 392, targets := 96 },{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0),(3,5),(3,6),(4,0)], upper := (rows 35 7 196 265 336 48 96 136 392), lower := (rows 35 7 196 265 336 48 96 128 256), losses := [] }

theorem u777 : Upper (D 9) (R 9) [34,5,192,257,320,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b777 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b778 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 35 7 196 265 336 48 192 168 296), lower := (rows 35 7 196 265 336 48 192 128 256), losses := [] }

theorem u778 : Upper (D 9) (R 9) [34,5,192,257,320,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b778 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b779 : PairBound 9 := { available := 48, camps := [{ cop := 6, region := 444, targets := 1 },{ cop := 0, region := 400, targets := 64 }], pairs := [(2,0),(3,0),(4,0),(4,6)], upper := (rows 35 7 196 328 400 40 65 176 304), lower := (rows 35 7 196 328 400 40 65 128 256), losses := [] }

theorem u779 : Upper (D 9) (R 9) [34,5,192,320,384,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b779 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u779
end Delivery.IrregularNine14.P09

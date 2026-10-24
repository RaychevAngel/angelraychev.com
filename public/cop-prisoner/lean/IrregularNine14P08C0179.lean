import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0051
import IrregularNine14P08C0052

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b10740 : PairBound 9 := { available := 296, camps := [{ cop := 3, region := 422, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 133 25 208 296 360 424 296), lower := (rows 67 38 133 25 208 32 64 128 256), losses := [] }

theorem u10740 : Upper (D 8) (R 8) [66,36,129,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10740 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10741 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 98, targets := 1 }], pairs := [(1,0)], upper := (rows 67 38 133 25 280 224 224 224 480), lower := (rows 67 38 133 25 280 32 64 128 256), losses := [] }

theorem u10741 : Upper (D 8) (R 8) [66,36,129,17,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10741 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10742 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 496, targets := 1 }], pairs := [(4,0)], upper := (rows 67 38 133 25 304 232 232 232 488), lower := (rows 67 38 133 25 304 32 64 128 256), losses := [] }

theorem u10742 : Upper (D 8) (R 8) [66,36,129,17,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10742 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10743 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 166, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 133 25 336 168 232 168 424), lower := (rows 67 38 133 25 336 32 64 128 256), losses := [] }

theorem u10743 : Upper (D 8) (R 8) [66,36,129,17,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10743 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10744 : PairBound 9 := { available := 104, camps := [{ cop := 3, region := 496, targets := 1 }], pairs := [(4,0)], upper := (rows 67 38 133 25 400 104 104 232 360), lower := (rows 67 38 133 25 400 32 64 128 256), losses := [] }

theorem u10744 : Upper (D 8) (R 8) [66,36,129,17,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10744 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10745 : PairBound 9 := { available := 464, camps := [{ cop := 3, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 67 38 133 41 56 496 464 464 464), lower := (rows 67 38 133 41 56 32 64 128 256), losses := [] }

theorem u10745 : Upper (D 8) (R 8) [66,36,129,33,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10745 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10746 : PairBound 9 := { available := 432, camps := [{ cop := 3, region := 464, targets := 1 }], pairs := [(4,0)], upper := (rows 67 38 133 41 88 432 496 432 432), lower := (rows 67 38 133 41 88 32 64 128 256), losses := [] }

theorem u10746 : Upper (D 8) (R 8) [66,36,129,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10746 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10747 : PairBound 9 := { available := 408, camps := [{ cop := 3, region := 464, targets := 1 }], pairs := [(4,0)], upper := (rows 67 38 133 41 112 440 472 408 408), lower := (rows 67 38 133 41 112 32 64 128 256), losses := [] }

theorem u10747 : Upper (D 8) (R 8) [66,36,129,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10747 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10748 : PairBound 9 := { available := 368, camps := [{ cop := 3, region := 464, targets := 1 }], pairs := [(4,0)], upper := (rows 67 38 133 41 152 368 368 496 368), lower := (rows 67 38 133 41 152 32 64 128 256), losses := [] }

theorem u10748 : Upper (D 8) (R 8) [66,36,129,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10748 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10749 : PairBound 9 := { available := 344, camps := [{ cop := 3, region := 464, targets := 1 }], pairs := [(4,0)], upper := (rows 67 38 133 41 176 376 344 472 344), lower := (rows 67 38 133 41 176 32 64 128 256), losses := [] }

theorem u10749 : Upper (D 8) (R 8) [66,36,129,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10749 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10750 : PairBound 9 := { available := 312, camps := [{ cop := 3, region := 464, targets := 1 }], pairs := [(4,0)], upper := (rows 67 38 133 41 208 312 376 440 312), lower := (rows 67 38 133 41 208 32 64 128 256), losses := [] }

theorem u10750 : Upper (D 8) (R 8) [66,36,129,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10750 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10751 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 464, targets := 1 }], pairs := [(4,0)], upper := (rows 67 38 133 41 280 240 240 240 496), lower := (rows 67 38 133 41 280 32 64 128 256), losses := [] }

theorem u10751 : Upper (D 8) (R 8) [66,36,129,33,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10751 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10752 : PairBound 9 := { available := 216, camps := [{ cop := 3, region := 464, targets := 1 }], pairs := [(4,0)], upper := (rows 67 38 133 41 304 248 216 216 472), lower := (rows 67 38 133 41 304 32 64 128 256), losses := [] }

theorem u10752 : Upper (D 8) (R 8) [66,36,129,33,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10752 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10753 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 464, targets := 1 }], pairs := [(4,0)], upper := (rows 67 38 133 41 336 184 248 184 440), lower := (rows 67 38 133 41 336 32 64 128 256), losses := [] }

theorem u10753 : Upper (D 8) (R 8) [66,36,129,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10753 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10754 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 464, targets := 1 }], pairs := [(4,0)], upper := (rows 67 38 133 41 400 120 120 248 376), lower := (rows 67 38 133 41 400 32 64 128 256), losses := [] }

theorem u10754 : Upper (D 8) (R 8) [66,36,129,33,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10754 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10755 : PairBound 9 := { available := 449, camps := [{ cop := 1, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 133 56 56 481 449 449 449), lower := (rows 67 38 133 56 56 32 64 128 256), losses := [] }

theorem u10755 : Upper (D 8) (R 8) [66,36,129,48,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10755 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10756 : PairBound 9 := { available := 424, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 133 56 81 424 488 424 424), lower := (rows 67 38 133 56 81 32 64 128 256), losses := [] }

theorem u10756 : Upper (D 8) (R 8) [66,36,129,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10756 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10757 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 422, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 133 56 88 417 481 417 417), lower := (rows 67 38 133 56 88 32 64 128 256), losses := [] }

theorem u10757 : Upper (D 8) (R 8) [66,36,129,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10757 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10758 : PairBound 9 := { available := 393, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 133 56 112 425 457 393 393), lower := (rows 67 38 133 56 112 32 64 128 256), losses := [] }

theorem u10758 : Upper (D 8) (R 8) [66,36,129,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10758 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10759 : PairBound 9 := { available := 360, camps := [{ cop := 2, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 67 38 133 56 145 360 360 488 360), lower := (rows 67 38 133 56 145 32 64 128 256), losses := [] }

theorem u10759 : Upper (D 8) (R 8) [66,36,129,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10759 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10760 : PairBound 9 := { available := 353, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 133 56 152 353 353 481 353), lower := (rows 67 38 133 56 152 32 64 128 256), losses := [] }

theorem u10760 : Upper (D 8) (R 8) [66,36,129,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10760 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10761 : PairBound 9 := { available := 329, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 133 56 176 361 329 457 329), lower := (rows 67 38 133 56 176 32 64 128 256), losses := [] }

theorem u10761 : Upper (D 8) (R 8) [66,36,129,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10761 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10762 : Route 9 := (fun mask => (mask,id))

def c10762 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u10762 : Upper (D 8) (R 8) [66,36,129,48,192] 13 := by
  apply FastRouting.sound _ _ [66,36,129,48,192] 13 (by decide) (choices 1) [1,8,256] r10762 c10762
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3075
  · exact u3076
  · exact u3077

def b10763 : PairBound 9 := { available := 232, camps := [{ cop := 4, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 133 56 273 232 232 232 488), lower := (rows 67 38 133 56 273 32 64 128 256), losses := [] }

theorem u10763 : Upper (D 8) (R 8) [66,36,129,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10763 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10764 : Route 9 := (fun mask => (mask,id))

def c10764 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u10764 : Upper (D 8) (R 8) [66,36,129,48,264] 13 := by
  apply FastRouting.sound _ _ [66,36,129,48,264] 13 (by decide) (choices 1) [1,64,128] r10764 c10764
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3078
  · exact u3079
  · exact u3080

def b10765 : PairBound 9 := { available := 201, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 133 56 304 233 201 201 457), lower := (rows 67 38 133 56 304 32 64 128 256), losses := [] }

theorem u10765 : Upper (D 8) (R 8) [66,36,129,48,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10765 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10766 : Route 9 := (fun mask => (mask,id))

def c10766 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10766 : Upper (D 8) (R 8) [66,36,129,48,320] 13 := by
  apply FastRouting.sound _ _ [66,36,129,48,320] 13 (by decide) (choices 1) [1,8,128] r10766 c10766
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3081
  · exact u3082
  · exact u3083

def r10767 : Route 9 := (fun mask => (mask,id))

def c10767 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10767 : Upper (D 8) (R 8) [66,36,129,48,384] 13 := by
  apply FastRouting.sound _ _ [66,36,129,48,384] 13 (by decide) (choices 1) [1,8,64] r10767 c10767
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3084
  · exact u3085
  · exact u3086

def b10768 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 133 73 152 304 368 432 304), lower := (rows 67 38 133 73 152 32 64 128 256), losses := [] }

theorem u10768 : Upper (D 8) (R 8) [66,36,129,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10768 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10769 : PairBound 9 := { available := 312, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 133 73 176 312 376 440 312), lower := (rows 67 38 133 73 176 32 64 128 256), losses := [] }

theorem u10769 : Upper (D 8) (R 8) [66,36,129,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10769 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10770 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 133 73 280 176 240 176 432), lower := (rows 67 38 133 73 280 32 64 128 256), losses := [] }

theorem u10770 : Upper (D 8) (R 8) [66,36,129,65,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10770 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10771 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 133 73 304 184 248 184 440), lower := (rows 67 38 133 73 304 32 64 128 256), losses := [] }

theorem u10771 : Upper (D 8) (R 8) [66,36,129,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10771 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10772 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 133 73 400 56 120 184 312), lower := (rows 67 38 133 73 400 32 64 128 256), losses := [] }

theorem u10772 : Upper (D 8) (R 8) [66,36,129,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10772 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10773 : PairBound 9 := { available := 296, camps := [{ cop := 2, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 67 38 133 88 145 296 360 424 296), lower := (rows 67 38 133 88 145 32 64 128 256), losses := [] }

theorem u10773 : Upper (D 8) (R 8) [66,36,129,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10773 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10774 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 422, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 133 88 152 289 353 417 289), lower := (rows 67 38 133 88 152 32 64 128 256), losses := [] }

theorem u10774 : Upper (D 8) (R 8) [66,36,129,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10774 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10775 : Route 9 := (fun mask => (mask,id))

def c10775 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u10775 : Upper (D 8) (R 8) [66,36,129,80,160] 13 := by
  apply FastRouting.sound _ _ [66,36,129,80,160] 13 (by decide) (choices 1) [1,8,256] r10775 c10775
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3087
  · exact u3088
  · exact u3089

def b10776 : PairBound 9 := { available := 168, camps := [{ cop := 4, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 133 88 273 168 232 168 424), lower := (rows 67 38 133 88 273 32 64 128 256), losses := [] }

theorem u10776 : Upper (D 8) (R 8) [66,36,129,80,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10776 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10777 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 166, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 133 88 280 161 225 161 417), lower := (rows 67 38 133 88 280 32 64 128 256), losses := [] }

theorem u10777 : Upper (D 8) (R 8) [66,36,129,80,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10777 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10778 : Route 9 := (fun mask => (mask,id))

def c10778 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10778 : Upper (D 8) (R 8) [66,36,129,80,288] 13 := by
  apply FastRouting.sound _ _ [66,36,129,80,288] 13 (by decide) (choices 1) [1,8,128] r10778 c10778
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3090
  · exact u3091
  · exact u3092

def r10779 : Route 9 := (fun mask => (mask,id))

def c10779 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10779 : Upper (D 8) (R 8) [66,36,129,80,384] 13 := by
  apply FastRouting.sound _ _ [66,36,129,80,384] 13 (by decide) (choices 1) [1,8] r10779 c10779
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3093
  · exact u3094

def b10780 : PairBound 9 := { available := 312, camps := [{ cop := 2, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 67 38 133 104 145 312 376 440 312), lower := (rows 67 38 133 104 145 32 64 128 256), losses := [] }

theorem u10780 : Upper (D 8) (R 8) [66,36,129,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10780 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10781 : Route 9 := (fun mask => (mask,id))

def c10781 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u10781 : Upper (D 8) (R 8) [66,36,129,96,136] 13 := by
  apply FastRouting.sound _ _ [66,36,129,96,136] 13 (by decide) (choices 1) [1,16,256] r10781 c10781
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3095
  · exact u3096
  · exact u3097

def r10782 : Route 9 := (fun mask => (mask,id))

def c10782 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u10782 : Upper (D 8) (R 8) [66,36,129,96,160] 13 := by
  apply FastRouting.sound _ _ [66,36,129,96,160] 13 (by decide) (choices 1) [1,8,16,256] r10782 c10782
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3098
  · exact u3099
  · exact u3100
  · exact u3101

def b10783 : PairBound 9 := { available := 184, camps := [{ cop := 4, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 133 104 273 184 248 184 440), lower := (rows 67 38 133 104 273 32 64 128 256), losses := [] }

theorem u10783 : Upper (D 8) (R 8) [66,36,129,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10783 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10784 : Route 9 := (fun mask => (mask,id))

def c10784 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10784 : Upper (D 8) (R 8) [66,36,129,96,264] 13 := by
  apply FastRouting.sound _ _ [66,36,129,96,264] 13 (by decide) (choices 1) [1,16,128] r10784 c10784
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3102
  · exact u3103
  · exact u3104

def r10785 : Route 9 := (fun mask => (mask,id))

def c10785 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10785 : Upper (D 8) (R 8) [66,36,129,96,288] 13 := by
  apply FastRouting.sound _ _ [66,36,129,96,288] 13 (by decide) (choices 1) [1,8,16,128] r10785 c10785
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3105
  · exact u3106
  · exact u3107
  · exact u3108

def r10786 : Route 9 := (fun mask => (mask,id))

def c10786 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10786 : Upper (D 8) (R 8) [66,36,129,96,384] 13 := by
  apply FastRouting.sound _ _ [66,36,129,96,384] 13 (by decide) (choices 1) [1,8,16] r10786 c10786
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3109
  · exact u3110
  · exact u3111

def b10787 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 67 38 133 137 280 112 112 240 368), lower := (rows 67 38 133 137 280 32 64 128 256), losses := [] }

theorem u10787 : Upper (D 8) (R 8) [66,36,129,129,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10787 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10788 : PairBound 9 := { available := 120, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 67 38 133 137 304 120 120 248 376), lower := (rows 67 38 133 137 304 32 64 128 256), losses := [] }

theorem u10788 : Upper (D 8) (R 8) [66,36,129,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10788 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10789 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 67 38 133 137 336 56 120 184 312), lower := (rows 67 38 133 137 336 32 64 128 256), losses := [] }

theorem u10789 : Upper (D 8) (R 8) [66,36,129,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10789 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10790 : PairBound 9 := { available := 104, camps := [{ cop := 4, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 133 152 273 104 104 232 360), lower := (rows 67 38 133 152 273 32 64 128 256), losses := [] }

theorem u10790 : Upper (D 8) (R 8) [66,36,129,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10790 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10791 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 133 152 280 97 97 225 353), lower := (rows 67 38 133 152 280 32 64 128 256), losses := [] }

theorem u10791 : Upper (D 8) (R 8) [66,36,129,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10791 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10792 : Route 9 := (fun mask => (mask,id))

def c10792 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10792 : Upper (D 8) (R 8) [66,36,129,144,288] 13 := by
  apply FastRouting.sound _ _ [66,36,129,144,288] 13 (by decide) (choices 1) [1,8,64] r10792 c10792
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3112
  · exact u3113
  · exact u3114

def r10793 : Route 9 := (fun mask => (mask,id))

def c10793 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10793 : Upper (D 8) (R 8) [66,36,129,144,320] 13 := by
  apply FastRouting.sound _ _ [66,36,129,144,320] 13 (by decide) (choices 1) [1,8] r10793 c10793
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3115
  · exact u3116

def b10794 : PairBound 9 := { available := 120, camps := [{ cop := 4, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 133 168 273 120 120 248 376), lower := (rows 67 38 133 168 273 32 64 128 256), losses := [] }

theorem u10794 : Upper (D 8) (R 8) [66,36,129,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10794 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10795 : Route 9 := (fun mask => (mask,id))

def c10795 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10795 : Upper (D 8) (R 8) [66,36,129,160,264] 13 := by
  apply FastRouting.sound _ _ [66,36,129,160,264] 13 (by decide) (choices 1) [1,16,64] r10795 c10795
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3117
  · exact u3118
  · exact u3119

def r10796 : Route 9 := (fun mask => (mask,id))

def c10796 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10796 : Upper (D 8) (R 8) [66,36,129,160,288] 13 := by
  apply FastRouting.sound _ _ [66,36,129,160,288] 13 (by decide) (choices 1) [1,8,16,64] r10796 c10796
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3120
  · exact u3121
  · exact u3122
  · exact u3123

def r10797 : Route 9 := (fun mask => (mask,id))

def c10797 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10797 : Upper (D 8) (R 8) [66,36,129,160,320] 13 := by
  apply FastRouting.sound _ _ [66,36,129,160,320] 13 (by decide) (choices 1) [1,8,16] r10797 c10797
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3124
  · exact u3125
  · exact u3126

def b10798 : PairBound 9 := { available := 56, camps := [{ cop := 4, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 133 200 273 56 120 184 312), lower := (rows 67 38 133 200 273 32 64 128 256), losses := [] }

theorem u10798 : Upper (D 8) (R 8) [66,36,129,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10798 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10799 : Route 9 := (fun mask => (mask,id))

def c10799 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10799 : Upper (D 8) (R 8) [66,36,129,192,264] 13 := by
  apply FastRouting.sound _ _ [66,36,129,192,264] 13 (by decide) (choices 1) [1,16] r10799 c10799
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3127
  · exact u3128

#print axioms u10799
end Delivery.IrregularNine14.P08

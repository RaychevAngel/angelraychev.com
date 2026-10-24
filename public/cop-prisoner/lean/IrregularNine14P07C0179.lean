import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0013

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b10740 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 402, targets := 32 },{ cop := 6, region := 177, targets := 2 }], pairs := [(0,1),(1,5),(4,1),(4,5)], upper := (rows 97 259 14 44 145 160 66 208 336), lower := (rows 97 259 14 44 145 160 66 128 256), losses := [] }

theorem u10740 : Upper (D 7) (R 7) [96,257,10,36,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10740 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10741 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 270, targets := 128 }], pairs := [(1,7),(2,7),(3,7)], upper := (rows 97 259 14 44 145 160 80 194 322), lower := (rows 97 259 14 44 145 160 80 128 256), losses := [] }

theorem u10741 : Upper (D 7) (R 7) [96,257,10,36,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10741 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10742 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 402, targets := 32 },{ cop := 3, region := 65, targets := 130 }], pairs := [(0,1),(0,7),(1,5),(4,5)], upper := (rows 97 259 14 44 208 160 65 146 274), lower := (rows 97 259 14 44 208 160 65 128 256), losses := [] }

theorem u10742 : Upper (D 7) (R 7) [96,257,10,36,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10742 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10743 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 402, targets := 32 },{ cop := 6, region := 177, targets := 2 }], pairs := [(0,1),(1,5),(4,1),(4,5)], upper := (rows 97 259 14 44 208 160 66 145 273), lower := (rows 97 259 14 44 208 160 66 128 256), losses := [] }

theorem u10743 : Upper (D 7) (R 7) [96,257,10,36,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10743 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10744 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 270, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 259 14 44 208 160 80 131 259), lower := (rows 97 259 14 44 208 160 80 128 256), losses := [] }

theorem u10744 : Upper (D 7) (R 7) [96,257,10,36,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10744 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10745 : PairBound 9 := { available := 132, camps := [{ cop := 4, region := 172, targets := 65 }], pairs := [(2,0),(2,6),(3,0),(3,6)], upper := (rows 97 259 14 56 82 160 65 132 388), lower := (rows 97 259 14 56 82 160 65 128 256), losses := [] }

theorem u10745 : Upper (D 7) (R 7) [96,257,10,48,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10745 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10746 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 80, targets := 161 }], pairs := [(4,0),(4,5),(4,7)], upper := (rows 97 259 14 56 82 160 68 129 385), lower := (rows 97 259 14 56 82 160 68 128 256), losses := [] }

theorem u10746 : Upper (D 7) (R 7) [96,257,10,48,66,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10746 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10747 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 286, targets := 128 }], pairs := [(1,7),(2,7),(3,7),(4,7)], upper := (rows 97 259 14 56 82 160 192 133 261), lower := (rows 97 259 14 56 82 160 192 128 256), losses := [] }

theorem u10747 : Upper (D 7) (R 7) [96,257,10,48,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10747 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10748 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 152, targets := 2 },{ cop := 0, region := 386, targets := 32 }], pairs := [(1,5),(3,1),(4,1)], upper := (rows 97 259 14 56 145 34 68 192 448), lower := (rows 97 259 14 56 145 34 68 128 256), losses := [] }

theorem u10748 : Upper (D 7) (R 7) [96,257,10,48,129,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10748 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r10749 : Route 9 := (fun mask => (mask,id))

def c10749 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u10749 : Upper (D 7) (R 7) [96,257,10,48,129,2,128] 13 := by
  apply FastRouting.sound _ _ [96,257,10,48,129,2,128] 13 (by decide) (choices 1) [4,64] r10749 c10749
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u799
  · exact u800

def b10750 : PairBound 9 := { available := 132, camps := [{ cop := 3, region := 65, targets := 130 },{ cop := 8, region := 99, targets := 128 }], pairs := [(0,1),(0,7),(1,7),(2,0)], upper := (rows 97 259 14 56 208 34 65 132 388), lower := (rows 97 259 14 56 208 34 65 128 256), losses := [{ target := 0, region := (rows 0 2 38 11 81 38 64 175 303), good := (rows 508 446 430 444 208 430 472 128 256) }] }

theorem u10750 : Upper (D 7) (R 7) [96,257,10,48,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10750 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10751 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 152, targets := 2 },{ cop := 0, region := 386, targets := 32 }], pairs := [(1,5),(3,1),(4,1)], upper := (rows 97 259 14 56 208 34 68 129 385), lower := (rows 97 259 14 56 208 34 68 128 256), losses := [] }

theorem u10751 : Upper (D 7) (R 7) [96,257,10,48,192,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10751 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10752 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 97 259 14 56 208 34 192 133 261), lower := (rows 97 259 14 56 208 34 192 128 256), losses := [] }

theorem u10752 : Upper (D 7) (R 7) [96,257,10,48,192,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10752 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10753 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 274, targets := 128 },{ cop := 2, region := 240, targets := 1 }], pairs := [(1,7),(4,0),(4,7)], upper := (rows 97 259 14 137 50 160 68 208 336), lower := (rows 97 259 14 137 50 160 68 128 256), losses := [] }

theorem u10753 : Upper (D 7) (R 7) [96,257,10,129,34,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10753 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10754 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 259 14 137 50 160 80 196 324), lower := (rows 97 259 14 137 50 160 80 128 256), losses := [] }

theorem u10754 : Upper (D 7) (R 7) [96,257,10,129,34,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10754 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10755 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 136, targets := 2 },{ cop := 0, region := 258, targets := 128 }], pairs := [(1,7),(3,1)], upper := (rows 97 259 14 137 146 36 80 224 352), lower := (rows 97 259 14 137 146 36 80 128 256), losses := [] }

theorem u10755 : Upper (D 7) (R 7) [96,257,10,129,130,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10755 [(5,2),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10756 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 259 14 137 146 36 96 208 336), lower := (rows 97 259 14 137 146 36 96 128 256), losses := [] }

theorem u10756 : Upper (D 7) (R 7) [96,257,10,129,130,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10756 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10757 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 259 14 137 146 48 96 196 324), lower := (rows 97 259 14 137 146 48 96 128 256), losses := [] }

theorem u10757 : Upper (D 7) (R 7) [96,257,10,129,130,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10757 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10758 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 355, targets := 128 },{ cop := 0, region := 136, targets := 2 }], pairs := [(0,7),(1,7),(3,1)], upper := (rows 97 259 14 137 148 34 80 224 352), lower := (rows 97 259 14 137 148 34 80 128 256), losses := [] }

theorem u10758 : Upper (D 7) (R 7) [96,257,10,129,132,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10758 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10759 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5),(4,5)], upper := (rows 97 259 14 137 148 34 96 208 336), lower := (rows 97 259 14 137 148 34 96 128 256), losses := [] }

theorem u10759 : Upper (D 7) (R 7) [96,257,10,129,132,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10759 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10760 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 152, targets := 2 },{ cop := 0, region := 144, targets := 1 }], pairs := [(3,1),(4,0),(4,1)], upper := (rows 97 259 14 137 176 34 68 208 336), lower := (rows 97 259 14 137 176 34 68 128 256), losses := [] }

theorem u10760 : Upper (D 7) (R 7) [96,257,10,129,160,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10760 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10761 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 259 14 137 176 34 80 196 324), lower := (rows 97 259 14 137 176 34 80 128 256), losses := [] }

theorem u10761 : Upper (D 7) (R 7) [96,257,10,129,160,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10761 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10762 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 355, targets := 128 },{ cop := 5, region := 209, targets := 2 }], pairs := [(0,1),(0,7),(1,7)], upper := (rows 97 259 14 140 145 34 80 224 352), lower := (rows 97 259 14 140 145 34 80 128 256), losses := [] }

theorem u10762 : Upper (D 7) (R 7) [96,257,10,132,129,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10762 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10763 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 259 14 140 145 48 96 194 322), lower := (rows 97 259 14 140 145 48 96 128 256), losses := [] }

theorem u10763 : Upper (D 7) (R 7) [96,257,10,132,129,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10763 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10764 : PairBound 9 := { available := 80, camps := [{ cop := 4, region := 323, targets := 128 },{ cop := 6, region := 177, targets := 2 }], pairs := [(0,1),(0,7),(1,7),(4,1)], upper := (rows 97 259 14 140 176 33 66 208 336), lower := (rows 97 259 14 140 176 33 66 128 256), losses := [] }

theorem u10764 : Upper (D 7) (R 7) [96,257,10,132,160,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10764 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10765 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 259 14 140 176 33 80 194 322), lower := (rows 97 259 14 140 176 33 80 128 256), losses := [] }

theorem u10765 : Upper (D 7) (R 7) [96,257,10,132,160,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10765 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10766 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 65, targets := 130 }], pairs := [(0,1),(0,7),(2,5),(4,0)], upper := (rows 97 259 14 152 50 160 65 196 324), lower := (rows 97 259 14 152 50 160 65 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 168 64 128 256), good := (rows 96 258 62 184 50 160 64 160 256) },{ target := 5, region := (rows 1 2 20 24 16 0 67 148 276), good := (rows 65 323 462 412 478 128 65 128 256) }] }

theorem u10766 : Upper (D 7) (R 7) [96,257,10,144,34,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10766 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10767 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 274, targets := 128 },{ cop := 0, region := 258, targets := 32 }], pairs := [(1,5),(1,7),(4,7)], upper := (rows 97 259 14 152 50 160 68 193 321), lower := (rows 97 259 14 152 50 160 68 128 256), losses := [] }

theorem u10767 : Upper (D 7) (R 7) [96,257,10,144,34,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10767 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10768 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 172, targets := 65 }], pairs := [(2,0),(2,6),(3,0)], upper := (rows 97 259 14 168 82 36 65 144 400), lower := (rows 97 259 14 168 82 36 65 128 256), losses := [] }

theorem u10768 : Upper (D 7) (R 7) [96,257,10,160,66,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10768 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10769 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 259 14 168 82 36 80 129 385), lower := (rows 97 259 14 168 82 36 80 128 256), losses := [] }

theorem u10769 : Upper (D 7) (R 7) [96,257,10,160,66,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10769 [(5,2),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10770 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 274, targets := 32 },{ cop := 0, region := 274, targets := 128 }], pairs := [(1,5),(1,7),(4,5)], upper := (rows 97 259 14 168 82 36 192 145 273), lower := (rows 97 259 14 168 82 36 192 128 256), losses := [] }

theorem u10770 : Upper (D 7) (R 7) [96,257,10,160,66,4,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10770 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10771 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 113, targets := 128 },{ cop := 3, region := 65, targets := 2 },{ cop := 8, region := 99, targets := 128 }], pairs := [(0,1),(0,7),(1,7),(4,7)], upper := (rows 97 259 14 168 84 34 65 144 400), lower := (rows 97 259 14 168 84 34 65 128 256), losses := [] }

theorem u10771 : Upper (D 7) (R 7) [96,257,10,160,68,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10771 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10772 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 259 14 168 84 34 80 129 385), lower := (rows 97 259 14 168 84 34 80 128 256), losses := [] }

theorem u10772 : Upper (D 7) (R 7) [96,257,10,160,68,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10772 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10773 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 291, targets := 128 },{ cop := 3, region := 65, targets := 2 }], pairs := [(0,1),(0,7),(1,7),(4,0)], upper := (rows 97 259 14 168 84 34 192 145 273), lower := (rows 97 259 14 168 84 34 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 38 200 128 256), good := (rows 96 290 126 232 116 34 192 192 256) }] }

theorem u10773 : Upper (D 7) (R 7) [96,257,10,160,68,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10773 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10774 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 152, targets := 2 },{ cop := 0, region := 402, targets := 32 }], pairs := [(1,5),(3,1),(4,1)], upper := (rows 97 259 14 168 145 34 68 208 336), lower := (rows 97 259 14 168 145 34 68 128 256), losses := [] }

theorem u10774 : Upper (D 7) (R 7) [96,257,10,160,129,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10774 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10775 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 81, targets := 2 }], pairs := [(0,1),(2,0),(4,1)], upper := (rows 97 259 14 168 145 34 80 196 324), lower := (rows 97 259 14 168 145 34 80 128 256), losses := [{ target := 0, region := (rows 0 2 38 11 16 38 80 129 257), good := (rows 492 430 46 172 472 46 80 128 256) }] }

theorem u10775 : Upper (D 7) (R 7) [96,257,10,160,129,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10775 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10776 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 81, targets := 2 },{ cop := 8, region := 99, targets := 128 }], pairs := [(0,1),(0,7),(1,7),(4,1)], upper := (rows 97 259 14 168 208 34 65 148 276), lower := (rows 97 259 14 168 208 34 65 128 256), losses := [] }

theorem u10776 : Upper (D 7) (R 7) [96,257,10,160,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10776 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10777 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 152, targets := 2 },{ cop := 0, region := 402, targets := 32 }], pairs := [(1,5),(3,1),(4,1)], upper := (rows 97 259 14 168 208 34 68 145 273), lower := (rows 97 259 14 168 208 34 68 128 256), losses := [] }

theorem u10777 : Upper (D 7) (R 7) [96,257,10,160,192,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10777 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10778 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 259 14 168 208 34 80 133 261), lower := (rows 97 259 14 168 208 34 80 128 256), losses := [] }

theorem u10778 : Upper (D 7) (R 7) [96,257,10,160,192,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10778 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10779 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 402, targets := 32 },{ cop := 2, region := 97, targets := 2 }], pairs := [(0,1),(1,5),(4,5)], upper := (rows 97 259 14 168 208 36 65 146 274), lower := (rows 97 259 14 168 208 36 65 128 256), losses := [] }

theorem u10779 : Upper (D 7) (R 7) [96,257,10,160,192,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10779 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10780 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 152, targets := 2 },{ cop := 0, region := 402, targets := 32 }], pairs := [(1,5),(3,1),(4,1)], upper := (rows 97 259 14 168 208 36 66 145 273), lower := (rows 97 259 14 168 208 36 66 128 256), losses := [] }

theorem u10780 : Upper (D 7) (R 7) [96,257,10,160,192,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10780 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10781 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 259 14 168 208 36 80 131 259), lower := (rows 97 259 14 168 208 36 80 128 256), losses := [] }

theorem u10781 : Upper (D 7) (R 7) [96,257,10,160,192,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10781 [(5,2),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10782 : PairBound 9 := { available := 132, camps := [{ cop := 3, region := 212, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 97 259 28 42 82 33 192 132 388), lower := (rows 97 259 28 42 82 33 192 128 256), losses := [] }

theorem u10782 : Upper (D 7) (R 7) [96,257,24,34,66,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10782 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10783 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 44, targets := 65 }], pairs := [(2,0),(2,6),(3,0)], upper := (rows 97 259 28 42 82 36 192 129 385), lower := (rows 97 259 28 42 82 36 192 128 256), losses := [] }

theorem u10783 : Upper (D 7) (R 7) [96,257,24,34,66,4,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10783 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10784 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 286, targets := 128 }], pairs := [(1,7),(2,7),(3,7),(4,7)], upper := (rows 97 259 28 42 82 160 192 133 261), lower := (rows 97 259 28 42 82 160 192 128 256), losses := [] }

theorem u10784 : Upper (D 7) (R 7) [96,257,24,34,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10784 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r10785 : Route 9 := (fun mask => (mask,id))

def c10785 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u10785 : Upper (D 7) (R 7) [96,257,24,34,129,128,2] 13 := by
  apply FastRouting.sound _ _ [96,257,24,34,129,128,2] 13 (by decide) (choices 1) [4,64] r10785 c10785
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u801
  · exact u802

def b10786 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 402, targets := 32 },{ cop := 0, region := 258, targets := 128 }], pairs := [(1,5),(1,7),(4,5)], upper := (rows 97 259 28 42 145 160 68 194 322), lower := (rows 97 259 28 42 145 160 68 128 256), losses := [] }

theorem u10786 : Upper (D 7) (R 7) [96,257,24,34,129,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10786 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10787 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 65, targets := 130 },{ cop := 5, region := 81, targets := 2 }], pairs := [(0,1),(0,7),(2,1),(4,1)], upper := (rows 97 259 28 42 208 160 65 134 262), lower := (rows 97 259 28 42 208 160 65 128 256), losses := [{ target := 1, region := (rows 189 0 12 8 176 176 255 128 256), good := (rows 113 321 125 125 241 241 65 241 256) }] }

theorem u10787 : Upper (D 7) (R 7) [96,257,24,34,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10787 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r10788 : Route 9 := (fun mask => (mask,id))

def c10788 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10788 : Upper (D 7) (R 7) [96,257,24,34,192,128,2] 13 := by
  apply FastRouting.sound _ _ [96,257,24,34,192,128,2] 13 (by decide) (choices 1) [1,4] r10788 c10788
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u803
  · exact u804

def b10789 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 402, targets := 32 },{ cop := 0, region := 258, targets := 64 }], pairs := [(1,5),(1,6),(4,5)], upper := (rows 97 259 28 42 208 160 68 131 259), lower := (rows 97 259 28 42 208 160 68 128 256), losses := [] }

theorem u10789 : Upper (D 7) (R 7) [96,257,24,34,192,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10789 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10790 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 156, targets := 2 },{ cop := 0, region := 386, targets := 32 }], pairs := [(1,5),(2,1),(3,1),(4,1)], upper := (rows 97 259 28 44 145 34 66 192 448), lower := (rows 97 259 28 44 145 34 66 128 256), losses := [] }

theorem u10790 : Upper (D 7) (R 7) [96,257,24,36,129,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10790 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10791 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 402, targets := 32 },{ cop := 6, region := 291, targets := 128 }], pairs := [(0,7),(1,5),(1,7),(4,5)], upper := (rows 97 259 28 44 145 34 192 194 322), lower := (rows 97 259 28 44 145 34 192 128 256), losses := [] }

theorem u10791 : Upper (D 7) (R 7) [96,257,24,36,129,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10791 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10792 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 0, region := 136, targets := 2 }], pairs := [(0,7),(1,7),(3,1)], upper := (rows 97 259 28 137 146 34 68 224 352), lower := (rows 97 259 28 137 146 34 68 128 256), losses := [] }

theorem u10792 : Upper (D 7) (R 7) [96,257,24,129,130,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10792 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10793 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5),(4,5)], upper := (rows 97 259 28 137 146 34 96 196 324), lower := (rows 97 259 28 137 146 34 96 128 256), losses := [] }

theorem u10793 : Upper (D 7) (R 7) [96,257,24,129,130,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10793 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10794 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 259 28 137 146 36 96 194 322), lower := (rows 97 259 28 137 146 36 96 128 256), losses := [] }

theorem u10794 : Upper (D 7) (R 7) [96,257,24,129,130,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10794 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10795 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 156, targets := 2 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 97 259 28 137 176 34 66 196 324), lower := (rows 97 259 28 137 176 34 66 128 256), losses := [] }

theorem u10795 : Upper (D 7) (R 7) [96,257,24,129,160,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10795 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10796 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 77, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 97 259 28 137 176 34 68 194 322), lower := (rows 97 259 28 137 176 34 68 128 256), losses := [] }

theorem u10796 : Upper (D 7) (R 7) [96,257,24,129,160,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10796 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10797 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 45, targets := 2 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,1),(0,7),(2,1),(3,1)], upper := (rows 97 259 28 168 208 33 66 134 262), lower := (rows 97 259 28 168 208 33 66 128 256), losses := [] }

theorem u10797 : Upper (D 7) (R 7) [96,257,24,160,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10797 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10798 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 156, targets := 2 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 97 259 28 168 208 34 66 133 261), lower := (rows 97 259 28 168 208 34 66 128 256), losses := [] }

theorem u10798 : Upper (D 7) (R 7) [96,257,24,160,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10798 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10799 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 84, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 97 259 28 168 208 34 68 131 259), lower := (rows 97 259 28 168 208 34 68 128 256), losses := [] }

theorem u10799 : Upper (D 7) (R 7) [96,257,24,160,192,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10799 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u10799
end Delivery.IrregularNine14.P07

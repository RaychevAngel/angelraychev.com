import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0023
import IrregularNine14P06C0024

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r10740 : Route 9 := (fun mask => (mask,id))

def c10740 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10740 : Upper (D 6) (R 6) [6,96,129,33,68,256] 13 := by
  apply FastRouting.sound _ _ [6,96,129,33,68,256] 13 (by decide) (choices 1) [2,8,16] r10740 c10740
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1436
  · exact u1437
  · exact u1438

def b10741 : PairBound 9 := { available := 276, camps := [{ cop := 3, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 7 98 133 41 88 34 340 404 276), lower := (rows 7 98 133 41 88 34 64 128 256), losses := [] }

theorem u10741 : Upper (D 6) (R 6) [6,96,129,33,72,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10741
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10742 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 338, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 7 98 133 41 88 36 338 402 274), lower := (rows 7 98 133 41 88 36 64 128 256), losses := [] }

theorem u10742 : Upper (D 6) (R 6) [6,96,129,33,72,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10742
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10743 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 98 133 41 88 48 326 390 262), lower := (rows 7 98 133 41 88 48 64 128 256), losses := [] }

theorem u10743 : Upper (D 6) (R 6) [6,96,129,33,72,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10743
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10744 : Route 9 := (fun mask => (mask,id))

def c10744 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10744 : Upper (D 6) (R 6) [6,96,129,33,72,256] 13 := by
  apply FastRouting.sound _ _ [6,96,129,33,72,256] 13 (by decide) (choices 1) [2,4,16] r10744 c10744
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1439
  · exact u1440
  · exact u1441

def b10745 : PairBound 9 := { available := 88, camps := [{ cop := 3, region := 338, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 7 98 133 41 274 36 88 216 344), lower := (rows 7 98 133 41 274 36 64 128 256), losses := [] }

theorem u10745 : Upper (D 6) (R 6) [6,96,129,33,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10745
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10746 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 40, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 98 133 41 274 40 84 212 340), lower := (rows 7 98 133 41 274 40 64 128 256), losses := [] }

theorem u10746 : Upper (D 6) (R 6) [6,96,129,33,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10746
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10747 : PairBound 9 := { available := 76, camps := [{ cop := 3, region := 196, targets := 34 }], pairs := [(2,1),(2,5)], upper := (rows 7 98 133 41 274 48 76 204 332), lower := (rows 7 98 133 41 274 48 64 128 256), losses := [] }

theorem u10747 : Upper (D 6) (R 6) [6,96,129,33,258,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10747
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10748 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 133 41 274 96 92 156 284), lower := (rows 7 98 133 41 274 96 64 128 256), losses := [] }

theorem u10748 : Upper (D 6) (R 6) [6,96,129,33,258,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10748
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10749 : PairBound 9 := { available := 88, camps := [{ cop := 3, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 7 98 133 41 276 34 88 216 344), lower := (rows 7 98 133 41 276 34 64 128 256), losses := [] }

theorem u10749 : Upper (D 6) (R 6) [6,96,129,33,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10749
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10750 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 40, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 98 133 41 276 40 82 210 338), lower := (rows 7 98 133 41 276 40 64 128 256), losses := [] }

theorem u10750 : Upper (D 6) (R 6) [6,96,129,33,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10750
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10751 : PairBound 9 := { available := 74, camps := [{ cop := 3, region := 66, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 98 133 41 276 48 74 202 330), lower := (rows 7 98 133 41 276 48 64 128 256), losses := [] }

theorem u10751 : Upper (D 6) (R 6) [6,96,129,33,260,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10751
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10752 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 133 41 276 96 90 154 282), lower := (rows 7 98 133 41 276 96 64 128 256), losses := [] }

theorem u10752 : Upper (D 6) (R 6) [6,96,129,33,260,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10752
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10753 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 7 98 133 41 280 34 84 212 340), lower := (rows 7 98 133 41 280 34 64 128 256), losses := [] }

theorem u10753 : Upper (D 6) (R 6) [6,96,129,33,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10753
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10754 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 338, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 7 98 133 41 280 36 82 210 338), lower := (rows 7 98 133 41 280 36 64 128 256), losses := [] }

theorem u10754 : Upper (D 6) (R 6) [6,96,129,33,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10754
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10755 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 133, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 98 133 41 280 48 70 198 326), lower := (rows 7 98 133 41 280 48 64 128 256), losses := [] }

theorem u10755 : Upper (D 6) (R 6) [6,96,129,33,264,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10755
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10756 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 133 41 280 96 86 150 278), lower := (rows 7 98 133 41 280 96 64 128 256), losses := [] }

theorem u10756 : Upper (D 6) (R 6) [6,96,129,33,264,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10756
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10757 : PairBound 9 := { available := 28, camps := [{ cop := 3, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 7 98 133 41 336 34 92 156 284), lower := (rows 7 98 133 41 336 34 64 128 256), losses := [] }

theorem u10757 : Upper (D 6) (R 6) [6,96,129,33,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10757
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10758 : PairBound 9 := { available := 26, camps := [{ cop := 3, region := 338, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 7 98 133 41 336 36 90 154 282), lower := (rows 7 98 133 41 336 36 64 128 256), losses := [] }

theorem u10758 : Upper (D 6) (R 6) [6,96,129,33,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10758
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10759 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 40, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 98 133 41 336 40 86 150 278), lower := (rows 7 98 133 41 336 40 64 128 256), losses := [] }

theorem u10759 : Upper (D 6) (R 6) [6,96,129,33,320,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10759
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10760 : PairBound 9 := { available := 14, camps := [{ cop := 1, region := 141, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 98 133 41 336 48 78 142 270), lower := (rows 7 98 133 41 336 48 64 128 256), losses := [] }

theorem u10760 : Upper (D 6) (R 6) [6,96,129,33,320,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10760
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10761 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 338, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 7 98 133 44 88 33 338 402 274), lower := (rows 7 98 133 44 88 33 64 128 256), losses := [] }

theorem u10761 : Upper (D 6) (R 6) [6,96,129,36,72,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10761
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10762 : PairBound 9 := { available := 273, camps := [{ cop := 4, region := 34, targets := 5 },{ cop := 0, region := 40, targets := 1 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 98 133 44 88 34 337 401 273), lower := (rows 7 98 133 44 88 34 64 128 256), losses := [] }

theorem u10762 : Upper (D 6) (R 6) [6,96,129,36,72,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10762
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10763 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 98 133 44 88 48 323 387 259), lower := (rows 7 98 133 44 88 48 64 128 256), losses := [] }

theorem u10763 : Upper (D 6) (R 6) [6,96,129,36,72,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10763
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10764 : Route 9 := (fun mask => (mask,id))

def c10764 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10764 : Upper (D 6) (R 6) [6,96,129,36,72,256] 13 := by
  apply FastRouting.sound _ _ [6,96,129,36,72,256] 13 (by decide) (choices 1) [1,2,16] r10764 c10764
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1442
  · exact u1443
  · exact u1444

def b10765 : PairBound 9 := { available := 88, camps := [{ cop := 6, region := 34, targets := 5 },{ cop := 0, region := 40, targets := 1 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 98 133 44 273 34 88 216 344), lower := (rows 7 98 133 44 273 34 64 128 256), losses := [] }

theorem u10765 : Upper (D 6) (R 6) [6,96,129,36,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10765
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10766 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 405, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 98 133 44 273 40 82 210 338), lower := (rows 7 98 133 44 273 40 64 128 256), losses := [] }

theorem u10766 : Upper (D 6) (R 6) [6,96,129,36,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10766
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10767 : PairBound 9 := { available := 74, camps := [{ cop := 3, region := 66, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 98 133 44 273 48 74 202 330), lower := (rows 7 98 133 44 273 48 64 128 256), losses := [] }

theorem u10767 : Upper (D 6) (R 6) [6,96,129,36,257,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10767
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10768 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 133 44 273 96 90 154 282), lower := (rows 7 98 133 44 273 96 64 128 256), losses := [] }

theorem u10768 : Upper (D 6) (R 6) [6,96,129,36,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10768
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10769 : PairBound 9 := { available := 88, camps := [{ cop := 3, region := 338, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 7 98 133 44 274 33 88 216 344), lower := (rows 7 98 133 44 274 33 64 128 256), losses := [] }

theorem u10769 : Upper (D 6) (R 6) [6,96,129,36,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10769
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10770 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 405, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 98 133 44 274 40 81 209 337), lower := (rows 7 98 133 44 274 40 64 128 256), losses := [] }

theorem u10770 : Upper (D 6) (R 6) [6,96,129,36,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10770
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10771 : Route 9 := (fun mask => (mask,id))

def c10771 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10771 : Upper (D 6) (R 6) [6,96,129,36,258,16] 13 := by
  apply FastRouting.sound _ _ [6,96,129,36,258,16] 13 (by decide) (choices 1) [1,8] r10771 c10771
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1445
  · exact u1446

def b10772 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 133 44 274 96 89 153 281), lower := (rows 7 98 133 44 274 96 64 128 256), losses := [] }

theorem u10772 : Upper (D 6) (R 6) [6,96,129,36,258,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10772
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10773 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 338, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 7 98 133 44 280 33 82 210 338), lower := (rows 7 98 133 44 280 33 64 128 256), losses := [] }

theorem u10773 : Upper (D 6) (R 6) [6,96,129,36,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10773
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10774 : PairBound 9 := { available := 81, camps := [{ cop := 6, region := 34, targets := 5 },{ cop := 0, region := 40, targets := 1 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 98 133 44 280 34 81 209 337), lower := (rows 7 98 133 44 280 34 64 128 256), losses := [] }

theorem u10774 : Upper (D 6) (R 6) [6,96,129,36,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10774
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10775 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 133, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 98 133 44 280 48 67 195 323), lower := (rows 7 98 133 44 280 48 64 128 256), losses := [] }

theorem u10775 : Upper (D 6) (R 6) [6,96,129,36,264,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10775
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10776 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 133 44 280 96 83 147 275), lower := (rows 7 98 133 44 280 96 64 128 256), losses := [] }

theorem u10776 : Upper (D 6) (R 6) [6,96,129,36,264,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10776
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10777 : PairBound 9 := { available := 26, camps := [{ cop := 3, region := 338, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 7 98 133 44 336 33 90 154 282), lower := (rows 7 98 133 44 336 33 64 128 256), losses := [] }

theorem u10777 : Upper (D 6) (R 6) [6,96,129,36,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10777
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10778 : PairBound 9 := { available := 25, camps := [{ cop := 4, region := 34, targets := 5 },{ cop := 0, region := 40, targets := 1 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 98 133 44 336 34 89 153 281), lower := (rows 7 98 133 44 336 34 64 128 256), losses := [] }

theorem u10778 : Upper (D 6) (R 6) [6,96,129,36,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10778
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10779 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 405, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 98 133 44 336 40 83 147 275), lower := (rows 7 98 133 44 336 40 64 128 256), losses := [] }

theorem u10779 : Upper (D 6) (R 6) [6,96,129,36,320,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10779
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10780 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 141, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 98 133 44 336 48 75 139 267), lower := (rows 7 98 133 44 336 48 64 128 256), losses := [] }

theorem u10780 : Upper (D 6) (R 6) [6,96,129,36,320,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10780
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10781 : PairBound 9 := { available := 76, camps := [{ cop := 6, region := 34, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 98 133 56 273 34 76 204 332), lower := (rows 7 98 133 56 273 34 64 128 256), losses := [{ target := 0, region := (rows 0 66 4 24 16 99 64 128 256), good := (rows 38 98 164 56 312 34 98 128 256) }] }

theorem u10781 : Upper (D 6) (R 6) [6,96,129,48,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10781
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10782 : PairBound 9 := { available := 74, camps := [{ cop := 3, region := 66, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 98 133 56 273 36 74 202 330), lower := (rows 7 98 133 56 273 36 64 128 256), losses := [{ target := 0, region := (rows 0 26 4 24 16 37 88 152 280), good := (rows 38 98 164 506 506 36 64 128 256) }] }

theorem u10782 : Upper (D 6) (R 6) [6,96,129,48,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10782
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10783 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 98 133 56 273 40 70 198 326), lower := (rows 7 98 133 56 273 40 64 128 256), losses := [] }

theorem u10783 : Upper (D 6) (R 6) [6,96,129,48,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10783
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10784 : PairBound 9 := { available := 14, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 133 56 273 96 78 142 270), lower := (rows 7 98 133 56 273 96 64 128 256), losses := [] }

theorem u10784 : Upper (D 6) (R 6) [6,96,129,48,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10784
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10785 : PairBound 9 := { available := 76, camps := [], pairs := [(1,0),(3,0),(4,0)], upper := (rows 7 98 133 56 274 33 76 204 332), lower := (rows 7 98 133 56 274 33 64 128 256), losses := [{ target := 0, region := (rows 0 34 4 42 49 32 65 129 257), good := (rows 478 122 468 58 282 506 64 128 256) }] }

theorem u10785 : Upper (D 6) (R 6) [6,96,129,48,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10785
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10786 : Route 9 := (fun mask => (mask,id))

def c10786 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10786 : Upper (D 6) (R 6) [6,96,129,48,258,4] 13 := by
  apply FastRouting.sound _ _ [6,96,129,48,258,4] 13 (by decide) (choices 1) [1,8] r10786 c10786
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1447
  · exact u1448

def b10787 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 98 133 56 274 40 69 197 325), lower := (rows 7 98 133 56 274 40 64 128 256), losses := [] }

theorem u10787 : Upper (D 6) (R 6) [6,96,129,48,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10787
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10788 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 133 56 274 96 77 141 269), lower := (rows 7 98 133 56 274 96 64 128 256), losses := [] }

theorem u10788 : Upper (D 6) (R 6) [6,96,129,48,258,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10788
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10789 : PairBound 9 := { available := 74, camps := [{ cop := 3, region := 66, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 98 133 56 276 33 74 202 330), lower := (rows 7 98 133 56 276 33 64 128 256), losses := [{ target := 0, region := (rows 0 42 4 40 17 32 106 170 298), good := (rows 470 490 148 506 276 506 64 128 256) }] }

theorem u10789 : Upper (D 6) (R 6) [6,96,129,48,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10789
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10790 : Route 9 := (fun mask => (mask,id))

def c10790 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10790 : Upper (D 6) (R 6) [6,96,129,48,260,2] 13 := by
  apply FastRouting.sound _ _ [6,96,129,48,260,2] 13 (by decide) (choices 1) [1,8] r10790 c10790
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1449
  · exact u1450

def b10791 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 98 133 56 276 40 67 195 323), lower := (rows 7 98 133 56 276 40 64 128 256), losses := [] }

theorem u10791 : Upper (D 6) (R 6) [6,96,129,48,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10791
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10792 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 133 56 276 96 75 139 267), lower := (rows 7 98 133 56 276 96 64 128 256), losses := [] }

theorem u10792 : Upper (D 6) (R 6) [6,96,129,48,260,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10792
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10793 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 133, targets := 32 }], pairs := [(0,5),(1,0),(2,5)], upper := (rows 7 98 133 56 280 33 70 198 326), lower := (rows 7 98 133 56 280 33 64 128 256), losses := [{ target := 0, region := (rows 0 34 4 42 49 32 65 129 257), good := (rows 478 122 468 58 280 506 64 128 256) }] }

theorem u10793 : Upper (D 6) (R 6) [6,96,129,48,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10793
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10794 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 196, targets := 34 },{ cop := 6, region := 34, targets := 1 }], pairs := [(1,0),(2,1),(2,5)], upper := (rows 7 98 133 56 280 34 69 197 325), lower := (rows 7 98 133 56 280 34 64 128 256), losses := [] }

theorem u10794 : Upper (D 6) (R 6) [6,96,129,48,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10794
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10795 : Route 9 := (fun mask => (mask,id))

def c10795 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10795 : Upper (D 6) (R 6) [6,96,129,48,264,4] 13 := by
  apply FastRouting.sound _ _ [6,96,129,48,264,4] 13 (by decide) (choices 1) [1,2] r10795 c10795
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1451
  · exact u1452

def b10796 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 133 56 280 96 71 135 263), lower := (rows 7 98 133 56 280 96 64 128 256), losses := [] }

theorem u10796 : Upper (D 6) (R 6) [6,96,129,48,264,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10796
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10797 : PairBound 9 := { available := 14, camps := [], pairs := [(1,0),(3,0),(4,0)], upper := (rows 7 98 133 56 336 33 78 142 270), lower := (rows 7 98 133 56 336 33 64 128 256), losses := [{ target := 0, region := (rows 0 34 4 42 53 32 65 129 257), good := (rows 478 122 468 58 336 506 64 128 256) }] }

theorem u10797 : Upper (D 6) (R 6) [6,96,129,48,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10797
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10798 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 42, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 98 133 56 336 34 77 141 269), lower := (rows 7 98 133 56 336 34 64 128 256), losses := [] }

theorem u10798 : Upper (D 6) (R 6) [6,96,129,48,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10798
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10799 : Route 9 := (fun mask => (mask,id))

def c10799 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10799 : Upper (D 6) (R 6) [6,96,129,48,320,4] 13 := by
  apply FastRouting.sound _ _ [6,96,129,48,320,4] 13 (by decide) (choices 1) [1,2,8] r10799 c10799
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1453
  · exact u1454
  · exact u1455

#print axioms u10799
end Delivery.IrregularNine14.P06

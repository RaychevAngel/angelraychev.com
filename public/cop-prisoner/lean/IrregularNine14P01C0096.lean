import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0034

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5760 : PairBound 9 := { available := 402, camps := [{ cop := 2, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 15 19 100 104 402 434 466 402 402), lower := (rows 15 19 100 104 16 32 64 128 256), losses := [] }

theorem u5760 : Upper (D 1) (R 1) [14,17,96,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5760
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5761 : PairBound 9 := { available := 466, camps := [{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5)], upper := (rows 15 19 100 168 466 498 466 466 466), lower := (rows 15 19 100 168 16 32 64 128 256), losses := [] }

theorem u5761 : Upper (D 1) (R 1) [14,17,96,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5761
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5762 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 244, targets := 2 }], pairs := [(2,1)], upper := (rows 15 19 100 266 240 240 240 240 496), lower := (rows 15 19 100 266 16 32 64 128 256), losses := [] }

theorem u5762 : Upper (D 1) (R 1) [14,17,96,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5762
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5763 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 228, targets := 16 }], pairs := [(2,4)], upper := (rows 15 19 100 280 242 226 226 226 482), lower := (rows 15 19 100 280 16 32 64 128 256), losses := [] }

theorem u5763 : Upper (D 1) (R 1) [14,17,96,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5763
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5764 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 210, targets := 32 }], pairs := [(1,5)], upper := (rows 15 19 100 296 210 242 210 210 466), lower := (rows 15 19 100 296 16 32 64 128 256), losses := [] }

theorem u5764 : Upper (D 1) (R 1) [14,17,96,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5764
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5765 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c5765 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u5765 : Upper (D 1) (R 1) [14,17,96,384] 13 := by
  apply FastRouting.sound _ _ [14,17,96,384] 13 (by decide) (choices 1) [2,32,128] r5765 c5765
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2071
  · exact u2072
  · exact u2073

def b5766 : PairBound 9 := { available := 496, camps := [{ cop := 0, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 15 50 7 200 496 496 496 496 496), lower := (rows 15 50 7 200 16 32 64 128 256), losses := [] }

theorem u5766 : Upper (D 1) (R 1) [14,48,3,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5766
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5767 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 15 50 7 328 240 240 240 240 496), lower := (rows 15 50 7 328 16 32 64 128 256), losses := [] }

theorem u5767 : Upper (D 1) (R 1) [14,48,3,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5767
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5768 : PairBound 9 := { available := 482, camps := [{ cop := 0, region := 488, targets := 16 }], pairs := [(3,4)], upper := (rows 15 50 21 200 498 482 482 482 482), lower := (rows 15 50 21 200 16 32 64 128 256), losses := [] }

theorem u5768 : Upper (D 1) (R 1) [14,48,17,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5768
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5769 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 488, targets := 16 }], pairs := [(3,4)], upper := (rows 15 50 21 328 242 226 226 226 482), lower := (rows 15 50 21 328 16 32 64 128 256), losses := [] }

theorem u5769 : Upper (D 1) (R 1) [14,48,17,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5769
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5770 : PairBound 9 := { available := 480, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 15 50 22 73 496 480 480 480 480), lower := (rows 15 50 22 73 16 32 64 128 256), losses := [] }

theorem u5770 : Upper (D 1) (R 1) [14,48,18,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5770
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5771 : PairBound 9 := { available := 481, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 15 50 22 200 497 481 481 481 481), lower := (rows 15 50 22 200 16 32 64 128 256), losses := [] }

theorem u5771 : Upper (D 1) (R 1) [14,48,18,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5771
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5772 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 15 50 22 265 240 224 224 224 480), lower := (rows 15 50 22 265 16 32 64 128 256), losses := [] }

theorem u5772 : Upper (D 1) (R 1) [14,48,18,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5772
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5773 : PairBound 9 := { available := 225, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 15 50 22 328 241 225 225 225 481), lower := (rows 15 50 22 328 16 32 64 128 256), losses := [] }

theorem u5773 : Upper (D 1) (R 1) [14,48,18,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5773
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5774 : PairBound 9 := { available := 450, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 15 50 52 73 466 482 450 450 450), lower := (rows 15 50 52 73 16 32 64 128 256), losses := [] }

theorem u5774 : Upper (D 1) (R 1) [14,48,48,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5774
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5775 : PairBound 9 := { available := 451, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 15 50 52 200 467 483 451 451 451), lower := (rows 15 50 52 200 16 32 64 128 256), losses := [] }

theorem u5775 : Upper (D 1) (R 1) [14,48,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5775
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5776 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 15 50 52 265 210 226 194 194 450), lower := (rows 15 50 52 265 16 32 64 128 256), losses := [] }

theorem u5776 : Upper (D 1) (R 1) [14,48,48,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5776
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5777 : PairBound 9 := { available := 195, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 15 50 52 328 211 227 195 195 451), lower := (rows 15 50 52 328 16 32 64 128 256), losses := [] }

theorem u5777 : Upper (D 1) (R 1) [14,48,48,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5777
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5778 : PairBound 9 := { available := 432, camps := [{ cop := 3, region := 5, targets := 16 }], pairs := [(0,4)], upper := (rows 15 50 69 74 432 432 496 432 432), lower := (rows 15 50 69 74 16 32 64 128 256), losses := [] }

theorem u5778 : Upper (D 1) (R 1) [14,48,65,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5778
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5779 : PairBound 9 := { available := 418, camps := [{ cop := 0, region := 484, targets := 16 }], pairs := [(2,4)], upper := (rows 15 50 69 88 434 418 482 418 418), lower := (rows 15 50 69 88 16 32 64 128 256), losses := [] }

theorem u5779 : Upper (D 1) (R 1) [14,48,65,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5779
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5780 : PairBound 9 := { available := 496, camps := [{ cop := 0, region := 500, targets := 2 }], pairs := [(2,1)], upper := (rows 15 50 69 138 496 496 496 496 496), lower := (rows 15 50 69 138 16 32 64 128 256), losses := [] }

theorem u5780 : Upper (D 1) (R 1) [14,48,65,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5780
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5781 : PairBound 9 := { available := 482, camps := [{ cop := 0, region := 484, targets := 16 }], pairs := [(2,4)], upper := (rows 15 50 69 152 498 482 482 482 482), lower := (rows 15 50 69 152 16 32 64 128 256), losses := [] }

theorem u5781 : Upper (D 1) (R 1) [14,48,65,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5781
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5782 : PairBound 9 := { available := 434, camps := [{ cop := 0, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 15 50 69 200 434 434 498 434 434), lower := (rows 15 50 69 200 16 32 64 128 256), losses := [] }

theorem u5782 : Upper (D 1) (R 1) [14,48,65,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5782
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5783 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 244, targets := 2 }], pairs := [(2,1)], upper := (rows 15 50 69 266 240 240 240 240 496), lower := (rows 15 50 69 266 16 32 64 128 256), losses := [] }

theorem u5783 : Upper (D 1) (R 1) [14,48,65,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5783
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5784 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 228, targets := 16 }], pairs := [(2,4)], upper := (rows 15 50 69 280 242 226 226 226 482), lower := (rows 15 50 69 280 16 32 64 128 256), losses := [] }

theorem u5784 : Upper (D 1) (R 1) [14,48,65,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5784
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5785 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 178, targets := 64 }], pairs := [(1,6)], upper := (rows 15 50 69 328 178 178 242 178 434), lower := (rows 15 50 69 328 16 32 64 128 256), losses := [] }

theorem u5785 : Upper (D 1) (R 1) [14,48,65,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5785
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5786 : Route 9 := (fun mask => (mask,id))

def c5786 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u5786 : Upper (D 1) (R 1) [14,48,65,384] 13 := by
  apply FastRouting.sound _ _ [14,48,65,384] 13 (by decide) (choices 1) [2,32,64,128] r5786 c5786
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2074
  · exact u2075
  · exact u2076
  · exact u2077

def b5787 : PairBound 9 := { available := 433, camps := [{ cop := 0, region := 504, targets := 2 }], pairs := [(3,1)], upper := (rows 15 50 70 200 433 433 497 433 433), lower := (rows 15 50 70 200 16 32 64 128 256), losses := [] }

theorem u5787 : Upper (D 1) (R 1) [14,48,66,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5787
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5788 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 504, targets := 2 }], pairs := [(3,1)], upper := (rows 15 50 70 265 240 240 240 240 496), lower := (rows 15 50 70 265 16 32 64 128 256), losses := [] }

theorem u5788 : Upper (D 1) (R 1) [14,48,66,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5788
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5789 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 504, targets := 2 }], pairs := [(3,1)], upper := (rows 15 50 70 328 177 177 241 177 433), lower := (rows 15 50 70 328 16 32 64 128 256), losses := [] }

theorem u5789 : Upper (D 1) (R 1) [14,48,66,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5789
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5790 : PairBound 9 := { available := 241, camps := [{ cop := 0, region := 504, targets := 2 }], pairs := [(3,1)], upper := (rows 15 50 70 392 241 241 241 241 497), lower := (rows 15 50 70 392 16 32 64 128 256), losses := [] }

theorem u5790 : Upper (D 1) (R 1) [14,48,66,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5790
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5791 : PairBound 9 := { available := 419, camps := [{ cop := 0, region := 488, targets := 16 }], pairs := [(3,4)], upper := (rows 15 50 84 200 435 419 483 419 419), lower := (rows 15 50 84 200 16 32 64 128 256), losses := [] }

theorem u5791 : Upper (D 1) (R 1) [14,48,80,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5791
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5792 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 488, targets := 16 }], pairs := [(3,4)], upper := (rows 15 50 84 265 242 226 226 226 482), lower := (rows 15 50 84 265 16 32 64 128 256), losses := [] }

theorem u5792 : Upper (D 1) (R 1) [14,48,80,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5792
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5793 : PairBound 9 := { available := 163, camps := [{ cop := 0, region := 488, targets := 16 }], pairs := [(3,4)], upper := (rows 15 50 84 328 179 163 227 163 419), lower := (rows 15 50 84 328 16 32 64 128 256), losses := [] }

theorem u5793 : Upper (D 1) (R 1) [14,48,80,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5793
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5794 : PairBound 9 := { available := 227, camps := [{ cop := 0, region := 488, targets := 16 }], pairs := [(3,4)], upper := (rows 15 50 84 392 243 227 227 227 483), lower := (rows 15 50 84 392 16 32 64 128 256), losses := [] }

theorem u5794 : Upper (D 1) (R 1) [14,48,80,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5794
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5795 : PairBound 9 := { available := 307, camps := [{ cop := 2, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 15 50 196 200 307 307 371 435 307), lower := (rows 15 50 196 200 16 32 64 128 256), losses := [] }

theorem u5795 : Upper (D 1) (R 1) [14,48,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5795
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5796 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c5796 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u5796 : Upper (D 1) (R 1) [14,48,192,257] 13 := by
  apply FastRouting.sound _ _ [14,48,192,257] 13 (by decide) (choices 1) [2,32,64] r5796 c5796
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2078
  · exact u2079
  · exact u2080

def b5797 : PairBound 9 := { available := 241, camps := [{ cop := 0, region := 244, targets := 2 }], pairs := [(2,1)], upper := (rows 15 50 196 266 241 241 241 241 497), lower := (rows 15 50 196 266 16 32 64 128 256), losses := [] }

theorem u5797 : Upper (D 1) (R 1) [14,48,192,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5797
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5798 : PairBound 9 := { available := 227, camps := [{ cop := 0, region := 228, targets := 16 }], pairs := [(2,4)], upper := (rows 15 50 196 280 243 227 227 227 483), lower := (rows 15 50 196 280 16 32 64 128 256), losses := [] }

theorem u5798 : Upper (D 1) (R 1) [14,48,192,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5798
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5799 : PairBound 9 := { available := 179, camps := [{ cop := 0, region := 178, targets := 64 }], pairs := [(1,6)], upper := (rows 15 50 196 328 179 179 243 179 435), lower := (rows 15 50 196 328 16 32 64 128 256), losses := [] }

theorem u5799 : Upper (D 1) (R 1) [14,48,192,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5799
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5800 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 248, targets := 2 }], pairs := [(3,1)], upper := (rows 15 259 22 56 240 224 224 224 480), lower := (rows 15 259 22 56 16 32 64 128 256), losses := [] }

theorem u5800 : Upper (D 1) (R 1) [14,257,18,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5800
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5801 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 248, targets := 2 }], pairs := [(3,1)], upper := (rows 15 259 22 104 240 240 240 240 496), lower := (rows 15 259 22 104 16 32 64 128 256), losses := [] }

theorem u5801 : Upper (D 1) (R 1) [14,257,18,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5801
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5802 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 15 259 52 56 210 226 194 194 450), lower := (rows 15 259 52 56 16 32 64 128 256), losses := [] }

theorem u5802 : Upper (D 1) (R 1) [14,257,48,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5802
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5803 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 15 259 52 88 242 226 226 226 482), lower := (rows 15 259 52 88 16 32 64 128 256), losses := [] }

theorem u5803 : Upper (D 1) (R 1) [14,257,48,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5803
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5804 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c5804 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u5804 : Upper (D 1) (R 1) [14,257,48,192] 13 := by
  apply FastRouting.sound _ _ [14,257,48,192] 13 (by decide) (choices 1) [2,32,64] r5804 c5804
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2081
  · exact u2082
  · exact u2083

def b5805 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 15 274 7 104 240 240 240 240 496), lower := (rows 15 274 7 104 16 32 64 128 256), losses := [] }

theorem u5805 : Upper (D 1) (R 1) [14,272,3,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5805
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5806 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 15 274 21 104 242 226 226 226 482), lower := (rows 15 274 21 104 16 32 64 128 256), losses := [] }

theorem u5806 : Upper (D 1) (R 1) [14,272,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5806
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5807 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 15 274 22 41 240 224 224 224 480), lower := (rows 15 274 22 41 16 32 64 128 256), losses := [] }

theorem u5807 : Upper (D 1) (R 1) [14,272,18,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5807
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5808 : PairBound 9 := { available := 225, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 15 274 22 104 241 225 225 225 481), lower := (rows 15 274 22 104 16 32 64 128 256), losses := [] }

theorem u5808 : Upper (D 1) (R 1) [14,272,18,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5808
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5809 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 5, targets := 16 }], pairs := [(0,4)], upper := (rows 15 274 37 42 208 240 208 208 464), lower := (rows 15 274 37 42 16 32 64 128 256), losses := [] }

theorem u5809 : Upper (D 1) (R 1) [14,272,33,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5809
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5810 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 228, targets := 16 }], pairs := [(2,4)], upper := (rows 15 274 37 56 210 226 194 194 450), lower := (rows 15 274 37 56 16 32 64 128 256), losses := [] }

theorem u5810 : Upper (D 1) (R 1) [14,272,33,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5810
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5811 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 244, targets := 2 }], pairs := [(2,1)], upper := (rows 15 274 37 74 240 240 240 240 496), lower := (rows 15 274 37 74 16 32 64 128 256), losses := [] }

theorem u5811 : Upper (D 1) (R 1) [14,272,33,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5811
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5812 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 228, targets := 16 }], pairs := [(2,4)], upper := (rows 15 274 37 88 242 226 226 226 482), lower := (rows 15 274 37 88 16 32 64 128 256), losses := [] }

theorem u5812 : Upper (D 1) (R 1) [14,272,33,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5812
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5813 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5)], upper := (rows 15 274 37 104 210 242 210 210 466), lower := (rows 15 274 37 104 16 32 64 128 256), losses := [] }

theorem u5813 : Upper (D 1) (R 1) [14,272,33,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5813
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5814 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c5814 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u5814 : Upper (D 1) (R 1) [14,272,33,192] 13 := by
  apply FastRouting.sound _ _ [14,272,33,192] 13 (by decide) (choices 1) [2,32,64] r5814 c5814
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2084
  · exact u2085
  · exact u2086

def b5815 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 248, targets := 2 }], pairs := [(3,1)], upper := (rows 15 274 38 104 209 241 209 209 465), lower := (rows 15 274 38 104 16 32 64 128 256), losses := [] }

theorem u5815 : Upper (D 1) (R 1) [14,272,34,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5815
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5816 : PairBound 9 := { available := 241, camps := [{ cop := 0, region := 248, targets := 2 }], pairs := [(3,1)], upper := (rows 15 274 38 200 241 241 241 241 497), lower := (rows 15 274 38 200 16 32 64 128 256), losses := [] }

theorem u5816 : Upper (D 1) (R 1) [14,272,34,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5816
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5817 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 15 274 52 104 211 227 195 195 451), lower := (rows 15 274 52 104 16 32 64 128 256), losses := [] }

theorem u5817 : Upper (D 1) (R 1) [14,272,48,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5817
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5818 : PairBound 9 := { available := 227, camps := [{ cop := 0, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 15 274 52 200 243 227 227 227 483), lower := (rows 15 274 52 200 16 32 64 128 256), losses := [] }

theorem u5818 : Upper (D 1) (R 1) [14,272,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5818
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5819 : PairBound 9 := { available := 147, camps := [{ cop := 2, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 15 274 100 104 147 179 211 147 403), lower := (rows 15 274 100 104 16 32 64 128 256), losses := [] }

theorem u5819 : Upper (D 1) (R 1) [14,272,96,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5819
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u5819
end Delivery.IrregularNine14.P01

import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0037
import IrregularNine14P05C0038

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5760 : PairBound 9 := { available := 58, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 35 76 392 21 58 122 186 314), lower := (rows 7 35 76 392 21 32 64 128 256), losses := [] }

theorem u5760 : Upper (D 5) (R 5) [6,33,72,384,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5760
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5761 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 16, targets := 40 }], pairs := [(4,3),(4,5)], upper := (rows 7 35 76 392 22 57 121 185 313), lower := (rows 7 35 76 392 22 32 64 128 256), losses := [] }

theorem u5761 : Upper (D 5) (R 5) [6,33,72,384,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5761
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5762 : Route 9 := (fun mask => (mask,id))

def c5762 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5762 : Upper (D 5) (R 5) [6,33,72,384,9] 13 := by
  apply FastRouting.sound _ _ [6,33,72,384,9] 13 (by decide) (choices 1) [2,4,16] r5762 c5762
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2263
  · exact u2264
  · exact u2265

def r5763 : Route 9 := (fun mask => (mask,id))

def c5763 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5763 : Upper (D 5) (R 5) [6,33,72,384,10] 13 := by
  apply FastRouting.sound _ _ [6,33,72,384,10] 13 (by decide) (choices 1) [1,4,16] r5763 c5763
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2266
  · exact u2267
  · exact u2268

def b5764 : PairBound 9 := { available := 51, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 35 76 392 28 51 115 179 307), lower := (rows 7 35 76 392 28 32 64 128 256), losses := [] }

theorem u5764 : Upper (D 5) (R 5) [6,33,72,384,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5764
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5765 : PairBound 9 := { available := 30, camps := [{ cop := 1, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 35 76 392 49 62 94 158 286), lower := (rows 7 35 76 392 49 32 64 128 256), losses := [] }

theorem u5765 : Upper (D 5) (R 5) [6,33,72,384,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5765
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5766 : PairBound 9 := { available := 29, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 35 76 392 50 61 93 157 285), lower := (rows 7 35 76 392 50 32 64 128 256), losses := [] }

theorem u5766 : Upper (D 5) (R 5) [6,33,72,384,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5766
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5767 : PairBound 9 := { available := 27, camps := [{ cop := 4, region := 3, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 35 76 392 52 59 91 155 283), lower := (rows 7 35 76 392 52 32 64 128 256), losses := [] }

theorem u5767 : Upper (D 5) (R 5) [6,33,72,384,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5767
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5768 : Route 9 := (fun mask => (mask,id))

def c5768 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5768 : Upper (D 5) (R 5) [6,33,72,384,40] 13 := by
  apply FastRouting.sound _ _ [6,33,72,384,40] 13 (by decide) (choices 1) [1,2,4,16] r5768 c5768
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2269
  · exact u2270
  · exact u2271
  · exact u2272

def b5769 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 426, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 35 84 137 22 296 360 424 296), lower := (rows 7 35 84 137 22 32 64 128 256), losses := [] }

theorem u5769 : Upper (D 5) (R 5) [6,33,80,129,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5769
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5770 : PairBound 9 := { available := 300, camps := [{ cop := 4, region := 356, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 35 84 137 26 300 364 428 300), lower := (rows 7 35 84 137 26 32 64 128 256), losses := [] }

theorem u5770 : Upper (D 5) (R 5) [6,33,80,129,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5770
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5771 : PairBound 9 := { available := 298, camps := [{ cop := 0, region := 426, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 35 84 137 28 298 362 426 298), lower := (rows 7 35 84 137 28 32 64 128 256), losses := [] }

theorem u5771 : Upper (D 5) (R 5) [6,33,80,129,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5771
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5772 : PairBound 9 := { available := 268, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 35 84 137 50 300 332 396 268), lower := (rows 7 35 84 137 50 32 64 128 256), losses := [] }

theorem u5772 : Upper (D 5) (R 5) [6,33,80,129,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5772
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5773 : PairBound 9 := { available := 266, camps := [{ cop := 0, region := 426, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 35 84 137 52 298 330 394 266), lower := (rows 7 35 84 137 52 32 64 128 256), losses := [] }

theorem u5773 : Upper (D 5) (R 5) [6,33,80,129,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5773
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5774 : Route 9 := (fun mask => (mask,id))

def c5774 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u5774 : Upper (D 5) (R 5) [6,33,80,129,40] 13 := by
  apply FastRouting.sound _ _ [6,33,80,129,40] 13 (by decide) (choices 1) [2,4,8,256] r5774 c5774
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2273
  · exact u2274
  · exact u2275
  · exact u2276

def b5775 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 168, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 84 137 274 44 108 172 300), lower := (rows 7 35 84 137 274 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 11 16 49 81 145 273), good := (rows 493 489 500 489 508 32 64 128 256) }] }

theorem u5775 : Upper (D 5) (R 5) [6,33,80,129,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5775
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5776 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 170, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 35 84 137 276 42 106 170 298), lower := (rows 7 35 84 137 276 32 64 128 256), losses := [] }

theorem u5776 : Upper (D 5) (R 5) [6,33,80,129,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5776
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5777 : Route 9 := (fun mask => (mask,id))

def c5777 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5777 : Upper (D 5) (R 5) [6,33,80,129,264] 13 := by
  apply FastRouting.sound _ _ [6,33,80,129,264] 13 (by decide) (choices 1) [2,4,8] r5777 c5777
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2277
  · exact u2278
  · exact u2279

def r5778 : Route 9 := (fun mask => (mask,id))

def c5778 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5778 : Upper (D 5) (R 5) [6,33,80,129,288] 13 := by
  apply FastRouting.sound _ _ [6,33,80,129,288] 13 (by decide) (choices 1) [2,4,8] r5778 c5778
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2280
  · exact u2281
  · exact u2282

def b5779 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 35 84 138 21 296 360 424 296), lower := (rows 7 35 84 138 21 32 64 128 256), losses := [] }

theorem u5779 : Upper (D 5) (R 5) [6,33,80,130,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5779
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5780 : PairBound 9 := { available := 300, camps := [{ cop := 4, region := 356, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 35 84 138 25 300 364 428 300), lower := (rows 7 35 84 138 25 32 64 128 256), losses := [] }

theorem u5780 : Upper (D 5) (R 5) [6,33,80,130,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5780
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5781 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 426, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 35 84 138 28 297 361 425 297), lower := (rows 7 35 84 138 28 32 64 128 256), losses := [] }

theorem u5781 : Upper (D 5) (R 5) [6,33,80,130,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5781
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5782 : PairBound 9 := { available := 268, camps := [{ cop := 1, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 35 84 138 49 300 332 396 268), lower := (rows 7 35 84 138 49 32 64 128 256), losses := [] }

theorem u5782 : Upper (D 5) (R 5) [6,33,80,130,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5782
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5783 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 426, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 35 84 138 52 297 329 393 265), lower := (rows 7 35 84 138 52 32 64 128 256), losses := [] }

theorem u5783 : Upper (D 5) (R 5) [6,33,80,130,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5783
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5784 : Route 9 := (fun mask => (mask,id))

def c5784 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u5784 : Upper (D 5) (R 5) [6,33,80,130,40] 13 := by
  apply FastRouting.sound _ _ [6,33,80,130,40] 13 (by decide) (choices 1) [1,4,8,256] r5784 c5784
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2283
  · exact u2284
  · exact u2285
  · exact u2286

def b5785 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 168, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 84 138 273 44 108 172 300), lower := (rows 7 35 84 138 273 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 11 16 49 81 145 273), good := (rows 494 490 500 138 508 32 64 128 256) }] }

theorem u5785 : Upper (D 5) (R 5) [6,33,80,130,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5785
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5786 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 170, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 35 84 138 276 41 105 169 297), lower := (rows 7 35 84 138 276 32 64 128 256), losses := [] }

theorem u5786 : Upper (D 5) (R 5) [6,33,80,130,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5786
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5787 : Route 9 := (fun mask => (mask,id))

def c5787 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5787 : Upper (D 5) (R 5) [6,33,80,130,264] 13 := by
  apply FastRouting.sound _ _ [6,33,80,130,264] 13 (by decide) (choices 1) [1,4,8] r5787 c5787
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2287
  · exact u2288
  · exact u2289

def r5788 : Route 9 := (fun mask => (mask,id))

def c5788 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5788 : Upper (D 5) (R 5) [6,33,80,130,288] 13 := by
  apply FastRouting.sound _ _ [6,33,80,130,288] 13 (by decide) (choices 1) [1,4,8] r5788 c5788
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2290
  · exact u2291
  · exact u2292

def b5789 : PairBound 9 := { available := 296, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 35 84 140 19 296 360 424 296), lower := (rows 7 35 84 140 19 32 64 128 256), losses := [] }

theorem u5789 : Upper (D 5) (R 5) [6,33,80,132,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5789
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5790 : PairBound 9 := { available := 298, camps := [{ cop := 0, region := 424, targets := 1 },{ cop := 4, region := 290, targets := 4 }], pairs := [(1,2),(3,0)], upper := (rows 7 35 84 140 25 298 362 426 298), lower := (rows 7 35 84 140 25 32 64 128 256), losses := [] }

theorem u5790 : Upper (D 5) (R 5) [6,33,80,132,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5790
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5791 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 424, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 84 140 26 297 361 425 297), lower := (rows 7 35 84 140 26 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 25 16 35 67 131 259), good := (rows 493 489 92 140 508 32 64 128 256) }] }

theorem u5791 : Upper (D 5) (R 5) [6,33,80,132,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5791
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5792 : PairBound 9 := { available := 266, camps := [{ cop := 1, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 35 84 140 49 298 330 394 266), lower := (rows 7 35 84 140 49 32 64 128 256), losses := [] }

theorem u5792 : Upper (D 5) (R 5) [6,33,80,132,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5792
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5793 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 35 84 140 50 297 329 393 265), lower := (rows 7 35 84 140 50 32 64 128 256), losses := [] }

theorem u5793 : Upper (D 5) (R 5) [6,33,80,132,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5793
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5794 : Route 9 := (fun mask => (mask,id))

def c5794 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u5794 : Upper (D 5) (R 5) [6,33,80,132,40] 13 := by
  apply FastRouting.sound _ _ [6,33,80,132,40] 13 (by decide) (choices 1) [1,2,8,256] r5794 c5794
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2293
  · exact u2294
  · exact u2295
  · exact u2296

def b5795 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 168, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 84 140 273 42 106 170 298), lower := (rows 7 35 84 140 273 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 25 16 35 67 131 259), good := (rows 494 490 92 140 508 32 64 128 256) }] }

theorem u5795 : Upper (D 5) (R 5) [6,33,80,132,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5795
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5796 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 168, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 84 140 274 41 105 169 297), lower := (rows 7 35 84 140 274 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 25 16 35 67 131 259), good := (rows 493 489 92 140 508 32 64 128 256) }] }

theorem u5796 : Upper (D 5) (R 5) [6,33,80,132,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5796
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5797 : Route 9 := (fun mask => (mask,id))

def c5797 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5797 : Upper (D 5) (R 5) [6,33,80,132,264] 13 := by
  apply FastRouting.sound _ _ [6,33,80,132,264] 13 (by decide) (choices 1) [1,2,8] r5797 c5797
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2297
  · exact u2298
  · exact u2299

def r5798 : Route 9 := (fun mask => (mask,id))

def c5798 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5798 : Upper (D 5) (R 5) [6,33,80,132,288] 13 := by
  apply FastRouting.sound _ _ [6,33,80,132,288] 13 (by decide) (choices 1) [1,2,8] r5798 c5798
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2300
  · exact u2301
  · exact u2302

def b5799 : PairBound 9 := { available := 268, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 35 84 168 19 300 332 396 268), lower := (rows 7 35 84 168 19 32 64 128 256), losses := [] }

theorem u5799 : Upper (D 5) (R 5) [6,33,80,160,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5799
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5800 : PairBound 9 := { available := 266, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 35 84 168 21 298 330 394 266), lower := (rows 7 35 84 168 21 32 64 128 256), losses := [] }

theorem u5800 : Upper (D 5) (R 5) [6,33,80,160,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5800
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5801 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 426, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 35 84 168 22 297 329 393 265), lower := (rows 7 35 84 168 22 32 64 128 256), losses := [] }

theorem u5801 : Upper (D 5) (R 5) [6,33,80,160,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5801
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5802 : PairBound 9 := { available := 270, camps := [{ cop := 0, region := 424, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 84 168 25 302 334 398 270), lower := (rows 7 35 84 168 25 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 27 16 33 65 129 257), good := (rows 494 490 92 168 508 32 64 128 256) }] }

theorem u5802 : Upper (D 5) (R 5) [6,33,80,160,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5802
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5803 : PairBound 9 := { available := 269, camps := [{ cop := 4, region := 325, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 35 84 168 26 301 333 397 269), lower := (rows 7 35 84 168 26 32 64 128 256), losses := [] }

theorem u5803 : Upper (D 5) (R 5) [6,33,80,160,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5803
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5804 : PairBound 9 := { available := 267, camps := [{ cop := 0, region := 426, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 35 84 168 28 299 331 395 267), lower := (rows 7 35 84 168 28 32 64 128 256), losses := [] }

theorem u5804 : Upper (D 5) (R 5) [6,33,80,160,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5804
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5805 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 168, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 84 168 273 46 78 142 270), lower := (rows 7 35 84 168 273 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 27 16 33 65 129 257), good := (rows 494 490 92 168 508 32 64 128 256) }] }

theorem u5805 : Upper (D 5) (R 5) [6,33,80,160,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5805
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5806 : Route 9 := (fun mask => (mask,id))

def c5806 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5806 : Upper (D 5) (R 5) [6,33,80,160,258] 13 := by
  apply FastRouting.sound _ _ [6,33,80,160,258] 13 (by decide) (choices 1) [1,4,8] r5806 c5806
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2303
  · exact u2304
  · exact u2305

def b5807 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 170, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 35 84 168 276 43 75 139 267), lower := (rows 7 35 84 168 276 32 64 128 256), losses := [] }

theorem u5807 : Upper (D 5) (R 5) [6,33,80,160,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5807
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5808 : Route 9 := (fun mask => (mask,id))

def c5808 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5808 : Upper (D 5) (R 5) [6,33,80,160,264] 13 := by
  apply FastRouting.sound _ _ [6,33,80,160,264] 13 (by decide) (choices 1) [1,2,4,8] r5808 c5808
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2306
  · exact u2307
  · exact u2308
  · exact u2309

def b5809 : PairBound 9 := { available := 44, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 35 84 392 19 44 108 172 300), lower := (rows 7 35 84 392 19 32 64 128 256), losses := [] }

theorem u5809 : Upper (D 5) (R 5) [6,33,80,384,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5809
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5810 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 35 84 392 21 42 106 170 298), lower := (rows 7 35 84 392 21 32 64 128 256), losses := [] }

theorem u5810 : Upper (D 5) (R 5) [6,33,80,384,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5810
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5811 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 426, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 35 84 392 22 41 105 169 297), lower := (rows 7 35 84 392 22 32 64 128 256), losses := [] }

theorem u5811 : Upper (D 5) (R 5) [6,33,80,384,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5811
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5812 : PairBound 9 := { available := 46, camps := [{ cop := 0, region := 424, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 84 392 25 46 110 174 302), lower := (rows 7 35 84 392 25 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 27 16 33 65 129 257), good := (rows 494 490 92 392 508 32 64 128 256) }] }

theorem u5812 : Upper (D 5) (R 5) [6,33,80,384,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5812
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5813 : Route 9 := (fun mask => (mask,id))

def c5813 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5813 : Upper (D 5) (R 5) [6,33,80,384,10] 13 := by
  apply FastRouting.sound _ _ [6,33,80,384,10] 13 (by decide) (choices 1) [1,4,8] r5813 c5813
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2310
  · exact u2311
  · exact u2312

def b5814 : PairBound 9 := { available := 43, camps := [{ cop := 0, region := 426, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 35 84 392 28 43 107 171 299), lower := (rows 7 35 84 392 28 32 64 128 256), losses := [] }

theorem u5814 : Upper (D 5) (R 5) [6,33,80,384,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5814
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5815 : PairBound 9 := { available := 14, camps := [{ cop := 1, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 35 84 392 49 46 78 142 270), lower := (rows 7 35 84 392 49 32 64 128 256), losses := [] }

theorem u5815 : Upper (D 5) (R 5) [6,33,80,384,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5815
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5816 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 35 84 392 50 45 77 141 269), lower := (rows 7 35 84 392 50 32 64 128 256), losses := [] }

theorem u5816 : Upper (D 5) (R 5) [6,33,80,384,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5816
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5817 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 426, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 35 84 392 52 43 75 139 267), lower := (rows 7 35 84 392 52 32 64 128 256), losses := [] }

theorem u5817 : Upper (D 5) (R 5) [6,33,80,384,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5817
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5818 : Route 9 := (fun mask => (mask,id))

def c5818 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5818 : Upper (D 5) (R 5) [6,33,80,384,40] 13 := by
  apply FastRouting.sound _ _ [6,33,80,384,40] 13 (by decide) (choices 1) [1,2,4,8] r5818 c5818
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2313
  · exact u2314
  · exact u2315
  · exact u2316

def b5819 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 24, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 35 196 25 22 296 360 424 296), lower := (rows 7 35 196 25 22 32 64 128 256), losses := [] }

theorem u5819 : Upper (D 5) (R 5) [6,33,192,17,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5819
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u5819
end Delivery.IrregularNine14.P05

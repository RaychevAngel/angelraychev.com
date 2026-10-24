import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0093
import IrregularNine14P05C0094
import IrregularNine14P05C0095
import IrregularNine14P05C0096

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r8820 : Route 9 := (fun mask => (mask,id))

def c8820 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 6 => 2 | 66 => 6 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8820 : Upper (D 5) (R 5) [6,24,192,36] 13 := by
  apply FastRouting.sound _ _ [6,24,192,36] 13 (by decide) (choices 2) [3,9,10,33,34,40,257,258,264,288] r8820 c8820
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5618
  · exact u5619
  · exact u5620
  · exact u5621
  · exact u5622
  · exact u5623
  · exact u5624
  · exact u5625
  · exact u5626
  · exact u5627

def r8821 : Route 9 := (fun mask => (mask,id))

def c8821 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8821 : Upper (D 5) (R 5) [6,24,192,257] 13 := by
  apply FastRouting.sound _ _ [6,24,192,257] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r8821 c8821
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5628
  · exact u5629
  · exact u5630
  · exact u5631
  · exact u5632
  · exact u5633
  · exact u5634
  · exact u5635
  · exact u5636
  · exact u5637

def r8822 : Route 9 := (fun mask => (mask,id))

def c8822 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8822 : Upper (D 5) (R 5) [6,24,192,258] 13 := by
  apply FastRouting.sound _ _ [6,24,192,258] 13 (by decide) (choices 2) [5,9,12,33,36,40] r8822 c8822
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5638
  · exact u5639
  · exact u5640
  · exact u5641
  · exact u5642
  · exact u5643

def r8823 : Route 9 := (fun mask => (mask,id))

def c8823 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8823 : Upper (D 5) (R 5) [6,24,192,260] 13 := by
  apply FastRouting.sound _ _ [6,24,192,260] 13 (by decide) (choices 2) [3,9,10,33,34,40] r8823 c8823
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5644
  · exact u5645
  · exact u5646
  · exact u5647
  · exact u5648
  · exact u5649

def r8824 : Route 9 := (fun mask => (mask,id))

def c8824 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8824 : Upper (D 5) (R 5) [6,24,192,288] 13 := by
  apply FastRouting.sound _ _ [6,24,192,288] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r8824 c8824
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5650
  · exact u5651
  · exact u5652
  · exact u5653
  · exact u5654
  · exact u5655
  · exact u5656
  · exact u5657
  · exact u5658
  · exact u5659

def b8825 : PairBound 9 := { available := 460, camps := [{ cop := 5, region := 7, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 35 37 26 476 492 460 460 460), lower := (rows 7 35 37 26 16 32 64 128 256), losses := [] }

theorem u8825 : Upper (D 5) (R 5) [6,33,33,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8825
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8826 : PairBound 9 := { available := 412, camps := [{ cop := 5, region := 7, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 35 37 74 412 444 476 412 412), lower := (rows 7 35 37 74 16 32 64 128 256), losses := [] }

theorem u8826 : Upper (D 5) (R 5) [6,33,33,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8826
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8827 : PairBound 9 := { available := 398, camps := [{ cop := 5, region := 7, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 35 37 88 414 430 462 398 398), lower := (rows 7 35 37 88 16 32 64 128 256), losses := [] }

theorem u8827 : Upper (D 5) (R 5) [6,33,33,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8827
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8828 : PairBound 9 := { available := 286, camps := [{ cop := 5, region := 7, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 35 37 200 286 318 350 414 286), lower := (rows 7 35 37 200 16 32 64 128 256), losses := [] }

theorem u8828 : Upper (D 5) (R 5) [6,33,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8828
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8829 : PairBound 9 := { available := 460, camps := [{ cop := 2, region := 473, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 7 35 38 25 476 492 460 460 460), lower := (rows 7 35 38 25 16 32 64 128 256), losses := [] }

theorem u8829 : Upper (D 5) (R 5) [6,33,34,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8829
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8830 : PairBound 9 := { available := 412, camps := [{ cop := 2, region := 473, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 7 35 38 73 412 444 476 412 412), lower := (rows 7 35 38 73 16 32 64 128 256), losses := [] }

theorem u8830 : Upper (D 5) (R 5) [6,33,34,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8830
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8831 : PairBound 9 := { available := 397, camps := [{ cop := 2, region := 473, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 7 35 38 88 413 429 461 397 397), lower := (rows 7 35 38 88 16 32 64 128 256), losses := [] }

theorem u8831 : Upper (D 5) (R 5) [6,33,34,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8831
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8832 : PairBound 9 := { available := 285, camps := [{ cop := 2, region := 473, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 7 35 38 200 285 317 349 413 285), lower := (rows 7 35 38 200 16 32 64 128 256), losses := [] }

theorem u8832 : Upper (D 5) (R 5) [6,33,34,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8832
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8833 : PairBound 9 := { available := 462, camps := [{ cop := 0, region := 472, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 35 44 25 478 494 462 462 462), lower := (rows 7 35 44 25 16 32 64 128 256), losses := [] }

theorem u8833 : Upper (D 5) (R 5) [6,33,40,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8833
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8834 : PairBound 9 := { available := 461, camps := [{ cop := 0, region := 472, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 35 44 26 477 493 461 461 461), lower := (rows 7 35 44 26 16 32 64 128 256), losses := [] }

theorem u8834 : Upper (D 5) (R 5) [6,33,40,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8834
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8835 : PairBound 9 := { available := 459, camps := [{ cop := 0, region := 472, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 35 44 28 475 491 459 459 459), lower := (rows 7 35 44 28 16 32 64 128 256), losses := [] }

theorem u8835 : Upper (D 5) (R 5) [6,33,40,20] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8835
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8836 : PairBound 9 := { available := 414, camps := [{ cop := 0, region := 472, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 35 44 73 414 446 478 414 414), lower := (rows 7 35 44 73 16 32 64 128 256), losses := [] }

theorem u8836 : Upper (D 5) (R 5) [6,33,40,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8836
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8837 : PairBound 9 := { available := 413, camps := [{ cop := 0, region := 472, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 35 44 74 413 445 477 413 413), lower := (rows 7 35 44 74 16 32 64 128 256), losses := [] }

theorem u8837 : Upper (D 5) (R 5) [6,33,40,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8837
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8838 : PairBound 9 := { available := 411, camps := [{ cop := 0, region := 472, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 35 44 76 411 443 475 411 411), lower := (rows 7 35 44 76 16 32 64 128 256), losses := [] }

theorem u8838 : Upper (D 5) (R 5) [6,33,40,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8838
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8839 : PairBound 9 := { available := 399, camps := [{ cop := 0, region := 472, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 35 44 88 415 431 463 399 399), lower := (rows 7 35 44 88 16 32 64 128 256), losses := [] }

theorem u8839 : Upper (D 5) (R 5) [6,33,40,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8839
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8840 : PairBound 9 := { available := 287, camps := [{ cop := 0, region := 472, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 35 44 200 287 319 351 415 287), lower := (rows 7 35 44 200 16 32 64 128 256), losses := [] }

theorem u8840 : Upper (D 5) (R 5) [6,33,40,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8840
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8841 : PairBound 9 := { available := 398, camps := [{ cop := 0, region := 472, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 35 52 73 414 430 462 398 398), lower := (rows 7 35 52 73 16 32 64 128 256), losses := [] }

theorem u8841 : Upper (D 5) (R 5) [6,33,48,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8841
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8842 : PairBound 9 := { available := 397, camps := [{ cop := 0, region := 472, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 35 52 74 413 429 461 397 397), lower := (rows 7 35 52 74 16 32 64 128 256), losses := [] }

theorem u8842 : Upper (D 5) (R 5) [6,33,48,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8842
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8843 : PairBound 9 := { available := 395, camps := [{ cop := 0, region := 472, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 35 52 76 411 427 459 395 395), lower := (rows 7 35 52 76 16 32 64 128 256), losses := [] }

theorem u8843 : Upper (D 5) (R 5) [6,33,48,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8843
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8844 : PairBound 9 := { available := 271, camps := [{ cop := 0, region := 472, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 35 52 200 287 303 335 399 271), lower := (rows 7 35 52 200 16 32 64 128 256), losses := [] }

theorem u8844 : Upper (D 5) (R 5) [6,33,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8844
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8845 : PairBound 9 := { available := 440, camps := [{ cop := 3, region := 432, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 35 69 14 440 440 504 440 440), lower := (rows 7 35 69 14 16 32 64 128 256), losses := [] }

theorem u8845 : Upper (D 5) (R 5) [6,33,65,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8845
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8846 : PairBound 9 := { available := 428, camps := [{ cop := 0, region := 440, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 69 26 444 428 492 428 428), lower := (rows 7 35 69 26 16 32 64 128 256), losses := [] }

theorem u8846 : Upper (D 5) (R 5) [6,33,65,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8846
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8847 : PairBound 9 := { available := 426, camps := [{ cop := 0, region := 440, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 69 28 442 426 490 426 426), lower := (rows 7 35 69 28 16 32 64 128 256), losses := [] }

theorem u8847 : Upper (D 5) (R 5) [6,33,65,20] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8847
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8848 : PairBound 9 := { available := 410, camps := [{ cop := 0, region := 440, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 69 44 410 442 474 410 410), lower := (rows 7 35 69 44 16 32 64 128 256), losses := [] }

theorem u8848 : Upper (D 5) (R 5) [6,33,65,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8848
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8849 : PairBound 9 := { available := 398, camps := [{ cop := 0, region := 440, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 69 56 414 430 462 398 398), lower := (rows 7 35 69 56 16 32 64 128 256), losses := [] }

theorem u8849 : Upper (D 5) (R 5) [6,33,65,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8849
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8850 : PairBound 9 := { available := 316, camps := [{ cop := 0, region := 440, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 69 138 316 316 380 444 316), lower := (rows 7 35 69 138 16 32 64 128 256), losses := [] }

theorem u8850 : Upper (D 5) (R 5) [6,33,65,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8850
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8851 : PairBound 9 := { available := 314, camps := [{ cop := 0, region := 440, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 69 140 314 314 378 442 314), lower := (rows 7 35 69 140 16 32 64 128 256), losses := [] }

theorem u8851 : Upper (D 5) (R 5) [6,33,65,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8851
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8852 : PairBound 9 := { available := 302, camps := [{ cop := 0, region := 440, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 69 152 318 302 366 430 302), lower := (rows 7 35 69 152 16 32 64 128 256), losses := [] }

theorem u8852 : Upper (D 5) (R 5) [6,33,65,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8852
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8853 : PairBound 9 := { available := 286, camps := [{ cop := 0, region := 440, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 69 168 286 318 350 414 286), lower := (rows 7 35 69 168 16 32 64 128 256), losses := [] }

theorem u8853 : Upper (D 5) (R 5) [6,33,65,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8853
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8854 : PairBound 9 := { available := 62, camps := [{ cop := 0, region := 440, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 69 392 62 62 126 190 318), lower := (rows 7 35 69 392 16 32 64 128 256), losses := [] }

theorem u8854 : Upper (D 5) (R 5) [6,33,65,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8854
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8855 : PairBound 9 := { available := 428, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 35 70 25 444 428 492 428 428), lower := (rows 7 35 70 25 16 32 64 128 256), losses := [] }

theorem u8855 : Upper (D 5) (R 5) [6,33,66,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8855
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8856 : PairBound 9 := { available := 425, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 35 70 28 441 425 489 425 425), lower := (rows 7 35 70 28 16 32 64 128 256), losses := [] }

theorem u8856 : Upper (D 5) (R 5) [6,33,66,20] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8856
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8857 : PairBound 9 := { available := 409, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 35 70 44 409 441 473 409 409), lower := (rows 7 35 70 44 16 32 64 128 256), losses := [] }

theorem u8857 : Upper (D 5) (R 5) [6,33,66,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8857
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8858 : PairBound 9 := { available := 397, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 35 70 56 413 429 461 397 397), lower := (rows 7 35 70 56 16 32 64 128 256), losses := [] }

theorem u8858 : Upper (D 5) (R 5) [6,33,66,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8858
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8859 : PairBound 9 := { available := 316, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 35 70 137 316 316 380 444 316), lower := (rows 7 35 70 137 16 32 64 128 256), losses := [] }

theorem u8859 : Upper (D 5) (R 5) [6,33,66,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8859
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8860 : PairBound 9 := { available := 313, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 35 70 140 313 313 377 441 313), lower := (rows 7 35 70 140 16 32 64 128 256), losses := [] }

theorem u8860 : Upper (D 5) (R 5) [6,33,66,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8860
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8861 : PairBound 9 := { available := 301, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 35 70 152 317 301 365 429 301), lower := (rows 7 35 70 152 16 32 64 128 256), losses := [] }

theorem u8861 : Upper (D 5) (R 5) [6,33,66,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8861
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8862 : PairBound 9 := { available := 285, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 35 70 168 285 317 349 413 285), lower := (rows 7 35 70 168 16 32 64 128 256), losses := [] }

theorem u8862 : Upper (D 5) (R 5) [6,33,66,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8862
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8863 : PairBound 9 := { available := 61, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 35 70 392 61 61 125 189 317), lower := (rows 7 35 70 392 16 32 64 128 256), losses := [] }

theorem u8863 : Upper (D 5) (R 5) [6,33,66,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8863
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8864 : PairBound 9 := { available := 441, camps := [{ cop := 0, region := 8, targets := 1 },{ cop := 0, region := 8, targets := 32 }], pairs := [(3,0),(3,5)], upper := (rows 7 35 76 14 441 441 505 441 441), lower := (rows 7 35 76 14 16 32 64 128 256), losses := [] }

theorem u8864 : Upper (D 5) (R 5) [6,33,72,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8864
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8865 : Route 9 := (fun mask => match mask with | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8865 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 68 => 6 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u8865 : Upper (D 5) (R 5) [6,33,72,17] 13 := by
  apply FastRouting.sound _ _ [6,33,72,17] 13 (by decide) (choices 2) [6,10,12,34,36,40,130,132,136,160,384] r8865 c8865
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5660
  · exact u5661
  · exact u5662
  · exact u5663
  · exact u5664
  · exact u5665
  · exact u5666
  · exact u5667
  · exact u5668
  · exact u5669
  · exact u5670

def r8866 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8866 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u8866 : Upper (D 5) (R 5) [6,33,72,18] 13 := by
  apply FastRouting.sound _ _ [6,33,72,18] 13 (by decide) (choices 2) [5,9,12,33,36,40,129,132,136,160,384] r8866 c8866
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5671
  · exact u5672
  · exact u5673
  · exact u5674
  · exact u5675
  · exact u5676
  · exact u5677
  · exact u5678
  · exact u5679
  · exact u5680
  · exact u5681

def r8867 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8867 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 6 => 2 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u8867 : Upper (D 5) (R 5) [6,33,72,20] 13 := by
  apply FastRouting.sound _ _ [6,33,72,20] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160,384] r8867 c8867
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5682
  · exact u5683
  · exact u5684
  · exact u5685
  · exact u5686
  · exact u5687
  · exact u5688
  · exact u5689
  · exact u5690
  · exact u5691
  · exact u5692

def b8868 : PairBound 9 := { available := 414, camps := [{ cop := 1, region := 8, targets := 2 },{ cop := 1, region := 8, targets := 4 }], pairs := [(3,1),(3,2)], upper := (rows 7 35 76 41 414 446 478 414 414), lower := (rows 7 35 76 41 16 32 64 128 256), losses := [] }

theorem u8868 : Upper (D 5) (R 5) [6,33,72,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8868
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8869 : PairBound 9 := { available := 413, camps := [{ cop := 3, region := 469, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 35 76 42 413 445 477 413 413), lower := (rows 7 35 76 42 16 32 64 128 256), losses := [] }

theorem u8869 : Upper (D 5) (R 5) [6,33,72,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8869
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8870 : PairBound 9 := { available := 411, camps := [{ cop := 3, region := 3, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 35 76 44 411 443 475 411 411), lower := (rows 7 35 76 44 16 32 64 128 256), losses := [] }

theorem u8870 : Upper (D 5) (R 5) [6,33,72,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8870
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8871 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8871 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 34 => 5 | 66 => 6 | 36 => 5 | 68 => 6 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u8871 : Upper (D 5) (R 5) [6,33,72,48] 13 := by
  apply FastRouting.sound _ _ [6,33,72,48] 13 (by decide) (choices 2) [3,5,6,9,10,12,129,130,132,136,384] r8871 c8871
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5693
  · exact u5694
  · exact u5695
  · exact u5696
  · exact u5697
  · exact u5698
  · exact u5699
  · exact u5700
  · exact u5701
  · exact u5702
  · exact u5703

def r8872 : Route 9 := (fun mask => (mask,id))

def c8872 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8872 : Upper (D 5) (R 5) [6,33,72,129] 13 := by
  apply FastRouting.sound _ _ [6,33,72,129] 13 (by decide) (choices 2) [6,10,12,34,36,40,258,260,264,288] r8872 c8872
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5704
  · exact u5705
  · exact u5706
  · exact u5707
  · exact u5708
  · exact u5709
  · exact u5710
  · exact u5711
  · exact u5712
  · exact u5713

def r8873 : Route 9 := (fun mask => (mask,id))

def c8873 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8873 : Upper (D 5) (R 5) [6,33,72,130] 13 := by
  apply FastRouting.sound _ _ [6,33,72,130] 13 (by decide) (choices 2) [5,9,12,33,36,40,257,260,264,288] r8873 c8873
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5714
  · exact u5715
  · exact u5716
  · exact u5717
  · exact u5718
  · exact u5719
  · exact u5720
  · exact u5721
  · exact u5722
  · exact u5723

def r8874 : Route 9 := (fun mask => (mask,id))

def c8874 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 6 => 2 | 66 => 6 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8874 : Upper (D 5) (R 5) [6,33,72,132] 13 := by
  apply FastRouting.sound _ _ [6,33,72,132] 13 (by decide) (choices 2) [3,9,10,33,34,40,257,258,264,288] r8874 c8874
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5724
  · exact u5725
  · exact u5726
  · exact u5727
  · exact u5728
  · exact u5729
  · exact u5730
  · exact u5731
  · exact u5732
  · exact u5733

def r8875 : Route 9 := (fun mask => (mask,id))

def c8875 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8875 : Upper (D 5) (R 5) [6,33,72,144] 13 := by
  apply FastRouting.sound _ _ [6,33,72,144] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40,257,258,260,264,288] r8875 c8875
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5734
  · exact u5735
  · exact u5736
  · exact u5737
  · exact u5738
  · exact u5739
  · exact u5740
  · exact u5741
  · exact u5742
  · exact u5743
  · exact u5744
  · exact u5745
  · exact u5746
  · exact u5747
  · exact u5748

def r8876 : Route 9 := (fun mask => (mask,id))

def c8876 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8876 : Upper (D 5) (R 5) [6,33,72,160] 13 := by
  apply FastRouting.sound _ _ [6,33,72,160] 13 (by decide) (choices 2) [3,5,6,9,10,12,257,258,260,264] r8876 c8876
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5749
  · exact u5750
  · exact u5751
  · exact u5752
  · exact u5753
  · exact u5754
  · exact u5755
  · exact u5756
  · exact u5757
  · exact u5758

def r8877 : Route 9 := (fun mask => (mask,id))

def c8877 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8877 : Upper (D 5) (R 5) [6,33,72,384] 13 := by
  apply FastRouting.sound _ _ [6,33,72,384] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r8877 c8877
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5759
  · exact u5760
  · exact u5761
  · exact u5762
  · exact u5763
  · exact u5764
  · exact u5765
  · exact u5766
  · exact u5767
  · exact u5768

def b8878 : PairBound 9 := { available := 425, camps := [{ cop := 0, region := 8, targets := 1 },{ cop := 0, region := 8, targets := 32 }], pairs := [(3,0),(3,5)], upper := (rows 7 35 84 14 441 425 489 425 425), lower := (rows 7 35 84 14 16 32 64 128 256), losses := [] }

theorem u8878 : Upper (D 5) (R 5) [6,33,80,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8878
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8879 : PairBound 9 := { available := 398, camps := [{ cop := 1, region := 8, targets := 2 },{ cop := 1, region := 8, targets := 4 }], pairs := [(3,1),(3,2)], upper := (rows 7 35 84 41 414 430 462 398 398), lower := (rows 7 35 84 41 16 32 64 128 256), losses := [] }

theorem u8879 : Upper (D 5) (R 5) [6,33,80,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8879
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u8879
end Delivery.IrregularNine14.P05

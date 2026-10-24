import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0050
import IrregularNine14P05C0051

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6540 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 67 164 266 21 56 120 184 312), lower := (rows 7 67 164 266 21 32 64 128 256), losses := [] }

theorem u6540 : Upper (D 5) (R 5) [6,65,160,258,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6540
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6541 : PairBound 9 := { available := 60, camps := [{ cop := 4, region := 164, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 164 266 25 60 124 188 316), lower := (rows 7 67 164 266 25 32 64 128 256), losses := [] }

theorem u6541 : Upper (D 5) (R 5) [6,65,160,258,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6541
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6542 : Route 9 := (fun mask => (mask,id))

def c6542 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6542 : Upper (D 5) (R 5) [6,65,160,258,12] 13 := by
  apply FastRouting.sound _ _ [6,65,160,258,12] 13 (by decide) (choices 1) [1,8,16] r6542 c6542
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3022
  · exact u3023
  · exact u3024

def r6543 : Route 9 := (fun mask => (mask,id))

def c6543 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6543 : Upper (D 5) (R 5) [6,65,160,258,33] 13 := by
  apply FastRouting.sound _ _ [6,65,160,258,33] 13 (by decide) (choices 1) [4,8,16] r6543 c6543
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3025
  · exact u3026
  · exact u3027

def b6544 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 67 164 266 52 57 89 153 281), lower := (rows 7 67 164 266 52 32 64 128 256), losses := [] }

theorem u6544 : Upper (D 5) (R 5) [6,65,160,258,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6544
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6545 : Route 9 := (fun mask => (mask,id))

def c6545 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6545 : Upper (D 5) (R 5) [6,65,160,258,40] 13 := by
  apply FastRouting.sound _ _ [6,65,160,258,40] 13 (by decide) (choices 1) [1,4,8,16] r6545 c6545
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3028
  · exact u3029
  · exact u3030
  · exact u3031

def b6546 : PairBound 9 := { available := 56, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 164 268 19 56 120 184 312), lower := (rows 7 67 164 268 19 32 64 128 256), losses := [] }

theorem u6546 : Upper (D 5) (R 5) [6,65,160,260,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6546
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6547 : Route 9 := (fun mask => (mask,id))

def c6547 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6547 : Upper (D 5) (R 5) [6,65,160,260,9] 13 := by
  apply FastRouting.sound _ _ [6,65,160,260,9] 13 (by decide) (choices 1) [2,8,16] r6547 c6547
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3032
  · exact u3033
  · exact u3034

def r6548 : Route 9 := (fun mask => (mask,id))

def c6548 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6548 : Upper (D 5) (R 5) [6,65,160,260,10] 13 := by
  apply FastRouting.sound _ _ [6,65,160,260,10] 13 (by decide) (choices 1) [1,8,16] r6548 c6548
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3035
  · exact u3036
  · exact u3037

def r6549 : Route 9 := (fun mask => (mask,id))

def c6549 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6549 : Upper (D 5) (R 5) [6,65,160,260,33] 13 := by
  apply FastRouting.sound _ _ [6,65,160,260,33] 13 (by decide) (choices 1) [2,8,16] r6549 c6549
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3038
  · exact u3039
  · exact u3040

def r6550 : Route 9 := (fun mask => (mask,id))

def c6550 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6550 : Upper (D 5) (R 5) [6,65,160,260,34] 13 := by
  apply FastRouting.sound _ _ [6,65,160,260,34] 13 (by decide) (choices 1) [1,8,16] r6550 c6550
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3041
  · exact u3042
  · exact u3043

def r6551 : Route 9 := (fun mask => (mask,id))

def c6551 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6551 : Upper (D 5) (R 5) [6,65,160,260,40] 13 := by
  apply FastRouting.sound _ _ [6,65,160,260,40] 13 (by decide) (choices 1) [1,2,8,16] r6551 c6551
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3044
  · exact u3045
  · exact u3046
  · exact u3047

def b6552 : PairBound 9 := { available := 44, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 164 280 19 44 108 172 300), lower := (rows 7 67 164 280 19 32 64 128 256), losses := [] }

theorem u6552 : Upper (D 5) (R 5) [6,65,160,272,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6552
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6553 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 67 164 280 21 42 106 170 298), lower := (rows 7 67 164 280 21 32 64 128 256), losses := [] }

theorem u6553 : Upper (D 5) (R 5) [6,65,160,272,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6553
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6554 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 16, targets := 40 }], pairs := [(4,3),(4,5)], upper := (rows 7 67 164 280 22 41 105 169 297), lower := (rows 7 67 164 280 22 32 64 128 256), losses := [] }

theorem u6554 : Upper (D 5) (R 5) [6,65,160,272,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6554
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6555 : Route 9 := (fun mask => (mask,id))

def c6555 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6555 : Upper (D 5) (R 5) [6,65,160,272,9] 13 := by
  apply FastRouting.sound _ _ [6,65,160,272,9] 13 (by decide) (choices 1) [2,4,8] r6555 c6555
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3048
  · exact u3049
  · exact u3050

def r6556 : Route 9 := (fun mask => (mask,id))

def c6556 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6556 : Upper (D 5) (R 5) [6,65,160,272,10] 13 := by
  apply FastRouting.sound _ _ [6,65,160,272,10] 13 (by decide) (choices 1) [1,4,8] r6556 c6556
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3051
  · exact u3052
  · exact u3053

def r6557 : Route 9 := (fun mask => (mask,id))

def c6557 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6557 : Upper (D 5) (R 5) [6,65,160,272,12] 13 := by
  apply FastRouting.sound _ _ [6,65,160,272,12] 13 (by decide) (choices 1) [1,2,8] r6557 c6557
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3054
  · exact u3055
  · exact u3056

def r6558 : Route 9 := (fun mask => (mask,id))

def c6558 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6558 : Upper (D 5) (R 5) [6,65,160,272,33] 13 := by
  apply FastRouting.sound _ _ [6,65,160,272,33] 13 (by decide) (choices 1) [2,4,8] r6558 c6558
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3057
  · exact u3058
  · exact u3059

def r6559 : Route 9 := (fun mask => (mask,id))

def c6559 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6559 : Upper (D 5) (R 5) [6,65,160,272,34] 13 := by
  apply FastRouting.sound _ _ [6,65,160,272,34] 13 (by decide) (choices 1) [1,4,8] r6559 c6559
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3060
  · exact u3061
  · exact u3062

def b6560 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 67 164 280 52 43 75 139 267), lower := (rows 7 67 164 280 52 32 64 128 256), losses := [] }

theorem u6560 : Upper (D 5) (R 5) [6,65,160,272,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6560
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6561 : Route 9 := (fun mask => (mask,id))

def c6561 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6561 : Upper (D 5) (R 5) [6,65,160,272,40] 13 := by
  apply FastRouting.sound _ _ [6,65,160,272,40] 13 (by decide) (choices 1) [1,2,4,8] r6561 c6561
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3063
  · exact u3064
  · exact u3065
  · exact u3066

def b6562 : PairBound 9 := { available := 28, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 164 296 19 60 92 156 284), lower := (rows 7 67 164 296 19 32 64 128 256), losses := [] }

theorem u6562 : Upper (D 5) (R 5) [6,65,160,288,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6562
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6563 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 67 164 296 21 58 90 154 282), lower := (rows 7 67 164 296 21 32 64 128 256), losses := [] }

theorem u6563 : Upper (D 5) (R 5) [6,65,160,288,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6563
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6564 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 16, targets := 40 }], pairs := [(4,3),(4,5)], upper := (rows 7 67 164 296 22 57 89 153 281), lower := (rows 7 67 164 296 22 32 64 128 256), losses := [] }

theorem u6564 : Upper (D 5) (R 5) [6,65,160,288,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6564
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6565 : Route 9 := (fun mask => (mask,id))

def c6565 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6565 : Upper (D 5) (R 5) [6,65,160,288,9] 13 := by
  apply FastRouting.sound _ _ [6,65,160,288,9] 13 (by decide) (choices 1) [2,4,8,16] r6565 c6565
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3067
  · exact u3068
  · exact u3069
  · exact u3070

def r6566 : Route 9 := (fun mask => (mask,id))

def c6566 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6566 : Upper (D 5) (R 5) [6,65,160,288,10] 13 := by
  apply FastRouting.sound _ _ [6,65,160,288,10] 13 (by decide) (choices 1) [1,4,8,16] r6566 c6566
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3071
  · exact u3072
  · exact u3073
  · exact u3074

def b6567 : PairBound 9 := { available := 27, camps := [{ cop := 4, region := 67, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 67 164 296 28 59 91 155 283), lower := (rows 7 67 164 296 28 32 64 128 256), losses := [] }

theorem u6567 : Upper (D 5) (R 5) [6,65,160,288,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6567
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6568 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 24, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 67 388 25 22 40 104 168 296), lower := (rows 7 67 388 25 22 32 64 128 256), losses := [] }

theorem u6568 : Upper (D 5) (R 5) [6,65,384,17,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6568
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6569 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 24, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 7 67 388 25 26 44 108 172 300), lower := (rows 7 67 388 25 26 32 64 128 256), losses := [] }

theorem u6569 : Upper (D 5) (R 5) [6,65,384,17,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6569
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6570 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 24, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 67 388 25 28 42 106 170 298), lower := (rows 7 67 388 25 28 32 64 128 256), losses := [] }

theorem u6570 : Upper (D 5) (R 5) [6,65,384,17,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6570
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6571 : PairBound 9 := { available := 44, camps := [{ cop := 3, region := 420, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 388 25 50 44 108 172 300), lower := (rows 7 67 388 25 50 32 64 128 256), losses := [] }

theorem u6571 : Upper (D 5) (R 5) [6,65,384,17,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6571
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6572 : Route 9 := (fun mask => (mask,id))

def c6572 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6572 : Upper (D 5) (R 5) [6,65,384,17,36] 13 := by
  apply FastRouting.sound _ _ [6,65,384,17,36] 13 (by decide) (choices 1) [2,8] r6572 c6572
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3075
  · exact u3076

def r6573 : Route 9 := (fun mask => (mask,id))

def c6573 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6573 : Upper (D 5) (R 5) [6,65,384,17,40] 13 := by
  apply FastRouting.sound _ _ [6,65,384,17,40] 13 (by decide) (choices 1) [2,4,8] r6573 c6573
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3077
  · exact u3078
  · exact u3079

def b6574 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 67 388 26 21 40 104 168 296), lower := (rows 7 67 388 26 21 32 64 128 256), losses := [] }

theorem u6574 : Upper (D 5) (R 5) [6,65,384,18,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6574
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6575 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 24, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 7 67 388 26 25 44 108 172 300), lower := (rows 7 67 388 26 25 32 64 128 256), losses := [] }

theorem u6575 : Upper (D 5) (R 5) [6,65,384,18,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6575
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6576 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 24, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 67 388 26 28 41 105 169 297), lower := (rows 7 67 388 26 28 32 64 128 256), losses := [] }

theorem u6576 : Upper (D 5) (R 5) [6,65,384,18,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6576
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6577 : PairBound 9 := { available := 44, camps := [{ cop := 3, region := 420, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 388 26 49 44 108 172 300), lower := (rows 7 67 388 26 49 32 64 128 256), losses := [] }

theorem u6577 : Upper (D 5) (R 5) [6,65,384,18,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6577
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6578 : Route 9 := (fun mask => (mask,id))

def c6578 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6578 : Upper (D 5) (R 5) [6,65,384,18,36] 13 := by
  apply FastRouting.sound _ _ [6,65,384,18,36] 13 (by decide) (choices 1) [1,8] r6578 c6578
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3080
  · exact u3081

def r6579 : Route 9 := (fun mask => (mask,id))

def c6579 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6579 : Upper (D 5) (R 5) [6,65,384,18,40] 13 := by
  apply FastRouting.sound _ _ [6,65,384,18,40] 13 (by decide) (choices 1) [1,4,8] r6579 c6579
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3082
  · exact u3083
  · exact u3084

def b6580 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 388 28 19 40 104 168 296), lower := (rows 7 67 388 28 19 32 64 128 256), losses := [] }

theorem u6580 : Upper (D 5) (R 5) [6,65,384,20,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6580
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6581 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 24, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 67 388 28 25 42 106 170 298), lower := (rows 7 67 388 28 25 32 64 128 256), losses := [] }

theorem u6581 : Upper (D 5) (R 5) [6,65,384,20,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6581
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6582 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 24, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 67 388 28 26 41 105 169 297), lower := (rows 7 67 388 28 26 32 64 128 256), losses := [] }

theorem u6582 : Upper (D 5) (R 5) [6,65,384,20,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6582
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6583 : Route 9 := (fun mask => (mask,id))

def c6583 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6583 : Upper (D 5) (R 5) [6,65,384,20,33] 13 := by
  apply FastRouting.sound _ _ [6,65,384,20,33] 13 (by decide) (choices 1) [2,8] r6583 c6583
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3085
  · exact u3086

def r6584 : Route 9 := (fun mask => (mask,id))

def c6584 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6584 : Upper (D 5) (R 5) [6,65,384,20,34] 13 := by
  apply FastRouting.sound _ _ [6,65,384,20,34] 13 (by decide) (choices 1) [1,8] r6584 c6584
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3087
  · exact u3088

def r6585 : Route 9 := (fun mask => (mask,id))

def c6585 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6585 : Upper (D 5) (R 5) [6,65,384,20,40] 13 := by
  apply FastRouting.sound _ _ [6,65,384,20,40] 13 (by decide) (choices 1) [1,2,8] r6585 c6585
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3089
  · exact u3090
  · exact u3091

def b6586 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 16, targets := 40 }], pairs := [(4,3),(4,5)], upper := (rows 7 67 388 41 22 56 120 184 312), lower := (rows 7 67 388 41 22 32 64 128 256), losses := [] }

theorem u6586 : Upper (D 5) (R 5) [6,65,384,33,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6586
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6587 : PairBound 9 := { available := 60, camps := [{ cop := 4, region := 420, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 388 41 26 60 124 188 316), lower := (rows 7 67 388 41 26 32 64 128 256), losses := [] }

theorem u6587 : Upper (D 5) (R 5) [6,65,384,33,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6587
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6588 : Route 9 := (fun mask => (mask,id))

def c6588 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6588 : Upper (D 5) (R 5) [6,65,384,33,12] 13 := by
  apply FastRouting.sound _ _ [6,65,384,33,12] 13 (by decide) (choices 1) [2,8,16] r6588 c6588
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3092
  · exact u3093
  · exact u3094

def r6589 : Route 9 := (fun mask => (mask,id))

def c6589 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6589 : Upper (D 5) (R 5) [6,65,384,33,34] 13 := by
  apply FastRouting.sound _ _ [6,65,384,33,34] 13 (by decide) (choices 1) [4,8,16] r6589 c6589
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3095
  · exact u3096
  · exact u3097

def r6590 : Route 9 := (fun mask => (mask,id))

def c6590 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6590 : Upper (D 5) (R 5) [6,65,384,33,36] 13 := by
  apply FastRouting.sound _ _ [6,65,384,33,36] 13 (by decide) (choices 1) [2,8,16] r6590 c6590
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3098
  · exact u3099
  · exact u3100

def b6591 : PairBound 9 := { available := 30, camps := [{ cop := 3, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 67 388 41 56 62 94 158 286), lower := (rows 7 67 388 41 56 32 64 128 256), losses := [] }

theorem u6591 : Upper (D 5) (R 5) [6,65,384,33,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6591
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6592 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 67 388 42 21 56 120 184 312), lower := (rows 7 67 388 42 21 32 64 128 256), losses := [] }

theorem u6592 : Upper (D 5) (R 5) [6,65,384,34,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6592
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6593 : PairBound 9 := { available := 60, camps := [{ cop := 4, region := 420, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 388 42 25 60 124 188 316), lower := (rows 7 67 388 42 25 32 64 128 256), losses := [] }

theorem u6593 : Upper (D 5) (R 5) [6,65,384,34,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6593
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6594 : Route 9 := (fun mask => (mask,id))

def c6594 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6594 : Upper (D 5) (R 5) [6,65,384,34,12] 13 := by
  apply FastRouting.sound _ _ [6,65,384,34,12] 13 (by decide) (choices 1) [1,8,16] r6594 c6594
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3101
  · exact u3102
  · exact u3103

def r6595 : Route 9 := (fun mask => (mask,id))

def c6595 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6595 : Upper (D 5) (R 5) [6,65,384,34,33] 13 := by
  apply FastRouting.sound _ _ [6,65,384,34,33] 13 (by decide) (choices 1) [4,8,16] r6595 c6595
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3104
  · exact u3105
  · exact u3106

def r6596 : Route 9 := (fun mask => (mask,id))

def c6596 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6596 : Upper (D 5) (R 5) [6,65,384,34,36] 13 := by
  apply FastRouting.sound _ _ [6,65,384,34,36] 13 (by decide) (choices 1) [1,8,16] r6596 c6596
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3107
  · exact u3108
  · exact u3109

def b6597 : PairBound 9 := { available := 29, camps := [{ cop := 3, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 67 388 42 56 61 93 157 285), lower := (rows 7 67 388 42 56 32 64 128 256), losses := [] }

theorem u6597 : Upper (D 5) (R 5) [6,65,384,34,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6597
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6598 : PairBound 9 := { available := 56, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 388 44 19 56 120 184 312), lower := (rows 7 67 388 44 19 32 64 128 256), losses := [] }

theorem u6598 : Upper (D 5) (R 5) [6,65,384,36,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6598
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6599 : Route 9 := (fun mask => (mask,id))

def c6599 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6599 : Upper (D 5) (R 5) [6,65,384,36,9] 13 := by
  apply FastRouting.sound _ _ [6,65,384,36,9] 13 (by decide) (choices 1) [2,8,16] r6599 c6599
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3110
  · exact u3111
  · exact u3112

#print axioms u6599
end Delivery.IrregularNine14.P05

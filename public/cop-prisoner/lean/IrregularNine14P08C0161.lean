import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0042
import IrregularNine14P08C0043

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b9660 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 24, targets := 64 }], pairs := [(3,6)], upper := (rows 35 262 76 56 49 225 193 193 449), lower := (rows 35 262 76 56 49 32 64 128 256), losses := [] }

theorem u9660 : Upper (D 8) (R 8) [34,260,72,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9660 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9661 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 76 56 81 161 225 161 417), lower := (rows 35 262 76 56 81 32 64 128 256), losses := [] }

theorem u9661 : Upper (D 8) (R 8) [34,260,72,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9661 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9662 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 35 262 76 56 112 161 193 129 385), lower := (rows 35 262 76 56 112 32 64 128 256), losses := [] }

theorem u9662 : Upper (D 8) (R 8) [34,260,72,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9662 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9663 : Route 9 := (fun mask => (mask,id))

def c9663 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u9663 : Upper (D 8) (R 8) [34,260,72,48,129] 13 := by
  apply FastRouting.sound _ _ [34,260,72,48,129] 13 (by decide) (choices 1) [1,64,128] r9663 c9663
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2529
  · exact u2530
  · exact u2531

def b9664 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 262 76 56 176 225 193 193 449), lower := (rows 35 262 76 56 176 32 64 128 256), losses := [] }

theorem u9664 : Upper (D 8) (R 8) [34,260,72,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9664 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9665 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 76 56 208 161 225 161 417), lower := (rows 35 262 76 56 208 32 64 128 256), losses := [] }

theorem u9665 : Upper (D 8) (R 8) [34,260,72,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9665 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9666 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 35 262 76 137 49 240 240 240 496), lower := (rows 35 262 76 137 49 32 64 128 256), losses := [] }

theorem u9666 : Upper (D 8) (R 8) [34,260,72,129,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9666 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9667 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 35 262 76 137 81 176 240 176 432), lower := (rows 35 262 76 137 81 32 64 128 256), losses := [] }

theorem u9667 : Upper (D 8) (R 8) [34,260,72,129,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9667 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9668 : Route 9 := (fun mask => (mask,id))

def c9668 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9668 : Upper (D 8) (R 8) [34,260,72,129,96] 13 := by
  apply FastRouting.sound _ _ [34,260,72,129,96] 13 (by decide) (choices 1) [1,16,128] r9668 c9668
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2532
  · exact u2533
  · exact u2534

def b9669 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 35 262 76 137 145 112 112 240 368), lower := (rows 35 262 76 137 145 32 64 128 256), losses := [] }

theorem u9669 : Upper (D 8) (R 8) [34,260,72,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9669 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9670 : Route 9 := (fun mask => (mask,id))

def c9670 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9670 : Upper (D 8) (R 8) [34,260,72,129,160] 13 := by
  apply FastRouting.sound _ _ [34,260,72,129,160] 13 (by decide) (choices 1) [1,16,64] r9670 c9670
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2535
  · exact u2536
  · exact u2537

def r9671 : Route 9 := (fun mask => (mask,id))

def c9671 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9671 : Upper (D 8) (R 8) [34,260,72,129,192] 13 := by
  apply FastRouting.sound _ _ [34,260,72,129,192] 13 (by decide) (choices 1) [1,16] r9671 c9671
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2538
  · exact u2539

def b9672 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 35 262 76 152 49 225 225 225 481), lower := (rows 35 262 76 152 49 32 64 128 256), losses := [] }

theorem u9672 : Upper (D 8) (R 8) [34,260,72,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9672 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9673 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 76 152 81 161 225 161 417), lower := (rows 35 262 76 152 81 32 64 128 256), losses := [] }

theorem u9673 : Upper (D 8) (R 8) [34,260,72,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9673 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9674 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 76 152 112 161 225 161 417), lower := (rows 35 262 76 152 112 32 64 128 256), losses := [] }

theorem u9674 : Upper (D 8) (R 8) [34,260,72,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9674 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9675 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 262 76 152 145 97 97 225 353), lower := (rows 35 262 76 152 145 32 64 128 256), losses := [] }

theorem u9675 : Upper (D 8) (R 8) [34,260,72,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9675 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9676 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 262 76 152 176 97 97 225 353), lower := (rows 35 262 76 152 176 32 64 128 256), losses := [] }

theorem u9676 : Upper (D 8) (R 8) [34,260,72,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9676 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9677 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 35 262 76 152 208 33 97 161 289), lower := (rows 35 262 76 152 208 32 64 128 256), losses := [] }

theorem u9677 : Upper (D 8) (R 8) [34,260,72,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9677 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9678 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 35 262 76 168 49 241 209 209 465), lower := (rows 35 262 76 168 49 32 64 128 256), losses := [] }

theorem u9678 : Upper (D 8) (R 8) [34,260,72,160,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9678 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9679 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 35 262 76 168 81 177 241 177 433), lower := (rows 35 262 76 168 81 32 64 128 256), losses := [] }

theorem u9679 : Upper (D 8) (R 8) [34,260,72,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9679 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9680 : Route 9 := (fun mask => (mask,id))

def c9680 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9680 : Upper (D 8) (R 8) [34,260,72,160,96] 13 := by
  apply FastRouting.sound _ _ [34,260,72,160,96] 13 (by decide) (choices 1) [1,16,128] r9680 c9680
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2540
  · exact u2541
  · exact u2542

def r9681 : Route 9 := (fun mask => (mask,id))

def c9681 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9681 : Upper (D 8) (R 8) [34,260,72,160,129] 13 := by
  apply FastRouting.sound _ _ [34,260,72,160,129] 13 (by decide) (choices 1) [1,16,64] r9681 c9681
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2543
  · exact u2544
  · exact u2545

def b9682 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 262 76 168 176 113 81 209 337), lower := (rows 35 262 76 168 176 32 64 128 256), losses := [] }

theorem u9682 : Upper (D 8) (R 8) [34,260,72,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9682 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9683 : Route 9 := (fun mask => (mask,id))

def c9683 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9683 : Upper (D 8) (R 8) [34,260,72,160,192] 13 := by
  apply FastRouting.sound _ _ [34,260,72,160,192] 13 (by decide) (choices 1) [1,16] r9683 c9683
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2546
  · exact u2547

def b9684 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 35 262 100 25 25 224 224 224 480), lower := (rows 35 262 100 25 25 32 64 128 256), losses := [] }

theorem u9684 : Upper (D 8) (R 8) [34,260,96,17,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9684 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9685 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 24, targets := 64 }], pairs := [(3,6)], upper := (rows 35 262 100 25 49 232 200 200 456), lower := (rows 35 262 100 25 49 32 64 128 256), losses := [] }

theorem u9685 : Upper (D 8) (R 8) [34,260,96,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9685 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9686 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 24, targets := 64 }], pairs := [(3,6)], upper := (rows 35 262 100 25 56 225 193 193 449), lower := (rows 35 262 100 25 56 32 64 128 256), losses := [] }

theorem u9686 : Upper (D 8) (R 8) [34,260,96,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9686 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9687 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 486, targets := 1 }], pairs := [(1,0)], upper := (rows 35 262 100 25 81 168 232 168 424), lower := (rows 35 262 100 25 81 32 64 128 256), losses := [] }

theorem u9687 : Upper (D 8) (R 8) [34,260,96,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9687 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9688 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 387, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 100 25 88 161 225 161 417), lower := (rows 35 262 100 25 88 32 64 128 256), losses := [] }

theorem u9688 : Upper (D 8) (R 8) [34,260,96,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9688 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9689 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 262 100 25 112 169 201 137 393), lower := (rows 35 262 100 25 112 32 64 128 256), losses := [] }

theorem u9689 : Upper (D 8) (R 8) [34,260,96,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9689 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9690 : PairBound 9 := { available := 232, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 262 100 25 145 232 232 232 488), lower := (rows 35 262 100 25 145 32 64 128 256), losses := [] }

theorem u9690 : Upper (D 8) (R 8) [34,260,96,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9690 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9691 : Route 9 := (fun mask => (mask,id))

def c9691 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u9691 : Upper (D 8) (R 8) [34,260,96,17,136] 13 := by
  apply FastRouting.sound _ _ [34,260,96,17,136] 13 (by decide) (choices 1) [1,64,128] r9691 c9691
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2548
  · exact u2549
  · exact u2550

def r9692 : Route 9 := (fun mask => (mask,id))

def c9692 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u9692 : Upper (D 8) (R 8) [34,260,96,17,160] 13 := by
  apply FastRouting.sound _ _ [34,260,96,17,160] 13 (by decide) (choices 1) [1,8,64,128] r9692 c9692
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2551
  · exact u2552
  · exact u2553
  · exact u2554

def r9693 : Route 9 := (fun mask => (mask,id))

def c9693 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9693 : Upper (D 8) (R 8) [34,260,96,17,192] 13 := by
  apply FastRouting.sound _ _ [34,260,96,17,192] 13 (by decide) (choices 1) [1,8,128] r9693 c9693
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2555
  · exact u2556
  · exact u2557

def b9694 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 262 100 41 88 177 209 145 401), lower := (rows 35 262 100 41 88 32 64 128 256), losses := [] }

theorem u9694 : Upper (D 8) (R 8) [34,260,96,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9694 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9695 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 262 100 41 145 248 216 216 472), lower := (rows 35 262 100 41 145 32 64 128 256), losses := [] }

theorem u9695 : Upper (D 8) (R 8) [34,260,96,33,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9695 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9696 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 262 100 41 152 241 209 209 465), lower := (rows 35 262 100 41 152 32 64 128 256), losses := [] }

theorem u9696 : Upper (D 8) (R 8) [34,260,96,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9696 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9697 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 262 100 41 208 185 217 153 409), lower := (rows 35 262 100 41 208 32 64 128 256), losses := [] }

theorem u9697 : Upper (D 8) (R 8) [34,260,96,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9697 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9698 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 35 262 100 56 81 169 201 137 393), lower := (rows 35 262 100 56 81 32 64 128 256), losses := [] }

theorem u9698 : Upper (D 8) (R 8) [34,260,96,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9698 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9699 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 35 262 100 56 88 161 193 129 385), lower := (rows 35 262 100 56 88 32 64 128 256), losses := [] }

theorem u9699 : Upper (D 8) (R 8) [34,260,96,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9699 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9700 : Route 9 := (fun mask => (mask,id))

def c9700 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u9700 : Upper (D 8) (R 8) [34,260,96,48,129] 13 := by
  apply FastRouting.sound _ _ [34,260,96,48,129] 13 (by decide) (choices 1) [1,8,64,128] r9700 c9700
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2558
  · exact u2559
  · exact u2560
  · exact u2561

def r9701 : Route 9 := (fun mask => (mask,id))

def c9701 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u9701 : Upper (D 8) (R 8) [34,260,96,48,136] 13 := by
  apply FastRouting.sound _ _ [34,260,96,48,136] 13 (by decide) (choices 1) [1,64,128] r9701 c9701
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2562
  · exact u2563
  · exact u2564

def r9702 : Route 9 := (fun mask => (mask,id))

def c9702 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9702 : Upper (D 8) (R 8) [34,260,96,48,192] 13 := by
  apply FastRouting.sound _ _ [34,260,96,48,192] 13 (by decide) (choices 1) [1,8,128] r9702 c9702
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2565
  · exact u2566
  · exact u2567

def b9703 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 35 262 100 73 145 184 248 184 440), lower := (rows 35 262 100 73 145 32 64 128 256), losses := [] }

theorem u9703 : Upper (D 8) (R 8) [34,260,96,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9703 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9704 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 35 262 100 73 152 177 241 177 433), lower := (rows 35 262 100 73 152 32 64 128 256), losses := [] }

theorem u9704 : Upper (D 8) (R 8) [34,260,96,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9704 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9705 : PairBound 9 := { available := 153, camps := [{ cop := 3, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 35 262 100 73 176 185 217 153 409), lower := (rows 35 262 100 73 176 32 64 128 256), losses := [] }

theorem u9705 : Upper (D 8) (R 8) [34,260,96,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9705 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9706 : Route 9 := (fun mask => (mask,id))

def c9706 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9706 : Upper (D 8) (R 8) [34,260,96,80,129] 13 := by
  apply FastRouting.sound _ _ [34,260,96,80,129] 13 (by decide) (choices 1) [1,8,128] r9706 c9706
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2568
  · exact u2569
  · exact u2570

def b9707 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 387, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 100 88 152 161 225 161 417), lower := (rows 35 262 100 88 152 32 64 128 256), losses := [] }

theorem u9707 : Upper (D 8) (R 8) [34,260,96,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9707 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9708 : Route 9 := (fun mask => (mask,id))

def c9708 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9708 : Upper (D 8) (R 8) [34,260,96,80,160] 13 := by
  apply FastRouting.sound _ _ [34,260,96,80,160] 13 (by decide) (choices 1) [1,8,128] r9708 c9708
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2571
  · exact u2572
  · exact u2573

def b9709 : PairBound 9 := { available := 153, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 262 100 104 145 185 217 153 409), lower := (rows 35 262 100 104 145 32 64 128 256), losses := [] }

theorem u9709 : Upper (D 8) (R 8) [34,260,96,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9709 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9710 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 262 100 104 152 177 209 145 401), lower := (rows 35 262 100 104 152 32 64 128 256), losses := [] }

theorem u9710 : Upper (D 8) (R 8) [34,260,96,96,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9710 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9711 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 35 262 100 137 145 120 120 248 376), lower := (rows 35 262 100 137 145 32 64 128 256), losses := [] }

theorem u9711 : Upper (D 8) (R 8) [34,260,96,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9711 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9712 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 262 100 137 152 113 113 241 369), lower := (rows 35 262 100 137 152 32 64 128 256), losses := [] }

theorem u9712 : Upper (D 8) (R 8) [34,260,96,129,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9712 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9713 : Route 9 := (fun mask => (mask,id))

def c9713 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9713 : Upper (D 8) (R 8) [34,260,96,129,160] 13 := by
  apply FastRouting.sound _ _ [34,260,96,129,160] 13 (by decide) (choices 1) [1,8,16,64] r9713 c9713
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2574
  · exact u2575
  · exact u2576
  · exact u2577

def r9714 : Route 9 := (fun mask => (mask,id))

def c9714 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9714 : Upper (D 8) (R 8) [34,260,96,129,192] 13 := by
  apply FastRouting.sound _ _ [34,260,96,129,192] 13 (by decide) (choices 1) [1,8,16] r9714 c9714
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2578
  · exact u2579
  · exact u2580

def b9715 : PairBound 9 := { available := 97, camps := [{ cop := 7, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 35 262 100 152 152 97 97 225 353), lower := (rows 35 262 100 152 152 32 64 128 256), losses := [] }

theorem u9715 : Upper (D 8) (R 8) [34,260,96,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9715 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9716 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 262 100 152 176 105 73 201 329), lower := (rows 35 262 100 152 176 32 64 128 256), losses := [] }

theorem u9716 : Upper (D 8) (R 8) [34,260,96,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9716 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9717 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 262 100 152 208 41 105 169 297), lower := (rows 35 262 100 152 208 32 64 128 256), losses := [] }

theorem u9717 : Upper (D 8) (R 8) [34,260,96,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9717 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9718 : Route 9 := (fun mask => (mask,id))

def c9718 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9718 : Upper (D 8) (R 8) [34,260,96,160,192] 13 := by
  apply FastRouting.sound _ _ [34,260,96,160,192] 13 (by decide) (choices 1) [1,8,16] r9718 c9718
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2581
  · exact u2582
  · exact u2583

def b9719 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 35 262 196 25 25 224 224 224 480), lower := (rows 35 262 196 25 25 32 64 128 256), losses := [] }

theorem u9719 : Upper (D 8) (R 8) [34,260,192,17,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9719 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u9719
end Delivery.IrregularNine14.P08

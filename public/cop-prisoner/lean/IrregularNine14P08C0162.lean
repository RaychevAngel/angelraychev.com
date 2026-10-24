import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0043

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b9720 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 24, targets := 64 }], pairs := [(3,6)], upper := (rows 35 262 196 25 49 232 232 232 488), lower := (rows 35 262 196 25 49 32 64 128 256), losses := [] }

theorem u9720 : Upper (D 8) (R 8) [34,260,192,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9720 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9721 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 24, targets := 64 }], pairs := [(3,6)], upper := (rows 35 262 196 25 56 225 225 225 481), lower := (rows 35 262 196 25 56 32 64 128 256), losses := [] }

theorem u9721 : Upper (D 8) (R 8) [34,260,192,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9721 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9722 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 486, targets := 1 }], pairs := [(1,0)], upper := (rows 35 262 196 25 81 168 232 168 424), lower := (rows 35 262 196 25 81 32 64 128 256), losses := [] }

theorem u9722 : Upper (D 8) (R 8) [34,260,192,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9722 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9723 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 291, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 196 25 88 161 225 161 417), lower := (rows 35 262 196 25 88 32 64 128 256), losses := [] }

theorem u9723 : Upper (D 8) (R 8) [34,260,192,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9723 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9724 : Route 9 := (fun mask => (mask,id))

def c9724 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9724 : Upper (D 8) (R 8) [34,260,192,17,96] 13 := by
  apply FastRouting.sound _ _ [34,260,192,17,96] 13 (by decide) (choices 1) [1,8,128] r9724 c9724
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2584
  · exact u2585
  · exact u2586

def b9725 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 262 196 25 208 41 105 169 297), lower := (rows 35 262 196 25 208 32 64 128 256), losses := [] }

theorem u9725 : Upper (D 8) (R 8) [34,260,192,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9725 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9726 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 262 196 41 56 241 209 209 465), lower := (rows 35 262 196 41 56 32 64 128 256), losses := [] }

theorem u9726 : Upper (D 8) (R 8) [34,260,192,33,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9726 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9727 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 262 196 41 88 177 241 177 433), lower := (rows 35 262 196 41 88 32 64 128 256), losses := [] }

theorem u9727 : Upper (D 8) (R 8) [34,260,192,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9727 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9728 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 262 196 41 112 185 217 153 409), lower := (rows 35 262 196 41 112 32 64 128 256), losses := [] }

theorem u9728 : Upper (D 8) (R 8) [34,260,192,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9728 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9729 : PairBound 9 := { available := 193, camps := [{ cop := 5, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 35 262 196 56 56 225 193 193 449), lower := (rows 35 262 196 56 56 32 64 128 256), losses := [] }

theorem u9729 : Upper (D 8) (R 8) [34,260,192,48,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9729 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9730 : PairBound 9 := { available := 169, camps := [{ cop := 4, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 35 262 196 56 81 169 233 169 425), lower := (rows 35 262 196 56 81 32 64 128 256), losses := [] }

theorem u9730 : Upper (D 8) (R 8) [34,260,192,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9730 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9731 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 291, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 196 56 88 161 225 161 417), lower := (rows 35 262 196 56 88 32 64 128 256), losses := [] }

theorem u9731 : Upper (D 8) (R 8) [34,260,192,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9731 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9732 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 262 196 56 112 169 201 137 393), lower := (rows 35 262 196 56 112 32 64 128 256), losses := [] }

theorem u9732 : Upper (D 8) (R 8) [34,260,192,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9732 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9733 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 262 196 56 208 41 105 169 297), lower := (rows 35 262 196 56 208 32 64 128 256), losses := [] }

theorem u9733 : Upper (D 8) (R 8) [34,260,192,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9733 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9734 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 35 262 196 73 152 49 113 177 305), lower := (rows 35 262 196 73 152 32 64 128 256), losses := [] }

theorem u9734 : Upper (D 8) (R 8) [34,260,192,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9734 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9735 : PairBound 9 := { available := 57, camps := [{ cop := 3, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 35 262 196 73 176 57 121 185 313), lower := (rows 35 262 196 73 176 32 64 128 256), losses := [] }

theorem u9735 : Upper (D 8) (R 8) [34,260,192,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9735 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9736 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 35 262 196 88 152 33 97 161 289), lower := (rows 35 262 196 88 152 32 64 128 256), losses := [] }

theorem u9736 : Upper (D 8) (R 8) [34,260,192,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9736 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9737 : Route 9 := (fun mask => (mask,id))

def c9737 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9737 : Upper (D 8) (R 8) [34,260,192,80,160] 13 := by
  apply FastRouting.sound _ _ [34,260,192,80,160] 13 (by decide) (choices 1) [1,8] r9737 c9737
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2587
  · exact u2588

theorem m9738_16 : Upper (D 8) (R 8) [34,260,192,96,160,16] 13 :=
  permutation_upper _ _ _ [34,260,192,96,160,8] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2590

def r9738 : Route 9 := (fun mask => (mask,id))

def c9738 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9738 : Upper (D 8) (R 8) [34,260,192,96,160] 13 := by
  apply FastRouting.sound _ _ [34,260,192,96,160] 13 (by decide) (choices 1) [1,8,16] r9738 c9738
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2589
  · exact u2590
  · exact m9738_16

def b9739 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 322 13 13 112 176 240 176 432), lower := (rows 35 322 13 13 112 32 64 128 256), losses := [] }

theorem u9739 : Upper (D 8) (R 8) [34,320,9,5,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9739 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9740 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 322 13 13 176 240 240 240 496), lower := (rows 35 322 13 13 176 32 64 128 256), losses := [] }

theorem u9740 : Upper (D 8) (R 8) [34,320,9,5,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9740 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9741 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 322 13 13 208 176 240 176 432), lower := (rows 35 322 13 13 208 32 64 128 256), losses := [] }

theorem u9741 : Upper (D 8) (R 8) [34,320,9,5,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9741 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9742 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 28, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 13 25 52 224 224 224 480), lower := (rows 35 322 13 25 52 32 64 128 256), losses := [] }

theorem u9742 : Upper (D 8) (R 8) [34,320,9,17,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9742 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9743 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 482, targets := 1 }], pairs := [(1,0)], upper := (rows 35 322 13 25 84 160 224 160 416), lower := (rows 35 322 13 25 84 32 64 128 256), losses := [] }

theorem u9743 : Upper (D 8) (R 8) [34,320,9,17,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9743 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9744 : PairBound 9 := { available := 164, camps := [{ cop := 2, region := 482, targets := 1 }], pairs := [(1,0)], upper := (rows 35 322 13 25 112 164 228 164 420), lower := (rows 35 322 13 25 112 32 64 128 256), losses := [] }

theorem u9744 : Upper (D 8) (R 8) [34,320,9,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9744 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9745 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 322 13 25 148 224 224 224 480), lower := (rows 35 322 13 25 148 32 64 128 256), losses := [] }

theorem u9745 : Upper (D 8) (R 8) [34,320,9,17,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9745 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9746 : PairBound 9 := { available := 228, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 322 13 25 176 228 228 228 484), lower := (rows 35 322 13 25 176 32 64 128 256), losses := [] }

theorem u9746 : Upper (D 8) (R 8) [34,320,9,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9746 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9747 : PairBound 9 := { available := 164, camps := [{ cop := 2, region := 482, targets := 1 }], pairs := [(1,0)], upper := (rows 35 322 13 25 208 164 228 164 420), lower := (rows 35 322 13 25 208 32 64 128 256), losses := [] }

theorem u9747 : Upper (D 8) (R 8) [34,320,9,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9747 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9748 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 28, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 13 28 49 224 224 224 480), lower := (rows 35 322 13 28 49 32 64 128 256), losses := [] }

theorem u9748 : Upper (D 8) (R 8) [34,320,9,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9748 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9749 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 322 13 28 81 160 224 160 416), lower := (rows 35 322 13 28 81 32 64 128 256), losses := [] }

theorem u9749 : Upper (D 8) (R 8) [34,320,9,20,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9749 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9750 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 322 13 28 112 161 225 161 417), lower := (rows 35 322 13 28 112 32 64 128 256), losses := [] }

theorem u9750 : Upper (D 8) (R 8) [34,320,9,20,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9750 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9751 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 322 13 28 145 224 224 224 480), lower := (rows 35 322 13 28 145 32 64 128 256), losses := [] }

theorem u9751 : Upper (D 8) (R 8) [34,320,9,20,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9751 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9752 : Route 9 := (fun mask => (mask,id))

def c9752 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u9752 : Upper (D 8) (R 8) [34,320,9,20,160] 13 := by
  apply FastRouting.sound _ _ [34,320,9,20,160] 13 (by decide) (choices 1) [1,64,128] r9752 c9752
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2591
  · exact u2592
  · exact u2593

def b9753 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 322 13 28 208 161 225 161 417), lower := (rows 35 322 13 28 208 32 64 128 256), losses := [] }

theorem u9753 : Upper (D 8) (R 8) [34,320,9,20,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9753 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9754 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 13 41 52 240 208 208 464), lower := (rows 35 322 13 41 52 32 64 128 256), losses := [] }

theorem u9754 : Upper (D 8) (R 8) [34,320,9,33,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9754 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9755 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 13 41 84 176 240 176 432), lower := (rows 35 322 13 41 84 32 64 128 256), losses := [] }

theorem u9755 : Upper (D 8) (R 8) [34,320,9,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9755 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9756 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 13 41 112 180 212 148 404), lower := (rows 35 322 13 41 112 32 64 128 256), losses := [] }

theorem u9756 : Upper (D 8) (R 8) [34,320,9,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9756 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9757 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 13 41 148 240 240 240 496), lower := (rows 35 322 13 41 148 32 64 128 256), losses := [] }

theorem u9757 : Upper (D 8) (R 8) [34,320,9,33,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9757 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9758 : PairBound 9 := { available := 212, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 13 41 176 244 212 212 468), lower := (rows 35 322 13 41 176 32 64 128 256), losses := [] }

theorem u9758 : Upper (D 8) (R 8) [34,320,9,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9758 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9759 : PairBound 9 := { available := 180, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 13 41 208 180 244 180 436), lower := (rows 35 322 13 41 208 32 64 128 256), losses := [] }

theorem u9759 : Upper (D 8) (R 8) [34,320,9,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9759 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9760 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 13 44 112 177 209 145 401), lower := (rows 35 322 13 44 112 32 64 128 256), losses := [] }

theorem u9760 : Upper (D 8) (R 8) [34,320,9,36,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9760 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9761 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 13 44 145 240 240 240 496), lower := (rows 35 322 13 44 145 32 64 128 256), losses := [] }

theorem u9761 : Upper (D 8) (R 8) [34,320,9,36,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9761 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9762 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 13 44 176 241 209 209 465), lower := (rows 35 322 13 44 176 32 64 128 256), losses := [] }

theorem u9762 : Upper (D 8) (R 8) [34,320,9,36,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9762 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9763 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 13 44 208 177 241 177 433), lower := (rows 35 322 13 44 208 32 64 128 256), losses := [] }

theorem u9763 : Upper (D 8) (R 8) [34,320,9,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9763 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9764 : PairBound 9 := { available := 196, camps := [{ cop := 0, region := 28, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 13 56 49 228 196 196 452), lower := (rows 35 322 13 56 49 32 64 128 256), losses := [] }

theorem u9764 : Upper (D 8) (R 8) [34,320,9,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9764 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9765 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 28, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 13 56 52 225 193 193 449), lower := (rows 35 322 13 56 52 32 64 128 256), losses := [] }

theorem u9765 : Upper (D 8) (R 8) [34,320,9,48,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9765 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9766 : PairBound 9 := { available := 164, camps := [{ cop := 4, region := 172, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 13 56 81 164 228 164 420), lower := (rows 35 322 13 56 81 32 64 128 256), losses := [] }

theorem u9766 : Upper (D 8) (R 8) [34,320,9,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9766 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9767 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 322 13 56 84 161 225 161 417), lower := (rows 35 322 13 56 84 32 64 128 256), losses := [] }

theorem u9767 : Upper (D 8) (R 8) [34,320,9,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9767 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9768 : PairBound 9 := { available := 133, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 322 13 56 112 165 197 133 389), lower := (rows 35 322 13 56 112 32 64 128 256), losses := [] }

theorem u9768 : Upper (D 8) (R 8) [34,320,9,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9768 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9769 : PairBound 9 := { available := 228, camps := [{ cop := 2, region := 482, targets := 1 }], pairs := [(1,0)], upper := (rows 35 322 13 56 145 228 228 228 484), lower := (rows 35 322 13 56 145 32 64 128 256), losses := [] }

theorem u9769 : Upper (D 8) (R 8) [34,320,9,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9769 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9770 : Route 9 := (fun mask => (mask,id))

def c9770 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u9770 : Upper (D 8) (R 8) [34,320,9,48,132] 13 := by
  apply FastRouting.sound _ _ [34,320,9,48,132] 13 (by decide) (choices 1) [1,64,128] r9770 c9770
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2594
  · exact u2595
  · exact u2596

def b9771 : PairBound 9 := { available := 197, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 322 13 56 176 229 197 197 453), lower := (rows 35 322 13 56 176 32 64 128 256), losses := [] }

theorem u9771 : Upper (D 8) (R 8) [34,320,9,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9771 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9772 : Route 9 := (fun mask => (mask,id))

def c9772 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9772 : Upper (D 8) (R 8) [34,320,9,48,192] 13 := by
  apply FastRouting.sound _ _ [34,320,9,48,192] 13 (by decide) (choices 1) [1,4,128] r9772 c9772
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2597
  · exact u2598
  · exact u2599

def b9773 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 498, targets := 1 }], pairs := [(1,0)], upper := (rows 35 322 13 73 52 176 240 176 432), lower := (rows 35 322 13 73 52 32 64 128 256), losses := [] }

theorem u9773 : Upper (D 8) (R 8) [34,320,9,65,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9773 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9774 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 498, targets := 1 }], pairs := [(1,0)], upper := (rows 35 322 13 73 148 176 240 176 432), lower := (rows 35 322 13 73 148 32 64 128 256), losses := [] }

theorem u9774 : Upper (D 8) (R 8) [34,320,9,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9774 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9775 : PairBound 9 := { available := 180, camps := [{ cop := 2, region := 498, targets := 1 }], pairs := [(1,0)], upper := (rows 35 322 13 73 176 180 244 180 436), lower := (rows 35 322 13 73 176 32 64 128 256), losses := [] }

theorem u9775 : Upper (D 8) (R 8) [34,320,9,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9775 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9776 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 35 322 13 76 145 176 240 176 432), lower := (rows 35 322 13 76 145 32 64 128 256), losses := [] }

theorem u9776 : Upper (D 8) (R 8) [34,320,9,68,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9776 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9777 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 35 322 13 76 176 177 241 177 433), lower := (rows 35 322 13 76 176 32 64 128 256), losses := [] }

theorem u9777 : Upper (D 8) (R 8) [34,320,9,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9777 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9778 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 322 13 88 52 161 225 161 417), lower := (rows 35 322 13 88 52 32 64 128 256), losses := [] }

theorem u9778 : Upper (D 8) (R 8) [34,320,9,80,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9778 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9779 : PairBound 9 := { available := 164, camps := [{ cop := 2, region := 482, targets := 1 }], pairs := [(1,0)], upper := (rows 35 322 13 88 145 164 228 164 420), lower := (rows 35 322 13 88 145 32 64 128 256), losses := [] }

theorem u9779 : Upper (D 8) (R 8) [34,320,9,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9779 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u9779
end Delivery.IrregularNine14.P08

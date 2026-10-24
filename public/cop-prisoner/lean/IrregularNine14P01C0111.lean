import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0048
import IrregularNine14P01C0049

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r6660 : Route 9 := (fun mask => (mask,id))

def c6660 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6660 : Upper (D 1) (R 1) [50,260,192,80] 13 := by
  apply FastRouting.sound _ _ [50,260,192,80] 13 (by decide) (choices 1) [1,2,8,32,128] r6660 c6660
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2924
  · exact u2925
  · exact u2926
  · exact u2927
  · exact u2928

def b6661 : PairBound 9 := { available := 59, camps := [{ cop := 2, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 51 262 196 200 59 59 123 187 315), lower := (rows 51 262 196 200 16 32 64 128 256), losses := [] }

theorem u6661 : Upper (D 1) (R 1) [50,260,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6661
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6662 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 322 7 28 248 232 232 232 488), lower := (rows 51 322 7 28 16 32 64 128 256), losses := [] }

theorem u6662 : Upper (D 1) (R 1) [50,320,3,20] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6662
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6663 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 51 322 7 76 184 184 248 184 440), lower := (rows 51 322 7 76 16 32 64 128 256), losses := [] }

theorem u6663 : Upper (D 1) (R 1) [50,320,3,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6663
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6664 : PairBound 9 := { available := 172, camps := [{ cop := 0, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 51 322 7 88 188 172 236 172 428), lower := (rows 51 322 7 88 16 32 64 128 256), losses := [] }

theorem u6664 : Upper (D 1) (R 1) [50,320,3,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6664
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6665 : PairBound 9 := { available := 248, camps := [{ cop := 0, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 51 322 7 140 248 248 248 248 504), lower := (rows 51 322 7 140 16 32 64 128 256), losses := [] }

theorem u6665 : Upper (D 1) (R 1) [50,320,3,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6665
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6666 : PairBound 9 := { available := 236, camps := [{ cop := 0, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 51 322 7 152 252 236 236 236 492), lower := (rows 51 322 7 152 16 32 64 128 256), losses := [] }

theorem u6666 : Upper (D 1) (R 1) [50,320,3,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6666
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6667 : PairBound 9 := { available := 188, camps := [{ cop := 0, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 51 322 7 200 188 188 252 188 444), lower := (rows 51 322 7 200 16 32 64 128 256), losses := [] }

theorem u6667 : Upper (D 1) (R 1) [50,320,3,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6667
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6668 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 12, targets := 16 }], pairs := [(2,4)], upper := (rows 51 322 13 14 240 240 240 240 496), lower := (rows 51 322 13 14 16 32 64 128 256), losses := [] }

theorem u6668 : Upper (D 1) (R 1) [50,320,9,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6668
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6669 : PairBound 9 := { available := 228, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 51 322 13 26 244 228 228 228 484), lower := (rows 51 322 13 26 16 32 64 128 256), losses := [] }

theorem u6669 : Upper (D 1) (R 1) [50,320,9,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6669
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6670 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 12, targets := 2 }], pairs := [(2,1)], upper := (rows 51 322 13 28 242 226 226 226 482), lower := (rows 51 322 13 28 16 32 64 128 256), losses := [] }

theorem u6670 : Upper (D 1) (R 1) [50,320,9,20] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6670
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6671 : PairBound 9 := { available := 198, camps := [{ cop := 0, region := 12, targets := 2 }], pairs := [(2,1)], upper := (rows 51 322 13 56 214 230 198 198 454), lower := (rows 51 322 13 56 16 32 64 128 256), losses := [] }

theorem u6671 : Upper (D 1) (R 1) [50,320,9,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6671
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6672 : PairBound 9 := { available := 180, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 51 322 13 74 180 180 244 180 436), lower := (rows 51 322 13 74 16 32 64 128 256), losses := [] }

theorem u6672 : Upper (D 1) (R 1) [50,320,9,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6672
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6673 : PairBound 9 := { available := 178, camps := [{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 51 322 13 76 178 178 242 178 434), lower := (rows 51 322 13 76 16 32 64 128 256), losses := [] }

theorem u6673 : Upper (D 1) (R 1) [50,320,9,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6673
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6674 : PairBound 9 := { available := 166, camps := [{ cop := 2, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 51 322 13 88 182 166 230 166 422), lower := (rows 51 322 13 88 16 32 64 128 256), losses := [] }

theorem u6674 : Upper (D 1) (R 1) [50,320,9,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6674
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6675 : Route 9 := (fun mask => (mask,id))

def c6675 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6675 : Upper (D 1) (R 1) [50,320,9,130] 13 := by
  apply FastRouting.sound _ _ [50,320,9,130] 13 (by decide) (choices 1) [4,32,64,128] r6675 c6675
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2929
  · exact u2930
  · exact u2931
  · exact u2932

def r6676 : Route 9 := (fun mask => (mask,id))

def c6676 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6676 : Upper (D 1) (R 1) [50,320,9,132] 13 := by
  apply FastRouting.sound _ _ [50,320,9,132] 13 (by decide) (choices 1) [2,32,64,128] r6676 c6676
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2933
  · exact u2934
  · exact u2935
  · exact u2936

def b6677 : PairBound 9 := { available := 230, camps := [{ cop := 2, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 51 322 13 152 246 230 230 230 486), lower := (rows 51 322 13 152 16 32 64 128 256), losses := [] }

theorem u6677 : Upper (D 1) (R 1) [50,320,9,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6677
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6678 : Route 9 := (fun mask => (mask,id))

def c6678 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6678 : Upper (D 1) (R 1) [50,320,9,192] 13 := by
  apply FastRouting.sound _ _ [50,320,9,192] 13 (by decide) (choices 1) [2,4,32,128] r6678 c6678
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2937
  · exact u2938
  · exact u2939
  · exact u2940

def b6679 : PairBound 9 := { available := 228, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 51 322 14 25 244 228 228 228 484), lower := (rows 51 322 14 25 16 32 64 128 256), losses := [] }

theorem u6679 : Upper (D 1) (R 1) [50,320,10,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6679
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6680 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 51 322 14 28 241 225 225 225 481), lower := (rows 51 322 14 28 16 32 64 128 256), losses := [] }

theorem u6680 : Upper (D 1) (R 1) [50,320,10,20] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6680
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6681 : PairBound 9 := { available := 197, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 51 322 14 56 213 229 197 197 453), lower := (rows 51 322 14 56 16 32 64 128 256), losses := [] }

theorem u6681 : Upper (D 1) (R 1) [50,320,10,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6681
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6682 : PairBound 9 := { available := 180, camps := [{ cop := 2, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 51 322 14 73 180 180 244 180 436), lower := (rows 51 322 14 73 16 32 64 128 256), losses := [] }

theorem u6682 : Upper (D 1) (R 1) [50,320,10,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6682
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6683 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 12, targets := 16 }], pairs := [(2,4)], upper := (rows 51 322 14 76 177 177 241 177 433), lower := (rows 51 322 14 76 16 32 64 128 256), losses := [] }

theorem u6683 : Upper (D 1) (R 1) [50,320,10,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6683
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6684 : PairBound 9 := { available := 165, camps := [{ cop := 2, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 51 322 14 88 181 165 229 165 421), lower := (rows 51 322 14 88 16 32 64 128 256), losses := [] }

theorem u6684 : Upper (D 1) (R 1) [50,320,10,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6684
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6685 : Route 9 := (fun mask => (mask,id))

def c6685 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6685 : Upper (D 1) (R 1) [50,320,10,129] 13 := by
  apply FastRouting.sound _ _ [50,320,10,129] 13 (by decide) (choices 1) [4,32,64,128] r6685 c6685
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2941
  · exact u2942
  · exact u2943
  · exact u2944

def r6686 : Route 9 := (fun mask => (mask,id))

def c6686 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6686 : Upper (D 1) (R 1) [50,320,10,132] 13 := by
  apply FastRouting.sound _ _ [50,320,10,132] 13 (by decide) (choices 1) [1,32,64,128] r6686 c6686
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2945
  · exact u2946
  · exact u2947
  · exact u2948

def r6687 : Route 9 := (fun mask => (mask,id))

def c6687 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6687 : Upper (D 1) (R 1) [50,320,10,144] 13 := by
  apply FastRouting.sound _ _ [50,320,10,144] 13 (by decide) (choices 1) [1,4,32,64,128] r6687 c6687
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2949
  · exact u2950
  · exact u2951
  · exact u2952
  · exact u2953

def b6688 : PairBound 9 := { available := 181, camps := [{ cop := 2, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 51 322 14 200 181 181 245 181 437), lower := (rows 51 322 14 200 16 32 64 128 256), losses := [] }

theorem u6688 : Upper (D 1) (R 1) [50,320,10,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6688
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6689 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 322 21 44 218 234 202 202 458), lower := (rows 51 322 21 44 16 32 64 128 256), losses := [] }

theorem u6689 : Upper (D 1) (R 1) [50,320,17,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6689
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6690 : PairBound 9 := { available := 170, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 322 21 76 186 170 234 170 426), lower := (rows 51 322 21 76 16 32 64 128 256), losses := [] }

theorem u6690 : Upper (D 1) (R 1) [50,320,17,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6690
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6691 : PairBound 9 := { available := 142, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 322 21 104 158 174 206 142 398), lower := (rows 51 322 21 104 16 32 64 128 256), losses := [] }

theorem u6691 : Upper (D 1) (R 1) [50,320,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6691
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6692 : PairBound 9 := { available := 236, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 322 21 138 252 236 236 236 492), lower := (rows 51 322 21 138 16 32 64 128 256), losses := [] }

theorem u6692 : Upper (D 1) (R 1) [50,320,17,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6692
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6693 : PairBound 9 := { available := 234, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 322 21 140 250 234 234 234 490), lower := (rows 51 322 21 140 16 32 64 128 256), losses := [] }

theorem u6693 : Upper (D 1) (R 1) [50,320,17,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6693
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6694 : PairBound 9 := { available := 206, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 322 21 168 222 238 206 206 462), lower := (rows 51 322 21 168 16 32 64 128 256), losses := [] }

theorem u6694 : Upper (D 1) (R 1) [50,320,17,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6694
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6695 : PairBound 9 := { available := 174, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 322 21 200 190 174 238 174 430), lower := (rows 51 322 21 200 16 32 64 128 256), losses := [] }

theorem u6695 : Upper (D 1) (R 1) [50,320,17,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6695
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6696 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 51 322 22 44 217 233 201 201 457), lower := (rows 51 322 22 44 16 32 64 128 256), losses := [] }

theorem u6696 : Upper (D 1) (R 1) [50,320,18,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6696
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6697 : PairBound 9 := { available := 172, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 322 22 73 188 172 236 172 428), lower := (rows 51 322 22 73 16 32 64 128 256), losses := [] }

theorem u6697 : Upper (D 1) (R 1) [50,320,18,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6697
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6698 : PairBound 9 := { available := 169, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 322 22 76 185 169 233 169 425), lower := (rows 51 322 22 76 16 32 64 128 256), losses := [] }

theorem u6698 : Upper (D 1) (R 1) [50,320,18,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6698
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6699 : PairBound 9 := { available := 141, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 322 22 104 157 173 205 141 397), lower := (rows 51 322 22 104 16 32 64 128 256), losses := [] }

theorem u6699 : Upper (D 1) (R 1) [50,320,18,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6699
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6700 : PairBound 9 := { available := 236, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 322 22 137 252 236 236 236 492), lower := (rows 51 322 22 137 16 32 64 128 256), losses := [] }

theorem u6700 : Upper (D 1) (R 1) [50,320,18,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6700
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6701 : PairBound 9 := { available := 233, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 322 22 140 249 233 233 233 489), lower := (rows 51 322 22 140 16 32 64 128 256), losses := [] }

theorem u6701 : Upper (D 1) (R 1) [50,320,18,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6701
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6702 : PairBound 9 := { available := 205, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 322 22 168 221 237 205 205 461), lower := (rows 51 322 22 168 16 32 64 128 256), losses := [] }

theorem u6702 : Upper (D 1) (R 1) [50,320,18,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6702
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6703 : PairBound 9 := { available := 173, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 322 22 200 189 173 237 173 429), lower := (rows 51 322 22 200 16 32 64 128 256), losses := [] }

theorem u6703 : Upper (D 1) (R 1) [50,320,18,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6703
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6704 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 12, targets := 2 }], pairs := [(2,1)], upper := (rows 51 322 28 44 211 227 195 195 451), lower := (rows 51 322 28 44 16 32 64 128 256), losses := [] }

theorem u6704 : Upper (D 1) (R 1) [50,320,24,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6704
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6705 : PairBound 9 := { available := 166, camps := [{ cop := 2, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 51 322 28 73 182 166 230 166 422), lower := (rows 51 322 28 73 16 32 64 128 256), losses := [] }

theorem u6705 : Upper (D 1) (R 1) [50,320,24,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6705
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6706 : PairBound 9 := { available := 165, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 51 322 28 74 181 165 229 165 421), lower := (rows 51 322 28 74 16 32 64 128 256), losses := [] }

theorem u6706 : Upper (D 1) (R 1) [50,320,24,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6706
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6707 : PairBound 9 := { available := 163, camps := [{ cop := 0, region := 450, targets := 16 }], pairs := [(1,4)], upper := (rows 51 322 28 76 179 163 227 163 419), lower := (rows 51 322 28 76 16 32 64 128 256), losses := [] }

theorem u6707 : Upper (D 1) (R 1) [50,320,24,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6707
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6708 : Route 9 := (fun mask => (mask,id))

def c6708 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6708 : Upper (D 1) (R 1) [50,320,24,96] 13 := by
  apply FastRouting.sound _ _ [50,320,24,96] 13 (by decide) (choices 1) [1,2,4,128] r6708 c6708
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2954
  · exact u2955
  · exact u2956
  · exact u2957

def b6709 : PairBound 9 := { available := 230, camps := [{ cop := 2, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 51 322 28 137 246 230 230 230 486), lower := (rows 51 322 28 137 16 32 64 128 256), losses := [] }

theorem u6709 : Upper (D 1) (R 1) [50,320,24,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6709
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6710 : Route 9 := (fun mask => (mask,id))

def c6710 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6710 : Upper (D 1) (R 1) [50,320,24,130] 13 := by
  apply FastRouting.sound _ _ [50,320,24,130] 13 (by decide) (choices 1) [1,4,32,64,128] r6710 c6710
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2958
  · exact u2959
  · exact u2960
  · exact u2961
  · exact u2962

def b6711 : PairBound 9 := { available := 227, camps := [{ cop := 0, region := 450, targets := 16 }], pairs := [(1,4)], upper := (rows 51 322 28 140 243 227 227 227 483), lower := (rows 51 322 28 140 16 32 64 128 256), losses := [] }

theorem u6711 : Upper (D 1) (R 1) [50,320,24,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6711
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6712 : Route 9 := (fun mask => (mask,id))

def c6712 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6712 : Upper (D 1) (R 1) [50,320,24,160] 13 := by
  apply FastRouting.sound _ _ [50,320,24,160] 13 (by decide) (choices 1) [1,2,4,64,128] r6712 c6712
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2963
  · exact u2964
  · exact u2965
  · exact u2966
  · exact u2967

def r6713 : Route 9 := (fun mask => (mask,id))

def c6713 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6713 : Upper (D 1) (R 1) [50,320,24,192] 13 := by
  apply FastRouting.sound _ _ [50,320,24,192] 13 (by decide) (choices 1) [1,2,4,32,128] r6713 c6713
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2968
  · exact u2969
  · exact u2970
  · exact u2971
  · exact u2972

def b6714 : PairBound 9 := { available := 142, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 322 52 73 158 174 206 142 398), lower := (rows 51 322 52 73 16 32 64 128 256), losses := [] }

theorem u6714 : Upper (D 1) (R 1) [50,320,48,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6714
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6715 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 322 52 76 155 171 203 139 395), lower := (rows 51 322 52 76 16 32 64 128 256), losses := [] }

theorem u6715 : Upper (D 1) (R 1) [50,320,48,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6715
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6716 : PairBound 9 := { available := 206, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 322 52 137 222 238 206 206 462), lower := (rows 51 322 52 137 16 32 64 128 256), losses := [] }

theorem u6716 : Upper (D 1) (R 1) [50,320,48,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6716
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6717 : PairBound 9 := { available := 205, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 322 52 138 221 237 205 205 461), lower := (rows 51 322 52 138 16 32 64 128 256), losses := [] }

theorem u6717 : Upper (D 1) (R 1) [50,320,48,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6717
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6718 : PairBound 9 := { available := 203, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 322 52 140 219 235 203 203 459), lower := (rows 51 322 52 140 16 32 64 128 256), losses := [] }

theorem u6718 : Upper (D 1) (R 1) [50,320,48,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6718
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6719 : PairBound 9 := { available := 143, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 322 52 200 159 175 207 143 399), lower := (rows 51 322 52 200 16 32 64 128 256), losses := [] }

theorem u6719 : Upper (D 1) (R 1) [50,320,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6719
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u6719
end Delivery.IrregularNine14.P01

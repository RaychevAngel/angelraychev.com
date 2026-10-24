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

def b5700 : PairBound 9 := { available := 172, camps := [{ cop := 1, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 305 194 7 88 18 172 236 172 428), lower := (rows 305 194 7 88 18 32 64 128 256), losses := [] }

theorem u5700 : Upper (D 1) (R 1) [304,192,3,80,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5700
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5701 : PairBound 9 := { available := 170, camps := [], pairs := [], upper := (rows 305 194 7 88 20 170 234 170 426), lower := (rows 305 194 7 88 20 32 64 128 256), losses := [] }

theorem u5701 : Upper (D 1) (R 1) [304,192,3,80,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5701
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5702 : PairBound 9 := { available := 166, camps := [], pairs := [], upper := (rows 305 194 7 88 24 166 230 166 422), lower := (rows 305 194 7 88 24 32 64 128 256), losses := [] }

theorem u5702 : Upper (D 1) (R 1) [304,192,3,80,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5702
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5703 : PairBound 9 := { available := 142, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 194 7 88 48 174 206 142 398), lower := (rows 305 194 7 88 48 32 64 128 256), losses := [] }

theorem u5703 : Upper (D 1) (R 1) [304,192,3,80,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5703
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5704 : PairBound 9 := { available := 46, camps := [{ cop := 1, region := 24, targets := 2 }], pairs := [(3,1)], upper := (rows 305 194 7 88 144 46 110 174 302), lower := (rows 305 194 7 88 144 32 64 128 256), losses := [] }

theorem u5704 : Upper (D 1) (R 1) [304,192,3,80,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5704
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5705 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 481, targets := 2 }], pairs := [(0,1)], upper := (rows 305 194 13 14 18 240 240 240 496), lower := (rows 305 194 13 14 18 32 64 128 256), losses := [] }

theorem u5705 : Upper (D 1) (R 1) [304,192,9,6,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5705
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5706 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 305 194 13 14 48 242 210 210 466), lower := (rows 305 194 13 14 48 32 64 128 256), losses := [] }

theorem u5706 : Upper (D 1) (R 1) [304,192,9,6,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5706
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m5707_2 : Upper (D 1) (R 1) [304,192,9,6,64,2] 13 :=
  permutation_upper _ _ _ [304,192,9,6,2,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2058

theorem m5707_16 : Upper (D 1) (R 1) [304,192,9,6,64,16] 13 :=
  permutation_upper _ _ _ [304,192,9,6,32,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2059

def r5707 : Route 9 := (fun mask => (mask,id))

def c5707 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5707 : Upper (D 1) (R 1) [304,192,9,6,64] 13 := by
  apply FastRouting.sound _ _ [304,192,9,6,64] 13 (by decide) (choices 1) [2,16,128] r5707 c5707
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m5707_2
  · exact m5707_16
  · exact u2060

def b5708 : PairBound 9 := { available := 204, camps := [], pairs := [], upper := (rows 305 194 22 42 17 236 204 204 460), lower := (rows 305 194 22 42 17 32 64 128 256), losses := [] }

theorem u5708 : Upper (D 1) (R 1) [304,192,18,34,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5708
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5709 : PairBound 9 := { available := 201, camps := [], pairs := [], upper := (rows 305 194 22 42 20 233 201 201 457), lower := (rows 305 194 22 42 20 32 64 128 256), losses := [] }

theorem u5709 : Upper (D 1) (R 1) [304,192,18,34,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5709
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5710 : PairBound 9 := { available := 197, camps := [], pairs := [], upper := (rows 305 194 22 42 24 229 197 197 453), lower := (rows 305 194 22 42 24 32 64 128 256), losses := [] }

theorem u5710 : Upper (D 1) (R 1) [304,192,18,34,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5710
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5711 : PairBound 9 := { available := 141, camps := [{ cop := 1, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 305 194 22 42 80 173 205 141 397), lower := (rows 305 194 22 42 80 32 64 128 256), losses := [] }

theorem u5711 : Upper (D 1) (R 1) [304,192,18,34,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5711
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5712 : PairBound 9 := { available := 202, camps := [], pairs := [], upper := (rows 305 194 22 44 17 234 202 202 458), lower := (rows 305 194 22 44 17 32 64 128 256), losses := [] }

theorem u5712 : Upper (D 1) (R 1) [304,192,18,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5712
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5713 : PairBound 9 := { available := 201, camps := [{ cop := 1, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 305 194 22 44 18 233 201 201 457), lower := (rows 305 194 22 44 18 32 64 128 256), losses := [] }

theorem u5713 : Upper (D 1) (R 1) [304,192,18,36,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5713
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5714 : PairBound 9 := { available := 195, camps := [], pairs := [], upper := (rows 305 194 22 44 24 227 195 195 451), lower := (rows 305 194 22 44 24 32 64 128 256), losses := [] }

theorem u5714 : Upper (D 1) (R 1) [304,192,18,36,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5714
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5715 : PairBound 9 := { available := 139, camps := [{ cop := 1, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 305 194 22 44 80 171 203 139 395), lower := (rows 305 194 22 44 80 32 64 128 256), losses := [] }

theorem u5715 : Upper (D 1) (R 1) [304,192,18,36,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5715
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5716 : PairBound 9 := { available := 172, camps := [{ cop := 1, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 305 194 22 73 18 172 236 172 428), lower := (rows 305 194 22 73 18 32 64 128 256), losses := [] }

theorem u5716 : Upper (D 1) (R 1) [304,192,18,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5716
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5717 : PairBound 9 := { available := 170, camps := [], pairs := [], upper := (rows 305 194 22 73 20 170 234 170 426), lower := (rows 305 194 22 73 20 32 64 128 256), losses := [] }

theorem u5717 : Upper (D 1) (R 1) [304,192,18,65,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5717
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5718 : PairBound 9 := { available := 166, camps := [], pairs := [], upper := (rows 305 194 22 73 24 166 230 166 422), lower := (rows 305 194 22 73 24 32 64 128 256), losses := [] }

theorem u5718 : Upper (D 1) (R 1) [304,192,18,65,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5718
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5719 : PairBound 9 := { available := 142, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 194 22 73 48 174 206 142 398), lower := (rows 305 194 22 73 48 32 64 128 256), losses := [] }

theorem u5719 : Upper (D 1) (R 1) [304,192,18,65,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5719
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5720 : PairBound 9 := { available := 46, camps := [{ cop := 1, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 305 194 22 73 144 46 110 174 302), lower := (rows 305 194 22 73 144 32 64 128 256), losses := [] }

theorem u5720 : Upper (D 1) (R 1) [304,192,18,65,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5720
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5721 : PairBound 9 := { available := 170, camps := [], pairs := [], upper := (rows 305 194 22 76 17 170 234 170 426), lower := (rows 305 194 22 76 17 32 64 128 256), losses := [] }

theorem u5721 : Upper (D 1) (R 1) [304,192,18,68,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5721
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5722 : PairBound 9 := { available := 169, camps := [{ cop := 1, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 305 194 22 76 18 169 233 169 425), lower := (rows 305 194 22 76 18 32 64 128 256), losses := [] }

theorem u5722 : Upper (D 1) (R 1) [304,192,18,68,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5722
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5723 : PairBound 9 := { available := 163, camps := [], pairs := [], upper := (rows 305 194 22 76 24 163 227 163 419), lower := (rows 305 194 22 76 24 32 64 128 256), losses := [] }

theorem u5723 : Upper (D 1) (R 1) [304,192,18,68,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5723
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5724 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 194 22 76 48 171 203 139 395), lower := (rows 305 194 22 76 48 32 64 128 256), losses := [] }

theorem u5724 : Upper (D 1) (R 1) [304,192,18,68,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5724
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5725 : PairBound 9 := { available := 43, camps := [{ cop := 1, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 305 194 22 76 144 43 107 171 299), lower := (rows 305 194 22 76 144 32 64 128 256), losses := [] }

theorem u5725 : Upper (D 1) (R 1) [304,192,18,68,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5725
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5726 : PairBound 9 := { available := 142, camps := [], pairs := [], upper := (rows 305 194 22 104 17 174 206 142 398), lower := (rows 305 194 22 104 17 32 64 128 256), losses := [] }

theorem u5726 : Upper (D 1) (R 1) [304,192,18,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5726
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5727 : PairBound 9 := { available := 141, camps := [{ cop := 1, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 305 194 22 104 18 173 205 141 397), lower := (rows 305 194 22 104 18 32 64 128 256), losses := [] }

theorem u5727 : Upper (D 1) (R 1) [304,192,18,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5727
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5728 : PairBound 9 := { available := 139, camps := [], pairs := [], upper := (rows 305 194 22 104 20 171 203 139 395), lower := (rows 305 194 22 104 20 32 64 128 256), losses := [] }

theorem u5728 : Upper (D 1) (R 1) [304,192,18,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5728
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5729 : PairBound 9 := { available := 135, camps := [], pairs := [], upper := (rows 305 194 22 104 24 167 199 135 391), lower := (rows 305 194 22 104 24 32 64 128 256), losses := [] }

theorem u5729 : Upper (D 1) (R 1) [304,192,18,96,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5729
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5730 : PairBound 9 := { available := 15, camps := [{ cop := 1, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 305 194 22 104 144 47 79 143 271), lower := (rows 305 194 22 104 144 32 64 128 256), losses := [] }

theorem u5730 : Upper (D 1) (R 1) [304,192,18,96,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5730
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5731 : PairBound 9 := { available := 134, camps := [], pairs := [], upper := (rows 305 194 28 104 17 166 198 134 390), lower := (rows 305 194 28 104 17 32 64 128 256), losses := [] }

theorem u5731 : Upper (D 1) (R 1) [304,192,24,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5731
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5732 : Route 9 := (fun mask => (mask,id))

def c5732 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5732 : Upper (D 1) (R 1) [304,192,24,96,2] 13 := by
  apply FastRouting.sound _ _ [304,192,24,96,2] 13 (by decide) (choices 1) [1,2,4,128] r5732 c5732
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2061
  · exact u2062
  · exact u2063
  · exact u2064

def b5733 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 305 194 28 104 20 163 195 131 387), lower := (rows 305 194 28 104 20 32 64 128 256), losses := [] }

theorem u5733 : Upper (D 1) (R 1) [304,192,24,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5733
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5734 : Route 9 := (fun mask => (mask,id))

def c5734 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5734 : Upper (D 1) (R 1) [304,192,24,96,128] 13 := by
  apply FastRouting.sound _ _ [304,192,24,96,128] 13 (by decide) (choices 1) [1,2,4] r5734 c5734
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2065
  · exact u2066
  · exact u2067

def r5735 : Route 9 := (fun mask => (mask,id))

def c5735 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5735 : Upper (D 1) (R 1) [304,192,65,132,2] 13 := by
  apply FastRouting.sound _ _ [304,192,65,132,2] 13 (by decide) (choices 1) [2,8,16] r5735 c5735
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2068
  · exact u2069
  · exact u2070

def b5736 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 305 194 69 140 24 50 114 178 306), lower := (rows 305 194 69 140 24 32 64 128 256), losses := [] }

theorem u5736 : Upper (D 1) (R 1) [304,192,65,132,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5736
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5737 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 194 69 140 48 58 90 154 282), lower := (rows 305 194 69 140 48 32 64 128 256), losses := [] }

theorem u5737 : Upper (D 1) (R 1) [304,192,65,132,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5737
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5738 : PairBound 9 := { available := 46, camps := [{ cop := 1, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 305 194 69 152 18 46 110 174 302), lower := (rows 305 194 69 152 18 32 64 128 256), losses := [] }

theorem u5738 : Upper (D 1) (R 1) [304,192,65,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5738
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5739 : PairBound 9 := { available := 42, camps := [], pairs := [], upper := (rows 305 194 69 152 20 42 106 170 298), lower := (rows 305 194 69 152 20 32 64 128 256), losses := [] }

theorem u5739 : Upper (D 1) (R 1) [304,192,65,144,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5739
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5740 : PairBound 9 := { available := 38, camps := [], pairs := [], upper := (rows 305 194 69 152 24 38 102 166 294), lower := (rows 305 194 69 152 24 32 64 128 256), losses := [] }

theorem u5740 : Upper (D 1) (R 1) [304,192,65,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5740
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5741 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 194 69 152 48 46 78 142 270), lower := (rows 305 194 69 152 48 32 64 128 256), losses := [] }

theorem u5741 : Upper (D 1) (R 1) [304,192,65,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5741
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5742 : PairBound 9 := { available := 38, camps := [], pairs := [], upper := (rows 305 194 76 152 17 38 102 166 294), lower := (rows 305 194 76 152 17 32 64 128 256), losses := [] }

theorem u5742 : Upper (D 1) (R 1) [304,192,72,144,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5742
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5743 : PairBound 9 := { available := 39, camps := [{ cop := 1, region := 28, targets := 32 }], pairs := [(2,5)], upper := (rows 305 194 76 152 18 39 103 167 295), lower := (rows 305 194 76 152 18 32 64 128 256), losses := [] }

theorem u5743 : Upper (D 1) (R 1) [304,192,72,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5743
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5744 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 305 194 76 152 20 35 99 163 291), lower := (rows 305 194 76 152 20 32 64 128 256), losses := [] }

theorem u5744 : Upper (D 1) (R 1) [304,192,72,144,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5744
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5745 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 194 76 152 48 39 71 135 263), lower := (rows 305 194 76 152 48 32 64 128 256), losses := [] }

theorem u5745 : Upper (D 1) (R 1) [304,192,72,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5745
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5746 : PairBound 9 := { available := 14, camps := [], pairs := [], upper := (rows 305 194 84 168 17 46 78 142 270), lower := (rows 305 194 84 168 17 32 64 128 256), losses := [] }

theorem u5746 : Upper (D 1) (R 1) [304,192,80,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5746
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5747 : PairBound 9 := { available := 15, camps := [{ cop := 1, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 305 194 84 168 18 47 79 143 271), lower := (rows 305 194 84 168 18 32 64 128 256), losses := [] }

theorem u5747 : Upper (D 1) (R 1) [304,192,80,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5747
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5748 : PairBound 9 := { available := 11, camps := [], pairs := [], upper := (rows 305 194 84 168 20 43 75 139 267), lower := (rows 305 194 84 168 20 32 64 128 256), losses := [] }

theorem u5748 : Upper (D 1) (R 1) [304,192,80,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5748
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5749 : PairBound 9 := { available := 7, camps := [], pairs := [], upper := (rows 305 194 84 168 24 39 71 135 263), lower := (rows 305 194 84 168 24 32 64 128 256), losses := [] }

theorem u5749 : Upper (D 1) (R 1) [304,192,80,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5749
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5750 : PairBound 9 := { available := 480, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 15 19 22 104 496 480 480 480 480), lower := (rows 15 19 22 104 16 32 64 128 256), losses := [] }

theorem u5750 : Upper (D 1) (R 1) [14,17,18,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5750
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5751 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 15 19 22 296 240 224 224 224 480), lower := (rows 15 19 22 296 16 32 64 128 256), losses := [] }

theorem u5751 : Upper (D 1) (R 1) [14,17,18,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5751
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5752 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 504, targets := 2 }], pairs := [(3,1)], upper := (rows 15 19 38 104 464 496 464 464 464), lower := (rows 15 19 38 104 16 32 64 128 256), losses := [] }

theorem u5752 : Upper (D 1) (R 1) [14,17,34,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5752
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5753 : PairBound 9 := { available := 496, camps := [{ cop := 0, region := 504, targets := 2 }], pairs := [(3,1)], upper := (rows 15 19 38 200 496 496 496 496 496), lower := (rows 15 19 38 200 16 32 64 128 256), losses := [] }

theorem u5753 : Upper (D 1) (R 1) [14,17,34,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5753
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5754 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 504, targets := 2 }], pairs := [(3,1)], upper := (rows 15 19 38 296 208 240 208 208 464), lower := (rows 15 19 38 296 16 32 64 128 256), losses := [] }

theorem u5754 : Upper (D 1) (R 1) [14,17,34,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5754
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5755 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 504, targets := 2 }], pairs := [(3,1)], upper := (rows 15 19 38 328 240 240 240 240 496), lower := (rows 15 19 38 328 16 32 64 128 256), losses := [] }

theorem u5755 : Upper (D 1) (R 1) [14,17,34,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5755
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5756 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 488, targets := 16 }], pairs := [(3,4)], upper := (rows 15 19 52 104 466 482 450 450 450), lower := (rows 15 19 52 104 16 32 64 128 256), losses := [] }

theorem u5756 : Upper (D 1) (R 1) [14,17,48,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5756
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5757 : PairBound 9 := { available := 482, camps := [{ cop := 0, region := 488, targets := 16 }], pairs := [(3,4)], upper := (rows 15 19 52 200 498 482 482 482 482), lower := (rows 15 19 52 200 16 32 64 128 256), losses := [] }

theorem u5757 : Upper (D 1) (R 1) [14,17,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5757
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5758 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 488, targets := 16 }], pairs := [(3,4)], upper := (rows 15 19 52 296 210 226 194 194 450), lower := (rows 15 19 52 296 16 32 64 128 256), losses := [] }

theorem u5758 : Upper (D 1) (R 1) [14,17,48,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5758
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5759 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 488, targets := 16 }], pairs := [(3,4)], upper := (rows 15 19 52 328 242 226 226 226 482), lower := (rows 15 19 52 328 16 32 64 128 256), losses := [] }

theorem u5759 : Upper (D 1) (R 1) [14,17,48,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5759
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u5759
end Delivery.IrregularNine14.P01

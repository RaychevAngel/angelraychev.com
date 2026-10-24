import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0036

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5700 : PairBound 9 := { available := 89, camps := [{ cop := 1, region := 220, targets := 32 }], pairs := [(2,5)], upper := (rows 289 35 69 138 148 121 89 217 345), lower := (rows 289 35 69 138 148 32 64 128 256), losses := [] }

theorem u5700 : Upper (D 3) (R 3) [288,33,65,130,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5700
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5701 : PairBound 9 := { available := 29, camps := [{ cop := 1, region := 220, targets := 32 }], pairs := [(2,5)], upper := (rows 289 35 69 138 208 61 93 157 285), lower := (rows 289 35 69 138 208 32 64 128 256), losses := [] }

theorem u5701 : Upper (D 3) (R 3) [288,33,65,130,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5701
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5702 : PairBound 9 := { available := 27, camps := [{ cop := 1, region := 220, targets := 32 }], pairs := [(2,5)], upper := (rows 289 35 69 140 208 59 91 155 283), lower := (rows 289 35 69 140 208 32 64 128 256), losses := [] }

theorem u5702 : Upper (D 3) (R 3) [288,33,65,132,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5702
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5703 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 220, targets := 32 }], pairs := [(2,5)], upper := (rows 289 35 70 140 208 57 89 153 281), lower := (rows 289 35 70 140 208 32 64 128 256), losses := [] }

theorem u5703 : Upper (D 3) (R 3) [288,33,66,132,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5703
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5704 : PairBound 9 := { available := 154, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 289 38 69 73 145 186 218 154 410), lower := (rows 289 38 69 73 145 32 64 128 256), losses := [] }

theorem u5704 : Upper (D 3) (R 3) [288,36,65,65,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5704
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5705 : PairBound 9 := { available := 153, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 289 38 69 73 146 185 217 153 409), lower := (rows 289 38 69 73 146 32 64 128 256), losses := [] }

theorem u5705 : Upper (D 3) (R 3) [288,36,65,65,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5705
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5706 : PairBound 9 := { available := 147, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 289 38 69 73 152 179 211 147 403), lower := (rows 289 38 69 73 152 32 64 128 256), losses := [] }

theorem u5706 : Upper (D 3) (R 3) [288,36,65,65,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5706
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5707 : PairBound 9 := { available := 153, camps := [{ cop := 3, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 69 74 145 185 217 153 409), lower := (rows 289 38 69 74 145 32 64 128 256), losses := [] }

theorem u5707 : Upper (D 3) (R 3) [288,36,65,66,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5707
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5708 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 69 74 152 177 209 145 401), lower := (rows 289 38 69 74 152 32 64 128 256), losses := [] }

theorem u5708 : Upper (D 3) (R 3) [288,36,65,66,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5708
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5709 : Route 9 := (fun mask => (mask,id))

def c5709 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5709 : Upper (D 3) (R 3) [288,36,65,80,129] 13 := by
  apply FastRouting.sound _ _ [288,36,65,80,129] 13 (by decide) (choices 1) [1,2,8,128] r5709 c5709
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2164
  · exact u2165
  · exact u2166
  · exact u2167

def b5710 : PairBound 9 := { available := 137, camps := [{ cop := 3, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 69 88 146 169 201 137 393), lower := (rows 289 38 69 88 146 32 64 128 256), losses := [] }

theorem u5710 : Upper (D 3) (R 3) [288,36,65,80,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5710
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5711 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 69 88 152 163 195 131 387), lower := (rows 289 38 69 88 152 32 64 128 256), losses := [] }

theorem u5711 : Upper (D 3) (R 3) [288,36,65,80,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5711
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5712 : PairBound 9 := { available := 90, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 289 38 69 137 145 122 90 218 346), lower := (rows 289 38 69 137 145 32 64 128 256), losses := [] }

theorem u5712 : Upper (D 3) (R 3) [288,36,65,129,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5712
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5713 : Route 9 := (fun mask => (mask,id))

def c5713 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5713 : Upper (D 3) (R 3) [288,36,65,129,130] 13 := by
  apply FastRouting.sound _ _ [288,36,65,129,130] 13 (by decide) (choices 1) [1,8,16,64] r5713 c5713
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2168
  · exact u2169
  · exact u2170
  · exact u2171

def b5714 : PairBound 9 := { available := 83, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 289 38 69 137 152 115 83 211 339), lower := (rows 289 38 69 137 152 32 64 128 256), losses := [] }

theorem u5714 : Upper (D 3) (R 3) [288,36,65,129,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5714
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5715 : Route 9 := (fun mask => (mask,id))

def c5715 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5715 : Upper (D 3) (R 3) [288,36,65,129,192] 13 := by
  apply FastRouting.sound _ _ [288,36,65,129,192] 13 (by decide) (choices 1) [1,2,8,16] r5715 c5715
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2172
  · exact u2173
  · exact u2174
  · exact u2175

def b5716 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 289 38 69 138 152 113 81 209 337), lower := (rows 289 38 69 138 152 32 64 128 256), losses := [] }

theorem u5716 : Upper (D 3) (R 3) [288,36,65,130,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5716
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5717 : Route 9 := (fun mask => (mask,id))

def c5717 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5717 : Upper (D 3) (R 3) [288,36,65,130,192] 13 := by
  apply FastRouting.sound _ _ [288,36,65,130,192] 13 (by decide) (choices 1) [1,8,16] r5717 c5717
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2176
  · exact u2177
  · exact u2178

def b5718 : PairBound 9 := { available := 67, camps := [{ cop := 7, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 289 38 69 152 152 99 67 195 323), lower := (rows 289 38 69 152 152 32 64 128 256), losses := [] }

theorem u5718 : Upper (D 3) (R 3) [288,36,65,144,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5718
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5719 : PairBound 9 := { available := 11, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 289 38 69 152 208 43 75 139 267), lower := (rows 289 38 69 152 208 32 64 128 256), losses := [] }

theorem u5719 : Upper (D 3) (R 3) [288,36,65,144,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5719
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5720 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 289 38 70 73 145 185 217 153 409), lower := (rows 289 38 70 73 145 32 64 128 256), losses := [] }

theorem u5720 : Upper (D 3) (R 3) [288,36,66,65,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5720
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5721 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 289 38 70 73 152 177 209 145 401), lower := (rows 289 38 70 73 152 32 64 128 256), losses := [] }

theorem u5721 : Upper (D 3) (R 3) [288,36,66,65,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5721
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5722 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 289 38 70 88 145 169 201 137 393), lower := (rows 289 38 70 88 145 32 64 128 256), losses := [] }

theorem u5722 : Upper (D 3) (R 3) [288,36,66,80,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5722
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5723 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 289 38 70 88 152 161 193 129 385), lower := (rows 289 38 70 88 152 32 64 128 256), losses := [] }

theorem u5723 : Upper (D 3) (R 3) [288,36,66,80,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5723
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5724 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 289 38 70 137 208 57 89 153 281), lower := (rows 289 38 70 137 208 32 64 128 256), losses := [] }

theorem u5724 : Upper (D 3) (R 3) [288,36,66,129,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5724
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5725 : PairBound 9 := { available := 147, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 76 73 145 179 211 147 403), lower := (rows 289 38 76 73 145 32 64 128 256), losses := [] }

theorem u5725 : Upper (D 3) (R 3) [288,36,72,65,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5725
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5726 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 76 73 146 177 209 145 401), lower := (rows 289 38 76 73 146 32 64 128 256), losses := [] }

theorem u5726 : Upper (D 3) (R 3) [288,36,72,65,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5726
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5727 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 76 74 145 177 209 145 401), lower := (rows 289 38 76 74 145 32 64 128 256), losses := [] }

theorem u5727 : Upper (D 3) (R 3) [288,36,72,66,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5727
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5728 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 76 88 145 163 195 131 387), lower := (rows 289 38 76 88 145 32 64 128 256), losses := [] }

theorem u5728 : Upper (D 3) (R 3) [288,36,72,80,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5728
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5729 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 76 88 146 161 193 129 385), lower := (rows 289 38 76 88 146 32 64 128 256), losses := [] }

theorem u5729 : Upper (D 3) (R 3) [288,36,72,80,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5729
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5730 : Route 9 := (fun mask => (mask,id))

def c5730 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5730 : Upper (D 3) (R 3) [288,36,72,129,65] 13 := by
  apply FastRouting.sound _ _ [288,36,72,129,65] 13 (by decide) (choices 1) [1,2,16,128] r5730 c5730
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2179
  · exact u2180
  · exact u2181
  · exact u2182

def b5731 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 76 137 82 177 209 145 401), lower := (rows 289 38 76 137 82 32 64 128 256), losses := [] }

theorem u5731 : Upper (D 3) (R 3) [288,36,72,129,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5731
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5732 : PairBound 9 := { available := 83, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 289 38 76 137 145 115 83 211 339), lower := (rows 289 38 76 137 145 32 64 128 256), losses := [] }

theorem u5732 : Upper (D 3) (R 3) [288,36,72,129,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5732
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5733 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 289 38 76 137 146 113 81 209 337), lower := (rows 289 38 76 137 146 32 64 128 256), losses := [] }

theorem u5733 : Upper (D 3) (R 3) [288,36,72,129,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5733
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5734 : Route 9 := (fun mask => (mask,id))

def c5734 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5734 : Upper (D 3) (R 3) [288,36,72,129,192] 13 := by
  apply FastRouting.sound _ _ [288,36,72,129,192] 13 (by decide) (choices 1) [1,2,16] r5734 c5734
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2183
  · exact u2184
  · exact u2185

def b5735 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 289 38 76 138 81 177 209 145 401), lower := (rows 289 38 76 138 81 32 64 128 256), losses := [] }

theorem u5735 : Upper (D 3) (R 3) [288,36,72,130,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5735
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5736 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 289 38 76 138 145 113 81 209 337), lower := (rows 289 38 76 138 145 32 64 128 256), losses := [] }

theorem u5736 : Upper (D 3) (R 3) [288,36,72,130,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5736
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5737 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 289 38 76 138 208 49 81 145 273), lower := (rows 289 38 76 138 208 32 64 128 256), losses := [] }

theorem u5737 : Upper (D 3) (R 3) [288,36,72,130,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5737
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5738 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 76 152 81 163 195 131 387), lower := (rows 289 38 76 152 81 32 64 128 256), losses := [] }

theorem u5738 : Upper (D 3) (R 3) [288,36,72,144,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5738
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5739 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 76 152 82 161 193 129 385), lower := (rows 289 38 76 152 82 32 64 128 256), losses := [] }

theorem u5739 : Upper (D 3) (R 3) [288,36,72,144,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5739
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5740 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 289 38 76 152 145 99 67 195 323), lower := (rows 289 38 76 152 145 32 64 128 256), losses := [] }

theorem u5740 : Upper (D 3) (R 3) [288,36,72,144,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5740
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5741 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 289 38 76 152 146 97 65 193 321), lower := (rows 289 38 76 152 146 32 64 128 256), losses := [] }

theorem u5741 : Upper (D 3) (R 3) [288,36,72,144,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5741
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5742 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 289 38 76 152 208 35 67 131 259), lower := (rows 289 38 76 152 208 32 64 128 256), losses := [] }

theorem u5742 : Upper (D 3) (R 3) [288,36,72,144,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5742
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5743 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 76 200 145 51 83 147 275), lower := (rows 289 38 76 200 145 32 64 128 256), losses := [] }

theorem u5743 : Upper (D 3) (R 3) [288,36,72,192,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5743
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5744 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 76 200 146 49 81 145 273), lower := (rows 289 38 76 200 146 32 64 128 256), losses := [] }

theorem u5744 : Upper (D 3) (R 3) [288,36,72,192,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5744
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m5745_16 : Upper (D 3) (R 3) [288,36,192,65,129,16] 13 :=
  permutation_upper _ _ _ [288,36,192,65,129,8] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2188

def r5745 : Route 9 := (fun mask => (mask,id))

def c5745 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5745 : Upper (D 3) (R 3) [288,36,192,65,129] 13 := by
  apply FastRouting.sound _ _ [288,36,192,65,129] 13 (by decide) (choices 1) [1,2,8,16] r5745 c5745
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2186
  · exact u2187
  · exact u2188
  · exact m5745_16

def b5746 : PairBound 9 := { available := 25, camps := [{ cop := 4, region := 361, targets := 128 }], pairs := [(0,7)], upper := (rows 289 38 196 73 146 57 89 153 281), lower := (rows 289 38 196 73 146 32 64 128 256), losses := [] }

theorem u5746 : Upper (D 3) (R 3) [288,36,192,65,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5746
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5747 : Route 9 := (fun mask => (mask,id))

def c5747 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5747 : Upper (D 3) (R 3) [288,36,192,65,136] 13 := by
  apply FastRouting.sound _ _ [288,36,192,65,136] 13 (by decide) (choices 1) [1,2,16] r5747 c5747
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2189
  · exact u2190
  · exact u2191

def b5748 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 196 74 152 49 81 145 273), lower := (rows 289 38 196 74 152 32 64 128 256), losses := [] }

theorem u5748 : Upper (D 3) (R 3) [288,36,192,66,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5748
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5749 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 289 38 196 88 152 35 67 131 259), lower := (rows 289 38 196 88 152 32 64 128 256), losses := [] }

theorem u5749 : Upper (D 3) (R 3) [288,36,192,80,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5749
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5750 : PairBound 9 := { available := 60, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 289 67 69 137 146 60 124 188 316), lower := (rows 289 67 69 137 146 32 64 128 256), losses := [] }

theorem u5750 : Upper (D 3) (R 3) [288,65,65,129,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5750
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5751 : PairBound 9 := { available := 30, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 289 67 69 137 176 62 94 158 286), lower := (rows 289 67 69 137 176 32 64 128 256), losses := [] }

theorem u5751 : Upper (D 3) (R 3) [288,65,65,129,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5751
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5752 : PairBound 9 := { available := 57, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 289 67 69 138 148 57 121 185 313), lower := (rows 289 67 69 138 148 32 64 128 256), losses := [] }

theorem u5752 : Upper (D 3) (R 3) [288,65,65,130,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5752
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5753 : PairBound 9 := { available := 29, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 289 67 69 138 176 61 93 157 285), lower := (rows 289 67 69 138 176 32 64 128 256), losses := [] }

theorem u5753 : Upper (D 3) (R 3) [288,65,65,130,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5753
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5754 : PairBound 9 := { available := 57, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 289 67 70 137 148 57 121 185 313), lower := (rows 289 67 70 137 148 32 64 128 256), losses := [] }

theorem u5754 : Upper (D 3) (R 3) [288,65,66,129,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5754
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5755 : PairBound 9 := { available := 29, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 289 67 70 137 176 61 93 157 285), lower := (rows 289 67 70 137 176 32 64 128 256), losses := [] }

theorem u5755 : Upper (D 3) (R 3) [288,65,66,129,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5755
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5756 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 289 67 70 140 176 57 89 153 281), lower := (rows 289 67 70 140 176 32 64 128 256), losses := [] }

theorem u5756 : Upper (D 3) (R 3) [288,65,66,132,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5756
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m5757_16 : Upper (D 3) (R 3) [288,65,72,129,130,16] 13 :=
  permutation_upper _ _ _ [288,65,72,129,130,4] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2193

def r5757 : Route 9 := (fun mask => (mask,id))

def c5757 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5757 : Upper (D 3) (R 3) [288,65,72,129,130] 13 := by
  apply FastRouting.sound _ _ [288,65,72,129,130] 13 (by decide) (choices 1) [1,4,16] r5757 c5757
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2192
  · exact u2193
  · exact m5757_16

def b5758 : PairBound 9 := { available := 51, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 289 67 76 137 148 51 115 179 307), lower := (rows 289 67 76 137 148 32 64 128 256), losses := [] }

theorem u5758 : Upper (D 3) (R 3) [288,65,72,129,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5758
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5759 : Route 9 := (fun mask => (mask,id))

def c5759 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5759 : Upper (D 3) (R 3) [288,65,72,129,160] 13 := by
  apply FastRouting.sound _ _ [288,65,72,129,160] 13 (by decide) (choices 1) [1,2,4,16] r5759 c5759
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2194
  · exact u2195
  · exact u2196
  · exact u2197

#print axioms u5759
end Delivery.IrregularNine14.P03

import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P00C0014
import IrregularNine14P00C0015

namespace Delivery.IrregularNine14.P00
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m2100_2 : Upper (D 0) (R 0) [304,5,72,129,128,2] 13 :=
  permutation_upper _ _ _ [304,5,72,129,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u875

theorem m2100_16 : Upper (D 0) (R 0) [304,5,72,129,128,16] 13 :=
  permutation_upper _ _ _ [304,5,72,129,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u877

theorem m2100_64 : Upper (D 0) (R 0) [304,5,72,129,128,64] 13 :=
  permutation_upper _ _ _ [304,5,72,129,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u878

def r2100 : Route 9 := (fun mask => (mask,id))

def c2100 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2100 : Upper (D 0) (R 0) [304,5,72,129,128] 13 := by
  apply FastRouting.sound _ _ [304,5,72,129,128] 13 (by decide) (choices 1) [2,16,64] r2100 c2100
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m2100_2
  · exact m2100_16
  · exact m2100_64

def b2101 : PairBound 9 := { available := 240, camps := [], pairs := [(2,0)], upper := (rows 305 7 76 138 17 240 240 240 496), lower := (rows 305 7 76 138 17 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 6 10 16 49 81 145 273), good := (rows 496 494 76 142 496 32 64 128 256) }] }

theorem u2101 : Upper (D 0) (R 0) [304,5,72,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2101
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2102 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 7 76 138 48 241 209 209 465), lower := (rows 305 7 76 138 48 32 64 128 256), losses := [] }

theorem u2102 : Upper (D 0) (R 0) [304,5,72,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2102
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2103 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 305 7 76 138 80 177 241 177 433), lower := (rows 305 7 76 138 80 32 64 128 256), losses := [] }

theorem u2103 : Upper (D 0) (R 0) [304,5,72,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2103
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2104 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 305 7 76 138 144 113 113 241 369), lower := (rows 305 7 76 138 144 32 64 128 256), losses := [] }

theorem u2104 : Upper (D 0) (R 0) [304,5,72,130,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2104
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2105 : Route 9 := (fun mask => (mask,id))

def c2105 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2105 : Upper (D 0) (R 0) [304,5,72,144,1] 13 := by
  apply FastRouting.sound _ _ [304,5,72,144,1] 13 (by decide) (choices 1) [2,64,128] r2105 c2105
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u879
  · exact u880
  · exact u881

def b2106 : PairBound 9 := { available := 225, camps := [], pairs := [], upper := (rows 305 7 76 152 18 225 225 225 481), lower := (rows 305 7 76 152 18 32 64 128 256), losses := [] }

theorem u2106 : Upper (D 0) (R 0) [304,5,72,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2106
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2107 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 7 76 152 48 227 195 195 451), lower := (rows 305 7 76 152 48 32 64 128 256), losses := [] }

theorem u2107 : Upper (D 0) (R 0) [304,5,72,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2107
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2108 : Route 9 := (fun mask => (mask,id))

def c2108 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2108 : Upper (D 0) (R 0) [304,5,72,144,64] 13 := by
  apply FastRouting.sound _ _ [304,5,72,144,64] 13 (by decide) (choices 1) [1,2,128] r2108 c2108
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u882
  · exact u883
  · exact u884

def b2109 : PairBound 9 := { available := 99, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 305 7 76 152 144 99 99 227 355), lower := (rows 305 7 76 152 144 32 64 128 256), losses := [] }

theorem u2109 : Upper (D 0) (R 0) [304,5,72,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2109
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2110 : PairBound 9 := { available := 232, camps := [{ cop := 1, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 305 7 196 26 17 232 232 232 488), lower := (rows 305 7 196 26 17 32 64 128 256), losses := [] }

theorem u2110 : Upper (D 0) (R 0) [304,5,192,18,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2110
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2111 : PairBound 9 := { available := 225, camps := [], pairs := [], upper := (rows 305 7 196 26 24 225 225 225 481), lower := (rows 305 7 196 26 24 32 64 128 256), losses := [] }

theorem u2111 : Upper (D 0) (R 0) [304,5,192,18,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2111
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2112 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 7 196 26 48 233 201 201 457), lower := (rows 305 7 196 26 48 32 64 128 256), losses := [] }

theorem u2112 : Upper (D 0) (R 0) [304,5,192,18,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2112
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2113 : PairBound 9 := { available := 169, camps := [{ cop := 3, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 305 7 196 26 80 169 233 169 425), lower := (rows 305 7 196 26 80 32 64 128 256), losses := [] }

theorem u2113 : Upper (D 0) (R 0) [304,5,192,18,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2113
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2114 : PairBound 9 := { available := 184, camps := [], pairs := [], upper := (rows 305 7 196 73 18 184 248 184 440), lower := (rows 305 7 196 73 18 32 64 128 256), losses := [] }

theorem u2114 : Upper (D 0) (R 0) [304,5,192,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2114
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2115 : PairBound 9 := { available := 178, camps := [], pairs := [], upper := (rows 305 7 196 73 24 178 242 178 434), lower := (rows 305 7 196 73 24 32 64 128 256), losses := [] }

theorem u2115 : Upper (D 0) (R 0) [304,5,192,65,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2115
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2116 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 7 196 73 48 186 218 154 410), lower := (rows 305 7 196 73 48 32 64 128 256), losses := [] }

theorem u2116 : Upper (D 0) (R 0) [304,5,192,65,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2116
    (constants 0).1 (constants 0).2 (by decide +kernel)

theorem m2117_2 : Upper (D 0) (R 0) [304,5,192,65,128,2] 13 :=
  permutation_upper _ _ _ [304,5,192,65,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u885

theorem m2117_8 : Upper (D 0) (R 0) [304,5,192,65,128,8] 13 :=
  permutation_upper _ _ _ [304,5,192,65,8,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u886

theorem m2117_16 : Upper (D 0) (R 0) [304,5,192,65,128,16] 13 :=
  permutation_upper _ _ _ [304,5,192,65,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u887

def r2117 : Route 9 := (fun mask => (mask,id))

def c2117 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2117 : Upper (D 0) (R 0) [304,5,192,65,128] 13 := by
  apply FastRouting.sound _ _ [304,5,192,65,128] 13 (by decide) (choices 1) [2,8,16] r2117 c2117
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m2117_2
  · exact m2117_8
  · exact m2117_16

def r2118 : Route 9 := (fun mask => (mask,id))

def c2118 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2118 : Upper (D 0) (R 0) [304,5,192,80,1] 13 := by
  apply FastRouting.sound _ _ [304,5,192,80,1] 13 (by decide) (choices 1) [2,8,128] r2118 c2118
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u888
  · exact u889
  · exact u890

def b2119 : PairBound 9 := { available := 169, camps := [], pairs := [], upper := (rows 305 7 196 88 18 169 233 169 425), lower := (rows 305 7 196 88 18 32 64 128 256), losses := [] }

theorem u2119 : Upper (D 0) (R 0) [304,5,192,80,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2119
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2120 : PairBound 9 := { available := 163, camps := [], pairs := [], upper := (rows 305 7 196 88 24 163 227 163 419), lower := (rows 305 7 196 88 24 32 64 128 256), losses := [] }

theorem u2120 : Upper (D 0) (R 0) [304,5,192,80,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2120
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2121 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 7 196 88 48 171 203 139 395), lower := (rows 305 7 196 88 48 32 64 128 256), losses := [] }

theorem u2121 : Upper (D 0) (R 0) [304,5,192,80,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2121
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2122 : PairBound 9 := { available := 43, camps := [{ cop := 2, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 305 7 196 88 144 43 107 171 299), lower := (rows 305 7 196 88 144 32 64 128 256), losses := [] }

theorem u2122 : Upper (D 0) (R 0) [304,5,192,80,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2122
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2123 : PairBound 9 := { available := 240, camps := [], pairs := [], upper := (rows 305 14 69 137 18 240 240 240 496), lower := (rows 305 14 69 137 18 32 64 128 256), losses := [] }

theorem u2123 : Upper (D 0) (R 0) [304,12,65,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2123
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2124 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 14 69 137 48 242 210 210 466), lower := (rows 305 14 69 137 48 32 64 128 256), losses := [] }

theorem u2124 : Upper (D 0) (R 0) [304,12,65,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2124
    (constants 0).1 (constants 0).2 (by decide +kernel)

theorem m2125_2 : Upper (D 0) (R 0) [304,12,65,129,64,2] 13 :=
  permutation_upper _ _ _ [304,12,65,129,2,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u891

theorem m2125_16 : Upper (D 0) (R 0) [304,12,65,129,64,16] 13 :=
  permutation_upper _ _ _ [304,12,65,129,32,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u892

def r2125 : Route 9 := (fun mask => (mask,id))

def c2125 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2125 : Upper (D 0) (R 0) [304,12,65,129,64] 13 := by
  apply FastRouting.sound _ _ [304,12,65,129,64] 13 (by decide) (choices 1) [2,16,128] r2125 c2125
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m2125_2
  · exact m2125_16
  · exact u893

def b2126 : PairBound 9 := { available := 240, camps := [], pairs := [(1,0)], upper := (rows 305 14 69 138 17 240 240 240 496), lower := (rows 305 14 69 138 17 32 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 12 16 49 81 145 273), good := (rows 496 14 494 138 496 32 64 128 256) }] }

theorem u2126 : Upper (D 0) (R 0) [304,12,65,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2126
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2127 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 14 69 138 48 241 209 209 465), lower := (rows 305 14 69 138 48 32 64 128 256), losses := [] }

theorem u2127 : Upper (D 0) (R 0) [304,12,65,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2127
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2128 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 305 14 69 138 80 177 241 177 433), lower := (rows 305 14 69 138 80 32 64 128 256), losses := [] }

theorem u2128 : Upper (D 0) (R 0) [304,12,65,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2128
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2129 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 305 14 69 138 144 113 113 241 369), lower := (rows 305 14 69 138 144 32 64 128 256), losses := [] }

theorem u2129 : Upper (D 0) (R 0) [304,12,65,130,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2129
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2130 : Route 9 := (fun mask => (mask,id))

def c2130 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2130 : Upper (D 0) (R 0) [304,12,65,144,1] 13 := by
  apply FastRouting.sound _ _ [304,12,65,144,1] 13 (by decide) (choices 1) [2,64,128] r2130 c2130
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u894
  · exact u895
  · exact u896

def b2131 : PairBound 9 := { available := 225, camps := [], pairs := [], upper := (rows 305 14 69 152 18 225 225 225 481), lower := (rows 305 14 69 152 18 32 64 128 256), losses := [] }

theorem u2131 : Upper (D 0) (R 0) [304,12,65,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2131
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2132 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 14 69 152 48 227 195 195 451), lower := (rows 305 14 69 152 48 32 64 128 256), losses := [] }

theorem u2132 : Upper (D 0) (R 0) [304,12,65,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2132
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2133 : Route 9 := (fun mask => (mask,id))

def c2133 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2133 : Upper (D 0) (R 0) [304,12,65,144,64] 13 := by
  apply FastRouting.sound _ _ [304,12,65,144,64] 13 (by decide) (choices 1) [1,2,128] r2133 c2133
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u897
  · exact u898
  · exact u899

def b2134 : PairBound 9 := { available := 99, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 305 14 69 152 144 99 99 227 355), lower := (rows 305 14 69 152 144 32 64 128 256), losses := [] }

theorem u2134 : Upper (D 0) (R 0) [304,12,65,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2134
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2135 : PairBound 9 := { available := 225, camps := [], pairs := [(1,4)], upper := (rows 305 14 70 152 17 225 225 225 481), lower := (rows 305 14 70 152 17 32 64 128 256), losses := [{ target := 4, region := (rows 1 10 12 8 0 49 81 145 273), good := (rows 481 14 70 494 481 32 64 128 256) }] }

theorem u2135 : Upper (D 0) (R 0) [304,12,66,144,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2135
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2136 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 14 70 152 48 225 193 193 449), lower := (rows 305 14 70 152 48 32 64 128 256), losses := [] }

theorem u2136 : Upper (D 0) (R 0) [304,12,66,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2136
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2137 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 305 14 70 152 80 161 225 161 417), lower := (rows 305 14 70 152 80 32 64 128 256), losses := [] }

theorem u2137 : Upper (D 0) (R 0) [304,12,66,144,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2137
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2138 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 305 14 70 152 144 97 97 225 353), lower := (rows 305 14 70 152 144 32 64 128 256), losses := [] }

theorem u2138 : Upper (D 0) (R 0) [304,12,66,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2138
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2139 : Route 9 := (fun mask => (mask,id))

def c2139 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2139 : Upper (D 0) (R 0) [304,12,80,160,1] 13 := by
  apply FastRouting.sound _ _ [304,12,80,160,1] 13 (by decide) (choices 1) [1,2,64,128] r2139 c2139
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u900
  · exact u901
  · exact u902
  · exact u903

def b2140 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 305 14 84 168 18 225 193 193 449), lower := (rows 305 14 84 168 18 32 64 128 256), losses := [] }

theorem u2140 : Upper (D 0) (R 0) [304,12,80,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2140
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2141 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6)], upper := (rows 305 14 84 168 80 163 195 131 387), lower := (rows 305 14 84 168 80 32 64 128 256), losses := [] }

theorem u2141 : Upper (D 0) (R 0) [304,12,80,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2141
    (constants 0).1 (constants 0).2 (by decide +kernel)

theorem m2142_1 : Upper (D 0) (R 0) [304,12,80,160,128,1] 13 :=
  permutation_upper _ _ _ [304,12,80,160,1,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u902

theorem m2142_2 : Upper (D 0) (R 0) [304,12,80,160,128,2] 13 :=
  permutation_upper _ _ _ [304,12,80,160,2,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u904

def r2142 : Route 9 := (fun mask => (mask,id))

def c2142 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2142 : Upper (D 0) (R 0) [304,12,80,160,128] 13 := by
  apply FastRouting.sound _ _ [304,12,80,160,128] 13 (by decide) (choices 1) [1,2,64] r2142 c2142
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m2142_1
  · exact m2142_2
  · exact u905

def b2143 : PairBound 9 := { available := 194, camps := [], pairs := [(1,5)], upper := (rows 305 22 44 73 17 226 194 194 450), lower := (rows 305 22 44 73 17 32 64 128 256), losses := [{ target := 5, region := (rows 1 6 4 8 25 0 70 134 262), good := (rows 273 470 478 89 17 0 64 128 256) }] }

theorem u2143 : Upper (D 0) (R 0) [304,20,40,65,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2143
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2144 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 305 22 44 73 18 225 193 193 449), lower := (rows 305 22 44 73 18 32 64 128 256), losses := [] }

theorem u2144 : Upper (D 0) (R 0) [304,20,40,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2144
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2145 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 305 22 44 73 80 163 195 131 387), lower := (rows 305 22 44 73 80 32 64 128 256), losses := [] }

theorem u2145 : Upper (D 0) (R 0) [304,20,40,65,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2145
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2146 : Route 9 := (fun mask => (mask,id))

def c2146 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2146 : Upper (D 0) (R 0) [304,20,40,65,128] 13 := by
  apply FastRouting.sound _ _ [304,20,40,65,128] 13 (by decide) (choices 1) [1,2,64,128] r2146 c2146
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u906
  · exact u907
  · exact u908
  · exact u909

def b2147 : PairBound 9 := { available := 193, camps := [], pairs := [(2,4)], upper := (rows 305 22 44 74 17 225 193 193 449), lower := (rows 305 22 44 74 17 32 64 128 256), losses := [{ target := 4, region := (rows 1 2 6 10 0 49 81 145 273), good := (rows 481 494 44 78 481 32 64 128 256) }] }

theorem u2147 : Upper (D 0) (R 0) [304,20,40,66,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2147
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2148 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 305 22 44 74 80 161 193 129 385), lower := (rows 305 22 44 74 80 32 64 128 256), losses := [] }

theorem u2148 : Upper (D 0) (R 0) [304,20,40,66,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2148
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2149 : Route 9 := (fun mask => (mask,id))

def c2149 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2149 : Upper (D 0) (R 0) [304,20,40,66,128] 13 := by
  apply FastRouting.sound _ _ [304,20,40,66,128] 13 (by decide) (choices 1) [1,64,128] r2149 c2149
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u910
  · exact u911
  · exact u912

def r2150 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c2150 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2150 : Upper (D 0) (R 0) [304,20,40,192,1] 13 := by
  apply FastRouting.sound _ _ [304,20,40,192,1] 13 (by decide) (choices 1) [1,2,64] r2150 c2150
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u913
  · exact u914
  · exact u915

def b2151 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 305 22 44 200 18 225 193 193 449), lower := (rows 305 22 44 200 18 32 64 128 256), losses := [] }

theorem u2151 : Upper (D 0) (R 0) [304,20,40,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2151
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2152 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 305 22 44 200 80 163 195 131 387), lower := (rows 305 22 44 200 80 32 64 128 256), losses := [] }

theorem u2152 : Upper (D 0) (R 0) [304,20,40,192,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2152
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2153 : PairBound 9 := { available := 138, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 305 22 69 104 17 170 202 138 394), lower := (rows 305 22 69 104 17 32 64 128 256), losses := [] }

theorem u2153 : Upper (D 0) (R 0) [304,20,65,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2153
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2154 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 305 22 69 104 18 169 201 137 393), lower := (rows 305 22 69 104 18 32 64 128 256), losses := [] }

theorem u2154 : Upper (D 0) (R 0) [304,20,65,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2154
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2155 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 305 22 69 104 24 163 195 131 387), lower := (rows 305 22 69 104 24 32 64 128 256), losses := [] }

theorem u2155 : Upper (D 0) (R 0) [304,20,65,96,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2155
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2156 : Route 9 := (fun mask => (mask,id))

def c2156 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2156 : Upper (D 0) (R 0) [304,20,65,96,128] 13 := by
  apply FastRouting.sound _ _ [304,20,65,96,128] 13 (by decide) (choices 1) [1,2,8,128] r2156 c2156
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u916
  · exact u917
  · exact u918
  · exact u919

def b2157 : PairBound 9 := { available := 232, camps := [], pairs := [], upper := (rows 305 22 69 137 18 232 232 232 488), lower := (rows 305 22 69 137 18 32 64 128 256), losses := [] }

theorem u2157 : Upper (D 0) (R 0) [304,20,65,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2157
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2158 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 305 22 69 137 24 226 226 226 482), lower := (rows 305 22 69 137 24 32 64 128 256), losses := [] }

theorem u2158 : Upper (D 0) (R 0) [304,20,65,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2158
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2159 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 22 69 137 48 234 202 202 458), lower := (rows 305 22 69 137 48 32 64 128 256), losses := [] }

theorem u2159 : Upper (D 0) (R 0) [304,20,65,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2159
    (constants 0).1 (constants 0).2 (by decide +kernel)

#print axioms u2159
end Delivery.IrregularNine14.P00

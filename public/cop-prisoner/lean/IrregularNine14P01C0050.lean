import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0011

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3000 : PairBound 9 := { available := 170, camps := [], pairs := [], upper := (rows 51 322 84 137 20 170 234 170 426), lower := (rows 51 322 84 137 20 32 64 128 256), losses := [] }

theorem u3000 : Upper (D 1) (R 1) [50,320,80,129,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3000
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3001 : PairBound 9 := { available := 166, camps := [], pairs := [], upper := (rows 51 322 84 137 24 166 230 166 422), lower := (rows 51 322 84 137 24 32 64 128 256), losses := [] }

theorem u3001 : Upper (D 1) (R 1) [50,320,80,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3001
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3002 : PairBound 9 := { available := 142, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 322 84 137 48 174 206 142 398), lower := (rows 51 322 84 137 48 32 64 128 256), losses := [] }

theorem u3002 : Upper (D 1) (R 1) [50,320,80,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3002
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r3003 : Route 9 := (fun mask => (mask,id))

def c3003 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3003 : Upper (D 1) (R 1) [50,320,80,129,128] 13 := by
  apply FastRouting.sound _ _ [50,320,80,129,128] 13 (by decide) (choices 1) [2,4,8] r3003 c3003
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u670
  · exact u671
  · exact u672

def b3004 : PairBound 9 := { available := 172, camps := [], pairs := [], upper := (rows 51 322 84 138 17 172 236 172 428), lower := (rows 51 322 84 138 17 32 64 128 256), losses := [] }

theorem u3004 : Upper (D 1) (R 1) [50,320,80,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3004
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3005 : PairBound 9 := { available := 169, camps := [], pairs := [], upper := (rows 51 322 84 138 20 169 233 169 425), lower := (rows 51 322 84 138 20 32 64 128 256), losses := [] }

theorem u3005 : Upper (D 1) (R 1) [50,320,80,130,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3005
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3006 : PairBound 9 := { available := 165, camps := [], pairs := [], upper := (rows 51 322 84 138 24 165 229 165 421), lower := (rows 51 322 84 138 24 32 64 128 256), losses := [] }

theorem u3006 : Upper (D 1) (R 1) [50,320,80,130,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3006
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3007 : PairBound 9 := { available := 141, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 322 84 138 48 173 205 141 397), lower := (rows 51 322 84 138 48 32 64 128 256), losses := [] }

theorem u3007 : Upper (D 1) (R 1) [50,320,80,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3007
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r3008 : Route 9 := (fun mask => (mask,id))

def c3008 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3008 : Upper (D 1) (R 1) [50,320,80,130,128] 13 := by
  apply FastRouting.sound _ _ [50,320,80,130,128] 13 (by decide) (choices 1) [1,4,8] r3008 c3008
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u673
  · exact u674
  · exact u675

def b3009 : PairBound 9 := { available := 170, camps := [], pairs := [], upper := (rows 51 322 84 140 17 170 234 170 426), lower := (rows 51 322 84 140 17 32 64 128 256), losses := [] }

theorem u3009 : Upper (D 1) (R 1) [50,320,80,132,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3009
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3010 : PairBound 9 := { available := 169, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 51 322 84 140 18 169 233 169 425), lower := (rows 51 322 84 140 18 32 64 128 256), losses := [] }

theorem u3010 : Upper (D 1) (R 1) [50,320,80,132,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3010
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3011 : PairBound 9 := { available := 163, camps := [], pairs := [], upper := (rows 51 322 84 140 24 163 227 163 419), lower := (rows 51 322 84 140 24 32 64 128 256), losses := [] }

theorem u3011 : Upper (D 1) (R 1) [50,320,80,132,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3011
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3012 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 322 84 140 48 171 203 139 395), lower := (rows 51 322 84 140 48 32 64 128 256), losses := [] }

theorem u3012 : Upper (D 1) (R 1) [50,320,80,132,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3012
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r3013 : Route 9 := (fun mask => (mask,id))

def c3013 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3013 : Upper (D 1) (R 1) [50,320,80,132,128] 13 := by
  apply FastRouting.sound _ _ [50,320,80,132,128] 13 (by decide) (choices 1) [1,2,8] r3013 c3013
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u676
  · exact u677
  · exact u678

def b3014 : PairBound 9 := { available := 142, camps := [], pairs := [], upper := (rows 51 322 84 168 17 174 206 142 398), lower := (rows 51 322 84 168 17 32 64 128 256), losses := [] }

theorem u3014 : Upper (D 1) (R 1) [50,320,80,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3014
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3015 : PairBound 9 := { available := 141, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 51 322 84 168 18 173 205 141 397), lower := (rows 51 322 84 168 18 32 64 128 256), losses := [] }

theorem u3015 : Upper (D 1) (R 1) [50,320,80,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3015
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3016 : PairBound 9 := { available := 139, camps := [], pairs := [], upper := (rows 51 322 84 168 20 171 203 139 395), lower := (rows 51 322 84 168 20 32 64 128 256), losses := [] }

theorem u3016 : Upper (D 1) (R 1) [50,320,80,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3016
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3017 : PairBound 9 := { available := 135, camps := [], pairs := [], upper := (rows 51 322 84 168 24 167 199 135 391), lower := (rows 51 322 84 168 24 32 64 128 256), losses := [] }

theorem u3017 : Upper (D 1) (R 1) [50,320,80,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3017
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r3018 : Route 9 := (fun mask => (mask,id))

def c3018 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3018 : Upper (D 1) (R 1) [50,320,80,160,128] 13 := by
  apply FastRouting.sound _ _ [50,320,80,160,128] 13 (by decide) (choices 1) [1,2,4,8] r3018 c3018
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u679
  · exact u680
  · exact u681
  · exact u682

def b3019 : PairBound 9 := { available := 120, camps := [], pairs := [], upper := (rows 51 322 133 138 20 120 120 248 376), lower := (rows 51 322 133 138 20 32 64 128 256), losses := [] }

theorem u3019 : Upper (D 1) (R 1) [50,320,129,130,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3019
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3020 : PairBound 9 := { available := 116, camps := [], pairs := [], upper := (rows 51 322 133 138 24 116 116 244 372), lower := (rows 51 322 133 138 24 32 64 128 256), losses := [] }

theorem u3020 : Upper (D 1) (R 1) [50,320,129,130,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3020
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3021 : PairBound 9 := { available := 92, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 322 133 138 48 124 92 220 348), lower := (rows 51 322 133 138 48 32 64 128 256), losses := [] }

theorem u3021 : Upper (D 1) (R 1) [50,320,129,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3021
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3022 : PairBound 9 := { available := 60, camps := [{ cop := 0, region := 140, targets := 64 }], pairs := [(2,6)], upper := (rows 51 322 133 138 80 60 124 188 316), lower := (rows 51 322 133 138 80 32 64 128 256), losses := [] }

theorem u3022 : Upper (D 1) (R 1) [50,320,129,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3022
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3023 : PairBound 9 := { available := 108, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 51 322 133 152 18 108 108 236 364), lower := (rows 51 322 133 152 18 32 64 128 256), losses := [] }

theorem u3023 : Upper (D 1) (R 1) [50,320,129,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3023
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3024 : PairBound 9 := { available := 106, camps := [], pairs := [], upper := (rows 51 322 133 152 20 106 106 234 362), lower := (rows 51 322 133 152 20 32 64 128 256), losses := [] }

theorem u3024 : Upper (D 1) (R 1) [50,320,129,144,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3024
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3025 : PairBound 9 := { available := 102, camps := [], pairs := [], upper := (rows 51 322 133 152 24 102 102 230 358), lower := (rows 51 322 133 152 24 32 64 128 256), losses := [] }

theorem u3025 : Upper (D 1) (R 1) [50,320,129,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3025
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3026 : PairBound 9 := { available := 78, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 322 133 152 48 110 78 206 334), lower := (rows 51 322 133 152 48 32 64 128 256), losses := [] }

theorem u3026 : Upper (D 1) (R 1) [50,320,129,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3026
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3027 : PairBound 9 := { available := 46, camps := [{ cop := 0, region := 140, targets := 64 }], pairs := [(2,6)], upper := (rows 51 322 133 152 80 46 110 174 302), lower := (rows 51 322 133 152 80 32 64 128 256), losses := [] }

theorem u3027 : Upper (D 1) (R 1) [50,320,129,144,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3027
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3028 : PairBound 9 := { available := 60, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 51 322 133 200 18 60 124 188 316), lower := (rows 51 322 133 200 18 32 64 128 256), losses := [] }

theorem u3028 : Upper (D 1) (R 1) [50,320,129,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3028
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3029 : PairBound 9 := { available := 58, camps := [], pairs := [], upper := (rows 51 322 133 200 20 58 122 186 314), lower := (rows 51 322 133 200 20 32 64 128 256), losses := [] }

theorem u3029 : Upper (D 1) (R 1) [50,320,129,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3029
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3030 : PairBound 9 := { available := 54, camps := [], pairs := [], upper := (rows 51 322 133 200 24 54 118 182 310), lower := (rows 51 322 133 200 24 32 64 128 256), losses := [] }

theorem u3030 : Upper (D 1) (R 1) [50,320,129,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3030
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3031 : PairBound 9 := { available := 30, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 322 133 200 48 62 94 158 286), lower := (rows 51 322 133 200 48 32 64 128 256), losses := [] }

theorem u3031 : Upper (D 1) (R 1) [50,320,129,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3031
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3032 : PairBound 9 := { available := 108, camps := [], pairs := [], upper := (rows 51 322 134 152 17 108 108 236 364), lower := (rows 51 322 134 152 17 32 64 128 256), losses := [] }

theorem u3032 : Upper (D 1) (R 1) [50,320,130,144,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3032
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3033 : PairBound 9 := { available := 105, camps := [], pairs := [], upper := (rows 51 322 134 152 20 105 105 233 361), lower := (rows 51 322 134 152 20 32 64 128 256), losses := [] }

theorem u3033 : Upper (D 1) (R 1) [50,320,130,144,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3033
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3034 : PairBound 9 := { available := 101, camps := [], pairs := [], upper := (rows 51 322 134 152 24 101 101 229 357), lower := (rows 51 322 134 152 24 32 64 128 256), losses := [] }

theorem u3034 : Upper (D 1) (R 1) [50,320,130,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3034
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3035 : PairBound 9 := { available := 77, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 322 134 152 48 109 77 205 333), lower := (rows 51 322 134 152 48 32 64 128 256), losses := [] }

theorem u3035 : Upper (D 1) (R 1) [50,320,130,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3035
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3036 : PairBound 9 := { available := 45, camps := [{ cop := 0, region := 140, targets := 64 }], pairs := [(2,6)], upper := (rows 51 322 134 152 80 45 109 173 301), lower := (rows 51 322 134 152 80 32 64 128 256), losses := [] }

theorem u3036 : Upper (D 1) (R 1) [50,320,130,144,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3036
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3037 : PairBound 9 := { available := 60, camps := [], pairs := [], upper := (rows 51 322 134 200 17 60 124 188 316), lower := (rows 51 322 134 200 17 32 64 128 256), losses := [] }

theorem u3037 : Upper (D 1) (R 1) [50,320,130,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3037
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3038 : PairBound 9 := { available := 57, camps := [], pairs := [], upper := (rows 51 322 134 200 20 57 121 185 313), lower := (rows 51 322 134 200 20 32 64 128 256), losses := [] }

theorem u3038 : Upper (D 1) (R 1) [50,320,130,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3038
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3039 : PairBound 9 := { available := 53, camps := [], pairs := [], upper := (rows 51 322 134 200 24 53 117 181 309), lower := (rows 51 322 134 200 24 32 64 128 256), losses := [] }

theorem u3039 : Upper (D 1) (R 1) [50,320,130,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3039
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3040 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 322 134 200 48 61 93 157 285), lower := (rows 51 322 134 200 48 32 64 128 256), losses := [] }

theorem u3040 : Upper (D 1) (R 1) [50,320,130,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3040
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3041 : PairBound 9 := { available := 78, camps := [], pairs := [], upper := (rows 51 322 148 168 17 110 78 206 334), lower := (rows 51 322 148 168 17 32 64 128 256), losses := [] }

theorem u3041 : Upper (D 1) (R 1) [50,320,144,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3041
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3042 : PairBound 9 := { available := 77, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 51 322 148 168 18 109 77 205 333), lower := (rows 51 322 148 168 18 32 64 128 256), losses := [] }

theorem u3042 : Upper (D 1) (R 1) [50,320,144,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3042
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3043 : PairBound 9 := { available := 75, camps := [], pairs := [], upper := (rows 51 322 148 168 20 107 75 203 331), lower := (rows 51 322 148 168 20 32 64 128 256), losses := [] }

theorem u3043 : Upper (D 1) (R 1) [50,320,144,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3043
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3044 : PairBound 9 := { available := 71, camps := [], pairs := [], upper := (rows 51 322 148 168 24 103 71 199 327), lower := (rows 51 322 148 168 24 32 64 128 256), losses := [] }

theorem u3044 : Upper (D 1) (R 1) [50,320,144,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3044
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3045 : PairBound 9 := { available := 15, camps := [{ cop := 0, region := 140, targets := 64 }], pairs := [(2,6)], upper := (rows 51 322 148 168 80 47 79 143 271), lower := (rows 51 322 148 168 80 32 64 128 256), losses := [] }

theorem u3045 : Upper (D 1) (R 1) [50,320,144,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3045
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3046 : PairBound 9 := { available := 46, camps := [], pairs := [], upper := (rows 51 322 148 200 17 46 110 174 302), lower := (rows 51 322 148 200 17 32 64 128 256), losses := [] }

theorem u3046 : Upper (D 1) (R 1) [50,320,144,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3046
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3047 : PairBound 9 := { available := 45, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 51 322 148 200 18 45 109 173 301), lower := (rows 51 322 148 200 18 32 64 128 256), losses := [] }

theorem u3047 : Upper (D 1) (R 1) [50,320,144,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3047
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3048 : PairBound 9 := { available := 43, camps := [], pairs := [], upper := (rows 51 322 148 200 20 43 107 171 299), lower := (rows 51 322 148 200 20 32 64 128 256), losses := [] }

theorem u3048 : Upper (D 1) (R 1) [50,320,144,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3048
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3049 : PairBound 9 := { available := 39, camps := [], pairs := [], upper := (rows 51 322 148 200 24 39 103 167 295), lower := (rows 51 322 148 200 24 32 64 128 256), losses := [] }

theorem u3049 : Upper (D 1) (R 1) [50,320,144,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3049
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3050 : PairBound 9 := { available := 15, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 322 148 200 48 47 79 143 271), lower := (rows 51 322 148 200 48 32 64 128 256), losses := [] }

theorem u3050 : Upper (D 1) (R 1) [50,320,144,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3050
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3051 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 456, targets := 2 }], pairs := [(3,1)], upper := (rows 53 11 70 392 18 240 240 240 496), lower := (rows 53 11 70 392 18 32 64 128 256), losses := [] }

theorem u3051 : Upper (D 1) (R 1) [52,9,66,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3051
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3052 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 11 70 392 48 242 210 210 466), lower := (rows 53 11 70 392 48 32 64 128 256), losses := [] }

theorem u3052 : Upper (D 1) (R 1) [52,9,66,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3052
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3053 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 394, targets := 64 }], pairs := [(1,6)], upper := (rows 53 11 70 392 80 178 242 178 434), lower := (rows 53 11 70 392 80 32 64 128 256), losses := [] }

theorem u3053 : Upper (D 1) (R 1) [52,9,66,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3053
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m3054_2 : Upper (D 1) (R 1) [52,9,66,384,128,2] 13 :=
  permutation_upper _ _ _ [52,9,66,384,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u683

theorem m3054_16 : Upper (D 1) (R 1) [52,9,66,384,128,16] 13 :=
  permutation_upper _ _ _ [52,9,66,384,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u684

theorem m3054_64 : Upper (D 1) (R 1) [52,9,66,384,128,64] 13 :=
  permutation_upper _ _ _ [52,9,66,384,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u685

def r3054 : Route 9 := (fun mask => (mask,id))

def c3054 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3054 : Upper (D 1) (R 1) [52,9,66,384,128] 13 := by
  apply FastRouting.sound _ _ [52,9,66,384,128] 13 (by decide) (choices 1) [2,16,64] r3054 c3054
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m3054_2
  · exact m3054_16
  · exact m3054_64

def b3055 : PairBound 9 := { available := 432, camps := [{ cop := 4, region := 485, targets := 2 }], pairs := [(0,1)], upper := (rows 53 11 196 74 18 432 496 432 432), lower := (rows 53 11 196 74 18 32 64 128 256), losses := [] }

theorem u3055 : Upper (D 1) (R 1) [52,9,192,66,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3055
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3056 : PairBound 9 := { available := 402, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 11 196 74 48 434 466 402 402), lower := (rows 53 11 196 74 48 32 64 128 256), losses := [] }

theorem u3056 : Upper (D 1) (R 1) [52,9,192,66,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3056
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3057 : PairBound 9 := { available := 306, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(1,7)], upper := (rows 53 11 196 74 144 306 370 434 306), lower := (rows 53 11 196 74 144 32 64 128 256), losses := [] }

theorem u3057 : Upper (D 1) (R 1) [52,9,192,66,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3057
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3058 : PairBound 9 := { available := 178, camps := [], pairs := [], upper := (rows 53 11 196 74 272 178 242 178 434), lower := (rows 53 11 196 74 272 32 64 128 256), losses := [] }

theorem u3058 : Upper (D 1) (R 1) [52,9,192,66,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3058
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3059 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 229, targets := 2 }], pairs := [(0,1)], upper := (rows 53 11 196 266 18 240 240 240 496), lower := (rows 53 11 196 266 18 32 64 128 256), losses := [] }

theorem u3059 : Upper (D 1) (R 1) [52,9,192,258,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3059
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u3059
end Delivery.IrregularNine14.P01

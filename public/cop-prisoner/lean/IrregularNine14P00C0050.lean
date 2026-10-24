import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P00C0030
import IrregularNine14P00C0031

namespace Delivery.IrregularNine14.P00
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3000 : PairBound 9 := { available := 205, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 113 50 133 266 221 237 205 205 461), lower := (rows 113 50 133 266 16 32 64 128 256), losses := [] }

theorem u3000 : Upper (D 0) (R 0) [112,48,129,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3000
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3001 : PairBound 9 := { available := 203, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 113 50 133 268 219 235 203 203 459), lower := (rows 113 50 133 268 16 32 64 128 256), losses := [] }

theorem u3001 : Upper (D 0) (R 0) [112,48,129,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3001
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3002 : PairBound 9 := { available := 143, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 113 50 133 328 159 175 207 143 399), lower := (rows 113 50 133 328 16 32 64 128 256), losses := [] }

theorem u3002 : Upper (D 0) (R 0) [112,48,129,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3002
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3003 : PairBound 9 := { available := 79, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 113 50 133 392 95 111 79 207 335), lower := (rows 113 50 133 392 16 32 64 128 256), losses := [] }

theorem u3003 : Upper (D 0) (R 0) [112,48,129,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3003
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3004 : PairBound 9 := { available := 269, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 113 50 134 200 285 301 333 397 269), lower := (rows 113 50 134 200 16 32 64 128 256), losses := [] }

theorem u3004 : Upper (D 0) (R 0) [112,48,130,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3004
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3005 : PairBound 9 := { available := 205, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 113 50 134 265 221 237 205 205 461), lower := (rows 113 50 134 265 16 32 64 128 256), losses := [] }

theorem u3005 : Upper (D 0) (R 0) [112,48,130,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3005
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3006 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 113 50 134 268 217 233 201 201 457), lower := (rows 113 50 134 268 16 32 64 128 256), losses := [] }

theorem u3006 : Upper (D 0) (R 0) [112,48,130,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3006
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3007 : PairBound 9 := { available := 141, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 113 50 134 328 157 173 205 141 397), lower := (rows 113 50 134 328 16 32 64 128 256), losses := [] }

theorem u3007 : Upper (D 0) (R 0) [112,48,130,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3007
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3008 : PairBound 9 := { available := 77, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 113 50 134 392 93 109 77 205 333), lower := (rows 113 50 134 392 16 32 64 128 256), losses := [] }

theorem u3008 : Upper (D 0) (R 0) [112,48,130,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3008
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3009 : PairBound 9 := { available := 199, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 113 50 140 265 215 231 199 199 455), lower := (rows 113 50 140 265 16 32 64 128 256), losses := [] }

theorem u3009 : Upper (D 0) (R 0) [112,48,136,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3009
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3010 : PairBound 9 := { available := 197, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 113 50 140 266 213 229 197 197 453), lower := (rows 113 50 140 266 16 32 64 128 256), losses := [] }

theorem u3010 : Upper (D 0) (R 0) [112,48,136,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3010
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3011 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 113 50 140 268 211 227 195 195 451), lower := (rows 113 50 140 268 16 32 64 128 256), losses := [] }

theorem u3011 : Upper (D 0) (R 0) [112,48,136,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3011
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3012 : PairBound 9 := { available := 135, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 113 50 140 328 151 167 199 135 391), lower := (rows 113 50 140 328 16 32 64 128 256), losses := [] }

theorem u3012 : Upper (D 0) (R 0) [112,48,136,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3012
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3013 : PairBound 9 := { available := 143, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 113 50 196 265 159 175 207 143 399), lower := (rows 113 50 196 265 16 32 64 128 256), losses := [] }

theorem u3013 : Upper (D 0) (R 0) [112,48,192,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3013
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3014 : PairBound 9 := { available := 141, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 113 50 196 266 157 173 205 141 397), lower := (rows 113 50 196 266 16 32 64 128 256), losses := [] }

theorem u3014 : Upper (D 0) (R 0) [112,48,192,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3014
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3015 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 113 50 196 268 155 171 203 139 395), lower := (rows 113 50 196 268 16 32 64 128 256), losses := [] }

theorem u3015 : Upper (D 0) (R 0) [112,48,192,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3015
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3016 : PairBound 9 := { available := 15, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 113 50 196 392 31 47 79 143 271), lower := (rows 113 50 196 392 16 32 64 128 256), losses := [] }

theorem u3016 : Upper (D 0) (R 0) [112,48,192,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3016
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3017 : PairBound 9 := { available := 124, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 113 131 133 266 124 124 124 252 380), lower := (rows 113 131 133 266 16 32 64 128 256), losses := [] }

theorem u3017 : Upper (D 0) (R 0) [112,129,129,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3017
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3018 : PairBound 9 := { available := 110, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 113 131 133 280 126 110 110 238 366), lower := (rows 113 131 133 280 16 32 64 128 256), losses := [] }

theorem u3018 : Upper (D 0) (R 0) [112,129,129,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3018
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3019 : PairBound 9 := { available := 124, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 113 131 134 265 124 124 124 252 380), lower := (rows 113 131 134 265 16 32 64 128 256), losses := [] }

theorem u3019 : Upper (D 0) (R 0) [112,129,130,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3019
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3020 : PairBound 9 := { available := 121, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 113 131 134 268 121 121 121 249 377), lower := (rows 113 131 134 268 16 32 64 128 256), losses := [] }

theorem u3020 : Upper (D 0) (R 0) [112,129,130,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3020
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3021 : PairBound 9 := { available := 109, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 113 131 134 280 125 109 109 237 365), lower := (rows 113 131 134 280 16 32 64 128 256), losses := [] }

theorem u3021 : Upper (D 0) (R 0) [112,129,130,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3021
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3022 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c3022 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3022 : Upper (D 0) (R 0) [112,129,136,257] 13 := by
  apply FastRouting.sound _ _ [112,129,136,257] 13 (by decide) (choices 1) [2,4,32] r3022 c3022
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1814
  · exact u1815
  · exact u1816

def b3023 : PairBound 9 := { available := 117, camps := [{ cop := 2, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 113 131 140 266 117 117 117 245 373), lower := (rows 113 131 140 266 16 32 64 128 256), losses := [] }

theorem u3023 : Upper (D 0) (R 0) [112,129,136,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3023
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3024 : PairBound 9 := { available := 115, camps := [{ cop := 1, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 113 131 140 268 115 115 115 243 371), lower := (rows 113 131 140 268 16 32 64 128 256), losses := [] }

theorem u3024 : Upper (D 0) (R 0) [112,129,136,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3024
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3025 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c3025 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3025 : Upper (D 0) (R 0) [112,129,136,272] 13 := by
  apply FastRouting.sound _ _ [112,129,136,272] 13 (by decide) (choices 1) [1,2,4,32] r3025 c3025
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1817
  · exact u1818
  · exact u1819
  · exact u1820

def r3026 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c3026 : Nat → Fin 9 := (fun mask => match mask with | 128 => 7 | 256 => 8 | _ => 0)

theorem u3026 : Upper (D 0) (R 0) [112,129,144,257] 13 := by
  apply FastRouting.sound _ _ [112,129,144,257] 13 (by decide) (choices 1) [2,4,8,32] r3026 c3026
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1821
  · exact u1822
  · exact u1823
  · exact u1824

def r3027 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c3027 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3027 : Upper (D 0) (R 0) [112,129,144,258] 13 := by
  apply FastRouting.sound _ _ [112,129,144,258] 13 (by decide) (choices 1) [1,4,8,32] r3027 c3027
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1825
  · exact u1826
  · exact u1827
  · exact u1828

def r3028 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c3028 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3028 : Upper (D 0) (R 0) [112,129,144,260] 13 := by
  apply FastRouting.sound _ _ [112,129,144,260] 13 (by decide) (choices 1) [1,2,8,32] r3028 c3028
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1829
  · exact u1830
  · exact u1831
  · exact u1832

def r3029 : Route 9 := (fun mask => (mask,id))

def c3029 : Nat → Fin 9 := (fun mask => match mask with | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3029 : Upper (D 0) (R 0) [112,129,144,288] 13 := by
  apply FastRouting.sound _ _ [112,129,144,288] 13 (by decide) (choices 1) [1,2,4,8,64] r3029 c3029
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u1833
  · exact u1834
  · exact u1835
  · exact u1836
  · exact u1837

def b3030 : PairBound 9 := { available := 121, camps := [{ cop := 7, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 113 134 134 265 121 121 121 249 377), lower := (rows 113 134 134 265 16 32 64 128 256), losses := [] }

theorem u3030 : Upper (D 0) (R 0) [112,132,130,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3030
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3031 : PairBound 9 := { available := 105, camps := [{ cop := 7, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 113 134 134 280 121 105 105 233 361), lower := (rows 113 134 134 280 16 32 64 128 256), losses := [] }

theorem u3031 : Upper (D 0) (R 0) [112,132,130,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3031
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3032 : PairBound 9 := { available := 115, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 113 134 140 265 115 115 115 243 371), lower := (rows 113 134 140 265 16 32 64 128 256), losses := [] }

theorem u3032 : Upper (D 0) (R 0) [112,132,136,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3032
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3033 : PairBound 9 := { available := 113, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 113 134 140 266 113 113 113 241 369), lower := (rows 113 134 140 266 16 32 64 128 256), losses := [] }

theorem u3033 : Upper (D 0) (R 0) [112,132,136,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3033
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3034 : PairBound 9 := { available := 99, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 113 134 140 280 115 99 99 227 355), lower := (rows 113 134 140 280 16 32 64 128 256), losses := [] }

theorem u3034 : Upper (D 0) (R 0) [112,132,136,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3034
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3035 : PairBound 9 := { available := 107, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 113 134 148 265 123 107 107 235 363), lower := (rows 113 134 148 265 16 32 64 128 256), losses := [] }

theorem u3035 : Upper (D 0) (R 0) [112,132,144,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3035
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3036 : PairBound 9 := { available := 105, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 113 134 148 266 121 105 105 233 361), lower := (rows 113 134 148 266 16 32 64 128 256), losses := [] }

theorem u3036 : Upper (D 0) (R 0) [112,132,144,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3036
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3037 : PairBound 9 := { available := 75, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 113 134 148 296 91 107 75 203 331), lower := (rows 113 134 148 296 16 32 64 128 256), losses := [] }

theorem u3037 : Upper (D 0) (R 0) [112,132,144,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3037
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3038 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c3038 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3038 : Upper (D 0) (R 0) [112,132,257,144] 13 := by
  apply FastRouting.sound _ _ [112,132,257,144] 13 (by decide) (choices 1) [1,2,8,32] r3038 c3038
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1838
  · exact u1839
  · exact u1840
  · exact u1841

def b3039 : PairBound 9 := { available := 105, camps := [{ cop := 3, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 113 134 262 152 121 105 105 233 361), lower := (rows 113 134 262 152 16 32 64 128 256), losses := [] }

theorem u3039 : Upper (D 0) (R 0) [112,132,258,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3039
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3040 : PairBound 9 := { available := 99, camps := [{ cop := 1, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 113 134 268 152 115 99 99 227 355), lower := (rows 113 134 268 152 16 32 64 128 256), losses := [] }

theorem u3040 : Upper (D 0) (R 0) [112,132,264,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3040
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3041 : Route 9 := (fun mask => (mask,id))

def c3041 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3041 : Upper (D 0) (R 0) [112,132,272,160] 13 := by
  apply FastRouting.sound _ _ [112,132,272,160] 13 (by decide) (choices 1) [1,2,8,64] r3041 c3041
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1842
  · exact u1843
  · exact u1844
  · exact u1845

def r3042 : Route 9 := (fun mask => (mask,id))

def c3042 : Nat → Fin 9 := (fun mask => match mask with | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3042 : Upper (D 0) (R 0) [112,144,160,257] 13 := by
  apply FastRouting.sound _ _ [112,144,160,257] 13 (by decide) (choices 1) [1,2,4,8,64] r3042 c3042
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u1846
  · exact u1847
  · exact u1848
  · exact u1849
  · exact u1850

def r3043 : Route 9 := (fun mask => (mask,id))

def c3043 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3043 : Upper (D 0) (R 0) [112,144,160,258] 13 := by
  apply FastRouting.sound _ _ [112,144,160,258] 13 (by decide) (choices 1) [1,4,8,64] r3043 c3043
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1851
  · exact u1852
  · exact u1853
  · exact u1854

def r3044 : Route 9 := (fun mask => (mask,id))

def c3044 : Nat → Fin 9 := (fun mask => match mask with | 32 => 5 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3044 : Upper (D 0) (R 0) [112,144,160,320] 13 := by
  apply FastRouting.sound _ _ [112,144,160,320] 13 (by decide) (choices 1) [1,2,4,8] r3044 c3044
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1855
  · exact u1856
  · exact u1857
  · exact u1858

def b3045 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 263 11 52 25 240 224 224 224 480), lower := (rows 263 11 52 25 16 32 64 128 256), losses := [] }

theorem u3045 : Upper (D 0) (R 0) [262,9,48,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3045
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3046 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 263 11 52 56 209 225 193 193 449), lower := (rows 263 11 52 56 16 32 64 128 256), losses := [] }

theorem u3046 : Upper (D 0) (R 0) [262,9,48,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3046
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3047 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 263 11 52 73 240 240 240 240 496), lower := (rows 263 11 52 73 16 32 64 128 256), losses := [] }

theorem u3047 : Upper (D 0) (R 0) [262,9,48,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3047
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3048 : Route 9 := (fun mask => (mask,id))

def c3048 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u3048 : Upper (D 0) (R 0) [262,9,48,80] 13 := by
  apply FastRouting.sound _ _ [262,9,48,80] 13 (by decide) (choices 1) [1,32,64,128] r3048 c3048
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1859
  · exact u1860
  · exact u1861
  · exact u1862

def r3049 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c3049 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u3049 : Upper (D 0) (R 0) [262,9,48,192] 13 := by
  apply FastRouting.sound _ _ [262,9,48,192] 13 (by decide) (choices 1) [1,32,64] r3049 c3049
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1863
  · exact u1864
  · exact u1865

def b3050 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 263 19 44 25 240 224 224 224 480), lower := (rows 263 19 44 25 16 32 64 128 256), losses := [] }

theorem u3050 : Upper (D 0) (R 0) [262,17,40,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3050
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3051 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 263 19 44 41 208 240 208 208 464), lower := (rows 263 19 44 41 16 32 64 128 256), losses := [] }

theorem u3051 : Upper (D 0) (R 0) [262,17,40,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3051
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3052 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 263 19 44 56 209 225 193 193 449), lower := (rows 263 19 44 56 16 32 64 128 256), losses := [] }

theorem u3052 : Upper (D 0) (R 0) [262,17,40,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3052
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3053 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 180, targets := 1 }], pairs := [(2,0)], upper := (rows 263 19 44 73 240 240 240 240 496), lower := (rows 263 19 44 73 16 32 64 128 256), losses := [] }

theorem u3053 : Upper (D 0) (R 0) [262,17,40,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3053
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3054 : Route 9 := (fun mask => (mask,id))

def c3054 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u3054 : Upper (D 0) (R 0) [262,17,40,80] 13 := by
  apply FastRouting.sound _ _ [262,17,40,80] 13 (by decide) (choices 1) [1,32,64,128] r3054 c3054
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1866
  · exact u1867
  · exact u1868
  · exact u1869

def b3055 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 263 19 44 104 209 241 209 209 465), lower := (rows 263 19 44 104 16 32 64 128 256), losses := [] }

theorem u3055 : Upper (D 0) (R 0) [262,17,40,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3055
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3056 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c3056 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u3056 : Upper (D 0) (R 0) [262,17,40,192] 13 := by
  apply FastRouting.sound _ _ [262,17,40,192] 13 (by decide) (choices 1) [1,32,64] r3056 c3056
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1870
  · exact u1871
  · exact u1872

def b3057 : PairBound 9 := { available := 232, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 263 19 100 25 248 232 232 232 488), lower := (rows 263 19 100 25 16 32 64 128 256), losses := [] }

theorem u3057 : Upper (D 0) (R 0) [262,17,96,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3057
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3058 : PairBound 9 := { available := 216, camps := [{ cop := 3, region := 212, targets := 1 }], pairs := [(2,0)], upper := (rows 263 19 100 41 216 248 216 216 472), lower := (rows 263 19 100 41 16 32 64 128 256), losses := [] }

theorem u3058 : Upper (D 0) (R 0) [262,17,96,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3058
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3059 : Route 9 := (fun mask => (mask,id))

def c3059 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3059 : Upper (D 0) (R 0) [262,17,96,48] 13 := by
  apply FastRouting.sound _ _ [262,17,96,48] 13 (by decide) (choices 1) [1,8,64,128] r3059 c3059
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1873
  · exact u1874
  · exact u1875
  · exact u1876

#print axioms u3059
end Delivery.IrregularNine14.P00

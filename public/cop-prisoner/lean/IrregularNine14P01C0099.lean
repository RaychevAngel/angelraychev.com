import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0036
import IrregularNine14P01C0037

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5940 : PairBound 9 := { available := 482, camps := [{ cop := 0, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 23 98 13 152 498 482 482 482 482), lower := (rows 23 98 13 152 16 32 64 128 256), losses := [] }

theorem u5940 : Upper (D 1) (R 1) [22,96,9,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5940
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5941 : Route 9 := (fun mask => (mask,id))

def c5941 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | _ => 0)

theorem u5941 : Upper (D 1) (R 1) [22,96,9,160] 13 := by
  apply FastRouting.sound _ _ [22,96,9,160] 13 (by decide) (choices 1) [2,64,128,256] r5941 c5941
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2193
  · exact u2194
  · exact u2195
  · exact u2196

def r5942 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c5942 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u5942 : Upper (D 1) (R 1) [22,96,9,258] 13 := by
  apply FastRouting.sound _ _ [22,96,9,258] 13 (by decide) (choices 1) [32,128] r5942 c5942
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2197
  · exact u2198

def b5943 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 23 98 13 280 242 226 226 226 482), lower := (rows 23 98 13 280 16 32 64 128 256), losses := [] }

theorem u5943 : Upper (D 1) (R 1) [22,96,9,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5943
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5944 : Route 9 := (fun mask => (mask,id))

def c5944 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5944 : Upper (D 1) (R 1) [22,96,9,288] 13 := by
  apply FastRouting.sound _ _ [22,96,9,288] 13 (by decide) (choices 1) [2,64,128] r5944 c5944
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2199
  · exact u2200
  · exact u2201

def r5945 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c5945 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u5945 : Upper (D 1) (R 1) [22,96,9,384] 13 := by
  apply FastRouting.sound _ _ [22,96,9,384] 13 (by decide) (choices 1) [2,32,128] r5945 c5945
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2202
  · exact u2203
  · exact u2204

def b5946 : PairBound 9 := { available := 488, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 23 98 133 26 504 488 488 488 488), lower := (rows 23 98 133 26 16 32 64 128 256), losses := [] }

theorem u5946 : Upper (D 1) (R 1) [22,96,129,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5946
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5947 : PairBound 9 := { available := 472, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 23 98 133 42 472 504 472 472 472), lower := (rows 23 98 133 42 16 32 64 128 256), losses := [] }

theorem u5947 : Upper (D 1) (R 1) [22,96,129,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5947
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5948 : PairBound 9 := { available := 458, camps := [{ cop := 3, region := 450, targets := 16 }], pairs := [(1,4)], upper := (rows 23 98 133 56 474 490 458 458 458), lower := (rows 23 98 133 56 16 32 64 128 256), losses := [] }

theorem u5948 : Upper (D 1) (R 1) [22,96,129,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5948
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5949 : PairBound 9 := { available := 410, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 23 98 133 104 410 442 474 410 410), lower := (rows 23 98 133 104 16 32 64 128 256), losses := [] }

theorem u5949 : Upper (D 1) (R 1) [22,96,129,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5949
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5950 : PairBound 9 := { available := 376, camps := [{ cop := 3, region := 370, targets := 128 }], pairs := [(1,7)], upper := (rows 23 98 133 138 376 376 376 504 376), lower := (rows 23 98 133 138 16 32 64 128 256), losses := [] }

theorem u5950 : Upper (D 1) (R 1) [22,96,129,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5950
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5951 : PairBound 9 := { available := 362, camps := [{ cop := 3, region := 354, targets := 16 }], pairs := [(1,4)], upper := (rows 23 98 133 152 378 362 362 490 362), lower := (rows 23 98 133 152 16 32 64 128 256), losses := [] }

theorem u5951 : Upper (D 1) (R 1) [22,96,129,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5951
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5952 : PairBound 9 := { available := 346, camps := [{ cop := 3, region := 338, targets := 128 }], pairs := [(1,7)], upper := (rows 23 98 133 168 346 378 346 474 346), lower := (rows 23 98 133 168 16 32 64 128 256), losses := [] }

theorem u5952 : Upper (D 1) (R 1) [22,96,129,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5952
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5953 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c5953 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u5953 : Upper (D 1) (R 1) [22,96,129,258] 13 := by
  apply FastRouting.sound _ _ [22,96,129,258] 13 (by decide) (choices 1) [8,32,128] r5953 c5953
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2205
  · exact u2206
  · exact u2207

def b5954 : PairBound 9 := { available := 234, camps := [{ cop := 3, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 23 98 133 280 250 234 234 234 490), lower := (rows 23 98 133 280 16 32 64 128 256), losses := [] }

theorem u5954 : Upper (D 1) (R 1) [22,96,129,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5954
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5955 : Route 9 := (fun mask => (mask,id))

def c5955 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5955 : Upper (D 1) (R 1) [22,96,129,288] 13 := by
  apply FastRouting.sound _ _ [22,96,129,288] 13 (by decide) (choices 1) [2,8,64,128] r5955 c5955
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2208
  · exact u2209
  · exact u2210
  · exact u2211

def b5956 : PairBound 9 := { available := 122, camps := [{ cop := 3, region := 114, targets := 128 }], pairs := [(1,7)], upper := (rows 23 98 133 392 122 122 122 250 378), lower := (rows 23 98 133 392 16 32 64 128 256), losses := [] }

theorem u5956 : Upper (D 1) (R 1) [22,96,129,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5956
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5957 : PairBound 9 := { available := 496, camps := [{ cop := 0, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 23 98 140 11 496 496 496 496 496), lower := (rows 23 98 140 11 16 32 64 128 256), losses := [] }

theorem u5957 : Upper (D 1) (R 1) [22,96,136,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5957
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5958 : PairBound 9 := { available := 482, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 23 98 140 25 498 482 482 482 482), lower := (rows 23 98 140 25 16 32 64 128 256), losses := [] }

theorem u5958 : Upper (D 1) (R 1) [22,96,136,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5958
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5959 : PairBound 9 := { available := 481, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 23 98 140 26 497 481 481 481 481), lower := (rows 23 98 140 26 16 32 64 128 256), losses := [] }

theorem u5959 : Upper (D 1) (R 1) [22,96,136,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5959
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5960 : PairBound 9 := { available := 466, camps := [], pairs := [(2,5)], upper := (rows 23 98 140 41 466 498 466 466 466), lower := (rows 23 98 140 41 16 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 12 8 19 0 67 131 259), good := (rows 471 466 140 477 16 0 64 128 256) }] }

theorem u5960 : Upper (D 1) (R 1) [22,96,136,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5960
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5961 : PairBound 9 := { available := 465, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 23 98 140 42 465 497 465 465 465), lower := (rows 23 98 140 42 16 32 64 128 256), losses := [] }

theorem u5961 : Upper (D 1) (R 1) [22,96,136,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5961
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5962 : PairBound 9 := { available := 451, camps := [{ cop := 0, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 23 98 140 56 467 483 451 451 451), lower := (rows 23 98 140 56 16 32 64 128 256), losses := [] }

theorem u5962 : Upper (D 1) (R 1) [22,96,136,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5962
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5963 : PairBound 9 := { available := 403, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 23 98 140 104 403 435 467 403 403), lower := (rows 23 98 140 104 16 32 64 128 256), losses := [] }

theorem u5963 : Upper (D 1) (R 1) [22,96,136,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5963
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5964 : PairBound 9 := { available := 370, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 23 98 140 137 370 370 370 498 370), lower := (rows 23 98 140 137 16 32 64 128 256), losses := [] }

theorem u5964 : Upper (D 1) (R 1) [22,96,136,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5964
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5965 : PairBound 9 := { available := 369, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 23 98 140 138 369 369 369 497 369), lower := (rows 23 98 140 138 16 32 64 128 256), losses := [] }

theorem u5965 : Upper (D 1) (R 1) [22,96,136,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5965
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5966 : PairBound 9 := { available := 355, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 23 98 140 152 371 355 355 483 355), lower := (rows 23 98 140 152 16 32 64 128 256), losses := [] }

theorem u5966 : Upper (D 1) (R 1) [22,96,136,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5966
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5967 : PairBound 9 := { available := 339, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 23 98 140 168 339 371 339 467 339), lower := (rows 23 98 140 168 16 32 64 128 256), losses := [] }

theorem u5967 : Upper (D 1) (R 1) [22,96,136,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5967
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5968 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c5968 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u5968 : Upper (D 1) (R 1) [22,96,136,257] 13 := by
  apply FastRouting.sound _ _ [22,96,136,257] 13 (by decide) (choices 1) [2,32,128] r5968 c5968
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2212
  · exact u2213
  · exact u2214

def r5969 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c5969 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u5969 : Upper (D 1) (R 1) [22,96,136,258] 13 := by
  apply FastRouting.sound _ _ [22,96,136,258] 13 (by decide) (choices 1) [1,32,128] r5969 c5969
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2215
  · exact u2216
  · exact u2217

def b5970 : PairBound 9 := { available := 227, camps := [{ cop := 0, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 23 98 140 280 243 227 227 227 483), lower := (rows 23 98 140 280 16 32 64 128 256), losses := [] }

theorem u5970 : Upper (D 1) (R 1) [22,96,136,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5970
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5971 : Route 9 := (fun mask => (mask,id))

def c5971 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5971 : Upper (D 1) (R 1) [22,96,136,288] 13 := by
  apply FastRouting.sound _ _ [22,96,136,288] 13 (by decide) (choices 1) [1,2,64,128] r5971 c5971
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2218
  · exact u2219
  · exact u2220
  · exact u2221

def b5972 : PairBound 9 := { available := 115, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 23 98 140 392 115 115 115 243 371), lower := (rows 23 98 140 392 16 32 64 128 256), losses := [] }

theorem u5972 : Upper (D 1) (R 1) [22,96,136,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5972
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5973 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 23 98 261 26 248 232 232 232 488), lower := (rows 23 98 261 26 16 32 64 128 256), losses := [] }

theorem u5973 : Upper (D 1) (R 1) [22,96,257,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5973
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5974 : PairBound 9 := { available := 216, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 23 98 261 42 216 248 216 216 472), lower := (rows 23 98 261 42 16 32 64 128 256), losses := [] }

theorem u5974 : Upper (D 1) (R 1) [22,96,257,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5974
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5975 : PairBound 9 := { available := 202, camps := [{ cop := 3, region := 194, targets := 16 }], pairs := [(1,4)], upper := (rows 23 98 261 56 218 234 202 202 458), lower := (rows 23 98 261 56 16 32 64 128 256), losses := [] }

theorem u5975 : Upper (D 1) (R 1) [22,96,257,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5975
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5976 : PairBound 9 := { available := 154, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 23 98 261 104 154 186 218 154 410), lower := (rows 23 98 261 104 16 32 64 128 256), losses := [] }

theorem u5976 : Upper (D 1) (R 1) [22,96,257,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5976
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5977 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c5977 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u5977 : Upper (D 1) (R 1) [22,96,257,130] 13 := by
  apply FastRouting.sound _ _ [22,96,257,130] 13 (by decide) (choices 1) [8,32,128] r5977 c5977
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2222
  · exact u2223
  · exact u2224

def b5978 : PairBound 9 := { available := 234, camps := [{ cop := 3, region := 98, targets := 16 }], pairs := [(1,4)], upper := (rows 23 98 261 152 250 234 234 234 490), lower := (rows 23 98 261 152 16 32 64 128 256), losses := [] }

theorem u5978 : Upper (D 1) (R 1) [22,96,257,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5978
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5979 : Route 9 := (fun mask => (mask,id))

def c5979 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5979 : Upper (D 1) (R 1) [22,96,257,160] 13 := by
  apply FastRouting.sound _ _ [22,96,257,160] 13 (by decide) (choices 1) [2,8,64,128] r5979 c5979
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2225
  · exact u2226
  · exact u2227
  · exact u2228

def b5980 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 23 98 268 11 240 240 240 240 496), lower := (rows 23 98 268 11 16 32 64 128 256), losses := [] }

theorem u5980 : Upper (D 1) (R 1) [22,96,264,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5980
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5981 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 23 98 268 25 242 226 226 226 482), lower := (rows 23 98 268 25 16 32 64 128 256), losses := [] }

theorem u5981 : Upper (D 1) (R 1) [22,96,264,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5981
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5982 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 23 98 268 26 241 225 225 225 481), lower := (rows 23 98 268 26 16 32 64 128 256), losses := [] }

theorem u5982 : Upper (D 1) (R 1) [22,96,264,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5982
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5983 : PairBound 9 := { available := 210, camps := [], pairs := [(2,5)], upper := (rows 23 98 268 41 210 242 210 210 466), lower := (rows 23 98 268 41 16 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 12 8 19 0 67 131 259), good := (rows 471 466 268 477 16 0 64 128 256) }] }

theorem u5983 : Upper (D 1) (R 1) [22,96,264,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5983
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5984 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 23 98 268 42 209 241 209 209 465), lower := (rows 23 98 268 42 16 32 64 128 256), losses := [] }

theorem u5984 : Upper (D 1) (R 1) [22,96,264,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5984
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5985 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 23 98 268 56 211 227 195 195 451), lower := (rows 23 98 268 56 16 32 64 128 256), losses := [] }

theorem u5985 : Upper (D 1) (R 1) [22,96,264,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5985
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5986 : PairBound 9 := { available := 147, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 23 98 268 104 147 179 211 147 403), lower := (rows 23 98 268 104 16 32 64 128 256), losses := [] }

theorem u5986 : Upper (D 1) (R 1) [22,96,264,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5986
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5987 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c5987 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u5987 : Upper (D 1) (R 1) [22,96,264,129] 13 := by
  apply FastRouting.sound _ _ [22,96,264,129] 13 (by decide) (choices 1) [2,32,128] r5987 c5987
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2229
  · exact u2230
  · exact u2231

def r5988 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c5988 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u5988 : Upper (D 1) (R 1) [22,96,264,130] 13 := by
  apply FastRouting.sound _ _ [22,96,264,130] 13 (by decide) (choices 1) [1,32,128] r5988 c5988
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2232
  · exact u2233
  · exact u2234

def b5989 : PairBound 9 := { available := 227, camps := [{ cop := 0, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 23 98 268 152 243 227 227 227 483), lower := (rows 23 98 268 152 16 32 64 128 256), losses := [] }

theorem u5989 : Upper (D 1) (R 1) [22,96,264,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5989
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5990 : Route 9 := (fun mask => (mask,id))

def c5990 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5990 : Upper (D 1) (R 1) [22,96,264,160] 13 := by
  apply FastRouting.sound _ _ [22,96,264,160] 13 (by decide) (choices 1) [1,2,64,128] r5990 c5990
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2235
  · exact u2236
  · exact u2237
  · exact u2238

def b5991 : PairBound 9 := { available := 248, camps := [{ cop := 0, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 23 98 388 11 248 248 248 248 504), lower := (rows 23 98 388 11 16 32 64 128 256), losses := [] }

theorem u5991 : Upper (D 1) (R 1) [22,96,384,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5991
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5992 : PairBound 9 := { available := 234, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 23 98 388 25 250 234 234 234 490), lower := (rows 23 98 388 25 16 32 64 128 256), losses := [] }

theorem u5992 : Upper (D 1) (R 1) [22,96,384,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5992
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5993 : PairBound 9 := { available := 233, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 23 98 388 26 249 233 233 233 489), lower := (rows 23 98 388 26 16 32 64 128 256), losses := [] }

theorem u5993 : Upper (D 1) (R 1) [22,96,384,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5993
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5994 : Route 9 := (fun mask => (mask,id))

def c5994 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5994 : Upper (D 1) (R 1) [22,96,384,33] 13 := by
  apply FastRouting.sound _ _ [22,96,384,33] 13 (by decide) (choices 1) [2,8,64,128] r5994 c5994
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2239
  · exact u2240
  · exact u2241
  · exact u2242

def b5995 : PairBound 9 := { available := 217, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 23 98 388 42 217 249 217 217 473), lower := (rows 23 98 388 42 16 32 64 128 256), losses := [] }

theorem u5995 : Upper (D 1) (R 1) [22,96,384,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5995
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5996 : Route 9 := (fun mask => (mask,id))

def c5996 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5996 : Upper (D 1) (R 1) [22,96,384,48] 13 := by
  apply FastRouting.sound _ _ [22,96,384,48] 13 (by decide) (choices 1) [1,2,8,64,128] r5996 c5996
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2243
  · exact u2244
  · exact u2245
  · exact u2246
  · exact u2247

def b5997 : PairBound 9 := { available := 155, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 23 98 388 104 155 187 219 155 411), lower := (rows 23 98 388 104 16 32 64 128 256), losses := [] }

theorem u5997 : Upper (D 1) (R 1) [22,96,384,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5997
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5998 : PairBound 9 := { available := 122, camps := [{ cop := 3, region := 114, targets := 128 }], pairs := [(1,7)], upper := (rows 23 98 388 137 122 122 122 250 378), lower := (rows 23 98 388 137 16 32 64 128 256), losses := [] }

theorem u5998 : Upper (D 1) (R 1) [22,96,384,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5998
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5999 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c5999 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5999 : Upper (D 1) (R 1) [22,96,384,130] 13 := by
  apply FastRouting.sound _ _ [22,96,384,130] 13 (by decide) (choices 1) [1,8,32] r5999 c5999
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2248
  · exact u2249
  · exact u2250

#print axioms u5999
end Delivery.IrregularNine14.P01

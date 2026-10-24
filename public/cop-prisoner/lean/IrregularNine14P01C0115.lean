import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0053
import IrregularNine14P01C0054
import IrregularNine14P01C0055

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6900 : PairBound 9 := { available := 434, camps := [{ cop := 3, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 53 74 134 73 434 434 498 434 434), lower := (rows 53 74 134 73 16 32 64 128 256), losses := [] }

theorem u6900 : Upper (D 1) (R 1) [52,72,130,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6900
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6901 : PairBound 9 := { available := 433, camps := [{ cop := 6, region := 10, targets := 16 }], pairs := [(1,4)], upper := (rows 53 74 134 74 433 433 497 433 433), lower := (rows 53 74 134 74 16 32 64 128 256), losses := [] }

theorem u6901 : Upper (D 1) (R 1) [52,72,130,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6901
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6902 : PairBound 9 := { available := 419, camps := [{ cop := 3, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 53 74 134 88 435 419 483 419 419), lower := (rows 53 74 134 88 16 32 64 128 256), losses := [] }

theorem u6902 : Upper (D 1) (R 1) [52,72,130,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6902
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6903 : PairBound 9 := { available := 370, camps := [{ cop := 2, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 53 74 134 137 370 370 370 498 370), lower := (rows 53 74 134 137 16 32 64 128 256), losses := [] }

theorem u6903 : Upper (D 1) (R 1) [52,72,130,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6903
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6904 : PairBound 9 := { available := 369, camps := [{ cop := 2, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 53 74 134 138 369 369 369 497 369), lower := (rows 53 74 134 138 16 32 64 128 256), losses := [] }

theorem u6904 : Upper (D 1) (R 1) [52,72,130,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6904
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6905 : PairBound 9 := { available := 355, camps := [{ cop := 2, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 53 74 134 152 371 355 355 483 355), lower := (rows 53 74 134 152 16 32 64 128 256), losses := [] }

theorem u6905 : Upper (D 1) (R 1) [52,72,130,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6905
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6906 : PairBound 9 := { available := 307, camps := [{ cop := 3, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 53 74 134 200 307 307 371 435 307), lower := (rows 53 74 134 200 16 32 64 128 256), losses := [] }

theorem u6906 : Upper (D 1) (R 1) [52,72,130,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6906
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6907 : Route 9 := (fun mask => (mask,id))

def c6907 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6907 : Upper (D 1) (R 1) [52,72,130,257] 13 := by
  apply FastRouting.sound _ _ [52,72,130,257] 13 (by decide) (choices 1) [2,32,64,128] r6907 c6907
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3229
  · exact u3230
  · exact u3231
  · exact u3232

def b6908 : PairBound 9 := { available := 241, camps := [{ cop := 2, region := 113, targets := 2 }], pairs := [(0,1)], upper := (rows 53 74 134 266 241 241 241 241 497), lower := (rows 53 74 134 266 16 32 64 128 256), losses := [] }

theorem u6908 : Upper (D 1) (R 1) [52,72,130,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6908
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6909 : Route 9 := (fun mask => (mask,id))

def c6909 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6909 : Upper (D 1) (R 1) [52,72,130,272] 13 := by
  apply FastRouting.sound _ _ [52,72,130,272] 13 (by decide) (choices 1) [1,2,32,64,128] r6909 c6909
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3233
  · exact u3234
  · exact u3235
  · exact u3236
  · exact u3237

def b6910 : PairBound 9 := { available := 179, camps := [{ cop := 3, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 53 74 134 328 179 179 243 179 435), lower := (rows 53 74 134 328 16 32 64 128 256), losses := [] }

theorem u6910 : Upper (D 1) (R 1) [52,72,130,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6910
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6911 : PairBound 9 := { available := 115, camps := [{ cop := 2, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 53 74 134 392 115 115 115 243 371), lower := (rows 53 74 134 392 16 32 64 128 256), losses := [] }

theorem u6911 : Upper (D 1) (R 1) [52,72,130,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6911
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6912 : Route 9 := (fun mask => (mask,id))

def c6912 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u6912 : Upper (D 1) (R 1) [52,72,192,3] 13 := by
  apply FastRouting.sound _ _ [52,72,192,3] 13 (by decide) (choices 1) [2,32,128,256] r6912 c6912
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3238
  · exact u3239
  · exact u3240
  · exact u3241

def b6913 : PairBound 9 := { available := 418, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 74 196 25 434 418 482 418 418), lower := (rows 53 74 196 25 16 32 64 128 256), losses := [] }

theorem u6913 : Upper (D 1) (R 1) [52,72,192,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6913
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6914 : Route 9 := (fun mask => (mask,id))

def c6914 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u6914 : Upper (D 1) (R 1) [52,72,192,18] 13 := by
  apply FastRouting.sound _ _ [52,72,192,18] 13 (by decide) (choices 1) [1,2,32,128,256] r6914 c6914
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3242
  · exact u3243
  · exact u3244
  · exact u3245
  · exact u3246

def b6915 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 74 196 56 403 419 451 387 387), lower := (rows 53 74 196 56 16 32 64 128 256), losses := [] }

theorem u6915 : Upper (D 1) (R 1) [52,72,192,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6915
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6916 : PairBound 9 := { available := 306, camps := [{ cop := 3, region := 370, targets := 128 }], pairs := [(1,7)], upper := (rows 53 74 196 137 306 306 370 434 306), lower := (rows 53 74 196 137 16 32 64 128 256), losses := [] }

theorem u6916 : Upper (D 1) (R 1) [52,72,192,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6916
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6917 : PairBound 9 := { available := 307, camps := [{ cop := 2, region := 10, targets := 16 }], pairs := [(1,4)], upper := (rows 53 74 196 138 307 307 371 435 307), lower := (rows 53 74 196 138 16 32 64 128 256), losses := [] }

theorem u6917 : Upper (D 1) (R 1) [52,72,192,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6917
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6918 : Route 9 := (fun mask => (mask,id))

def c6918 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6918 : Upper (D 1) (R 1) [52,72,192,144] 13 := by
  apply FastRouting.sound _ _ [52,72,192,144] 13 (by decide) (choices 1) [1,2,32,256] r6918 c6918
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3247
  · exact u3248
  · exact u3249
  · exact u3250

def r6919 : Route 9 := (fun mask => (mask,id))

def c6919 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6919 : Upper (D 1) (R 1) [52,72,192,257] 13 := by
  apply FastRouting.sound _ _ [52,72,192,257] 13 (by decide) (choices 1) [2,32,128] r6919 c6919
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3251
  · exact u3252
  · exact u3253

def r6920 : Route 9 := (fun mask => (mask,id))

def c6920 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6920 : Upper (D 1) (R 1) [52,72,192,258] 13 := by
  apply FastRouting.sound _ _ [52,72,192,258] 13 (by decide) (choices 1) [1,2,32,128] r6920 c6920
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3254
  · exact u3255
  · exact u3256
  · exact u3257

def r6921 : Route 9 := (fun mask => (mask,id))

def c6921 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6921 : Upper (D 1) (R 1) [52,72,192,272] 13 := by
  apply FastRouting.sound _ _ [52,72,192,272] 13 (by decide) (choices 1) [1,2,32,128] r6921 c6921
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3258
  · exact u3259
  · exact u3260
  · exact u3261

def r6922 : Route 9 := (fun mask => (mask,id))

def c6922 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6922 : Upper (D 1) (R 1) [52,72,192,384] 13 := by
  apply FastRouting.sound _ _ [52,72,192,384] 13 (by decide) (choices 1) [1,2,32] r6922 c6922
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3262
  · exact u3263
  · exact u3264

def b6923 : PairBound 9 := { available := 226, camps := [{ cop := 3, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 53 74 261 26 242 226 226 226 482), lower := (rows 53 74 261 26 16 32 64 128 256), losses := [] }

theorem u6923 : Upper (D 1) (R 1) [52,72,257,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6923
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6924 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 74 261 56 210 226 194 194 450), lower := (rows 53 74 261 56 16 32 64 128 256), losses := [] }

theorem u6924 : Upper (D 1) (R 1) [52,72,257,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6924
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6925 : PairBound 9 := { available := 178, camps := [{ cop := 6, region := 10, targets := 16 }], pairs := [(1,4)], upper := (rows 53 74 261 74 178 178 242 178 434), lower := (rows 53 74 261 74 16 32 64 128 256), losses := [] }

theorem u6925 : Upper (D 1) (R 1) [52,72,257,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6925
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6926 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6)], upper := (rows 53 74 261 88 178 162 226 162 418), lower := (rows 53 74 261 88 16 32 64 128 256), losses := [] }

theorem u6926 : Upper (D 1) (R 1) [52,72,257,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6926
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6927 : Route 9 := (fun mask => (mask,id))

def c6927 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6927 : Upper (D 1) (R 1) [52,72,257,130] 13 := by
  apply FastRouting.sound _ _ [52,72,257,130] 13 (by decide) (choices 1) [2,32,64,128] r6927 c6927
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3265
  · exact u3266
  · exact u3267
  · exact u3268

def b6928 : PairBound 9 := { available := 226, camps := [{ cop := 3, region := 98, targets := 16 }], pairs := [(1,4)], upper := (rows 53 74 261 152 242 226 226 226 482), lower := (rows 53 74 261 152 16 32 64 128 256), losses := [] }

theorem u6928 : Upper (D 1) (R 1) [52,72,257,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6928
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6929 : PairBound 9 := { available := 178, camps := [{ cop := 3, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 53 74 261 200 178 178 242 178 434), lower := (rows 53 74 261 200 16 32 64 128 256), losses := [] }

theorem u6929 : Upper (D 1) (R 1) [52,72,257,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6929
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6930 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 241, targets := 2 }], pairs := [(0,1)], upper := (rows 53 74 262 11 240 240 240 240 496), lower := (rows 53 74 262 11 16 32 64 128 256), losses := [] }

theorem u6930 : Upper (D 1) (R 1) [52,72,258,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6930
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6931 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 74 262 25 242 226 226 226 482), lower := (rows 53 74 262 25 16 32 64 128 256), losses := [] }

theorem u6931 : Upper (D 1) (R 1) [52,72,258,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6931
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6932 : PairBound 9 := { available := 225, camps := [{ cop := 2, region := 241, targets := 2 }], pairs := [(0,1)], upper := (rows 53 74 262 26 241 225 225 225 481), lower := (rows 53 74 262 26 16 32 64 128 256), losses := [] }

theorem u6932 : Upper (D 1) (R 1) [52,72,258,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6932
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6933 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 74 262 56 211 227 195 195 451), lower := (rows 53 74 262 56 16 32 64 128 256), losses := [] }

theorem u6933 : Upper (D 1) (R 1) [52,72,258,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6933
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6934 : PairBound 9 := { available := 178, camps := [{ cop := 3, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 53 74 262 73 178 178 242 178 434), lower := (rows 53 74 262 73 16 32 64 128 256), losses := [] }

theorem u6934 : Upper (D 1) (R 1) [52,72,258,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6934
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6935 : PairBound 9 := { available := 177, camps := [{ cop := 6, region := 10, targets := 16 }], pairs := [(1,4)], upper := (rows 53 74 262 74 177 177 241 177 433), lower := (rows 53 74 262 74 16 32 64 128 256), losses := [] }

theorem u6935 : Upper (D 1) (R 1) [52,72,258,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6935
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6936 : PairBound 9 := { available := 163, camps := [{ cop := 3, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 53 74 262 88 179 163 227 163 419), lower := (rows 53 74 262 88 16 32 64 128 256), losses := [] }

theorem u6936 : Upper (D 1) (R 1) [52,72,258,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6936
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6937 : Route 9 := (fun mask => (mask,id))

def c6937 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6937 : Upper (D 1) (R 1) [52,72,258,129] 13 := by
  apply FastRouting.sound _ _ [52,72,258,129] 13 (by decide) (choices 1) [2,32,64,128] r6937 c6937
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3269
  · exact u3270
  · exact u3271
  · exact u3272

def b6938 : PairBound 9 := { available := 241, camps := [{ cop := 2, region := 241, targets := 2 }], pairs := [(0,1)], upper := (rows 53 74 262 138 241 241 241 241 497), lower := (rows 53 74 262 138 16 32 64 128 256), losses := [] }

theorem u6938 : Upper (D 1) (R 1) [52,72,258,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6938
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6939 : Route 9 := (fun mask => (mask,id))

def c6939 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6939 : Upper (D 1) (R 1) [52,72,258,144] 13 := by
  apply FastRouting.sound _ _ [52,72,258,144] 13 (by decide) (choices 1) [1,2,32,64,128] r6939 c6939
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3273
  · exact u3274
  · exact u3275
  · exact u3276
  · exact u3277

def b6940 : PairBound 9 := { available := 179, camps := [{ cop := 3, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 53 74 262 200 179 179 243 179 435), lower := (rows 53 74 262 200 16 32 64 128 256), losses := [] }

theorem u6940 : Upper (D 1) (R 1) [52,72,258,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6940
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6941 : Route 9 := (fun mask => (mask,id))

def c6941 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6941 : Upper (D 1) (R 1) [52,72,320,3] 13 := by
  apply FastRouting.sound _ _ [52,72,320,3] 13 (by decide) (choices 1) [2,32,128] r6941 c6941
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3278
  · exact u3279
  · exact u3280

def b6942 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 74 324 25 178 162 226 162 418), lower := (rows 53 74 324 25 16 32 64 128 256), losses := [] }

theorem u6942 : Upper (D 1) (R 1) [52,72,320,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6942
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6943 : Route 9 := (fun mask => (mask,id))

def c6943 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6943 : Upper (D 1) (R 1) [52,72,320,18] 13 := by
  apply FastRouting.sound _ _ [52,72,320,18] 13 (by decide) (choices 1) [1,2,32,128] r6943 c6943
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3281
  · exact u3282
  · exact u3283
  · exact u3284

def b6944 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 74 324 56 147 163 195 131 387), lower := (rows 53 74 324 56 16 32 64 128 256), losses := [] }

theorem u6944 : Upper (D 1) (R 1) [52,72,320,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6944
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6945 : Route 9 := (fun mask => (mask,id))

def c6945 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6945 : Upper (D 1) (R 1) [52,72,320,129] 13 := by
  apply FastRouting.sound _ _ [52,72,320,129] 13 (by decide) (choices 1) [2,32,128] r6945 c6945
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3285
  · exact u3286
  · exact u3287

def r6946 : Route 9 := (fun mask => (mask,id))

def c6946 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6946 : Upper (D 1) (R 1) [52,72,320,130] 13 := by
  apply FastRouting.sound _ _ [52,72,320,130] 13 (by decide) (choices 1) [1,2,32,128] r6946 c6946
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3288
  · exact u3289
  · exact u3290
  · exact u3291

def r6947 : Route 9 := (fun mask => (mask,id))

def c6947 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6947 : Upper (D 1) (R 1) [52,72,320,144] 13 := by
  apply FastRouting.sound _ _ [52,72,320,144] 13 (by decide) (choices 1) [1,2,32,128] r6947 c6947
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3292
  · exact u3293
  · exact u3294
  · exact u3295

def r6948 : Route 9 := (fun mask => (mask,id))

def c6948 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6948 : Upper (D 1) (R 1) [52,72,384,3] 13 := by
  apply FastRouting.sound _ _ [52,72,384,3] 13 (by decide) (choices 1) [2,32,64,128] r6948 c6948
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3296
  · exact u3297
  · exact u3298
  · exact u3299

def b6949 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 74 388 25 242 226 226 226 482), lower := (rows 53 74 388 25 16 32 64 128 256), losses := [] }

theorem u6949 : Upper (D 1) (R 1) [52,72,384,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6949
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6950 : Route 9 := (fun mask => (mask,id))

def c6950 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6950 : Upper (D 1) (R 1) [52,72,384,18] 13 := by
  apply FastRouting.sound _ _ [52,72,384,18] 13 (by decide) (choices 1) [1,2,32,64,128] r6950 c6950
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3300
  · exact u3301
  · exact u3302
  · exact u3303
  · exact u3304

def b6951 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 74 388 56 211 227 195 195 451), lower := (rows 53 74 388 56 16 32 64 128 256), losses := [] }

theorem u6951 : Upper (D 1) (R 1) [52,72,384,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6951
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6952 : PairBound 9 := { available := 178, camps := [{ cop := 3, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 53 74 388 73 178 178 242 178 434), lower := (rows 53 74 388 73 16 32 64 128 256), losses := [] }

theorem u6952 : Upper (D 1) (R 1) [52,72,384,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6952
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6953 : PairBound 9 := { available := 179, camps := [{ cop := 6, region := 10, targets := 16 }], pairs := [(1,4)], upper := (rows 53 74 388 74 179 179 243 179 435), lower := (rows 53 74 388 74 16 32 64 128 256), losses := [] }

theorem u6953 : Upper (D 1) (R 1) [52,72,384,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6953
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6954 : PairBound 9 := { available := 163, camps := [{ cop := 3, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 53 74 388 88 179 163 227 163 419), lower := (rows 53 74 388 88 16 32 64 128 256), losses := [] }

theorem u6954 : Upper (D 1) (R 1) [52,72,384,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6954
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6955 : PairBound 9 := { available := 114, camps := [{ cop := 3, region := 114, targets := 128 }], pairs := [(1,7)], upper := (rows 53 74 388 137 114 114 114 242 370), lower := (rows 53 74 388 137 16 32 64 128 256), losses := [] }

theorem u6955 : Upper (D 1) (R 1) [52,72,384,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6955
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6956 : Route 9 := (fun mask => (mask,id))

def c6956 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6956 : Upper (D 1) (R 1) [52,72,384,130] 13 := by
  apply FastRouting.sound _ _ [52,72,384,130] 13 (by decide) (choices 1) [1,2,32,64] r6956 c6956
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3305
  · exact u3306
  · exact u3307
  · exact u3308

def r6957 : Route 9 := (fun mask => (mask,id))

def c6957 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6957 : Upper (D 1) (R 1) [52,72,384,144] 13 := by
  apply FastRouting.sound _ _ [52,72,384,144] 13 (by decide) (choices 1) [1,2,32,64] r6957 c6957
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3309
  · exact u3310
  · exact u3311
  · exact u3312

def b6958 : PairBound 9 := { available := 51, camps := [{ cop := 3, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 53 74 388 200 51 51 115 179 307), lower := (rows 53 74 388 200 16 32 64 128 256), losses := [] }

theorem u6958 : Upper (D 1) (R 1) [52,72,384,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6958
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6959 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 53 82 14 11 496 480 480 480 480), lower := (rows 53 82 14 11 16 32 64 128 256), losses := [] }

theorem u6959 : Upper (D 1) (R 1) [52,80,10,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6959
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u6959
end Delivery.IrregularNine14.P01

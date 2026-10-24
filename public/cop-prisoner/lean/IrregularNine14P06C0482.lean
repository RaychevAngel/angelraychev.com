import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0170
import IrregularNine14P06C0171

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b28920 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 98, targets := 5 },{ cop := 0, region := 368, targets := 1 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 7 42 133 25 276 98 98 226 354), lower := (rows 7 42 133 25 276 32 64 128 256), losses := [] }

theorem u28920 : Upper (D 6) (R 6) [6,40,129,17,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28920
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28921 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 197, targets := 32 },{ cop := 0, region := 368, targets := 1 }], pairs := [(0,5),(2,5),(4,0)], upper := (rows 7 42 133 25 304 102 70 198 326), lower := (rows 7 42 133 25 304 32 64 128 256), losses := [] }

theorem u28921 : Upper (D 6) (R 6) [6,40,129,17,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28921
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28922 : Route 9 := (fun mask => (mask,id))

def c28922 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28922 : Upper (D 6) (R 6) [6,40,129,17,320] 13 := by
  apply FastRouting.sound _ _ [6,40,129,17,320] 13 (by decide) (choices 1) [2,4,64] r28922 c28922
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10217
  · exact u10218
  · exact u10219

def b28923 : PairBound 9 := { available := 352, camps := [{ cop := 0, region := 24, targets := 96 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 7 42 133 26 21 352 352 480 352), lower := (rows 7 42 133 26 21 32 64 128 256), losses := [] }

theorem u28923 : Upper (D 6) (R 6) [6,40,129,18,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28923
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28924 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 10, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 133 26 49 356 324 452 324), lower := (rows 7 42 133 26 49 32 64 128 256), losses := [] }

theorem u28924 : Upper (D 6) (R 6) [6,40,129,18,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28924
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28925 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 10, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 42 133 26 52 353 321 449 321), lower := (rows 7 42 133 26 52 32 64 128 256), losses := [] }

theorem u28925 : Upper (D 6) (R 6) [6,40,129,18,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28925
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28926 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 500, targets := 2 }], pairs := [(1,0),(2,1),(4,1)], upper := (rows 7 42 133 26 81 356 356 484 356), lower := (rows 7 42 133 26 81 32 64 128 256), losses := [{ target := 0, region := (rows 0 18 4 24 16 37 69 133 261), good := (rows 486 42 484 26 506 32 64 128 256) }] }

theorem u28926 : Upper (D 6) (R 6) [6,40,129,18,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28926
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28927 : PairBound 9 := { available := 353, camps := [{ cop := 0, region := 500, targets := 2 }], pairs := [(1,2),(2,1),(4,1)], upper := (rows 7 42 133 26 84 353 353 481 353), lower := (rows 7 42 133 26 84 32 64 128 256), losses := [{ target := 2, region := (rows 1 18 0 24 16 37 69 133 261), good := (rows 483 42 481 26 506 32 64 128 256) }] }

theorem u28927 : Upper (D 6) (R 6) [6,40,129,18,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28927
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28928 : PairBound 9 := { available := 325, camps := [{ cop := 4, region := 10, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 133 26 112 357 325 453 325), lower := (rows 7 42 133 26 112 32 64 128 256), losses := [] }

theorem u28928 : Upper (D 6) (R 6) [6,40,129,18,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28928
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28929 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 500, targets := 2 }], pairs := [(1,0),(2,1),(4,1)], upper := (rows 7 42 133 26 273 100 100 228 356), lower := (rows 7 42 133 26 273 32 64 128 256), losses := [{ target := 0, region := (rows 0 18 4 24 16 37 69 133 261), good := (rows 486 42 484 26 506 32 64 128 256) }] }

theorem u28929 : Upper (D 6) (R 6) [6,40,129,18,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28929
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28930 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 500, targets := 2 }], pairs := [(1,2),(2,1),(4,1)], upper := (rows 7 42 133 26 276 97 97 225 353), lower := (rows 7 42 133 26 276 32 64 128 256), losses := [{ target := 2, region := (rows 1 18 0 24 16 37 69 133 261), good := (rows 483 42 481 26 506 32 64 128 256) }] }

theorem u28930 : Upper (D 6) (R 6) [6,40,129,18,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28930
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28931 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 10, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 133 26 304 101 69 197 325), lower := (rows 7 42 133 26 304 32 64 128 256), losses := [] }

theorem u28931 : Upper (D 6) (R 6) [6,40,129,18,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28931
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28932 : Route 9 := (fun mask => (mask,id))

def c28932 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28932 : Upper (D 6) (R 6) [6,40,129,18,320] 13 := by
  apply FastRouting.sound _ _ [6,40,129,18,320] 13 (by decide) (choices 1) [1,4,64] r28932 c28932
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10220
  · exact u10221
  · exact u10222

def b28933 : PairBound 9 := { available := 352, camps := [{ cop := 0, region := 24, targets := 96 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 7 42 133 28 19 352 352 480 352), lower := (rows 7 42 133 28 19 32 64 128 256), losses := [] }

theorem u28933 : Upper (D 6) (R 6) [6,40,129,20,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28933
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28934 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 453, targets := 32 },{ cop := 3, region := 354, targets := 1 }], pairs := [(0,5),(1,0),(2,5)], upper := (rows 7 42 133 28 49 354 322 450 322), lower := (rows 7 42 133 28 49 32 64 128 256), losses := [] }

theorem u28934 : Upper (D 6) (R 6) [6,40,129,20,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28934
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28935 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 7 42 133 28 50 353 321 449 321), lower := (rows 7 42 133 28 50 32 64 128 256), losses := [] }

theorem u28935 : Upper (D 6) (R 6) [6,40,129,20,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28935
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28936 : PairBound 9 := { available := 354, camps := [{ cop := 3, region := 354, targets := 5 },{ cop := 0, region := 368, targets := 4 }], pairs := [(1,0),(1,2),(4,2)], upper := (rows 7 42 133 28 81 354 354 482 354), lower := (rows 7 42 133 28 81 32 64 128 256), losses := [] }

theorem u28936 : Upper (D 6) (R 6) [6,40,129,20,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28936
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28937 : PairBound 9 := { available := 353, camps := [{ cop := 0, region := 484, targets := 2 },{ cop := 0, region := 368, targets := 4 }], pairs := [(1,2),(2,1),(4,2)], upper := (rows 7 42 133 28 82 353 353 481 353), lower := (rows 7 42 133 28 82 32 64 128 256), losses := [{ target := 2, region := (rows 1 10 0 8 25 37 69 133 261), good := (rows 499 58 497 506 82 32 64 128 256) }] }

theorem u28937 : Upper (D 6) (R 6) [6,40,129,20,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28937
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28938 : PairBound 9 := { available := 323, camps := [{ cop := 1, region := 453, targets := 32 },{ cop := 0, region := 368, targets := 4 }], pairs := [(0,5),(2,5),(4,2)], upper := (rows 7 42 133 28 112 355 323 451 323), lower := (rows 7 42 133 28 112 32 64 128 256), losses := [] }

theorem u28938 : Upper (D 6) (R 6) [6,40,129,20,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28938
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28939 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 98, targets := 5 },{ cop := 0, region := 368, targets := 4 }], pairs := [(1,0),(1,2),(4,2)], upper := (rows 7 42 133 28 273 98 98 226 354), lower := (rows 7 42 133 28 273 32 64 128 256), losses := [] }

theorem u28939 : Upper (D 6) (R 6) [6,40,129,20,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28939
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28940 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 228, targets := 2 },{ cop := 0, region := 368, targets := 4 }], pairs := [(1,2),(2,1),(4,2)], upper := (rows 7 42 133 28 274 97 97 225 353), lower := (rows 7 42 133 28 274 32 64 128 256), losses := [{ target := 2, region := (rows 1 10 0 8 25 37 69 133 261), good := (rows 499 58 497 506 274 32 64 128 256) }] }

theorem u28940 : Upper (D 6) (R 6) [6,40,129,20,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28940
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28941 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 197, targets := 32 },{ cop := 0, region := 368, targets := 4 }], pairs := [(0,5),(2,5),(4,2)], upper := (rows 7 42 133 28 304 99 67 195 323), lower := (rows 7 42 133 28 304 32 64 128 256), losses := [] }

theorem u28941 : Upper (D 6) (R 6) [6,40,129,20,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28941
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28942 : Route 9 := (fun mask => (mask,id))

def c28942 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28942 : Upper (D 6) (R 6) [6,40,129,20,320] 13 := by
  apply FastRouting.sound _ _ [6,40,129,20,320] 13 (by decide) (choices 1) [1,2,64] r28942 c28942
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10223
  · exact u10224
  · exact u10225

def b28943 : PairBound 9 := { available := 368, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 4, region := 1, targets := 32 }], pairs := [(0,5),(4,5),(4,6)], upper := (rows 7 42 133 73 22 368 368 496 368), lower := (rows 7 42 133 73 22 32 64 128 256), losses := [] }

theorem u28943 : Upper (D 6) (R 6) [6,40,129,65,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28943
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28944 : PairBound 9 := { available := 340, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 7 42 133 73 50 372 340 468 340), lower := (rows 7 42 133 73 50 32 64 128 256), losses := [] }

theorem u28944 : Upper (D 6) (R 6) [6,40,129,65,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28944
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28945 : Route 9 := (fun mask => (mask,id))

def c28945 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u28945 : Upper (D 6) (R 6) [6,40,129,65,36] 13 := by
  apply FastRouting.sound _ _ [6,40,129,65,36] 13 (by decide) (choices 1) [2,16,64,256] r28945 c28945
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10226
  · exact u10227
  · exact u10228
  · exact u10229

def b28946 : PairBound 9 := { available := 308, camps := [{ cop := 4, region := 421, targets := 64 },{ cop := 0, region := 368, targets := 1 }], pairs := [(0,6),(2,6),(4,0)], upper := (rows 7 42 133 73 82 308 372 436 308), lower := (rows 7 42 133 73 82 32 64 128 256), losses := [] }

theorem u28946 : Upper (D 6) (R 6) [6,40,129,65,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28946
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28947 : Route 9 := (fun mask => (mask,id))

def c28947 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u28947 : Upper (D 6) (R 6) [6,40,129,65,68] 13 := by
  apply FastRouting.sound _ _ [6,40,129,65,68] 13 (by decide) (choices 1) [2,16,256] r28947 c28947
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10230
  · exact u10231
  · exact u10232

def r28948 : Route 9 := (fun mask => (mask,id))

def c28948 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u28948 : Upper (D 6) (R 6) [6,40,129,65,96] 13 := by
  apply FastRouting.sound _ _ [6,40,129,65,96] 13 (by decide) (choices 1) [2,4,16,256] r28948 c28948
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10233
  · exact u10234
  · exact u10235
  · exact u10236

def r28949 : Route 9 := (fun mask => (mask,id))

def c28949 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28949 : Upper (D 6) (R 6) [6,40,129,65,258] 13 := by
  apply FastRouting.sound _ _ [6,40,129,65,258] 13 (by decide) (choices 1) [4,16,64] r28949 c28949
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10237
  · exact u10238
  · exact u10239

def r28950 : Route 9 := (fun mask => (mask,id))

def c28950 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28950 : Upper (D 6) (R 6) [6,40,129,65,260] 13 := by
  apply FastRouting.sound _ _ [6,40,129,65,260] 13 (by decide) (choices 1) [2,16,64] r28950 c28950
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10240
  · exact u10241
  · exact u10242

def r28951 : Route 9 := (fun mask => (mask,id))

def c28951 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28951 : Upper (D 6) (R 6) [6,40,129,65,288] 13 := by
  apply FastRouting.sound _ _ [6,40,129,65,288] 13 (by decide) (choices 1) [2,4,16,64] r28951 c28951
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10243
  · exact u10244
  · exact u10245
  · exact u10246

def r28952 : Route 9 := (fun mask => (mask,id))

def c28952 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28952 : Upper (D 6) (R 6) [6,40,129,65,320] 13 := by
  apply FastRouting.sound _ _ [6,40,129,65,320] 13 (by decide) (choices 1) [2,4,16] r28952 c28952
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10247
  · exact u10248
  · exact u10249

def b28953 : PairBound 9 := { available := 368, camps := [{ cop := 4, region := 362, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 42 133 74 21 368 368 496 368), lower := (rows 7 42 133 74 21 32 64 128 256), losses := [] }

theorem u28953 : Upper (D 6) (R 6) [6,40,129,66,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28953
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28954 : PairBound 9 := { available := 340, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 4, region := 452, targets := 32 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 7 42 133 74 49 372 340 468 340), lower := (rows 7 42 133 74 49 32 64 128 256), losses := [] }

theorem u28954 : Upper (D 6) (R 6) [6,40,129,66,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28954
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28955 : Route 9 := (fun mask => (mask,id))

def c28955 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u28955 : Upper (D 6) (R 6) [6,40,129,66,36] 13 := by
  apply FastRouting.sound _ _ [6,40,129,66,36] 13 (by decide) (choices 1) [1,16,64,256] r28955 c28955
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10250
  · exact u10251
  · exact u10252
  · exact u10253

def b28956 : PairBound 9 := { available := 308, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 4, region := 420, targets := 64 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 7 42 133 74 81 308 372 436 308), lower := (rows 7 42 133 74 81 32 64 128 256), losses := [] }

theorem u28956 : Upper (D 6) (R 6) [6,40,129,66,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28956
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28957 : Route 9 := (fun mask => (mask,id))

def c28957 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u28957 : Upper (D 6) (R 6) [6,40,129,66,68] 13 := by
  apply FastRouting.sound _ _ [6,40,129,66,68] 13 (by decide) (choices 1) [1,16,256] r28957 c28957
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10254
  · exact u10255
  · exact u10256

def b28958 : PairBound 9 := { available := 277, camps := [{ cop := 4, region := 10, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 42 133 74 112 309 341 405 277), lower := (rows 7 42 133 74 112 32 64 128 256), losses := [] }

theorem u28958 : Upper (D 6) (R 6) [6,40,129,66,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28958
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28959 : Route 9 := (fun mask => (mask,id))

def c28959 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28959 : Upper (D 6) (R 6) [6,40,129,66,257] 13 := by
  apply FastRouting.sound _ _ [6,40,129,66,257] 13 (by decide) (choices 1) [4,16,64] r28959 c28959
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10257
  · exact u10258
  · exact u10259

def r28960 : Route 9 := (fun mask => (mask,id))

def c28960 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28960 : Upper (D 6) (R 6) [6,40,129,66,260] 13 := by
  apply FastRouting.sound _ _ [6,40,129,66,260] 13 (by decide) (choices 1) [1,16,64] r28960 c28960
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10260
  · exact u10261
  · exact u10262

def r28961 : Route 9 := (fun mask => (mask,id))

def c28961 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28961 : Upper (D 6) (R 6) [6,40,129,66,288] 13 := by
  apply FastRouting.sound _ _ [6,40,129,66,288] 13 (by decide) (choices 1) [1,4,16,64] r28961 c28961
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10263
  · exact u10264
  · exact u10265
  · exact u10266

def r28962 : Route 9 := (fun mask => (mask,id))

def c28962 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28962 : Upper (D 6) (R 6) [6,40,129,66,320] 13 := by
  apply FastRouting.sound _ _ [6,40,129,66,320] 13 (by decide) (choices 1) [1,4,16] r28962 c28962
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10267
  · exact u10268
  · exact u10269

def b28963 : PairBound 9 := { available := 368, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 4, region := 484, targets := 2 }], pairs := [(2,1),(4,5),(4,6)], upper := (rows 7 42 133 76 19 368 368 496 368), lower := (rows 7 42 133 76 19 32 64 128 256), losses := [] }

theorem u28963 : Upper (D 6) (R 6) [6,40,129,68,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28963
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28964 : Route 9 := (fun mask => (mask,id))

def c28964 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u28964 : Upper (D 6) (R 6) [6,40,129,68,33] 13 := by
  apply FastRouting.sound _ _ [6,40,129,68,33] 13 (by decide) (choices 1) [2,16,64,256] r28964 c28964
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10270
  · exact u10271
  · exact u10272
  · exact u10273

def b28965 : PairBound 9 := { available := 337, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 7 42 133 76 50 369 337 465 337), lower := (rows 7 42 133 76 50 32 64 128 256), losses := [] }

theorem u28965 : Upper (D 6) (R 6) [6,40,129,68,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28965
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28966 : Route 9 := (fun mask => (mask,id))

def c28966 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u28966 : Upper (D 6) (R 6) [6,40,129,68,65] 13 := by
  apply FastRouting.sound _ _ [6,40,129,68,65] 13 (by decide) (choices 1) [2,16,256] r28966 c28966
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10274
  · exact u10275
  · exact u10276

def b28967 : PairBound 9 := { available := 305, camps := [{ cop := 4, region := 421, targets := 64 },{ cop := 0, region := 368, targets := 4 }], pairs := [(0,6),(2,6),(4,2)], upper := (rows 7 42 133 76 82 305 369 433 305), lower := (rows 7 42 133 76 82 32 64 128 256), losses := [] }

theorem u28967 : Upper (D 6) (R 6) [6,40,129,68,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28967
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28968 : Route 9 := (fun mask => (mask,id))

def c28968 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u28968 : Upper (D 6) (R 6) [6,40,129,68,96] 13 := by
  apply FastRouting.sound _ _ [6,40,129,68,96] 13 (by decide) (choices 1) [1,2,16,256] r28968 c28968
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10277
  · exact u10278
  · exact u10279
  · exact u10280

def r28969 : Route 9 := (fun mask => (mask,id))

def c28969 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28969 : Upper (D 6) (R 6) [6,40,129,68,257] 13 := by
  apply FastRouting.sound _ _ [6,40,129,68,257] 13 (by decide) (choices 1) [2,16,64] r28969 c28969
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10281
  · exact u10282
  · exact u10283

def r28970 : Route 9 := (fun mask => (mask,id))

def c28970 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28970 : Upper (D 6) (R 6) [6,40,129,68,258] 13 := by
  apply FastRouting.sound _ _ [6,40,129,68,258] 13 (by decide) (choices 1) [1,16,64] r28970 c28970
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10284
  · exact u10285
  · exact u10286

def r28971 : Route 9 := (fun mask => (mask,id))

def c28971 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28971 : Upper (D 6) (R 6) [6,40,129,68,288] 13 := by
  apply FastRouting.sound _ _ [6,40,129,68,288] 13 (by decide) (choices 1) [1,2,16,64] r28971 c28971
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10287
  · exact u10288
  · exact u10289
  · exact u10290

def r28972 : Route 9 := (fun mask => (mask,id))

def c28972 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28972 : Upper (D 6) (R 6) [6,40,129,68,320] 13 := by
  apply FastRouting.sound _ _ [6,40,129,68,320] 13 (by decide) (choices 1) [1,2,16] r28972 c28972
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10291
  · exact u10292
  · exact u10293

def b28973 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 7 42 133 88 19 356 356 484 356), lower := (rows 7 42 133 88 19 32 64 128 256), losses := [] }

theorem u28973 : Upper (D 6) (R 6) [6,40,129,80,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28973
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28974 : PairBound 9 := { available := 354, camps := [{ cop := 4, region := 362, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 42 133 88 21 354 354 482 354), lower := (rows 7 42 133 88 21 32 64 128 256), losses := [] }

theorem u28974 : Upper (D 6) (R 6) [6,40,129,80,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28974
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28975 : PairBound 9 := { available := 353, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 4, region := 1, targets := 32 }], pairs := [(0,5),(4,5),(4,6)], upper := (rows 7 42 133 88 22 353 353 481 353), lower := (rows 7 42 133 88 22 32 64 128 256), losses := [] }

theorem u28975 : Upper (D 6) (R 6) [6,40,129,80,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28975
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28976 : PairBound 9 := { available := 326, camps := [{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(1,0),(2,5)], upper := (rows 7 42 133 88 49 358 326 454 326), lower := (rows 7 42 133 88 49 32 64 128 256), losses := [{ target := 0, region := (rows 0 18 4 24 16 33 65 129 257), good := (rows 486 42 484 90 506 32 64 128 256) }] }

theorem u28976 : Upper (D 6) (R 6) [6,40,129,80,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28976
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28977 : PairBound 9 := { available := 325, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 7 42 133 88 50 357 325 453 325), lower := (rows 7 42 133 88 50 32 64 128 256), losses := [] }

theorem u28977 : Upper (D 6) (R 6) [6,40,129,80,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28977
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28978 : Route 9 := (fun mask => (mask,id))

def c28978 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u28978 : Upper (D 6) (R 6) [6,40,129,80,36] 13 := by
  apply FastRouting.sound _ _ [6,40,129,80,36] 13 (by decide) (choices 1) [1,2,64,256] r28978 c28978
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10294
  · exact u10295
  · exact u10296
  · exact u10297

def b28979 : PairBound 9 := { available := 294, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 42 133 88 81 294 358 422 294), lower := (rows 7 42 133 88 81 32 64 128 256), losses := [] }

theorem u28979 : Upper (D 6) (R 6) [6,40,129,80,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28979
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u28979
end Delivery.IrregularNine14.P06

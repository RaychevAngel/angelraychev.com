import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0288
import IrregularNine14P06C0289
import IrregularNine14P06C0290

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r33960 : Route 9 := (fun mask => (mask,id))

def c33960 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33960 : Upper (D 6) (R 6) [10,160,65,260,6] 13 := by
  apply FastRouting.sound _ _ [10,160,65,260,6] 13 (by decide) (choices 1) [1,16,64] r33960 c33960
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17323
  · exact u17324
  · exact u17325

def r33961 : Route 9 := (fun mask => (mask,id))

def c33961 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33961 : Upper (D 6) (R 6) [10,160,65,260,33] 13 := by
  apply FastRouting.sound _ _ [10,160,65,260,33] 13 (by decide) (choices 1) [2,4,16,64] r33961 c33961
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17326
  · exact u17327
  · exact u17328
  · exact u17329

def b33962 : PairBound 9 := { available := 85, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 162 69 268 50 117 85 213 341), lower := (rows 11 162 69 268 50 32 64 128 256), losses := [] }

theorem u33962 : Upper (D 6) (R 6) [10,160,65,260,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33962 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33963 : Route 9 := (fun mask => (mask,id))

def c33963 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33963 : Upper (D 6) (R 6) [10,160,65,260,36] 13 := by
  apply FastRouting.sound _ _ [10,160,65,260,36] 13 (by decide) (choices 1) [1,2,16,64] r33963 c33963
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17330
  · exact u17331
  · exact u17332
  · exact u17333

def b33964 : PairBound 9 := { available := 54, camps := [{ cop := 2, region := 16, targets := 34 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,5)], upper := (rows 11 162 69 268 81 54 118 182 310), lower := (rows 11 162 69 268 81 32 64 128 256), losses := [] }

theorem u33964 : Upper (D 6) (R 6) [10,160,65,260,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33964 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33965 : Route 9 := (fun mask => (mask,id))

def c33965 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33965 : Upper (D 6) (R 6) [10,160,65,260,66] 13 := by
  apply FastRouting.sound _ _ [10,160,65,260,66] 13 (by decide) (choices 1) [1,4,16] r33965 c33965
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17334
  · exact u17335
  · exact u17336

def b33966 : PairBound 9 := { available := 51, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 162 69 268 84 51 115 179 307), lower := (rows 11 162 69 268 84 32 64 128 256), losses := [] }

theorem u33966 : Upper (D 6) (R 6) [10,160,65,260,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33966 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33967 : Route 9 := (fun mask => (mask,id))

def c33967 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33967 : Upper (D 6) (R 6) [10,160,65,260,96] 13 := by
  apply FastRouting.sound _ _ [10,160,65,260,96] 13 (by decide) (choices 1) [1,2,4,16] r33967 c33967
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17337
  · exact u17338
  · exact u17339
  · exact u17340

def b33968 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 162 69 280 19 100 100 228 356), lower := (rows 11 162 69 280 19 32 64 128 256), losses := [] }

theorem u33968 : Upper (D 6) (R 6) [10,160,65,272,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33968 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33969 : PairBound 9 := { available := 102, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 162 69 280 21 102 102 230 358), lower := (rows 11 162 69 280 21 32 64 128 256), losses := [] }

theorem u33969 : Upper (D 6) (R 6) [10,160,65,272,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33969 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33970 : Route 9 := (fun mask => (mask,id))

def c33970 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33970 : Upper (D 6) (R 6) [10,160,65,272,6] 13 := by
  apply FastRouting.sound _ _ [10,160,65,272,6] 13 (by decide) (choices 1) [1,4,64] r33970 c33970
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17341
  · exact u17342
  · exact u17343

def b33971 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 68, targets := 32 },{ cop := 2, region := 162, targets := 1 }], pairs := [(1,0),(2,5),(3,5)], upper := (rows 11 162 69 280 49 102 70 198 326), lower := (rows 11 162 69 280 49 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 21 24 16 0 65 129 257), good := (rows 463 130 453 284 477 0 64 128 256) }] }

theorem u33971 : Upper (D 6) (R 6) [10,160,65,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33971 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33972 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 162 69 280 50 101 69 197 325), lower := (rows 11 162 69 280 50 32 64 128 256), losses := [] }

theorem u33972 : Upper (D 6) (R 6) [10,160,65,272,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33972 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33973 : Route 9 := (fun mask => (mask,id))

def c33973 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33973 : Upper (D 6) (R 6) [10,160,65,272,36] 13 := by
  apply FastRouting.sound _ _ [10,160,65,272,36] 13 (by decide) (choices 1) [1,2,4,64] r33973 c33973
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17344
  · exact u17345
  · exact u17346
  · exact u17347

def b33974 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 16, targets := 34 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,5)], upper := (rows 11 162 69 280 81 38 102 166 294), lower := (rows 11 162 69 280 81 32 64 128 256), losses := [] }

theorem u33974 : Upper (D 6) (R 6) [10,160,65,272,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33974 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33975 : Route 9 := (fun mask => (mask,id))

def c33975 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33975 : Upper (D 6) (R 6) [10,160,65,272,66] 13 := by
  apply FastRouting.sound _ _ [10,160,65,272,66] 13 (by decide) (choices 1) [1,4] r33975 c33975
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u17348
  · exact u17349

def b33976 : PairBound 9 := { available := 39, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 162 69 280 84 39 103 167 295), lower := (rows 11 162 69 280 84 32 64 128 256), losses := [] }

theorem u33976 : Upper (D 6) (R 6) [10,160,65,272,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33976 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33977 : Route 9 := (fun mask => (mask,id))

def c33977 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33977 : Upper (D 6) (R 6) [10,160,65,272,96] 13 := by
  apply FastRouting.sound _ _ [10,160,65,272,96] 13 (by decide) (choices 1) [1,2,4] r33977 c33977
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17350
  · exact u17351
  · exact u17352

def b33978 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 0, region := 84, targets := 32 }], pairs := [(2,5),(4,2),(4,6)], upper := (rows 11 162 69 296 19 116 84 212 340), lower := (rows 11 162 69 296 19 32 64 128 256), losses := [] }

theorem u33978 : Upper (D 6) (R 6) [10,160,65,288,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33978 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33979 : PairBound 9 := { available := 86, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 162 69 296 21 118 86 214 342), lower := (rows 11 162 69 296 21 32 64 128 256), losses := [] }

theorem u33979 : Upper (D 6) (R 6) [10,160,65,288,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33979 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33980 : Route 9 := (fun mask => (mask,id))

def c33980 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33980 : Upper (D 6) (R 6) [10,160,65,288,6] 13 := by
  apply FastRouting.sound _ _ [10,160,65,288,6] 13 (by decide) (choices 1) [1,4,16,64] r33980 c33980
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17353
  · exact u17354
  · exact u17355
  · exact u17356

def b33981 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 84, targets := 32 },{ cop := 2, region := 16, targets := 2 }], pairs := [(2,5),(4,1),(4,5)], upper := (rows 11 162 69 296 81 54 86 150 278), lower := (rows 11 162 69 296 81 32 64 128 256), losses := [] }

theorem u33981 : Upper (D 6) (R 6) [10,160,65,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33981 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33982 : Route 9 := (fun mask => (mask,id))

def c33982 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33982 : Upper (D 6) (R 6) [10,160,65,288,66] 13 := by
  apply FastRouting.sound _ _ [10,160,65,288,66] 13 (by decide) (choices 1) [1,4,16] r33982 c33982
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17357
  · exact u17358
  · exact u17359

def b33983 : PairBound 9 := { available := 23, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 162 69 296 84 55 87 151 279), lower := (rows 11 162 69 296 84 32 64 128 256), losses := [] }

theorem u33983 : Upper (D 6) (R 6) [10,160,65,288,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33983 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33984 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 162 69 328 19 52 116 180 308), lower := (rows 11 162 69 328 19 32 64 128 256), losses := [] }

theorem u33984 : Upper (D 6) (R 6) [10,160,65,320,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33984 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33985 : PairBound 9 := { available := 54, camps := [{ cop := 2, region := 16, targets := 34 },{ cop := 2, region := 178, targets := 64 }], pairs := [(1,6),(4,1),(4,5)], upper := (rows 11 162 69 328 21 54 118 182 310), lower := (rows 11 162 69 328 21 32 64 128 256), losses := [] }

theorem u33985 : Upper (D 6) (R 6) [10,160,65,320,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33985 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33986 : Route 9 := (fun mask => (mask,id))

def c33986 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33986 : Upper (D 6) (R 6) [10,160,65,320,6] 13 := by
  apply FastRouting.sound _ _ [10,160,65,320,6] 13 (by decide) (choices 1) [1,4,16] r33986 c33986
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17360
  · exact u17361
  · exact u17362

def r33987 : Route 9 := (fun mask => (mask,id))

def c33987 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33987 : Upper (D 6) (R 6) [10,160,65,320,33] 13 := by
  apply FastRouting.sound _ _ [10,160,65,320,33] 13 (by decide) (choices 1) [2,4,16] r33987 c33987
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17363
  · exact u17364
  · exact u17365

def b33988 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 162 69 328 50 53 85 149 277), lower := (rows 11 162 69 328 50 32 64 128 256), losses := [] }

theorem u33988 : Upper (D 6) (R 6) [10,160,65,320,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33988 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33989 : Route 9 := (fun mask => (mask,id))

def c33989 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33989 : Upper (D 6) (R 6) [10,160,65,320,36] 13 := by
  apply FastRouting.sound _ _ [10,160,65,320,36] 13 (by decide) (choices 1) [1,2,4,16] r33989 c33989
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17366
  · exact u17367
  · exact u17368
  · exact u17369

def b33990 : PairBound 9 := { available := 356, camps := [{ cop := 2, region := 25, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 162 70 25 21 356 356 484 356), lower := (rows 11 162 70 25 21 32 64 128 256), losses := [] }

theorem u33990 : Upper (D 6) (R 6) [10,160,66,17,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33990 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33991 : PairBound 9 := { available := 324, camps := [{ cop := 1, region := 25, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 162 70 25 49 356 324 452 324), lower := (rows 11 162 70 25 49 32 64 128 256), losses := [] }

theorem u33991 : Upper (D 6) (R 6) [10,160,66,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33991 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33992 : Route 9 := (fun mask => (mask,id))

def c33992 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u33992 : Upper (D 6) (R 6) [10,160,66,17,36] 13 := by
  apply FastRouting.sound _ _ [10,160,66,17,36] 13 (by decide) (choices 1) [1,4,64,256] r33992 c33992
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17370
  · exact u17371
  · exact u17372
  · exact u17373

def b33993 : PairBound 9 := { available := 292, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 11 162 70 25 81 292 356 420 292), lower := (rows 11 162 70 25 81 32 64 128 256), losses := [] }

theorem u33993 : Upper (D 6) (R 6) [10,160,66,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33993 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33994 : PairBound 9 := { available := 293, camps := [{ cop := 2, region := 25, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 162 70 25 84 293 357 421 293), lower := (rows 11 162 70 25 84 32 64 128 256), losses := [] }

theorem u33994 : Upper (D 6) (R 6) [10,160,66,17,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33994 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33995 : Route 9 := (fun mask => (mask,id))

def c33995 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u33995 : Upper (D 6) (R 6) [10,160,66,17,96] 13 := by
  apply FastRouting.sound _ _ [10,160,66,17,96] 13 (by decide) (choices 1) [1,4,256] r33995 c33995
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17374
  · exact u17375
  · exact u17376

def b33996 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 11 162 70 25 273 100 100 228 356), lower := (rows 11 162 70 25 273 32 64 128 256), losses := [] }

theorem u33996 : Upper (D 6) (R 6) [10,160,66,17,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33996 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33997 : Route 9 := (fun mask => (mask,id))

def c33997 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33997 : Upper (D 6) (R 6) [10,160,66,17,260] 13 := by
  apply FastRouting.sound _ _ [10,160,66,17,260] 13 (by decide) (choices 1) [1,4,64] r33997 c33997
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17377
  · exact u17378
  · exact u17379

def r33998 : Route 9 := (fun mask => (mask,id))

def c33998 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33998 : Upper (D 6) (R 6) [10,160,66,17,288] 13 := by
  apply FastRouting.sound _ _ [10,160,66,17,288] 13 (by decide) (choices 1) [1,4,64] r33998 c33998
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17380
  · exact u17381
  · exact u17382

def r33999 : Route 9 := (fun mask => (mask,id))

def c33999 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33999 : Upper (D 6) (R 6) [10,160,66,17,320] 13 := by
  apply FastRouting.sound _ _ [10,160,66,17,320] 13 (by decide) (choices 1) [1,4] r33999 c33999
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u17383
  · exact u17384

def b34000 : PairBound 9 := { available := 353, camps := [{ cop := 2, region := 25, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 162 70 28 21 353 353 481 353), lower := (rows 11 162 70 28 21 32 64 128 256), losses := [] }

theorem u34000 : Upper (D 6) (R 6) [10,160,66,20,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34000 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34001 : Route 9 := (fun mask => (mask,id))

def c34001 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u34001 : Upper (D 6) (R 6) [10,160,66,20,33] 13 := by
  apply FastRouting.sound _ _ [10,160,66,20,33] 13 (by decide) (choices 1) [1,4,64,256] r34001 c34001
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17385
  · exact u17386
  · exact u17387
  · exact u17388

def b34002 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 162 70 28 52 353 321 449 321), lower := (rows 11 162 70 28 52 32 64 128 256), losses := [] }

theorem u34002 : Upper (D 6) (R 6) [10,160,66,20,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34002 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34003 : PairBound 9 := { available := 293, camps := [{ cop := 2, region := 25, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 162 70 28 81 293 357 421 293), lower := (rows 11 162 70 28 81 32 64 128 256), losses := [] }

theorem u34003 : Upper (D 6) (R 6) [10,160,66,20,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34003 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34004 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 24, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 162 70 28 84 289 353 417 289), lower := (rows 11 162 70 28 84 32 64 128 256), losses := [] }

theorem u34004 : Upper (D 6) (R 6) [10,160,66,20,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34004 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34005 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 419, targets := 64 },{ cop := 0, region := 324, targets := 32 }], pairs := [(0,6),(1,6),(2,5)], upper := (rows 11 162 70 28 112 293 325 389 261), lower := (rows 11 162 70 28 112 32 64 128 256), losses := [] }

theorem u34005 : Upper (D 6) (R 6) [10,160,66,20,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34005 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34006 : Route 9 := (fun mask => (mask,id))

def c34006 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34006 : Upper (D 6) (R 6) [10,160,66,20,257] 13 := by
  apply FastRouting.sound _ _ [10,160,66,20,257] 13 (by decide) (choices 1) [1,4,64] r34006 c34006
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17389
  · exact u17390
  · exact u17391

def b34007 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 162 70 28 276 97 97 225 353), lower := (rows 11 162 70 28 276 32 64 128 256), losses := [] }

theorem u34007 : Upper (D 6) (R 6) [10,160,66,20,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34007 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34008 : Route 9 := (fun mask => (mask,id))

def c34008 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34008 : Upper (D 6) (R 6) [10,160,66,20,288] 13 := by
  apply FastRouting.sound _ _ [10,160,66,20,288] 13 (by decide) (choices 1) [1,4,64] r34008 c34008
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17392
  · exact u17393
  · exact u17394

def r34009 : Route 9 := (fun mask => (mask,id))

def c34009 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34009 : Upper (D 6) (R 6) [10,160,66,20,320] 13 := by
  apply FastRouting.sound _ _ [10,160,66,20,320] 13 (by decide) (choices 1) [1,4] r34009 c34009
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u17395
  · exact u17396

def b34010 : PairBound 9 := { available := 337, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 4, region := 360, targets := 2 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 11 162 70 44 21 369 337 465 337), lower := (rows 11 162 70 44 21 32 64 128 256), losses := [] }

theorem u34010 : Upper (D 6) (R 6) [10,160,66,36,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34010 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34011 : Route 9 := (fun mask => (mask,id))

def c34011 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u34011 : Upper (D 6) (R 6) [10,160,66,36,65] 13 := by
  apply FastRouting.sound _ _ [10,160,66,36,65] 13 (by decide) (choices 1) [1,4,16,256] r34011 c34011
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17397
  · exact u17398
  · exact u17399
  · exact u17400

def b34012 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 162 70 44 84 305 337 401 273), lower := (rows 11 162 70 44 84 32 64 128 256), losses := [] }

theorem u34012 : Upper (D 6) (R 6) [10,160,66,36,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34012 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34013 : Route 9 := (fun mask => (mask,id))

def c34013 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34013 : Upper (D 6) (R 6) [10,160,66,36,257] 13 := by
  apply FastRouting.sound _ _ [10,160,66,36,257] 13 (by decide) (choices 1) [1,4,16,64] r34013 c34013
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17401
  · exact u17402
  · exact u17403
  · exact u17404

def r34014 : Route 9 := (fun mask => (mask,id))

def c34014 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34014 : Upper (D 6) (R 6) [10,160,66,36,260] 13 := by
  apply FastRouting.sound _ _ [10,160,66,36,260] 13 (by decide) (choices 1) [1,16,64] r34014 c34014
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17405
  · exact u17406
  · exact u17407

def r34015 : Route 9 := (fun mask => (mask,id))

def c34015 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34015 : Upper (D 6) (R 6) [10,160,66,36,320] 13 := by
  apply FastRouting.sound _ _ [10,160,66,36,320] 13 (by decide) (choices 1) [1,4,16] r34015 c34015
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17408
  · exact u17409
  · exact u17410

def b34016 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 4, region := 360, targets := 2 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 11 162 70 56 21 357 325 453 325), lower := (rows 11 162 70 56 21 32 64 128 256), losses := [] }

theorem u34016 : Upper (D 6) (R 6) [10,160,66,48,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34016 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34017 : Route 9 := (fun mask => (mask,id))

def c34017 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u34017 : Upper (D 6) (R 6) [10,160,66,48,65] 13 := by
  apply FastRouting.sound _ _ [10,160,66,48,65] 13 (by decide) (choices 1) [1,4,256] r34017 c34017
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17411
  · exact u17412
  · exact u17413

def b34018 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 162 70 56 84 293 325 389 261), lower := (rows 11 162 70 56 84 32 64 128 256), losses := [] }

theorem u34018 : Upper (D 6) (R 6) [10,160,66,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34018 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34019 : Route 9 := (fun mask => (mask,id))

def c34019 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34019 : Upper (D 6) (R 6) [10,160,66,48,257] 13 := by
  apply FastRouting.sound _ _ [10,160,66,48,257] 13 (by decide) (choices 1) [1,4,64] r34019 c34019
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17414
  · exact u17415
  · exact u17416

#print axioms u34019
end Delivery.IrregularNine14.P06

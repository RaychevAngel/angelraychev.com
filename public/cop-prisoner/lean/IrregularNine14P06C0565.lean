import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0287
import IrregularNine14P06C0288

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b33900 : PairBound 9 := { available := 292, camps := [{ cop := 4, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 162 69 25 82 292 356 420 292), lower := (rows 11 162 69 25 82 32 64 128 256), losses := [] }

theorem u33900 : Upper (D 6) (R 6) [10,160,65,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33900 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33901 : PairBound 9 := { available := 294, camps := [{ cop := 2, region := 24, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 162 69 25 84 294 358 422 294), lower := (rows 11 162 69 25 84 32 64 128 256), losses := [] }

theorem u33901 : Upper (D 6) (R 6) [10,160,65,17,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33901 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33902 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 434, targets := 1 },{ cop := 0, region := 324, targets := 32 }], pairs := [(1,0),(2,5),(4,0)], upper := (rows 11 162 69 25 112 294 326 390 262), lower := (rows 11 162 69 25 112 32 64 128 256), losses := [] }

theorem u33902 : Upper (D 6) (R 6) [10,160,65,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33902 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33903 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 162 69 25 274 100 100 228 356), lower := (rows 11 162 69 25 274 32 64 128 256), losses := [] }

theorem u33903 : Upper (D 6) (R 6) [10,160,65,17,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33903 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33904 : Route 9 := (fun mask => (mask,id))

def c33904 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33904 : Upper (D 6) (R 6) [10,160,65,17,260] 13 := by
  apply FastRouting.sound _ _ [10,160,65,17,260] 13 (by decide) (choices 1) [2,4,64] r33904 c33904
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17267
  · exact u17268
  · exact u17269

def b33905 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 434, targets := 1 },{ cop := 0, region := 68, targets := 32 }], pairs := [(1,0),(2,5),(4,0)], upper := (rows 11 162 69 25 304 102 70 198 326), lower := (rows 11 162 69 25 304 32 64 128 256), losses := [] }

theorem u33905 : Upper (D 6) (R 6) [10,160,65,17,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33905 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33906 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 434, targets := 1 },{ cop := 2, region := 162, targets := 64 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 162 69 25 336 38 102 166 294), lower := (rows 11 162 69 25 336 32 64 128 256), losses := [] }

theorem u33906 : Upper (D 6) (R 6) [10,160,65,17,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33906 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33907 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 162 69 28 19 356 356 484 356), lower := (rows 11 162 69 28 19 32 64 128 256), losses := [] }

theorem u33907 : Upper (D 6) (R 6) [10,160,65,20,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33907 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33908 : PairBound 9 := { available := 354, camps := [{ cop := 2, region := 24, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 11 162 69 28 21 354 354 482 354), lower := (rows 11 162 69 28 21 32 64 128 256), losses := [] }

theorem u33908 : Upper (D 6) (R 6) [10,160,65,20,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33908 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33909 : PairBound 9 := { available := 353, camps := [{ cop := 4, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 162 69 28 22 353 353 481 353), lower := (rows 11 162 69 28 22 32 64 128 256), losses := [] }

theorem u33909 : Upper (D 6) (R 6) [10,160,65,20,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33909 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33910 : PairBound 9 := { available := 326, camps := [{ cop := 0, region := 324, targets := 32 },{ cop := 2, region := 418, targets := 1 }], pairs := [(1,0),(2,5),(3,5)], upper := (rows 11 162 69 28 49 358 326 454 326), lower := (rows 11 162 69 28 49 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 21 24 16 0 65 129 257), good := (rows 463 130 453 28 477 0 64 128 256) }] }

theorem u33910 : Upper (D 6) (R 6) [10,160,65,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33910 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33911 : PairBound 9 := { available := 325, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 162 69 28 50 357 325 453 325), lower := (rows 11 162 69 28 50 32 64 128 256), losses := [] }

theorem u33911 : Upper (D 6) (R 6) [10,160,65,20,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33911 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33912 : PairBound 9 := { available := 323, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 162 69 28 52 355 323 451 323), lower := (rows 11 162 69 28 52 32 64 128 256), losses := [] }

theorem u33912 : Upper (D 6) (R 6) [10,160,65,20,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33912 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33913 : PairBound 9 := { available := 294, camps := [{ cop := 2, region := 24, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 162 69 28 81 294 358 422 294), lower := (rows 11 162 69 28 81 32 64 128 256), losses := [] }

theorem u33913 : Upper (D 6) (R 6) [10,160,65,20,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33913 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33914 : PairBound 9 := { available := 293, camps := [{ cop := 4, region := 13, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 162 69 28 82 293 357 421 293), lower := (rows 11 162 69 28 82 32 64 128 256), losses := [] }

theorem u33914 : Upper (D 6) (R 6) [10,160,65,20,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33914 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33915 : PairBound 9 := { available := 291, camps := [{ cop := 2, region := 24, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 162 69 28 84 291 355 419 291), lower := (rows 11 162 69 28 84 32 64 128 256), losses := [] }

theorem u33915 : Upper (D 6) (R 6) [10,160,65,20,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33915 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33916 : PairBound 9 := { available := 263, camps := [{ cop := 3, region := 419, targets := 64 },{ cop := 0, region := 324, targets := 32 }], pairs := [(0,6),(1,6),(2,5)], upper := (rows 11 162 69 28 112 295 327 391 263), lower := (rows 11 162 69 28 112 32 64 128 256), losses := [] }

theorem u33916 : Upper (D 6) (R 6) [10,160,65,20,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33916 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33917 : Route 9 := (fun mask => (mask,id))

def c33917 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33917 : Upper (D 6) (R 6) [10,160,65,20,257] 13 := by
  apply FastRouting.sound _ _ [10,160,65,20,257] 13 (by decide) (choices 1) [2,4,64] r33917 c33917
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17270
  · exact u17271
  · exact u17272

def r33918 : Route 9 := (fun mask => (mask,id))

def c33918 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33918 : Upper (D 6) (R 6) [10,160,65,20,258] 13 := by
  apply FastRouting.sound _ _ [10,160,65,20,258] 13 (by decide) (choices 1) [1,4,64] r33918 c33918
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17273
  · exact u17274
  · exact u17275

def b33919 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 162 69 28 276 99 99 227 355), lower := (rows 11 162 69 28 276 32 64 128 256), losses := [] }

theorem u33919 : Upper (D 6) (R 6) [10,160,65,20,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33919 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33920 : Route 9 := (fun mask => (mask,id))

def c33920 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33920 : Upper (D 6) (R 6) [10,160,65,20,288] 13 := by
  apply FastRouting.sound _ _ [10,160,65,20,288] 13 (by decide) (choices 1) [1,2,4,64] r33920 c33920
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17276
  · exact u17277
  · exact u17278
  · exact u17279

def r33921 : Route 9 := (fun mask => (mask,id))

def c33921 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33921 : Upper (D 6) (R 6) [10,160,65,20,320] 13 := by
  apply FastRouting.sound _ _ [10,160,65,20,320] 13 (by decide) (choices 1) [1,2,4] r33921 c33921
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17280
  · exact u17281
  · exact u17282

def b33922 : PairBound 9 := { available := 340, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(4,2),(4,6)], upper := (rows 11 162 69 44 19 372 340 468 340), lower := (rows 11 162 69 44 19 32 64 128 256), losses := [] }

theorem u33922 : Upper (D 6) (R 6) [10,160,65,36,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33922 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33923 : PairBound 9 := { available := 338, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 162 69 44 21 370 338 466 338), lower := (rows 11 162 69 44 21 32 64 128 256), losses := [] }

theorem u33923 : Upper (D 6) (R 6) [10,160,65,36,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33923 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33924 : Route 9 := (fun mask => (mask,id))

def c33924 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u33924 : Upper (D 6) (R 6) [10,160,65,36,6] 13 := by
  apply FastRouting.sound _ _ [10,160,65,36,6] 13 (by decide) (choices 1) [1,16,64,256] r33924 c33924
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17283
  · exact u17284
  · exact u17285
  · exact u17286

def b33925 : PairBound 9 := { available := 278, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 2, region := 16, targets := 2 }], pairs := [(2,5),(4,1),(4,5)], upper := (rows 11 162 69 44 81 310 342 406 278), lower := (rows 11 162 69 44 81 32 64 128 256), losses := [] }

theorem u33925 : Upper (D 6) (R 6) [10,160,65,36,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33925 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33926 : Route 9 := (fun mask => (mask,id))

def c33926 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u33926 : Upper (D 6) (R 6) [10,160,65,36,66] 13 := by
  apply FastRouting.sound _ _ [10,160,65,36,66] 13 (by decide) (choices 1) [1,4,16,256] r33926 c33926
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17287
  · exact u17288
  · exact u17289
  · exact u17290

def b33927 : PairBound 9 := { available := 275, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 162 69 44 84 307 339 403 275), lower := (rows 11 162 69 44 84 32 64 128 256), losses := [] }

theorem u33927 : Upper (D 6) (R 6) [10,160,65,36,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33927 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33928 : Route 9 := (fun mask => (mask,id))

def c33928 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33928 : Upper (D 6) (R 6) [10,160,65,36,257] 13 := by
  apply FastRouting.sound _ _ [10,160,65,36,257] 13 (by decide) (choices 1) [2,4,16,64] r33928 c33928
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17291
  · exact u17292
  · exact u17293
  · exact u17294

def r33929 : Route 9 := (fun mask => (mask,id))

def c33929 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33929 : Upper (D 6) (R 6) [10,160,65,36,258] 13 := by
  apply FastRouting.sound _ _ [10,160,65,36,258] 13 (by decide) (choices 1) [1,4,16,64] r33929 c33929
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17295
  · exact u17296
  · exact u17297
  · exact u17298

def r33930 : Route 9 := (fun mask => (mask,id))

def c33930 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33930 : Upper (D 6) (R 6) [10,160,65,36,260] 13 := by
  apply FastRouting.sound _ _ [10,160,65,36,260] 13 (by decide) (choices 1) [1,2,16,64] r33930 c33930
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17299
  · exact u17300
  · exact u17301
  · exact u17302

def r33931 : Route 9 := (fun mask => (mask,id))

def c33931 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33931 : Upper (D 6) (R 6) [10,160,65,36,320] 13 := by
  apply FastRouting.sound _ _ [10,160,65,36,320] 13 (by decide) (choices 1) [1,2,4,16] r33931 c33931
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17303
  · exact u17304
  · exact u17305
  · exact u17306

def b33932 : PairBound 9 := { available := 324, camps := [{ cop := 1, region := 25, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 162 69 56 19 356 324 452 324), lower := (rows 11 162 69 56 19 32 64 128 256), losses := [] }

theorem u33932 : Upper (D 6) (R 6) [10,160,65,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33932 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33933 : PairBound 9 := { available := 326, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 162 69 56 21 358 326 454 326), lower := (rows 11 162 69 56 21 32 64 128 256), losses := [] }

theorem u33933 : Upper (D 6) (R 6) [10,160,65,48,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33933 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33934 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 0, region := 324, targets := 2 }], pairs := [(2,1),(2,5),(4,5)], upper := (rows 11 162 69 56 22 357 325 453 325), lower := (rows 11 162 69 56 22 32 64 128 256), losses := [] }

theorem u33934 : Upper (D 6) (R 6) [10,160,65,48,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33934 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33935 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 2, region := 418, targets := 1 }], pairs := [(1,0),(2,5),(4,5)], upper := (rows 11 162 69 56 81 294 326 390 262), lower := (rows 11 162 69 56 81 32 64 128 256), losses := [] }

theorem u33935 : Upper (D 6) (R 6) [10,160,65,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33935 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33936 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 0, region := 324, targets := 2 }], pairs := [(2,1),(2,5),(4,5)], upper := (rows 11 162 69 56 82 293 325 389 261), lower := (rows 11 162 69 56 82 32 64 128 256), losses := [] }

theorem u33936 : Upper (D 6) (R 6) [10,160,65,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33936 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33937 : PairBound 9 := { available := 263, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 162 69 56 84 295 327 391 263), lower := (rows 11 162 69 56 84 32 64 128 256), losses := [] }

theorem u33937 : Upper (D 6) (R 6) [10,160,65,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33937 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33938 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 2, region := 162, targets := 1 }], pairs := [(1,0),(2,5),(4,5)], upper := (rows 11 162 69 56 273 102 70 198 326), lower := (rows 11 162 69 56 273 32 64 128 256), losses := [] }

theorem u33938 : Upper (D 6) (R 6) [10,160,65,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33938 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33939 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 0, region := 68, targets := 2 }], pairs := [(2,1),(2,5),(4,5)], upper := (rows 11 162 69 56 274 101 69 197 325), lower := (rows 11 162 69 56 274 32 64 128 256), losses := [] }

theorem u33939 : Upper (D 6) (R 6) [10,160,65,48,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33939 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33940 : Route 9 := (fun mask => (mask,id))

def c33940 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33940 : Upper (D 6) (R 6) [10,160,65,48,260] 13 := by
  apply FastRouting.sound _ _ [10,160,65,48,260] 13 (by decide) (choices 1) [1,2,4,64] r33940 c33940
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17307
  · exact u17308
  · exact u17309
  · exact u17310

def b33941 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 2, region := 162, targets := 64 }], pairs := [(1,6),(2,5),(4,5)], upper := (rows 11 162 69 56 336 39 71 135 263), lower := (rows 11 162 69 56 336 32 64 128 256), losses := [] }

theorem u33941 : Upper (D 6) (R 6) [10,160,65,48,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33941 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33942 : PairBound 9 := { available := 292, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 162 69 88 19 292 356 420 292), lower := (rows 11 162 69 88 19 32 64 128 256), losses := [] }

theorem u33942 : Upper (D 6) (R 6) [10,160,65,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33942 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33943 : PairBound 9 := { available := 294, camps := [{ cop := 2, region := 24, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 162 69 88 21 294 358 422 294), lower := (rows 11 162 69 88 21 32 64 128 256), losses := [] }

theorem u33943 : Upper (D 6) (R 6) [10,160,65,80,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33943 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33944 : PairBound 9 := { available := 293, camps := [{ cop := 2, region := 434, targets := 64 },{ cop := 0, region := 356, targets := 2 }], pairs := [(1,6),(2,1),(4,6)], upper := (rows 11 162 69 88 22 293 357 421 293), lower := (rows 11 162 69 88 22 32 64 128 256), losses := [] }

theorem u33944 : Upper (D 6) (R 6) [10,160,65,80,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33944 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33945 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 434, targets := 64 },{ cop := 0, region := 324, targets := 32 }], pairs := [(1,6),(2,5),(4,6)], upper := (rows 11 162 69 88 49 294 326 390 262), lower := (rows 11 162 69 88 49 32 64 128 256), losses := [] }

theorem u33945 : Upper (D 6) (R 6) [10,160,65,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33945 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33946 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 162 69 88 50 293 325 389 261), lower := (rows 11 162 69 88 50 32 64 128 256), losses := [] }

theorem u33946 : Upper (D 6) (R 6) [10,160,65,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33946 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33947 : PairBound 9 := { available := 263, camps := [{ cop := 2, region := 434, targets := 64 },{ cop := 0, region := 324, targets := 32 }], pairs := [(1,6),(2,5),(4,6)], upper := (rows 11 162 69 88 52 295 327 391 263), lower := (rows 11 162 69 88 52 32 64 128 256), losses := [] }

theorem u33947 : Upper (D 6) (R 6) [10,160,65,80,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33947 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33948 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 434, targets := 64 },{ cop := 2, region := 162, targets := 1 }], pairs := [(1,0),(1,6),(4,6)], upper := (rows 11 162 69 88 273 38 102 166 294), lower := (rows 11 162 69 88 273 32 64 128 256), losses := [] }

theorem u33948 : Upper (D 6) (R 6) [10,160,65,80,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33948 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33949 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 434, targets := 64 },{ cop := 0, region := 100, targets := 2 }], pairs := [(1,6),(2,1),(4,6)], upper := (rows 11 162 69 88 274 37 101 165 293), lower := (rows 11 162 69 88 274 32 64 128 256), losses := [] }

theorem u33949 : Upper (D 6) (R 6) [10,160,65,80,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33949 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33950 : PairBound 9 := { available := 39, camps := [{ cop := 2, region := 434, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 11 162 69 88 276 39 103 167 295), lower := (rows 11 162 69 88 276 32 64 128 256), losses := [{ target := 6, region := (rows 9 22 4 8 20 36 0 132 260), good := (rows 11 162 439 27 438 32 0 128 256) }] }

theorem u33950 : Upper (D 6) (R 6) [10,160,65,80,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33950 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33951 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 434, targets := 64 },{ cop := 0, region := 68, targets := 32 }], pairs := [(1,6),(2,5),(4,6)], upper := (rows 11 162 69 88 304 39 71 135 263), lower := (rows 11 162 69 88 304 32 64 128 256), losses := [] }

theorem u33951 : Upper (D 6) (R 6) [10,160,65,80,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33951 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33952 : Route 9 := (fun mask => (mask,id))

def c33952 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33952 : Upper (D 6) (R 6) [10,160,65,257,6] 13 := by
  apply FastRouting.sound _ _ [10,160,65,257,6] 13 (by decide) (choices 1) [4,16,64] r33952 c33952
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17311
  · exact u17312
  · exact u17313

def b33953 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 162 69 265 50 116 84 212 340), lower := (rows 11 162 69 265 50 32 64 128 256), losses := [] }

theorem u33953 : Upper (D 6) (R 6) [10,160,65,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33953 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33954 : Route 9 := (fun mask => (mask,id))

def c33954 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33954 : Upper (D 6) (R 6) [10,160,65,257,36] 13 := by
  apply FastRouting.sound _ _ [10,160,65,257,36] 13 (by decide) (choices 1) [2,4,16,64] r33954 c33954
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17314
  · exact u17315
  · exact u17316
  · exact u17317

def r33955 : Route 9 := (fun mask => (mask,id))

def c33955 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33955 : Upper (D 6) (R 6) [10,160,65,257,66] 13 := by
  apply FastRouting.sound _ _ [10,160,65,257,66] 13 (by decide) (choices 1) [4,16] r33955 c33955
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u17318
  · exact u17319

def b33956 : PairBound 9 := { available := 54, camps := [{ cop := 4, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 162 69 265 84 54 118 182 310), lower := (rows 11 162 69 265 84 32 64 128 256), losses := [] }

theorem u33956 : Upper (D 6) (R 6) [10,160,65,257,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33956 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33957 : Route 9 := (fun mask => (mask,id))

def c33957 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33957 : Upper (D 6) (R 6) [10,160,65,257,96] 13 := by
  apply FastRouting.sound _ _ [10,160,65,257,96] 13 (by decide) (choices 1) [2,4,16] r33957 c33957
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17320
  · exact u17321
  · exact u17322

def b33958 : PairBound 9 := { available := 116, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 162 69 268 19 116 116 244 372), lower := (rows 11 162 69 268 19 32 64 128 256), losses := [] }

theorem u33958 : Upper (D 6) (R 6) [10,160,65,260,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33958 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33959 : PairBound 9 := { available := 114, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 162 69 268 21 114 114 242 370), lower := (rows 11 162 69 268 21 32 64 128 256), losses := [] }

theorem u33959 : Upper (D 6) (R 6) [10,160,65,260,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33959 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u33959
end Delivery.IrregularNine14.P06

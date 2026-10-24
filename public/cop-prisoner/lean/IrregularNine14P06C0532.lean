import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0237
import IrregularNine14P06C0238

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r31920 : Route 9 := (fun mask => (mask,id))

def c31920 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31920 : Upper (D 6) (R 6) [10,48,96,132,320] 13 := by
  apply FastRouting.sound _ _ [10,48,96,132,320] 13 (by decide) (choices 1) [1,2,4] r31920 c31920
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14231
  · exact u14232
  · exact u14233

def b31921 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 50 100 200 19 293 325 389 261), lower := (rows 11 50 100 200 19 32 64 128 256), losses := [] }

theorem u31921 : Upper (D 6) (R 6) [10,48,96,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31921 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31922 : Route 9 := (fun mask => (mask,id))

def c31922 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31922 : Upper (D 6) (R 6) [10,48,96,192,5] 13 := by
  apply FastRouting.sound _ _ [10,48,96,192,5] 13 (by decide) (choices 1) [1,2,4,256] r31922 c31922
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14234
  · exact u14235
  · exact u14236
  · exact u14237

def b31923 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 18, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 50 100 200 22 293 325 389 261), lower := (rows 11 50 100 200 22 32 64 128 256), losses := [] }

theorem u31923 : Upper (D 6) (R 6) [10,48,96,192,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31923 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31924 : Route 9 := (fun mask => (mask,id))

def c31924 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31924 : Upper (D 6) (R 6) [10,48,96,192,257] 13 := by
  apply FastRouting.sound _ _ [10,48,96,192,257] 13 (by decide) (choices 1) [1,2,4] r31924 c31924
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14238
  · exact u14239
  · exact u14240

def r31925 : Route 9 := (fun mask => (mask,id))

def c31925 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31925 : Upper (D 6) (R 6) [10,48,96,192,258] 13 := by
  apply FastRouting.sound _ _ [10,48,96,192,258] 13 (by decide) (choices 1) [1,4] r31925 c31925
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u14241
  · exact u14242

def r31926 : Route 9 := (fun mask => (mask,id))

def c31926 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31926 : Upper (D 6) (R 6) [10,48,96,192,260] 13 := by
  apply FastRouting.sound _ _ [10,48,96,192,260] 13 (by decide) (choices 1) [1,2,4] r31926 c31926
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14243
  · exact u14244
  · exact u14245

def b31927 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 50 100 392 19 101 69 197 325), lower := (rows 11 50 100 392 19 32 64 128 256), losses := [] }

theorem u31927 : Upper (D 6) (R 6) [10,48,96,384,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31927 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31928 : Route 9 := (fun mask => (mask,id))

def c31928 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31928 : Upper (D 6) (R 6) [10,48,96,384,5] 13 := by
  apply FastRouting.sound _ _ [10,48,96,384,5] 13 (by decide) (choices 1) [1,2,4,64] r31928 c31928
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14246
  · exact u14247
  · exact u14248
  · exact u14249

def b31929 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 18, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 50 100 392 22 101 69 197 325), lower := (rows 11 50 100 392 22 32 64 128 256), losses := [] }

theorem u31929 : Upper (D 6) (R 6) [10,48,96,384,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31929 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31930 : Route 9 := (fun mask => (mask,id))

def c31930 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31930 : Upper (D 6) (R 6) [10,48,96,384,65] 13 := by
  apply FastRouting.sound _ _ [10,48,96,384,65] 13 (by decide) (choices 1) [1,2,4] r31930 c31930
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14250
  · exact u14251
  · exact u14252

def b31931 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 2, region := 18, targets := 1 }], pairs := [(1,0),(2,1),(3,1)], upper := (rows 11 50 100 392 82 37 69 133 261), lower := (rows 11 50 100 392 82 32 64 128 256), losses := [] }

theorem u31931 : Upper (D 6) (R 6) [10,48,96,384,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31931 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31932 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 50 100 392 84 39 71 135 263), lower := (rows 11 50 100 392 84 32 64 128 256), losses := [] }

theorem u31932 : Upper (D 6) (R 6) [10,48,96,384,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31932 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31933 : PairBound 9 := { available := 324, camps := [{ cop := 3, region := 19, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 50 133 44 19 356 324 452 324), lower := (rows 11 50 133 44 19 32 64 128 256), losses := [] }

theorem u31933 : Upper (D 6) (R 6) [10,48,129,36,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31933 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31934 : PairBound 9 := { available := 322, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 50 133 44 21 354 322 450 322), lower := (rows 11 50 133 44 21 32 64 128 256), losses := [] }

theorem u31934 : Upper (D 6) (R 6) [10,48,129,36,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31934 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31935 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 19, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 11 50 133 44 22 353 321 449 321), lower := (rows 11 50 133 44 22 32 64 128 256), losses := [] }

theorem u31935 : Upper (D 6) (R 6) [10,48,129,36,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31935 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31936 : Route 9 := (fun mask => (mask,id))

def c31936 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u31936 : Upper (D 6) (R 6) [10,48,129,36,65] 13 := by
  apply FastRouting.sound _ _ [10,48,129,36,65] 13 (by decide) (choices 1) [2,4,64,256] r31936 c31936
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14253
  · exact u14254
  · exact u14255
  · exact u14256

def b31937 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 0, region := 452, targets := 32 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 11 50 133 44 82 357 325 453 325), lower := (rows 11 50 133 44 82 32 64 128 256), losses := [] }

theorem u31937 : Upper (D 6) (R 6) [10,48,129,36,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31937 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31938 : Route 9 := (fun mask => (mask,id))

def c31938 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u31938 : Upper (D 6) (R 6) [10,48,129,36,68] 13 := by
  apply FastRouting.sound _ _ [10,48,129,36,68] 13 (by decide) (choices 1) [1,2,64,256] r31938 c31938
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14257
  · exact u14258
  · exact u14259
  · exact u14260

def r31939 : Route 9 := (fun mask => (mask,id))

def c31939 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31939 : Upper (D 6) (R 6) [10,48,129,36,257] 13 := by
  apply FastRouting.sound _ _ [10,48,129,36,257] 13 (by decide) (choices 1) [2,4,64] r31939 c31939
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14261
  · exact u14262
  · exact u14263

def b31940 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 0, region := 196, targets := 32 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 11 50 133 44 274 101 69 197 325), lower := (rows 11 50 133 44 274 32 64 128 256), losses := [] }

theorem u31940 : Upper (D 6) (R 6) [10,48,129,36,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31940 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31941 : Route 9 := (fun mask => (mask,id))

def c31941 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31941 : Upper (D 6) (R 6) [10,48,129,36,260] 13 := by
  apply FastRouting.sound _ _ [10,48,129,36,260] 13 (by decide) (choices 1) [1,2,64] r31941 c31941
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14264
  · exact u14265
  · exact u14266

def r31942 : Route 9 := (fun mask => (mask,id))

def c31942 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31942 : Upper (D 6) (R 6) [10,48,129,36,320] 13 := by
  apply FastRouting.sound _ _ [10,48,129,36,320] 13 (by decide) (choices 1) [1,2,4,64] r31942 c31942
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14267
  · exact u14268
  · exact u14269
  · exact u14270

def b31943 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 2, region := 370, targets := 1 }], pairs := [(1,0),(2,1),(3,1)], upper := (rows 11 50 133 73 22 356 356 484 356), lower := (rows 11 50 133 73 22 32 64 128 256), losses := [] }

theorem u31943 : Upper (D 6) (R 6) [10,48,129,65,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31943 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31944 : PairBound 9 := { available := 324, camps := [{ cop := 5, region := 18, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 50 133 73 50 356 324 452 324), lower := (rows 11 50 133 73 50 32 64 128 256), losses := [] }

theorem u31944 : Upper (D 6) (R 6) [10,48,129,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31944 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31945 : PairBound 9 := { available := 326, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 133 73 52 358 326 454 326), lower := (rows 11 50 133 73 52 32 64 128 256), losses := [] }

theorem u31945 : Upper (D 6) (R 6) [10,48,129,65,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31945 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31946 : PairBound 9 := { available := 292, camps := [{ cop := 4, region := 9, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 50 133 73 82 292 356 420 292), lower := (rows 11 50 133 73 82 32 64 128 256), losses := [] }

theorem u31946 : Upper (D 6) (R 6) [10,48,129,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31946 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31947 : PairBound 9 := { available := 294, camps := [{ cop := 2, region := 370, targets := 1 },{ cop := 0, region := 420, targets := 64 }], pairs := [(1,0),(2,6),(4,0)], upper := (rows 11 50 133 73 84 294 358 422 294), lower := (rows 11 50 133 73 84 32 64 128 256), losses := [] }

theorem u31947 : Upper (D 6) (R 6) [10,48,129,65,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31947 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31948 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 133 73 112 294 326 390 262), lower := (rows 11 50 133 73 112 32 64 128 256), losses := [] }

theorem u31948 : Upper (D 6) (R 6) [10,48,129,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31948 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31949 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 2, region := 370, targets := 1 }], pairs := [(1,0),(2,1),(3,1)], upper := (rows 11 50 133 73 274 100 100 228 356), lower := (rows 11 50 133 73 274 32 64 128 256), losses := [] }

theorem u31949 : Upper (D 6) (R 6) [10,48,129,65,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31949 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31950 : Route 9 := (fun mask => (mask,id))

def c31950 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31950 : Upper (D 6) (R 6) [10,48,129,65,260] 13 := by
  apply FastRouting.sound _ _ [10,48,129,65,260] 13 (by decide) (choices 1) [2,4,64] r31950 c31950
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14271
  · exact u14272
  · exact u14273

def b31951 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 205, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 133 73 304 102 70 198 326), lower := (rows 11 50 133 73 304 32 64 128 256), losses := [] }

theorem u31951 : Upper (D 6) (R 6) [10,48,129,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31951 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31952 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 370, targets := 1 },{ cop := 0, region := 164, targets := 64 }], pairs := [(1,0),(2,6),(4,0)], upper := (rows 11 50 133 73 336 38 102 166 294), lower := (rows 11 50 133 73 336 32 64 128 256), losses := [] }

theorem u31952 : Upper (D 6) (R 6) [10,48,129,65,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31952 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31953 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 50 133 76 19 356 356 484 356), lower := (rows 11 50 133 76 19 32 64 128 256), losses := [] }

theorem u31953 : Upper (D 6) (R 6) [10,48,129,68,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31953 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31954 : PairBound 9 := { available := 354, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 50 133 76 21 354 354 482 354), lower := (rows 11 50 133 76 21 32 64 128 256), losses := [] }

theorem u31954 : Upper (D 6) (R 6) [10,48,129,68,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31954 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31955 : PairBound 9 := { available := 353, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(1,2),(2,1),(3,1)], upper := (rows 11 50 133 76 22 353 353 481 353), lower := (rows 11 50 133 76 22 32 64 128 256), losses := [{ target := 2, region := (rows 1 18 0 8 16 37 69 133 261), good := (rows 491 50 481 488 498 32 64 128 256) }] }

theorem u31955 : Upper (D 6) (R 6) [10,48,129,68,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31955 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31956 : PairBound 9 := { available := 326, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 133 76 49 358 326 454 326), lower := (rows 11 50 133 76 49 32 64 128 256), losses := [] }

theorem u31956 : Upper (D 6) (R 6) [10,48,129,68,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31956 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31957 : PairBound 9 := { available := 325, camps := [{ cop := 5, region := 18, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 50 133 76 50 357 325 453 325), lower := (rows 11 50 133 76 50 32 64 128 256), losses := [] }

theorem u31957 : Upper (D 6) (R 6) [10,48,129,68,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31957 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31958 : PairBound 9 := { available := 323, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 133 76 52 355 323 451 323), lower := (rows 11 50 133 76 52 32 64 128 256), losses := [] }

theorem u31958 : Upper (D 6) (R 6) [10,48,129,68,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31958 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31959 : Route 9 := (fun mask => (mask,id))

def c31959 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31959 : Upper (D 6) (R 6) [10,48,129,68,65] 13 := by
  apply FastRouting.sound _ _ [10,48,129,68,65] 13 (by decide) (choices 1) [2,4,256] r31959 c31959
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14274
  · exact u14275
  · exact u14276

def b31960 : PairBound 9 := { available := 293, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 0, region := 420, targets := 64 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 11 50 133 76 82 293 357 421 293), lower := (rows 11 50 133 76 82 32 64 128 256), losses := [] }

theorem u31960 : Upper (D 6) (R 6) [10,48,129,68,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31960 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31961 : PairBound 9 := { available := 291, camps := [{ cop := 3, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 50 133 76 84 291 355 419 291), lower := (rows 11 50 133 76 84 32 64 128 256), losses := [] }

theorem u31961 : Upper (D 6) (R 6) [10,48,129,68,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31961 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31962 : PairBound 9 := { available := 263, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 133 76 112 295 327 391 263), lower := (rows 11 50 133 76 112 32 64 128 256), losses := [] }

theorem u31962 : Upper (D 6) (R 6) [10,48,129,68,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31962 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31963 : Route 9 := (fun mask => (mask,id))

def c31963 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31963 : Upper (D 6) (R 6) [10,48,129,68,257] 13 := by
  apply FastRouting.sound _ _ [10,48,129,68,257] 13 (by decide) (choices 1) [2,4,64] r31963 c31963
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14277
  · exact u14278
  · exact u14279

def r31964 : Route 9 := (fun mask => (mask,id))

def c31964 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31964 : Upper (D 6) (R 6) [10,48,129,68,258] 13 := by
  apply FastRouting.sound _ _ [10,48,129,68,258] 13 (by decide) (choices 1) [1,4,64] r31964 c31964
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14280
  · exact u14281
  · exact u14282

def r31965 : Route 9 := (fun mask => (mask,id))

def c31965 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31965 : Upper (D 6) (R 6) [10,48,129,68,260] 13 := by
  apply FastRouting.sound _ _ [10,48,129,68,260] 13 (by decide) (choices 1) [1,2,64] r31965 c31965
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14283
  · exact u14284
  · exact u14285

def b31966 : PairBound 9 := { available := 71, camps := [{ cop := 1, region := 205, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 133 76 304 103 71 199 327), lower := (rows 11 50 133 76 304 32 64 128 256), losses := [] }

theorem u31966 : Upper (D 6) (R 6) [10,48,129,68,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31966 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31967 : Route 9 := (fun mask => (mask,id))

def c31967 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31967 : Upper (D 6) (R 6) [10,48,129,68,320] 13 := by
  apply FastRouting.sound _ _ [10,48,129,68,320] 13 (by decide) (choices 1) [1,2,4] r31967 c31967
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14286
  · exact u14287
  · exact u14288

def b31968 : PairBound 9 := { available := 324, camps := [{ cop := 3, region := 19, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 50 133 104 19 356 324 452 324), lower := (rows 11 50 133 104 19 32 64 128 256), losses := [] }

theorem u31968 : Upper (D 6) (R 6) [10,48,129,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31968 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31969 : PairBound 9 := { available := 326, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 50 133 104 21 358 326 454 326), lower := (rows 11 50 133 104 21 32 64 128 256), losses := [] }

theorem u31969 : Upper (D 6) (R 6) [10,48,129,96,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31969 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31970 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 0, region := 452, targets := 32 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 11 50 133 104 22 357 325 453 325), lower := (rows 11 50 133 104 22 32 64 128 256), losses := [] }

theorem u31970 : Upper (D 6) (R 6) [10,48,129,96,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31970 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31971 : PairBound 9 := { available := 262, camps := [{ cop := 3, region := 19, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 50 133 104 81 294 326 390 262), lower := (rows 11 50 133 104 81 32 64 128 256), losses := [] }

theorem u31971 : Upper (D 6) (R 6) [10,48,129,96,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31971 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31972 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 19, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 50 133 104 82 293 325 389 261), lower := (rows 11 50 133 104 82 32 64 128 256), losses := [] }

theorem u31972 : Upper (D 6) (R 6) [10,48,129,96,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31972 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31973 : PairBound 9 := { available := 263, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 0, region := 388, targets := 64 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 50 133 104 84 295 327 391 263), lower := (rows 11 50 133 104 84 32 64 128 256), losses := [] }

theorem u31973 : Upper (D 6) (R 6) [10,48,129,96,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31973 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31974 : Route 9 := (fun mask => (mask,id))

def c31974 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31974 : Upper (D 6) (R 6) [10,48,129,96,257] 13 := by
  apply FastRouting.sound _ _ [10,48,129,96,257] 13 (by decide) (choices 1) [2,4,64] r31974 c31974
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14289
  · exact u14290
  · exact u14291

def b31975 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 0, region := 196, targets := 32 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 11 50 133 104 274 101 69 197 325), lower := (rows 11 50 133 104 274 32 64 128 256), losses := [] }

theorem u31975 : Upper (D 6) (R 6) [10,48,129,96,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31975 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31976 : Route 9 := (fun mask => (mask,id))

def c31976 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31976 : Upper (D 6) (R 6) [10,48,129,96,260] 13 := by
  apply FastRouting.sound _ _ [10,48,129,96,260] 13 (by decide) (choices 1) [1,2,4,64] r31976 c31976
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14292
  · exact u14293
  · exact u14294
  · exact u14295

def b31977 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 0, region := 132, targets := 64 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 50 133 104 336 39 71 135 263), lower := (rows 11 50 133 104 336 32 64 128 256), losses := [] }

theorem u31977 : Upper (D 6) (R 6) [10,48,129,96,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31977 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31978 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 2, region := 114, targets := 1 }], pairs := [(1,0),(2,1),(3,1)], upper := (rows 11 50 133 265 22 100 100 228 356), lower := (rows 11 50 133 265 22 32 64 128 256), losses := [] }

theorem u31978 : Upper (D 6) (R 6) [10,48,129,257,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31978 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31979 : PairBound 9 := { available := 68, camps := [{ cop := 5, region := 18, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 50 133 265 50 100 68 196 324), lower := (rows 11 50 133 265 50 32 64 128 256), losses := [] }

theorem u31979 : Upper (D 6) (R 6) [10,48,129,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31979 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u31979
end Delivery.IrregularNine14.P06

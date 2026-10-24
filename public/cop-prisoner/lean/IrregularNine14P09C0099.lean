import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0040
import IrregularNine14P09C0041

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5940 : PairBound 9 := { available := 280, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 388 42 145 96 344 408 280), lower := (rows 97 7 388 42 145 96 64 128 256), losses := [] }

theorem u5940 : Upper (D 9) (R 9) [96,5,384,34,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5940 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5941 : PairBound 9 := { available := 88, camps := [{ cop := 3, region := 209, targets := 256 }], pairs := [(0,8),(3,0),(3,6),(3,7),(4,8)], upper := (rows 97 7 388 42 145 288 88 216 344), lower := (rows 97 7 388 42 145 288 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 10 16 292 64 128 256), good := (rows 96 46 420 42 144 288 64 128 288) },{ target := 6, region := (rows 1 2 4 10 16 292 0 128 256), good := (rows 33 47 420 42 145 288 0 128 288) },{ target := 7, region := (rows 1 2 4 10 16 292 64 0 256), good := (rows 97 47 292 42 17 288 64 0 288) }] }

theorem u5941 : Upper (D 9) (R 9) [96,5,384,34,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5941 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5942 : PairBound 9 := { available := 336, camps := [{ cop := 3, region := 468, targets := 33 },{ cop := 1, region := 40, targets := 64 }], pairs := [(2,0),(2,5),(3,6),(4,0),(4,5)], upper := (rows 97 7 388 42 152 33 336 464 336), lower := (rows 97 7 388 42 152 33 64 128 256), losses := [] }

theorem u5942 : Upper (D 9) (R 9) [96,5,384,34,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5942 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5943 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 390, targets := 32 },{ cop := 3, region := 321, targets := 128 }], pairs := [(0,7),(1,5),(2,5),(4,5)], upper := (rows 97 7 388 42 152 48 321 449 321), lower := (rows 97 7 388 42 152 48 64 128 256), losses := [{ target := 5, region := (rows 1 3 15 8 24 0 67 131 259), good := (rows 455 455 388 478 156 16 64 128 256) }] }

theorem u5943 : Upper (D 9) (R 9) [96,5,384,34,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5943 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5944 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 388 42 152 96 337 401 273), lower := (rows 97 7 388 42 152 96 64 128 256), losses := [] }

theorem u5944 : Upper (D 9) (R 9) [96,5,384,34,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5944 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5945 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 209, targets := 256 },{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7),(0,8),(3,0),(3,6),(4,8)], upper := (rows 97 7 388 42 152 288 81 209 337), lower := (rows 97 7 388 42 152 288 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 10 16 292 64 128 256), good := (rows 96 46 420 42 152 288 64 128 288) },{ target := 6, region := (rows 1 2 4 10 16 292 0 128 256), good := (rows 33 47 420 42 152 288 0 128 288) }] }

theorem u5945 : Upper (D 9) (R 9) [96,5,384,34,136,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5945 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5946 : PairBound 9 := { available := 280, camps := [{ cop := 3, region := 468, targets := 33 },{ cop := 1, region := 40, targets := 64 }], pairs := [(2,0),(2,5),(3,6),(4,0),(4,5)], upper := (rows 97 7 388 42 208 33 344 408 280), lower := (rows 97 7 388 42 208 33 64 128 256), losses := [] }

theorem u5946 : Upper (D 9) (R 9) [96,5,384,34,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5946 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5947 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 40, targets := 449 }], pairs := [(3,0),(3,6),(3,7),(3,8)], upper := (rows 97 7 388 42 208 40 337 401 273), lower := (rows 97 7 388 42 208 40 64 128 256), losses := [] }

theorem u5947 : Upper (D 9) (R 9) [96,5,384,34,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5947 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5948 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 398, targets := 64 },{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6)], upper := (rows 97 7 388 42 208 48 329 393 265), lower := (rows 97 7 388 42 208 48 64 128 256), losses := [] }

theorem u5948 : Upper (D 9) (R 9) [96,5,384,34,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5948 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5949 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 209, targets := 256 }], pairs := [(0,8),(3,0),(3,6),(3,7),(4,8)], upper := (rows 97 7 388 42 208 288 89 153 281), lower := (rows 97 7 388 42 208 288 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 10 16 292 64 128 256), good := (rows 96 46 420 42 208 288 64 128 288) },{ target := 6, region := (rows 1 2 4 10 16 292 0 128 256), good := (rows 33 47 420 42 144 288 0 128 288) },{ target := 7, region := (rows 1 2 4 10 16 292 64 0 256), good := (rows 97 47 292 42 80 288 64 0 288) }] }

theorem u5949 : Upper (D 9) (R 9) [96,5,384,34,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5949 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5950 : Route 9 := (fun mask => (mask,id))

def c5950 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5950 : Upper (D 9) (R 9) [96,5,384,48,129,2] 13 := by
  apply FastRouting.sound _ _ [96,5,384,48,129,2] 13 (by decide) (choices 1) [8,256] r5950 c5950
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2417
  · exact u2418

def b5951 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 40, targets := 449 }], pairs := [(3,0),(3,6),(3,7),(3,8)], upper := (rows 97 7 388 56 145 40 322 450 322), lower := (rows 97 7 388 56 145 40 64 128 256), losses := [] }

theorem u5951 : Upper (D 9) (R 9) [96,5,384,48,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5951 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5952 : PairBound 9 := { available := 266, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 388 56 145 96 330 394 266), lower := (rows 97 7 388 56 145 96 64 128 256), losses := [] }

theorem u5952 : Upper (D 9) (R 9) [96,5,384,48,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5952 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5953 : Route 9 := (fun mask => (mask,id))

def c5953 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5953 : Upper (D 9) (R 9) [96,5,384,48,129,256] 13 := by
  apply FastRouting.sound _ _ [96,5,384,48,129,256] 13 (by decide) (choices 1) [2,8] r5953 c5953
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2419
  · exact u2420

def b5954 : PairBound 9 := { available := 328, camps := [{ cop := 3, region := 452, targets := 33 },{ cop := 4, region := 361, targets := 128 },{ cop := 6, region := 33, targets := 256 }], pairs := [(0,7),(0,8),(2,0),(2,5),(3,7)], upper := (rows 97 7 388 56 146 33 328 456 328), lower := (rows 97 7 388 56 146 33 64 128 256), losses := [] }

theorem u5954 : Upper (D 9) (R 9) [96,5,384,48,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5954 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5955 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 406, targets := 32 },{ cop := 4, region := 40, targets := 1 }], pairs := [(1,5),(2,5),(3,0),(4,5)], upper := (rows 97 7 388 56 146 40 321 449 321), lower := (rows 97 7 388 56 146 40 64 128 256), losses := [] }

theorem u5955 : Upper (D 9) (R 9) [96,5,384,48,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5955 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5956 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 4, region := 361, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 388 56 146 96 329 393 265), lower := (rows 97 7 388 56 146 96 64 128 256), losses := [] }

theorem u5956 : Upper (D 9) (R 9) [96,5,384,48,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5956 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5957 : Route 9 := (fun mask => (mask,id))

def c5957 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5957 : Upper (D 9) (R 9) [96,5,384,48,130,256] 13 := by
  apply FastRouting.sound _ _ [96,5,384,48,130,256] 13 (by decide) (choices 1) [1,8] r5957 c5957
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2421
  · exact u2422

def b5958 : PairBound 9 := { available := 322, camps := [{ cop := 0, region := 390, targets := 32 },{ cop := 2, region := 99, targets := 128 },{ cop := 1, region := 452, targets := 1 }], pairs := [(0,7),(1,5),(1,7),(2,0),(2,5)], upper := (rows 97 7 388 56 152 33 322 450 322), lower := (rows 97 7 388 56 152 33 64 128 256), losses := [] }

theorem u5958 : Upper (D 9) (R 9) [96,5,384,48,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5958 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5959 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 390, targets := 32 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(1,5),(1,7),(2,5)], upper := (rows 97 7 388 56 152 34 321 449 321), lower := (rows 97 7 388 56 152 34 64 128 256), losses := [] }

theorem u5959 : Upper (D 9) (R 9) [96,5,384,48,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5959 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5960 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 0, region := 390, targets := 32 }], pairs := [(1,5),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 388 56 152 96 323 387 259), lower := (rows 97 7 388 56 152 96 64 128 256), losses := [] }

theorem u5960 : Upper (D 9) (R 9) [96,5,384,48,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5960 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5961 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 56, targets := 65 },{ cop := 0, region := 390, targets := 32 }], pairs := [(1,5),(3,0),(3,6),(4,0),(4,6)], upper := (rows 97 7 388 56 152 288 67 195 323), lower := (rows 97 7 388 56 152 288 64 128 256), losses := [] }

theorem u5961 : Upper (D 9) (R 9) [96,5,384,48,136,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5961 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5962 : Route 9 := (fun mask => (mask,id))

def c5962 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5962 : Upper (D 9) (R 9) [96,5,384,48,192,1] 13 := by
  apply FastRouting.sound _ _ [96,5,384,48,192,1] 13 (by decide) (choices 1) [2,8,256] r5962 c5962
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2423
  · exact u2424
  · exact u2425

def r5963 : Route 9 := (fun mask => (mask,id))

def c5963 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5963 : Upper (D 9) (R 9) [96,5,384,48,192,2] 13 := by
  apply FastRouting.sound _ _ [96,5,384,48,192,2] 13 (by decide) (choices 1) [1,8,256] r5963 c5963
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2426
  · exact u2427
  · exact u2428

def b5964 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 41, targets := 384 }], pairs := [(0,7),(0,8),(3,7),(3,8)], upper := (rows 97 7 388 56 208 40 323 387 259), lower := (rows 97 7 388 56 208 40 64 128 256), losses := [] }

theorem u5964 : Upper (D 9) (R 9) [96,5,384,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5964 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5965 : Route 9 := (fun mask => (mask,id))

def c5965 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5965 : Upper (D 9) (R 9) [96,5,384,48,192,256] 13 := by
  apply FastRouting.sound _ _ [96,5,384,48,192,256] 13 (by decide) (choices 1) [1,2,8] r5965 c5965
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2429
  · exact u2430
  · exact u2431

def r5966 : Route 9 := (fun mask => (mask,id))

def c5966 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5966 : Upper (D 9) (R 9) [96,5,384,129,258,8] 13 := by
  apply FastRouting.sound _ _ [96,5,384,129,258,8] 13 (by decide) (choices 1) [16,32] r5966 c5966
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2432
  · exact u2433

theorem m5967_8 : Upper (D 9) (R 9) [96,5,384,129,258,16,8] 13 :=
  permutation_upper _ _ _ [96,5,384,129,258,8,16] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2432

def r5967 : Route 9 := (fun mask => (mask,id))

def c5967 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5967 : Upper (D 9) (R 9) [96,5,384,129,258,16] 13 := by
  apply FastRouting.sound _ _ [96,5,384,129,258,16] 13 (by decide) (choices 1) [8,32] r5967 c5967
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m5967_8
  · exact u2434

def b5968 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 4, region := 233, targets := 256 }], pairs := [(0,8),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 388 137 274 96 120 184 312), lower := (rows 97 7 388 137 274 96 64 128 256), losses := [] }

theorem u5968 : Upper (D 9) (R 9) [96,5,384,129,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5968 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5969 : Route 9 := (fun mask => (mask,id))

def c5969 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5969 : Upper (D 9) (R 9) [96,5,384,129,264,2] 13 := by
  apply FastRouting.sound _ _ [96,5,384,129,264,2] 13 (by decide) (choices 1) [16,32] r5969 c5969
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2435
  · exact u2436

theorem m5970_2 : Upper (D 9) (R 9) [96,5,384,129,264,16,2] 13 :=
  permutation_upper _ _ _ [96,5,384,129,264,2,16] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2435

def r5970 : Route 9 := (fun mask => (mask,id))

def c5970 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5970 : Upper (D 9) (R 9) [96,5,384,129,264,16] 13 := by
  apply FastRouting.sound _ _ [96,5,384,129,264,16] 13 (by decide) (choices 1) [2,32] r5970 c5970
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m5970_2
  · exact u2437

def b5971 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 388 137 280 96 114 178 306), lower := (rows 97 7 388 137 280 96 64 128 256), losses := [] }

theorem u5971 : Upper (D 9) (R 9) [96,5,384,129,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5971 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5972 : Route 9 := (fun mask => (mask,id))

def c5972 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5972 : Upper (D 9) (R 9) [96,5,384,129,288,2] 13 := by
  apply FastRouting.sound _ _ [96,5,384,129,288,2] 13 (by decide) (choices 1) [8,16] r5972 c5972
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2438
  · exact u2439

def r5973 : Route 9 := (fun mask => (mask,id))

def c5973 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5973 : Upper (D 9) (R 9) [96,5,384,129,288,8] 13 := by
  apply FastRouting.sound _ _ [96,5,384,129,288,8] 13 (by decide) (choices 1) [2,16] r5973 c5973
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2440
  · exact u2441

def b5974 : PairBound 9 := { available := 74, camps := [{ cop := 0, region := 398, targets := 32 },{ cop := 2, region := 48, targets := 1 }], pairs := [(1,5),(2,5),(3,5),(4,0)], upper := (rows 97 7 388 137 304 48 74 202 330), lower := (rows 97 7 388 137 304 48 64 128 256), losses := [] }

theorem u5974 : Upper (D 9) (R 9) [96,5,384,129,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5974 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5975 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 388 137 304 96 90 154 282), lower := (rows 97 7 388 137 304 96 64 128 256), losses := [] }

theorem u5975 : Upper (D 9) (R 9) [96,5,384,129,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5975 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5976 : Route 9 := (fun mask => (mask,id))

def c5976 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5976 : Upper (D 9) (R 9) [96,5,384,130,264,1] 13 := by
  apply FastRouting.sound _ _ [96,5,384,130,264,1] 13 (by decide) (choices 1) [16,32] r5976 c5976
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2442
  · exact u2443

def b5977 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 369, targets := 128 },{ cop := 4, region := 97, targets := 256 }], pairs := [(0,7),(0,8),(3,8),(4,7)], upper := (rows 97 7 388 138 280 48 97 225 353), lower := (rows 97 7 388 138 280 48 64 128 256), losses := [{ target := 8, region := (rows 49 2 4 10 16 48 113 177 0), good := (rows 225 207 132 138 249 241 64 128 0) }] }

theorem u5977 : Upper (D 9) (R 9) [96,5,384,130,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5977 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5978 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 388 138 280 96 113 177 305), lower := (rows 97 7 388 138 280 96 64 128 256), losses := [] }

theorem u5978 : Upper (D 9) (R 9) [96,5,384,130,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5978 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5979 : Route 9 := (fun mask => (mask,id))

def c5979 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5979 : Upper (D 9) (R 9) [96,5,384,130,288,1] 13 := by
  apply FastRouting.sound _ _ [96,5,384,130,288,1] 13 (by decide) (choices 1) [8,16] r5979 c5979
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2444
  · exact u2445

def r5980 : Route 9 := (fun mask => (mask,id))

def c5980 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5980 : Upper (D 9) (R 9) [96,5,384,130,288,8] 13 := by
  apply FastRouting.sound _ _ [96,5,384,130,288,8] 13 (by decide) (choices 1) [1,16] r5980 c5980
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2446
  · exact u2447

def b5981 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 398, targets := 32 },{ cop := 2, region := 48, targets := 1 }], pairs := [(1,5),(2,5),(3,5),(4,0)], upper := (rows 97 7 388 138 304 48 73 201 329), lower := (rows 97 7 388 138 304 48 64 128 256), losses := [] }

theorem u5981 : Upper (D 9) (R 9) [96,5,384,130,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5981 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5982 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 388 138 304 96 89 153 281), lower := (rows 97 7 388 138 304 96 64 128 256), losses := [] }

theorem u5982 : Upper (D 9) (R 9) [96,5,384,130,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5982 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5983 : Route 9 := (fun mask => (mask,id))

def c5983 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5983 : Upper (D 9) (R 9) [96,5,384,144,288,1] 13 := by
  apply FastRouting.sound _ _ [96,5,384,144,288,1] 13 (by decide) (choices 1) [2,8] r5983 c5983
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2448
  · exact u2449

def r5984 : Route 9 := (fun mask => (mask,id))

def c5984 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5984 : Upper (D 9) (R 9) [96,5,384,144,288,2] 13 := by
  apply FastRouting.sound _ _ [96,5,384,144,288,2] 13 (by decide) (choices 1) [1,8] r5984 c5984
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2450
  · exact u2451

def b5985 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 56, targets := 65 }], pairs := [(3,0),(3,6),(4,0),(4,6)], upper := (rows 97 7 388 152 304 40 67 195 323), lower := (rows 97 7 388 152 304 40 64 128 256), losses := [] }

theorem u5985 : Upper (D 9) (R 9) [96,5,384,144,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5985 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5986 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 388 152 304 96 75 139 267), lower := (rows 97 7 388 152 304 96 64 128 256), losses := [] }

theorem u5986 : Upper (D 9) (R 9) [96,5,384,144,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5986 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5987 : Route 9 := (fun mask => (mask,id))

def c5987 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5987 : Upper (D 9) (R 9) [96,5,384,160,320,1] 13 := by
  apply FastRouting.sound _ _ [96,5,384,160,320,1] 13 (by decide) (choices 1) [2,8,16] r5987 c5987
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2452
  · exact u2453
  · exact u2454

theorem m5988_1 : Upper (D 9) (R 9) [96,5,384,160,320,2,1] 13 :=
  permutation_upper _ _ _ [96,5,384,160,320,1,2] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2452

def r5988 : Route 9 := (fun mask => (mask,id))

def c5988 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5988 : Upper (D 9) (R 9) [96,5,384,160,320,2] 13 := by
  apply FastRouting.sound _ _ [96,5,384,160,320,2] 13 (by decide) (choices 1) [1,8,16] r5988 c5988
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m5988_1
  · exact u2455
  · exact u2456

def b5989 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 406, targets := 32 },{ cop := 2, region := 40, targets := 1 }], pairs := [(1,5),(2,5),(3,0),(4,5)], upper := (rows 97 7 388 168 336 40 83 147 275), lower := (rows 97 7 388 168 336 40 64 128 256), losses := [] }

theorem u5989 : Upper (D 9) (R 9) [96,5,384,160,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5989 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5990 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 398, targets := 64 },{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6)], upper := (rows 97 7 388 168 336 48 75 139 267), lower := (rows 97 7 388 168 336 48 64 128 256), losses := [] }

theorem u5990 : Upper (D 9) (R 9) [96,5,384,160,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5990 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5991 : PairBound 9 := { available := 320, camps := [{ cop := 3, region := 54, targets := 320 }], pairs := [(1,6),(1,8),(2,6),(2,8),(4,6)], upper := (rows 97 14 22 137 176 33 320 448 320), lower := (rows 97 14 22 137 176 33 64 128 256), losses := [] }

theorem u5991 : Upper (D 9) (R 9) [96,12,18,129,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5991 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5992 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 0, region := 392, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(3,6),(4,6)], upper := (rows 97 14 22 137 176 96 321 385 257), lower := (rows 97 14 22 137 176 96 64 128 256), losses := [] }

theorem u5992 : Upper (D 9) (R 9) [96,12,18,129,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5992 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5993 : Route 9 := (fun mask => (mask,id))

def c5993 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5993 : Upper (D 9) (R 9) [96,12,18,129,160,256] 13 := by
  apply FastRouting.sound _ _ [96,12,18,129,160,256] 13 (by decide) (choices 1) [1,256] r5993 c5993
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2457
  · exact u2458

def b5994 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 14 22 137 273 96 480 416 416), lower := (rows 97 14 22 137 273 96 64 128 256), losses := [] }

theorem u5994 : Upper (D 9) (R 9) [96,12,18,129,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5994 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m5995_32 : Upper (D 9) (R 9) [96,12,18,129,257,128,32] 13 :=
  permutation_upper _ _ _ [96,12,18,129,257,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2459

def r5995 : Route 9 := (fun mask => (mask,id))

def c5995 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u5995 : Upper (D 9) (R 9) [96,12,18,129,257,128] 13 := by
  apply FastRouting.sound _ _ [96,12,18,129,257,128] 13 (by decide) (choices 1) [32,256] r5995 c5995
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m5995_32
  · exact u2460

def b5996 : PairBound 9 := { available := 448, camps := [{ cop := 6, region := 33, targets := 384 },{ cop := 0, region := 400, targets := 1 },{ cop := 0, region := 392, targets := 32 }], pairs := [(0,7),(0,8),(1,0),(3,5),(4,0)], upper := (rows 97 14 22 137 304 33 448 448 448), lower := (rows 97 14 22 137 304 33 64 128 256), losses := [{ target := 0, region := (rows 0 10 12 8 49 32 511 511 511), good := (rows 496 462 470 478 496 496 448 448 448) }] }

theorem u5996 : Upper (D 9) (R 9) [96,12,18,129,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5996 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5997 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 14 22 137 304 96 449 385 385), lower := (rows 97 14 22 137 304 96 64 128 256), losses := [] }

theorem u5997 : Upper (D 9) (R 9) [96,12,18,129,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5997 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5998 : PairBound 9 := { available := 321, camps := [{ cop := 5, region := 337, targets := 128 },{ cop := 0, region := 392, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(3,5),(4,7)], upper := (rows 97 14 22 137 304 160 321 449 321), lower := (rows 97 14 22 137 304 160 64 128 256), losses := [{ target := 7, region := (rows 49 10 12 8 49 32 125 0 317), good := (rows 369 334 343 351 369 369 64 0 256) }] }

theorem u5998 : Upper (D 9) (R 9) [96,12,18,129,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5998 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5999 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 207, targets := 256 },{ cop := 5, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 97 14 22 137 304 288 193 193 449), lower := (rows 97 14 22 137 304 288 64 128 256), losses := [] }

theorem u5999 : Upper (D 9) (R 9) [96,12,18,129,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5999 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u5999
end Delivery.IrregularNine14.P09

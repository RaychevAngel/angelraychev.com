import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0355
import IrregularNine14P07C0356
import IrregularNine14P07C0357

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b35940 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,6),(3,1),(4,1)], upper := (rows 35 262 70 88 152 161 225 161 417), lower := (rows 35 262 70 88 152 32 64 128 256), losses := [] }

theorem u35940 : Upper (D 7) (R 7) [34,260,66,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35940 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35941 : Route 9 := (fun mask => (mask,id))

def c35941 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35941 : Upper (D 7) (R 7) [34,260,66,80,160] 13 := by
  apply FastRouting.sound _ _ [34,260,66,80,160] 13 (by decide) (choices 1) [1,8,128] r35941 c35941
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21354
  · exact u21355
  · exact u21356

def r35942 : Route 9 := (fun mask => (mask,id))

def c35942 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35942 : Upper (D 7) (R 7) [34,260,66,96,129] 13 := by
  apply FastRouting.sound _ _ [34,260,66,96,129] 13 (by decide) (choices 1) [1,8,16,128] r35942 c35942
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21357
  · exact u21358
  · exact u21359
  · exact u21360

def r35943 : Route 9 := (fun mask => (mask,id))

def c35943 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35943 : Upper (D 7) (R 7) [34,260,66,96,136] 13 := by
  apply FastRouting.sound _ _ [34,260,66,96,136] 13 (by decide) (choices 1) [1,16,128] r35943 c35943
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21361
  · exact u21362
  · exact u21363

def b35944 : PairBound 9 := { available := 120, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 3, region := 16, targets := 96 }], pairs := [(3,1),(4,1),(4,5),(4,6)], upper := (rows 35 262 70 137 145 120 120 248 376), lower := (rows 35 262 70 137 145 32 64 128 256), losses := [] }

theorem u35944 : Upper (D 7) (R 7) [34,260,66,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35944 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35945 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 16, targets := 97 },{ cop := 4, region := 359, targets := 128 }], pairs := [(0,7),(4,0),(4,5),(4,6)], upper := (rows 35 262 70 137 152 113 113 241 369), lower := (rows 35 262 70 137 152 32 64 128 256), losses := [] }

theorem u35945 : Upper (D 7) (R 7) [34,260,66,129,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35945 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35946 : Route 9 := (fun mask => (mask,id))

def c35946 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35946 : Upper (D 7) (R 7) [34,260,66,129,160] 13 := by
  apply FastRouting.sound _ _ [34,260,66,129,160] 13 (by decide) (choices 1) [1,8,16,64] r35946 c35946
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21364
  · exact u21365
  · exact u21366
  · exact u21367

def r35947 : Route 9 := (fun mask => (mask,id))

def c35947 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35947 : Upper (D 7) (R 7) [34,260,66,129,192] 13 := by
  apply FastRouting.sound _ _ [34,260,66,129,192] 13 (by decide) (choices 1) [1,8,16] r35947 c35947
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21368
  · exact u21369
  · exact u21370

def b35948 : PairBound 9 := { available := 97, camps := [{ cop := 7, region := 24, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 262 70 152 152 97 97 225 353), lower := (rows 35 262 70 152 152 32 64 128 256), losses := [] }

theorem u35948 : Upper (D 7) (R 7) [34,260,66,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35948 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35949 : PairBound 9 := { available := 73, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 262 70 152 176 105 73 201 329), lower := (rows 35 262 70 152 176 32 64 128 256), losses := [] }

theorem u35949 : Upper (D 7) (R 7) [34,260,66,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35949 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35950 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 262 70 152 208 41 105 169 297), lower := (rows 35 262 70 152 208 32 64 128 256), losses := [] }

theorem u35950 : Upper (D 7) (R 7) [34,260,66,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35950 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35951 : Route 9 := (fun mask => (mask,id))

def c35951 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35951 : Upper (D 7) (R 7) [34,260,66,160,192] 13 := by
  apply FastRouting.sound _ _ [34,260,66,160,192] 13 (by decide) (choices 1) [1,8,16] r35951 c35951
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21371
  · exact u21372
  · exact u21373

def b35952 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 24, targets := 224 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 35 262 76 25 19 224 224 224 480), lower := (rows 35 262 76 25 19 32 64 128 256), losses := [] }

theorem u35952 : Upper (D 7) (R 7) [34,260,72,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35952 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35953 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 24, targets := 194 }], pairs := [(3,1),(3,6),(3,7),(4,1)], upper := (rows 35 262 76 25 49 226 194 194 450), lower := (rows 35 262 76 25 49 32 64 128 256), losses := [] }

theorem u35953 : Upper (D 7) (R 7) [34,260,72,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35953 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35954 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 35 262 76 25 50 225 193 193 449), lower := (rows 35 262 76 25 50 32 64 128 256), losses := [] }

theorem u35954 : Upper (D 7) (R 7) [34,260,72,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35954 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35955 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 12, targets := 162 }], pairs := [(2,1),(2,5),(2,7),(3,1)], upper := (rows 35 262 76 25 81 162 226 162 418), lower := (rows 35 262 76 25 81 32 64 128 256), losses := [] }

theorem u35955 : Upper (D 7) (R 7) [34,260,72,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35955 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35956 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 3, region := 228, targets := 2 },{ cop := 4, region := 169, targets := 64 }], pairs := [(0,6),(1,6),(2,1),(3,6)], upper := (rows 35 262 76 25 82 161 225 161 417), lower := (rows 35 262 76 25 82 32 64 128 256), losses := [] }

theorem u35956 : Upper (D 7) (R 7) [34,260,72,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35956 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35957 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 3, region := 454, targets := 32 }], pairs := [(0,6),(1,5),(1,6),(2,5)], upper := (rows 35 262 76 25 112 163 195 131 387), lower := (rows 35 262 76 25 112 32 64 128 256), losses := [] }

theorem u35957 : Upper (D 7) (R 7) [34,260,72,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35957 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35958 : PairBound 9 := { available := 226, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 35 262 76 25 145 226 226 226 482), lower := (rows 35 262 76 25 145 32 64 128 256), losses := [] }

theorem u35958 : Upper (D 7) (R 7) [34,260,72,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35958 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35959 : Route 9 := (fun mask => (mask,id))

def c35959 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35959 : Upper (D 7) (R 7) [34,260,72,17,130] 13 := by
  apply FastRouting.sound _ _ [34,260,72,17,130] 13 (by decide) (choices 1) [1,64,128] r35959 c35959
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21374
  · exact u21375
  · exact u21376

def r35960 : Route 9 := (fun mask => (mask,id))

def c35960 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35960 : Upper (D 7) (R 7) [34,260,72,17,160] 13 := by
  apply FastRouting.sound _ _ [34,260,72,17,160] 13 (by decide) (choices 1) [1,2,64,128] r35960 c35960
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21377
  · exact u21378
  · exact u21379
  · exact u21380

def r35961 : Route 9 := (fun mask => (mask,id))

def c35961 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35961 : Upper (D 7) (R 7) [34,260,72,17,192] 13 := by
  apply FastRouting.sound _ _ [34,260,72,17,192] 13 (by decide) (choices 1) [1,2,128] r35961 c35961
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21381
  · exact u21382
  · exact u21383

def b35962 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 35 262 76 26 49 225 193 193 449), lower := (rows 35 262 76 26 49 32 64 128 256), losses := [] }

theorem u35962 : Upper (D 7) (R 7) [34,260,72,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35962 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35963 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 0, region := 208, targets := 2 }], pairs := [(0,6),(1,6),(2,1),(4,1)], upper := (rows 35 262 76 26 81 161 225 161 417), lower := (rows 35 262 76 26 81 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 17 49 81 145 273), good := (rows 497 260 76 508 497 32 64 128 256) }] }

theorem u35963 : Upper (D 7) (R 7) [34,260,72,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35963 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35964 : Route 9 := (fun mask => (mask,id))

def c35964 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35964 : Upper (D 7) (R 7) [34,260,72,18,96] 13 := by
  apply FastRouting.sound _ _ [34,260,72,18,96] 13 (by decide) (choices 1) [1,128] r35964 c35964
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u21384
  · exact u21385

def r35965 : Route 9 := (fun mask => (mask,id))

def c35965 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35965 : Upper (D 7) (R 7) [34,260,72,18,129] 13 := by
  apply FastRouting.sound _ _ [34,260,72,18,129] 13 (by decide) (choices 1) [1,64,128] r35965 c35965
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21386
  · exact u21387
  · exact u21388

def r35966 : Route 9 := (fun mask => (mask,id))

def c35966 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35966 : Upper (D 7) (R 7) [34,260,72,18,160] 13 := by
  apply FastRouting.sound _ _ [34,260,72,18,160] 13 (by decide) (choices 1) [1,64,128] r35966 c35966
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21389
  · exact u21390
  · exact u21391

def r35967 : Route 9 := (fun mask => (mask,id))

def c35967 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35967 : Upper (D 7) (R 7) [34,260,72,18,192] 13 := by
  apply FastRouting.sound _ _ [34,260,72,18,192] 13 (by decide) (choices 1) [1,128] r35967 c35967
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u21392
  · exact u21393

def b35968 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 35 262 76 56 19 225 193 193 449), lower := (rows 35 262 76 56 19 32 64 128 256), losses := [] }

theorem u35968 : Upper (D 7) (R 7) [34,260,72,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35968 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35969 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 0, region := 208, targets := 32 }], pairs := [(0,6),(1,6),(3,6),(4,5)], upper := (rows 35 262 76 56 81 163 195 131 387), lower := (rows 35 262 76 56 81 32 64 128 256), losses := [{ target := 6, region := (rows 7 6 4 24 16 39 0 135 263), good := (rows 419 423 431 56 441 32 0 128 256) }] }

theorem u35969 : Upper (D 7) (R 7) [34,260,72,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35969 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35970 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 0, region := 208, targets := 32 },{ cop := 4, region := 169, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,5)], upper := (rows 35 262 76 56 82 161 193 129 385), lower := (rows 35 262 76 56 82 32 64 128 256), losses := [] }

theorem u35970 : Upper (D 7) (R 7) [34,260,72,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35970 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35971 : Route 9 := (fun mask => (mask,id))

def c35971 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35971 : Upper (D 7) (R 7) [34,260,72,48,129] 13 := by
  apply FastRouting.sound _ _ [34,260,72,48,129] 13 (by decide) (choices 1) [1,2,64,128] r35971 c35971
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21394
  · exact u21395
  · exact u21396
  · exact u21397

def r35972 : Route 9 := (fun mask => (mask,id))

def c35972 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35972 : Upper (D 7) (R 7) [34,260,72,48,130] 13 := by
  apply FastRouting.sound _ _ [34,260,72,48,130] 13 (by decide) (choices 1) [1,64,128] r35972 c35972
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21398
  · exact u21399
  · exact u21400

def r35973 : Route 9 := (fun mask => (mask,id))

def c35973 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35973 : Upper (D 7) (R 7) [34,260,72,48,192] 13 := by
  apply FastRouting.sound _ _ [34,260,72,48,192] 13 (by decide) (choices 1) [1,2,128] r35973 c35973
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21401
  · exact u21402
  · exact u21403

def b35974 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 16, targets := 224 },{ cop := 4, region := 236, targets := 2 }], pairs := [(2,1),(4,5),(4,6),(4,7)], upper := (rows 35 262 76 137 19 240 240 240 496), lower := (rows 35 262 76 137 19 32 64 128 256), losses := [] }

theorem u35974 : Upper (D 7) (R 7) [34,260,72,129,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35974 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35975 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 35 262 76 137 49 242 210 210 466), lower := (rows 35 262 76 137 49 32 64 128 256), losses := [] }

theorem u35975 : Upper (D 7) (R 7) [34,260,72,129,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35975 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35976 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 16, targets := 192 },{ cop := 4, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(4,6),(4,7)], upper := (rows 35 262 76 137 50 241 209 209 465), lower := (rows 35 262 76 137 50 32 64 128 256), losses := [] }

theorem u35976 : Upper (D 7) (R 7) [34,260,72,129,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35976 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35977 : Route 9 := (fun mask => (mask,id))

def c35977 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35977 : Upper (D 7) (R 7) [34,260,72,129,65] 13 := by
  apply FastRouting.sound _ _ [34,260,72,129,65] 13 (by decide) (choices 1) [2,16,128] r35977 c35977
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21404
  · exact u21405
  · exact u21406

def r35978 : Route 9 := (fun mask => (mask,id))

def c35978 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35978 : Upper (D 7) (R 7) [34,260,72,129,66] 13 := by
  apply FastRouting.sound _ _ [34,260,72,129,66] 13 (by decide) (choices 1) [1,16,128] r35978 c35978
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21407
  · exact u21408
  · exact u21409

def r35979 : Route 9 := (fun mask => (mask,id))

def c35979 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35979 : Upper (D 7) (R 7) [34,260,72,129,96] 13 := by
  apply FastRouting.sound _ _ [34,260,72,129,96] 13 (by decide) (choices 1) [1,2,16,128] r35979 c35979
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21410
  · exact u21411
  · exact u21412
  · exact u21413

def b35980 : PairBound 9 := { available := 114, camps := [{ cop := 3, region := 16, targets := 98 },{ cop := 4, region := 8, targets := 2 }], pairs := [(3,1),(4,1),(4,5),(4,6)], upper := (rows 35 262 76 137 145 114 114 242 370), lower := (rows 35 262 76 137 145 32 64 128 256), losses := [] }

theorem u35980 : Upper (D 7) (R 7) [34,260,72,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35980 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35981 : Route 9 := (fun mask => (mask,id))

def c35981 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35981 : Upper (D 7) (R 7) [34,260,72,129,130] 13 := by
  apply FastRouting.sound _ _ [34,260,72,129,130] 13 (by decide) (choices 1) [1,16,64] r35981 c35981
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21414
  · exact u21415
  · exact u21416

def r35982 : Route 9 := (fun mask => (mask,id))

def c35982 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35982 : Upper (D 7) (R 7) [34,260,72,129,160] 13 := by
  apply FastRouting.sound _ _ [34,260,72,129,160] 13 (by decide) (choices 1) [1,2,16,64] r35982 c35982
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21417
  · exact u21418
  · exact u21419
  · exact u21420

def r35983 : Route 9 := (fun mask => (mask,id))

def c35983 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35983 : Upper (D 7) (R 7) [34,260,72,129,192] 13 := by
  apply FastRouting.sound _ _ [34,260,72,129,192] 13 (by decide) (choices 1) [1,2,16] r35983 c35983
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21421
  · exact u21422
  · exact u21423

def b35984 : PairBound 9 := { available := 209, camps := [{ cop := 4, region := 462, targets := 32 },{ cop := 0, region := 16, targets := 64 }], pairs := [(1,5),(2,5),(3,5),(4,6)], upper := (rows 35 262 76 138 49 241 209 209 465), lower := (rows 35 262 76 138 49 32 64 128 256), losses := [] }

theorem u35984 : Upper (D 7) (R 7) [34,260,72,130,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35984 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35985 : Route 9 := (fun mask => (mask,id))

def c35985 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35985 : Upper (D 7) (R 7) [34,260,72,130,65] 13 := by
  apply FastRouting.sound _ _ [34,260,72,130,65] 13 (by decide) (choices 1) [1,16,128] r35985 c35985
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21424
  · exact u21425
  · exact u21426

def r35986 : Route 9 := (fun mask => (mask,id))

def c35986 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35986 : Upper (D 7) (R 7) [34,260,72,130,96] 13 := by
  apply FastRouting.sound _ _ [34,260,72,130,96] 13 (by decide) (choices 1) [1,16,128] r35986 c35986
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21427
  · exact u21428
  · exact u21429

def r35987 : Route 9 := (fun mask => (mask,id))

def c35987 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35987 : Upper (D 7) (R 7) [34,260,72,130,129] 13 := by
  apply FastRouting.sound _ _ [34,260,72,130,129] 13 (by decide) (choices 1) [1,16,64] r35987 c35987
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21430
  · exact u21431
  · exact u21432

def r35988 : Route 9 := (fun mask => (mask,id))

def c35988 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35988 : Upper (D 7) (R 7) [34,260,72,130,160] 13 := by
  apply FastRouting.sound _ _ [34,260,72,130,160] 13 (by decide) (choices 1) [1,16,64] r35988 c35988
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21433
  · exact u21434
  · exact u21435

def r35989 : Route 9 := (fun mask => (mask,id))

def c35989 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35989 : Upper (D 7) (R 7) [34,260,72,130,192] 13 := by
  apply FastRouting.sound _ _ [34,260,72,130,192] 13 (by decide) (choices 1) [1,16] r35989 c35989
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u21436
  · exact u21437

def b35990 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 16, targets := 224 },{ cop := 4, region := 236, targets := 2 }], pairs := [(2,1),(4,5),(4,6),(4,7)], upper := (rows 35 262 76 152 19 225 225 225 481), lower := (rows 35 262 76 152 19 32 64 128 256), losses := [] }

theorem u35990 : Upper (D 7) (R 7) [34,260,72,144,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35990 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35991 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 35 262 76 152 49 227 195 195 451), lower := (rows 35 262 76 152 49 32 64 128 256), losses := [] }

theorem u35991 : Upper (D 7) (R 7) [34,260,72,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35991 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35992 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 16, targets := 192 },{ cop := 4, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(4,6),(4,7)], upper := (rows 35 262 76 152 50 225 193 193 449), lower := (rows 35 262 76 152 50 32 64 128 256), losses := [] }

theorem u35992 : Upper (D 7) (R 7) [34,260,72,144,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35992 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35993 : Route 9 := (fun mask => (mask,id))

def c35993 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35993 : Upper (D 7) (R 7) [34,260,72,144,65] 13 := by
  apply FastRouting.sound _ _ [34,260,72,144,65] 13 (by decide) (choices 1) [1,2,128] r35993 c35993
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21438
  · exact u21439
  · exact u21440

def r35994 : Route 9 := (fun mask => (mask,id))

def c35994 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35994 : Upper (D 7) (R 7) [34,260,72,144,66] 13 := by
  apply FastRouting.sound _ _ [34,260,72,144,66] 13 (by decide) (choices 1) [1,128] r35994 c35994
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u21441
  · exact u21442

def r35995 : Route 9 := (fun mask => (mask,id))

def c35995 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35995 : Upper (D 7) (R 7) [34,260,72,144,96] 13 := by
  apply FastRouting.sound _ _ [34,260,72,144,96] 13 (by decide) (choices 1) [1,2,128] r35995 c35995
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21443
  · exact u21444
  · exact u21445

def b35996 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 262 76 152 145 99 99 227 355), lower := (rows 35 262 76 152 145 32 64 128 256), losses := [] }

theorem u35996 : Upper (D 7) (R 7) [34,260,72,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35996 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35997 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 262 76 152 146 97 97 225 353), lower := (rows 35 262 76 152 146 32 64 128 256), losses := [] }

theorem u35997 : Upper (D 7) (R 7) [34,260,72,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35997 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35998 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 262 76 152 176 99 67 195 323), lower := (rows 35 262 76 152 176 32 64 128 256), losses := [] }

theorem u35998 : Upper (D 7) (R 7) [34,260,72,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35998 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35999 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 12, targets := 35 }], pairs := [(2,0),(2,1),(2,5),(3,0)], upper := (rows 35 262 76 152 208 35 99 163 291), lower := (rows 35 262 76 152 208 32 64 128 256), losses := [] }

theorem u35999 : Upper (D 7) (R 7) [34,260,72,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35999 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u35999
end Delivery.IrregularNine14.P07

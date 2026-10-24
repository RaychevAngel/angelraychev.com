import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0556
import IrregularNine14P06C0557
import IrregularNine14P06C0558
import IrregularNine14P06C0559
import IrregularNine14P06C0560

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b41940 : PairBound 9 := { available := 116, camps := [{ cop := 1, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 134 261 11 116 116 116 244 372), lower := (rows 11 134 261 11 16 32 64 128 256), losses := [] }

theorem u41940 : Upper (D 6) (R 6) [10,132,257,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41940 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41941 : PairBound 9 := { available := 114, camps := [{ cop := 1, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 134 261 13 114 114 114 242 370), lower := (rows 11 134 261 13 16 32 64 128 256), losses := [] }

theorem u41941 : Upper (D 6) (R 6) [10,132,257,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41941 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41942 : PairBound 9 := { available := 113, camps := [{ cop := 1, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 134 261 14 113 113 113 241 369), lower := (rows 11 134 261 14 16 32 64 128 256), losses := [] }

theorem u41942 : Upper (D 6) (R 6) [10,132,257,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41942 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41943 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41943 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41943 : Upper (D 6) (R 6) [10,132,257,17] 13 := by
  apply FastRouting.sound _ _ [10,132,257,17] 13 (by decide) (choices 2) [6,34,36,96] r41943 c41943
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u33371
  · exact u33372
  · exact u33373
  · exact u33374

def b41944 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 134 261 26 117 101 101 229 357), lower := (rows 11 134 261 26 16 32 64 128 256), losses := [] }

theorem u41944 : Upper (D 6) (R 6) [10,132,257,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41944 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41945 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41945 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 2 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41945 : Upper (D 6) (R 6) [10,132,257,20] 13 := by
  apply FastRouting.sound _ _ [10,132,257,20] 13 (by decide) (choices 2) [3,33,34,96] r41945 c41945
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u33375
  · exact u33376
  · exact u33377
  · exact u33378

def r41946 : Route 9 := (fun mask => (mask,id))

def c41946 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41946 : Upper (D 6) (R 6) [10,132,257,33] 13 := by
  apply FastRouting.sound _ _ [10,132,257,33] 13 (by decide) (choices 2) [6,34,36,66,68,96] r41946 c41946
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33379
  · exact u33380
  · exact u33381
  · exact u33382
  · exact u33383
  · exact u33384

def b41947 : PairBound 9 := { available := 117, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 134 261 42 117 117 117 245 373), lower := (rows 11 134 261 42 16 32 64 128 256), losses := [] }

theorem u41947 : Upper (D 6) (R 6) [10,132,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41947 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41948 : Route 9 := (fun mask => (mask,id))

def c41948 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 2 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41948 : Upper (D 6) (R 6) [10,132,257,36] 13 := by
  apply FastRouting.sound _ _ [10,132,257,36] 13 (by decide) (choices 2) [3,33,34,65,66,96] r41948 c41948
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33385
  · exact u33386
  · exact u33387
  · exact u33388
  · exact u33389
  · exact u33390

def r41949 : Route 9 := (fun mask => (mask,id))

def c41949 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41949 : Upper (D 6) (R 6) [10,132,257,48] 13 := by
  apply FastRouting.sound _ _ [10,132,257,48] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r41949 c41949
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33391
  · exact u33392
  · exact u33393
  · exact u33394
  · exact u33395
  · exact u33396
  · exact u33397
  · exact u33398
  · exact u33399
  · exact u33400

def r41950 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41950 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41950 : Upper (D 6) (R 6) [10,132,257,96] 13 := by
  apply FastRouting.sound _ _ [10,132,257,96] 13 (by decide) (choices 2) [3,5,6,33,34,36,96] r41950 c41950
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33401
  · exact u33402
  · exact u33403
  · exact u33404
  · exact u33405
  · exact u33406
  · exact u33407

def b41951 : PairBound 9 := { available := 113, camps := [{ cop := 1, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 134 262 13 113 113 113 241 369), lower := (rows 11 134 262 13 16 32 64 128 256), losses := [] }

theorem u41951 : Upper (D 6) (R 6) [10,132,258,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41951 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41952 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41952 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41952 : Upper (D 6) (R 6) [10,132,258,17] 13 := by
  apply FastRouting.sound _ _ [10,132,258,17] 13 (by decide) (choices 2) [5,33,36,96] r41952 c41952
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u33408
  · exact u33409
  · exact u33410
  · exact u33411

def r41953 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41953 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41953 : Upper (D 6) (R 6) [10,132,258,20] 13 := by
  apply FastRouting.sound _ _ [10,132,258,20] 13 (by decide) (choices 2) [33,96] r41953 c41953
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u33412
  · exact u33413

def r41954 : Route 9 := (fun mask => (mask,id))

def c41954 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41954 : Upper (D 6) (R 6) [10,132,258,33] 13 := by
  apply FastRouting.sound _ _ [10,132,258,33] 13 (by decide) (choices 2) [5,33,36,65,68,96] r41954 c41954
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33414
  · exact u33415
  · exact u33416
  · exact u33417
  · exact u33418
  · exact u33419

def r41955 : Route 9 := (fun mask => (mask,id))

def c41955 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41955 : Upper (D 6) (R 6) [10,132,258,36] 13 := by
  apply FastRouting.sound _ _ [10,132,258,36] 13 (by decide) (choices 2) [33,65,96] r41955 c41955
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u33420
  · exact u33421
  · exact u33422

def r41956 : Route 9 := (fun mask => (mask,id))

def c41956 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41956 : Upper (D 6) (R 6) [10,132,258,48] 13 := by
  apply FastRouting.sound _ _ [10,132,258,48] 13 (by decide) (choices 2) [5,33,36,65,68,96] r41956 c41956
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33423
  · exact u33424
  · exact u33425
  · exact u33426
  · exact u33427
  · exact u33428

def r41957 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41957 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41957 : Upper (D 6) (R 6) [10,132,258,96] 13 := by
  apply FastRouting.sound _ _ [10,132,258,96] 13 (by decide) (choices 2) [5,33,36,96] r41957 c41957
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u33429
  · exact u33430
  · exact u33431
  · exact u33432

def b41958 : PairBound 9 := { available := 101, camps := [{ cop := 1, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 134 276 11 117 101 101 229 357), lower := (rows 11 134 276 11 16 32 64 128 256), losses := [] }

theorem u41958 : Upper (D 6) (R 6) [10,132,272,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41958 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41959 : PairBound 9 := { available := 99, camps := [{ cop := 1, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 134 276 13 115 99 99 227 355), lower := (rows 11 134 276 13 16 32 64 128 256), losses := [] }

theorem u41959 : Upper (D 6) (R 6) [10,132,272,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41959 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41960 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 134 276 14 113 97 97 225 353), lower := (rows 11 134 276 14 16 32 64 128 256), losses := [] }

theorem u41960 : Upper (D 6) (R 6) [10,132,272,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41960 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41961 : Route 9 := (fun mask => (mask,id))

def c41961 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41961 : Upper (D 6) (R 6) [10,132,272,33] 13 := by
  apply FastRouting.sound _ _ [10,132,272,33] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r41961 c41961
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33433
  · exact u33434
  · exact u33435
  · exact u33436
  · exact u33437
  · exact u33438
  · exact u33439
  · exact u33440
  · exact u33441
  · exact u33442

def b41962 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 134 276 42 117 101 101 229 357), lower := (rows 11 134 276 42 16 32 64 128 256), losses := [] }

theorem u41962 : Upper (D 6) (R 6) [10,132,272,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41962 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41963 : Route 9 := (fun mask => (mask,id))

def c41963 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 2 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41963 : Upper (D 6) (R 6) [10,132,272,36] 13 := by
  apply FastRouting.sound _ _ [10,132,272,36] 13 (by decide) (choices 2) [3,33,34,65,66,96] r41963 c41963
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33443
  · exact u33444
  · exact u33445
  · exact u33446
  · exact u33447
  · exact u33448

def r41964 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41964 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41964 : Upper (D 6) (R 6) [10,132,272,96] 13 := by
  apply FastRouting.sound _ _ [10,132,272,96] 13 (by decide) (choices 2) [3,5,6,33,34,36,96] r41964 c41964
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33449
  · exact u33450
  · exact u33451
  · exact u33452
  · exact u33453
  · exact u33454
  · exact u33455

def b41965 : PairBound 9 := { available := 117, camps := [{ cop := 1, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 134 292 11 117 117 117 245 373), lower := (rows 11 134 292 11 16 32 64 128 256), losses := [] }

theorem u41965 : Upper (D 6) (R 6) [10,132,288,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41965 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41966 : PairBound 9 := { available := 115, camps := [{ cop := 1, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 134 292 13 115 115 115 243 371), lower := (rows 11 134 292 13 16 32 64 128 256), losses := [] }

theorem u41966 : Upper (D 6) (R 6) [10,132,288,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41966 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41967 : PairBound 9 := { available := 113, camps := [{ cop := 1, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 134 292 14 113 113 113 241 369), lower := (rows 11 134 292 14 16 32 64 128 256), losses := [] }

theorem u41967 : Upper (D 6) (R 6) [10,132,288,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41967 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41968 : Route 9 := (fun mask => (mask,id))

def c41968 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41968 : Upper (D 6) (R 6) [10,132,288,17] 13 := by
  apply FastRouting.sound _ _ [10,132,288,17] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r41968 c41968
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33456
  · exact u33457
  · exact u33458
  · exact u33459
  · exact u33460
  · exact u33461
  · exact u33462
  · exact u33463
  · exact u33464
  · exact u33465

def b41969 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 134 292 26 117 101 101 229 357), lower := (rows 11 134 292 26 16 32 64 128 256), losses := [] }

theorem u41969 : Upper (D 6) (R 6) [10,132,288,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41969 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41970 : Route 9 := (fun mask => (mask,id))

def c41970 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 2 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41970 : Upper (D 6) (R 6) [10,132,288,20] 13 := by
  apply FastRouting.sound _ _ [10,132,288,20] 13 (by decide) (choices 2) [3,33,34,65,66,96] r41970 c41970
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33466
  · exact u33467
  · exact u33468
  · exact u33469
  · exact u33470
  · exact u33471

def r41971 : Route 9 := (fun mask => (mask,id))

def c41971 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41971 : Upper (D 6) (R 6) [10,132,288,33] 13 := by
  apply FastRouting.sound _ _ [10,132,288,33] 13 (by decide) (choices 2) [3,5,6,65,66,68] r41971 c41971
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33472
  · exact u33473
  · exact u33474
  · exact u33475
  · exact u33476
  · exact u33477

def b41972 : PairBound 9 := { available := 85, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 134 292 42 85 117 85 213 341), lower := (rows 11 134 292 42 16 32 64 128 256), losses := [] }

theorem u41972 : Upper (D 6) (R 6) [10,132,288,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41972 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41973 : PairBound 9 := { available := 83, camps := [{ cop := 2, region := 8, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 134 292 44 83 115 83 211 339), lower := (rows 11 134 292 44 16 32 64 128 256), losses := [] }

theorem u41973 : Upper (D 6) (R 6) [10,132,288,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41973 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41974 : Route 9 := (fun mask => (mask,id))

def c41974 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41974 : Upper (D 6) (R 6) [10,132,288,48] 13 := by
  apply FastRouting.sound _ _ [10,132,288,48] 13 (by decide) (choices 2) [3,5,6,65,66,68] r41974 c41974
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33478
  · exact u33479
  · exact u33480
  · exact u33481
  · exact u33482
  · exact u33483

def r41975 : Route 9 := (fun mask => (mask,id))

def c41975 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41975 : Upper (D 6) (R 6) [10,132,288,65] 13 := by
  apply FastRouting.sound _ _ [10,132,288,65] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r41975 c41975
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33484
  · exact u33485
  · exact u33486
  · exact u33487
  · exact u33488
  · exact u33489
  · exact u33490
  · exact u33491
  · exact u33492
  · exact u33493

def b41976 : PairBound 9 := { available := 117, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 134 292 74 117 117 117 245 373), lower := (rows 11 134 292 74 16 32 64 128 256), losses := [] }

theorem u41976 : Upper (D 6) (R 6) [10,132,288,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41976 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41977 : Route 9 := (fun mask => (mask,id))

def c41977 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 2 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41977 : Upper (D 6) (R 6) [10,132,288,68] 13 := by
  apply FastRouting.sound _ _ [10,132,288,68] 13 (by decide) (choices 2) [3,33,34,65,66,96] r41977 c41977
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33494
  · exact u33495
  · exact u33496
  · exact u33497
  · exact u33498
  · exact u33499

def r41978 : Route 9 := (fun mask => (mask,id))

def c41978 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41978 : Upper (D 6) (R 6) [10,132,288,80] 13 := by
  apply FastRouting.sound _ _ [10,132,288,80] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r41978 c41978
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33500
  · exact u33501
  · exact u33502
  · exact u33503
  · exact u33504
  · exact u33505
  · exact u33506
  · exact u33507
  · exact u33508
  · exact u33509

def r41979 : Route 9 := (fun mask => (mask,id))

def c41979 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41979 : Upper (D 6) (R 6) [10,132,288,96] 13 := by
  apply FastRouting.sound _ _ [10,132,288,96] 13 (by decide) (choices 2) [3,5,6,65,66,68] r41979 c41979
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33510
  · exact u33511
  · exact u33512
  · exact u33513
  · exact u33514
  · exact u33515

def b41980 : PairBound 9 := { available := 356, camps := [{ cop := 1, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 146 37 11 372 356 356 484 356), lower := (rows 11 146 37 11 16 32 64 128 256), losses := [] }

theorem u41980 : Upper (D 6) (R 6) [10,144,33,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41980 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41981 : PairBound 9 := { available := 358, camps := [{ cop := 2, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 11 146 37 13 374 358 358 486 358), lower := (rows 11 146 37 13 16 32 64 128 256), losses := [] }

theorem u41981 : Upper (D 6) (R 6) [10,144,33,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41981 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41982 : PairBound 9 := { available := 357, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 146 37 14 373 357 357 485 357), lower := (rows 11 146 37 14 16 32 64 128 256), losses := [] }

theorem u41982 : Upper (D 6) (R 6) [10,144,33,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41982 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41983 : PairBound 9 := { available := 326, camps := [{ cop := 2, region := 466, targets := 1 },{ cop := 2, region := 8, targets := 2 }], pairs := [(1,0),(3,1),(4,0)], upper := (rows 11 146 37 41 342 358 326 454 326), lower := (rows 11 146 37 41 16 32 64 128 256), losses := [] }

theorem u41983 : Upper (D 6) (R 6) [10,144,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41983 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41984 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 372, targets := 2 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(2,1),(4,1)], upper := (rows 11 146 37 42 341 357 325 453 325), lower := (rows 11 146 37 42 16 32 64 128 256), losses := [] }

theorem u41984 : Upper (D 6) (R 6) [10,144,33,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41984 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41985 : PairBound 9 := { available := 327, camps := [{ cop := 2, region := 8, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 146 37 44 343 359 327 455 327), lower := (rows 11 146 37 44 16 32 64 128 256), losses := [] }

theorem u41985 : Upper (D 6) (R 6) [10,144,33,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41985 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41986 : Route 9 := (fun mask => (mask,id))

def c41986 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41986 : Upper (D 6) (R 6) [10,144,33,65] 13 := by
  apply FastRouting.sound _ _ [10,144,33,65] 13 (by decide) (choices 2) [6,34,36,66,68,96,258,260,288,320] r41986 c41986
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33516
  · exact u33517
  · exact u33518
  · exact u33519
  · exact u33520
  · exact u33521
  · exact u33522
  · exact u33523
  · exact u33524
  · exact u33525

def b41987 : PairBound 9 := { available := 357, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 146 37 74 373 357 357 485 357), lower := (rows 11 146 37 74 16 32 64 128 256), losses := [] }

theorem u41987 : Upper (D 6) (R 6) [10,144,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41987 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41988 : Route 9 := (fun mask => (mask,id))

def c41988 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41988 : Upper (D 6) (R 6) [10,144,33,68] 13 := by
  apply FastRouting.sound _ _ [10,144,33,68] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,257,258,260,288,320] r41988 c41988
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33526
  · exact u33527
  · exact u33528
  · exact u33529
  · exact u33530
  · exact u33531
  · exact u33532
  · exact u33533
  · exact u33534
  · exact u33535
  · exact u33536
  · exact u33537
  · exact u33538
  · exact u33539
  · exact u33540

def r41989 : Route 9 := (fun mask => (mask,id))

def c41989 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41989 : Upper (D 6) (R 6) [10,144,33,96] 13 := by
  apply FastRouting.sound _ _ [10,144,33,96] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r41989 c41989
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33541
  · exact u33542
  · exact u33543
  · exact u33544
  · exact u33545
  · exact u33546
  · exact u33547
  · exact u33548
  · exact u33549
  · exact u33550

def r41990 : Route 9 := (fun mask => (mask,id))

def c41990 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41990 : Upper (D 6) (R 6) [10,144,33,257] 13 := by
  apply FastRouting.sound _ _ [10,144,33,257] 13 (by decide) (choices 2) [6,34,36,66,68,96] r41990 c41990
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33551
  · exact u33552
  · exact u33553
  · exact u33554
  · exact u33555
  · exact u33556

def b41991 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 146 37 266 117 101 101 229 357), lower := (rows 11 146 37 266 16 32 64 128 256), losses := [] }

theorem u41991 : Upper (D 6) (R 6) [10,144,33,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41991 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41992 : Route 9 := (fun mask => (mask,id))

def c41992 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41992 : Upper (D 6) (R 6) [10,144,33,260] 13 := by
  apply FastRouting.sound _ _ [10,144,33,260] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r41992 c41992
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33557
  · exact u33558
  · exact u33559
  · exact u33560
  · exact u33561
  · exact u33562
  · exact u33563
  · exact u33564
  · exact u33565
  · exact u33566

def r41993 : Route 9 := (fun mask => (mask,id))

def c41993 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41993 : Upper (D 6) (R 6) [10,144,33,288] 13 := by
  apply FastRouting.sound _ _ [10,144,33,288] 13 (by decide) (choices 2) [3,5,6,65,66,68] r41993 c41993
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33567
  · exact u33568
  · exact u33569
  · exact u33570
  · exact u33571
  · exact u33572

def r41994 : Route 9 := (fun mask => (mask,id))

def c41994 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41994 : Upper (D 6) (R 6) [10,144,33,320] 13 := by
  apply FastRouting.sound _ _ [10,144,33,320] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r41994 c41994
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33573
  · exact u33574
  · exact u33575
  · exact u33576
  · exact u33577
  · exact u33578
  · exact u33579
  · exact u33580
  · exact u33581
  · exact u33582

def b41995 : PairBound 9 := { available := 357, camps := [{ cop := 2, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 146 38 13 373 357 357 485 357), lower := (rows 11 146 38 13 16 32 64 128 256), losses := [] }

theorem u41995 : Upper (D 6) (R 6) [10,144,34,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41995 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41996 : PairBound 9 := { available := 325, camps := [{ cop := 2, region := 9, targets := 4 },{ cop := 2, region := 9, targets := 64 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 146 38 41 341 357 325 453 325), lower := (rows 11 146 38 41 16 32 64 128 256), losses := [] }

theorem u41996 : Upper (D 6) (R 6) [10,144,34,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41996 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41997 : PairBound 9 := { available := 325, camps := [{ cop := 3, region := 467, targets := 32 }], pairs := [(0,5),(1,5),(4,5)], upper := (rows 11 146 38 44 341 357 325 453 325), lower := (rows 11 146 38 44 16 32 64 128 256), losses := [] }

theorem u41997 : Upper (D 6) (R 6) [10,144,34,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41997 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41998 : Route 9 := (fun mask => (mask,id))

def c41998 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41998 : Upper (D 6) (R 6) [10,144,34,65] 13 := by
  apply FastRouting.sound _ _ [10,144,34,65] 13 (by decide) (choices 2) [5,33,36,65,68,96,257,260,288,320] r41998 c41998
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33583
  · exact u33584
  · exact u33585
  · exact u33586
  · exact u33587
  · exact u33588
  · exact u33589
  · exact u33590
  · exact u33591
  · exact u33592

def r41999 : Route 9 := (fun mask => (mask,id))

def c41999 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41999 : Upper (D 6) (R 6) [10,144,34,68] 13 := by
  apply FastRouting.sound _ _ [10,144,34,68] 13 (by decide) (choices 2) [5,33,36,65,68,96,257,260,288,320] r41999 c41999
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33593
  · exact u33594
  · exact u33595
  · exact u33596
  · exact u33597
  · exact u33598
  · exact u33599
  · exact u33600
  · exact u33601
  · exact u33602

#print axioms u41999
end Delivery.IrregularNine14.P06

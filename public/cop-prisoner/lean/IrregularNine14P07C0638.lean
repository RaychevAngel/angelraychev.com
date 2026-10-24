import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0424
import IrregularNine14P07C0425
import IrregularNine14P07C0426

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b38280 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 24, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 194 262 26 208 41 105 169 297), lower := (rows 37 194 262 26 208 32 64 128 256), losses := [] }

theorem u38280 : Upper (D 7) (R 7) [36,192,258,18,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38280 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38281 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 210, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 194 262 41 81 186 218 154 410), lower := (rows 37 194 262 41 81 32 64 128 256), losses := [] }

theorem u38281 : Upper (D 7) (R 7) [36,192,258,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38281 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38282 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 210, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 194 262 41 88 179 211 147 403), lower := (rows 37 194 262 41 88 32 64 128 256), losses := [] }

theorem u38282 : Upper (D 7) (R 7) [36,192,258,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38282 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38283 : Route 9 := (fun mask => (mask,id))

def c38283 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38283 : Upper (D 7) (R 7) [36,192,258,34,65] 13 := by
  apply FastRouting.sound _ _ [36,192,258,34,65] 13 (by decide) (choices 1) [1,8,16,128] r38283 c38283
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25481
  · exact u25482
  · exact u25483
  · exact u25484

def r38284 : Route 9 := (fun mask => (mask,id))

def c38284 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38284 : Upper (D 7) (R 7) [36,192,258,34,72] 13 := by
  apply FastRouting.sound _ _ [36,192,258,34,72] 13 (by decide) (choices 1) [1,16,128] r38284 c38284
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25485
  · exact u25486
  · exact u25487

def b38285 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 16, targets := 33 },{ cop := 4, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 37 194 262 42 208 57 89 153 281), lower := (rows 37 194 262 42 208 32 64 128 256), losses := [] }

theorem u38285 : Upper (D 7) (R 7) [36,192,258,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38285 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38286 : Route 9 := (fun mask => (mask,id))

def c38286 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38286 : Upper (D 7) (R 7) [36,192,258,48,65] 13 := by
  apply FastRouting.sound _ _ [36,192,258,48,65] 13 (by decide) (choices 1) [1,2,8,128] r38286 c38286
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25488
  · exact u25489
  · exact u25490
  · exact u25491

def b38287 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 194 262 56 82 169 201 137 393), lower := (rows 37 194 262 56 82 32 64 128 256), losses := [] }

theorem u38287 : Upper (D 7) (R 7) [36,192,258,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38287 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38288 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 1, region := 293, targets := 64 }], pairs := [(0,6),(1,5),(2,5),(2,6)], upper := (rows 37 194 262 56 88 163 195 131 387), lower := (rows 37 194 262 56 88 32 64 128 256), losses := [] }

theorem u38288 : Upper (D 7) (R 7) [36,192,258,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38288 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38289 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 16, targets := 33 },{ cop := 4, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 37 194 262 56 208 43 75 139 267), lower := (rows 37 194 262 56 208 32 64 128 256), losses := [] }

theorem u38289 : Upper (D 7) (R 7) [36,192,258,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38289 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m38290_16 : Upper (D 7) (R 7) [36,192,258,65,129,16] 13 :=
  permutation_upper _ _ _ [36,192,258,65,129,8] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u25493

def r38290 : Route 9 := (fun mask => (mask,id))

def c38290 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38290 : Upper (D 7) (R 7) [36,192,258,65,129] 13 := by
  apply FastRouting.sound _ _ [36,192,258,65,129] 13 (by decide) (choices 1) [2,8,16] r38290 c38290
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25492
  · exact u25493
  · exact m38290_16

def b38291 : PairBound 9 := { available := 57, camps := [{ cop := 1, region := 16, targets := 97 },{ cop := 4, region := 365, targets := 128 }], pairs := [(0,7),(4,0),(4,5),(4,6)], upper := (rows 37 194 262 73 146 57 121 185 313), lower := (rows 37 194 262 73 146 32 64 128 256), losses := [] }

theorem u38291 : Upper (D 7) (R 7) [36,192,258,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38291 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38292 : Route 9 := (fun mask => (mask,id))

def c38292 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38292 : Upper (D 7) (R 7) [36,192,258,65,136] 13 := by
  apply FastRouting.sound _ _ [36,192,258,65,136] 13 (by decide) (choices 1) [1,2,16] r38292 c38292
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25494
  · exact u25495
  · exact u25496

def r38293 : Route 9 := (fun mask => (mask,id))

def c38293 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38293 : Upper (D 7) (R 7) [36,192,258,65,160] 13 := by
  apply FastRouting.sound _ _ [36,192,258,65,160] 13 (by decide) (choices 1) [1,2,8,16] r38293 c38293
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25497
  · exact u25498
  · exact u25499
  · exact u25500

def b38294 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 24, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 194 262 74 152 49 113 177 305), lower := (rows 37 194 262 74 152 32 64 128 256), losses := [] }

theorem u38294 : Upper (D 7) (R 7) [36,192,258,66,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38294 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38295 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 37 194 262 74 176 57 89 153 281), lower := (rows 37 194 262 74 176 32 64 128 256), losses := [] }

theorem u38295 : Upper (D 7) (R 7) [36,192,258,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38295 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38296 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 24, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 194 262 88 152 35 99 163 291), lower := (rows 37 194 262 88 152 32 64 128 256), losses := [] }

theorem u38296 : Upper (D 7) (R 7) [36,192,258,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38296 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38297 : Route 9 := (fun mask => (mask,id))

def c38297 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38297 : Upper (D 7) (R 7) [36,192,258,80,160] 13 := by
  apply FastRouting.sound _ _ [36,192,258,80,160] 13 (by decide) (choices 1) [1,2,8] r38297 c38297
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25501
  · exact u25502
  · exact u25503

def b38298 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 16, targets := 224 },{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5),(4,5),(4,6),(4,7)], upper := (rows 37 194 268 11 19 240 240 240 496), lower := (rows 37 194 268 11 19 32 64 128 256), losses := [] }

theorem u38298 : Upper (D 7) (R 7) [36,192,264,3,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38298 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38299 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 194, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 194 268 11 49 242 210 210 466), lower := (rows 37 194 268 11 49 32 64 128 256), losses := [] }

theorem u38299 : Upper (D 7) (R 7) [36,192,264,3,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38299 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38300 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c38300 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u38300 : Upper (D 7) (R 7) [36,192,264,3,34] 13 := by
  apply FastRouting.sound _ _ [36,192,264,3,34] 13 (by decide) (choices 1) [1,16,64] r38300 c38300
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25504
  · exact u25505
  · exact u25506

def r38301 : Route 9 := (fun mask => (mask,id))

def c38301 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38301 : Upper (D 7) (R 7) [36,192,264,3,65] 13 := by
  apply FastRouting.sound _ _ [36,192,264,3,65] 13 (by decide) (choices 1) [2,16,128] r38301 c38301
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25507
  · exact u25508
  · exact u25509

def b38302 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 194 268 11 82 177 241 177 433), lower := (rows 37 194 268 11 82 32 64 128 256), losses := [] }

theorem u38302 : Upper (D 7) (R 7) [36,192,264,3,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38302 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38303 : Route 9 := (fun mask => (mask,id))

def c38303 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38303 : Upper (D 7) (R 7) [36,192,264,3,96] 13 := by
  apply FastRouting.sound _ _ [36,192,264,3,96] 13 (by decide) (choices 1) [1,2,16,128] r38303 c38303
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25510
  · exact u25511
  · exact u25512
  · exact u25513

def b38304 : PairBound 9 := { available := 51, camps := [{ cop := 1, region := 16, targets := 33 },{ cop := 4, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 37 194 268 11 208 51 115 179 307), lower := (rows 37 194 268 11 208 32 64 128 256), losses := [] }

theorem u38304 : Upper (D 7) (R 7) [36,192,264,3,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38304 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38305 : PairBound 9 := { available := 226, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 37 194 268 25 19 226 226 226 482), lower := (rows 37 194 268 25 19 32 64 128 256), losses := [] }

theorem u38305 : Upper (D 7) (R 7) [36,192,264,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38305 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38306 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 24, targets := 194 }], pairs := [(3,1),(3,6),(3,7),(4,1)], upper := (rows 37 194 268 25 49 226 194 194 450), lower := (rows 37 194 268 25 49 32 64 128 256), losses := [] }

theorem u38306 : Upper (D 7) (R 7) [36,192,264,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38306 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38307 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c38307 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38307 : Upper (D 7) (R 7) [36,192,264,17,34] 13 := by
  apply FastRouting.sound _ _ [36,192,264,17,34] 13 (by decide) (choices 1) [1,2,64] r38307 c38307
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25514
  · exact u25515
  · exact u25516

def b38308 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 37 194 268 25 81 162 226 162 418), lower := (rows 37 194 268 25 81 32 64 128 256), losses := [] }

theorem u38308 : Upper (D 7) (R 7) [36,192,264,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38308 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38309 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 194 268 25 82 163 227 163 419), lower := (rows 37 194 268 25 82 32 64 128 256), losses := [] }

theorem u38309 : Upper (D 7) (R 7) [36,192,264,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38309 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38310 : Route 9 := (fun mask => (mask,id))

def c38310 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38310 : Upper (D 7) (R 7) [36,192,264,17,96] 13 := by
  apply FastRouting.sound _ _ [36,192,264,17,96] 13 (by decide) (choices 1) [1,2,128] r38310 c38310
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25517
  · exact u25518
  · exact u25519

def b38311 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 16, targets := 33 },{ cop := 4, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 37 194 268 25 208 35 99 163 291), lower := (rows 37 194 268 25 208 32 64 128 256), losses := [] }

theorem u38311 : Upper (D 7) (R 7) [36,192,264,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38311 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38312 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 37 194 268 26 19 225 225 225 481), lower := (rows 37 194 268 26 19 32 64 128 256), losses := [] }

theorem u38312 : Upper (D 7) (R 7) [36,192,264,18,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38312 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38313 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 194, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 194 268 26 49 227 195 195 451), lower := (rows 37 194 268 26 49 32 64 128 256), losses := [] }

theorem u38313 : Upper (D 7) (R 7) [36,192,264,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38313 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38314 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 37 194 268 26 50 225 193 193 449), lower := (rows 37 194 268 26 50 32 64 128 256), losses := [] }

theorem u38314 : Upper (D 7) (R 7) [36,192,264,18,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38314 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38315 : Route 9 := (fun mask => (mask,id))

def c38315 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38315 : Upper (D 7) (R 7) [36,192,264,18,65] 13 := by
  apply FastRouting.sound _ _ [36,192,264,18,65] 13 (by decide) (choices 1) [1,2,128] r38315 c38315
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25520
  · exact u25521
  · exact u25522

def b38316 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 24, targets := 161 }], pairs := [(3,0),(3,5),(3,7),(4,0)], upper := (rows 37 194 268 26 82 161 225 161 417), lower := (rows 37 194 268 26 82 32 64 128 256), losses := [] }

theorem u38316 : Upper (D 7) (R 7) [36,192,264,18,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38316 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38317 : Route 9 := (fun mask => (mask,id))

def c38317 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38317 : Upper (D 7) (R 7) [36,192,264,18,96] 13 := by
  apply FastRouting.sound _ _ [36,192,264,18,96] 13 (by decide) (choices 1) [1,2,128] r38317 c38317
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25523
  · exact u25524
  · exact u25525

def b38318 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 24, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 194 268 26 208 35 99 163 291), lower := (rows 37 194 268 26 208 32 64 128 256), losses := [] }

theorem u38318 : Upper (D 7) (R 7) [36,192,264,18,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38318 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38319 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c38319 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u38319 : Upper (D 7) (R 7) [36,192,264,34,3] 13 := by
  apply FastRouting.sound _ _ [36,192,264,34,3] 13 (by decide) (choices 1) [1,16,64] r38319 c38319
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25526
  · exact u25527
  · exact u25528

def r38320 : Route 9 := (fun mask => (mask,id))

def c38320 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38320 : Upper (D 7) (R 7) [36,192,264,34,65] 13 := by
  apply FastRouting.sound _ _ [36,192,264,34,65] 13 (by decide) (choices 1) [1,2,16,128] r38320 c38320
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25529
  · exact u25530
  · exact u25531
  · exact u25532

def b38321 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 194 268 42 82 177 209 145 401), lower := (rows 37 194 268 42 82 32 64 128 256), losses := [] }

theorem u38321 : Upper (D 7) (R 7) [36,192,264,34,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38321 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38322 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 210, targets := 32 },{ cop := 1, region := 16, targets := 1 },{ cop := 1, region := 16, targets := 2 }], pairs := [(1,5),(4,0),(4,1),(4,5)], upper := (rows 37 194 268 42 208 51 83 147 275), lower := (rows 37 194 268 42 208 32 64 128 256), losses := [] }

theorem u38322 : Upper (D 7) (R 7) [36,192,264,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38322 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38323 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c38323 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38323 : Upper (D 7) (R 7) [36,192,264,48,3] 13 := by
  apply FastRouting.sound _ _ [36,192,264,48,3] 13 (by decide) (choices 1) [1,2,64] r38323 c38323
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25533
  · exact u25534
  · exact u25535

def r38324 : Route 9 := (fun mask => (mask,id))

def c38324 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38324 : Upper (D 7) (R 7) [36,192,264,48,65] 13 := by
  apply FastRouting.sound _ _ [36,192,264,48,65] 13 (by decide) (choices 1) [1,2,128] r38324 c38324
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25536
  · exact u25537
  · exact u25538

def b38325 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 194 268 56 82 163 195 131 387), lower := (rows 37 194 268 56 82 32 64 128 256), losses := [] }

theorem u38325 : Upper (D 7) (R 7) [36,192,264,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38325 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38326 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 210, targets := 32 },{ cop := 1, region := 16, targets := 1 },{ cop := 1, region := 16, targets := 2 }], pairs := [(1,5),(4,0),(4,1),(4,5)], upper := (rows 37 194 268 56 208 35 67 131 259), lower := (rows 37 194 268 56 208 32 64 128 256), losses := [] }

theorem u38326 : Upper (D 7) (R 7) [36,192,264,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38326 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38327 : Route 9 := (fun mask => (mask,id))

def c38327 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38327 : Upper (D 7) (R 7) [36,192,264,65,3] 13 := by
  apply FastRouting.sound _ _ [36,192,264,65,3] 13 (by decide) (choices 1) [2,16,128] r38327 c38327
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25539
  · exact u25540
  · exact u25541

def b38328 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 194, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 194 268 73 49 178 210 146 402), lower := (rows 37 194 268 73 49 32 64 128 256), losses := [] }

theorem u38328 : Upper (D 7) (R 7) [36,192,264,65,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38328 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38329 : Route 9 := (fun mask => (mask,id))

def c38329 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38329 : Upper (D 7) (R 7) [36,192,264,65,34] 13 := by
  apply FastRouting.sound _ _ [36,192,264,65,34] 13 (by decide) (choices 1) [1,2,16,128] r38329 c38329
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25542
  · exact u25543
  · exact u25544
  · exact u25545

def r38330 : Route 9 := (fun mask => (mask,id))

def c38330 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38330 : Upper (D 7) (R 7) [36,192,264,65,129] 13 := by
  apply FastRouting.sound _ _ [36,192,264,65,129] 13 (by decide) (choices 1) [2,16] r38330 c38330
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25546
  · exact u25547

def b38331 : PairBound 9 := { available := 51, camps := [{ cop := 1, region := 16, targets := 97 },{ cop := 4, region := 365, targets := 128 }], pairs := [(0,7),(4,0),(4,5),(4,6)], upper := (rows 37 194 268 73 146 51 115 179 307), lower := (rows 37 194 268 73 146 32 64 128 256), losses := [] }

theorem u38331 : Upper (D 7) (R 7) [36,192,264,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38331 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38332 : Route 9 := (fun mask => (mask,id))

def c38332 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38332 : Upper (D 7) (R 7) [36,192,264,65,160] 13 := by
  apply FastRouting.sound _ _ [36,192,264,65,160] 13 (by decide) (choices 1) [1,2,16] r38332 c38332
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25548
  · exact u25549
  · exact u25550

def r38333 : Route 9 := (fun mask => (mask,id))

def c38333 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38333 : Upper (D 7) (R 7) [36,192,264,80,3] 13 := by
  apply FastRouting.sound _ _ [36,192,264,80,3] 13 (by decide) (choices 1) [1,2,128] r38333 c38333
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25551
  · exact u25552
  · exact u25553

def b38334 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 194, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 194 268 88 49 163 195 131 387), lower := (rows 37 194 268 88 49 32 64 128 256), losses := [] }

theorem u38334 : Upper (D 7) (R 7) [36,192,264,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38334 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38335 : Route 9 := (fun mask => (mask,id))

def c38335 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38335 : Upper (D 7) (R 7) [36,192,264,80,34] 13 := by
  apply FastRouting.sound _ _ [36,192,264,80,34] 13 (by decide) (choices 1) [1,2,128] r38335 c38335
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25554
  · exact u25555
  · exact u25556

def r38336 : Route 9 := (fun mask => (mask,id))

def c38336 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38336 : Upper (D 7) (R 7) [36,192,264,80,129] 13 := by
  apply FastRouting.sound _ _ [36,192,264,80,129] 13 (by decide) (choices 1) [1,2] r38336 c38336
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25557
  · exact u25558

def b38337 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 24, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 194 268 88 146 35 99 163 291), lower := (rows 37 194 268 88 146 32 64 128 256), losses := [] }

theorem u38337 : Upper (D 7) (R 7) [36,192,264,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38337 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38338 : Route 9 := (fun mask => (mask,id))

def c38338 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38338 : Upper (D 7) (R 7) [36,192,264,80,160] 13 := by
  apply FastRouting.sound _ _ [36,192,264,80,160] 13 (by decide) (choices 1) [1,2] r38338 c38338
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25559
  · exact u25560

def r38339 : Route 9 := (fun mask => (mask,id))

def c38339 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38339 : Upper (D 7) (R 7) [36,192,264,96,3] 13 := by
  apply FastRouting.sound _ _ [36,192,264,96,3] 13 (by decide) (choices 1) [1,2,16,128] r38339 c38339
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25561
  · exact u25562
  · exact u25563
  · exact u25564

#print axioms u38339
end Delivery.IrregularNine14.P07

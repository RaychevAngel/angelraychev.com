import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0257
import IrregularNine14P07C0258

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b32280 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 244, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 7 290 196 11 88 177 241 177 433), lower := (rows 7 290 196 11 88 32 64 128 256), losses := [] }

theorem u32280 : Upper (D 7) (R 7) [6,288,192,3,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32280 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32281 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 244, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 7 290 196 11 112 185 217 153 409), lower := (rows 7 290 196 11 112 32 64 128 256), losses := [] }

theorem u32281 : Upper (D 7) (R 7) [6,288,192,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32281 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32282 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 24, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 7 290 196 25 25 226 226 226 482), lower := (rows 7 290 196 25 25 32 64 128 256), losses := [] }

theorem u32282 : Upper (D 7) (R 7) [6,288,192,17,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32282 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32283 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 24, targets := 224 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 7 290 196 25 26 225 225 225 481), lower := (rows 7 290 196 25 26 32 64 128 256), losses := [] }

theorem u32283 : Upper (D 7) (R 7) [6,288,192,17,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32283 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32284 : PairBound 9 := { available := 202, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 7 290 196 25 49 234 202 202 458), lower := (rows 7 290 196 25 49 32 64 128 256), losses := [] }

theorem u32284 : Upper (D 7) (R 7) [6,288,192,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32284 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32285 : PairBound 9 := { available := 201, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 205, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 7 290 196 25 50 233 201 201 457), lower := (rows 7 290 196 25 50 32 64 128 256), losses := [] }

theorem u32285 : Upper (D 7) (R 7) [6,288,192,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32285 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32286 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c32286 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32286 : Upper (D 7) (R 7) [6,288,192,17,40] 13 := by
  apply FastRouting.sound _ _ [6,288,192,17,40] 13 (by decide) (choices 1) [1,2,64] r32286 c32286
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15439
  · exact u15440
  · exact u15441

def b32287 : PairBound 9 := { available := 170, camps := [{ cop := 4, region := 8, targets := 162 },{ cop := 3, region := 418, targets := 1 }], pairs := [(1,0),(3,1),(3,5),(3,7)], upper := (rows 7 290 196 25 81 170 234 170 426), lower := (rows 7 290 196 25 81 32 64 128 256), losses := [] }

theorem u32287 : Upper (D 7) (R 7) [6,288,192,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32287 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32288 : Route 9 := (fun mask => (mask,id))

def c32288 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32288 : Upper (D 7) (R 7) [6,288,192,17,66] 13 := by
  apply FastRouting.sound _ _ [6,288,192,17,66] 13 (by decide) (choices 1) [1,8,128] r32288 c32288
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15442
  · exact u15443
  · exact u15444

def r32289 : Route 9 := (fun mask => (mask,id))

def c32289 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32289 : Upper (D 7) (R 7) [6,288,192,17,72] 13 := by
  apply FastRouting.sound _ _ [6,288,192,17,72] 13 (by decide) (choices 1) [1,2,128] r32289 c32289
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15445
  · exact u15446
  · exact u15447

def r32290 : Route 9 := (fun mask => (mask,id))

def c32290 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32290 : Upper (D 7) (R 7) [6,288,192,17,96] 13 := by
  apply FastRouting.sound _ _ [6,288,192,17,96] 13 (by decide) (choices 1) [1,2,8,128] r32290 c32290
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15448
  · exact u15449
  · exact u15450
  · exact u15451

def b32291 : PairBound 9 := { available := 43, camps := [{ cop := 2, region := 16, targets := 35 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,1),(4,5)], upper := (rows 7 290 196 25 208 43 107 171 299), lower := (rows 7 290 196 25 208 32 64 128 256), losses := [] }

theorem u32291 : Upper (D 7) (R 7) [6,288,192,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32291 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32292 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c32292 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32292 : Upper (D 7) (R 7) [6,288,192,18,33] 13 := by
  apply FastRouting.sound _ _ [6,288,192,18,33] 13 (by decide) (choices 1) [1,8,64] r32292 c32292
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15452
  · exact u15453
  · exact u15454

def b32293 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 24, targets := 193 }], pairs := [(3,0),(3,6),(3,7),(4,0)], upper := (rows 7 290 196 26 56 225 193 193 449), lower := (rows 7 290 196 26 56 32 64 128 256), losses := [] }

theorem u32293 : Upper (D 7) (R 7) [6,288,192,18,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32293 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32294 : Route 9 := (fun mask => (mask,id))

def c32294 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32294 : Upper (D 7) (R 7) [6,288,192,18,65] 13 := by
  apply FastRouting.sound _ _ [6,288,192,18,65] 13 (by decide) (choices 1) [1,8,128] r32294 c32294
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15455
  · exact u15456
  · exact u15457

def r32295 : Route 9 := (fun mask => (mask,id))

def c32295 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32295 : Upper (D 7) (R 7) [6,288,192,18,72] 13 := by
  apply FastRouting.sound _ _ [6,288,192,18,72] 13 (by decide) (choices 1) [1,128] r32295 c32295
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u15458
  · exact u15459

def r32296 : Route 9 := (fun mask => (mask,id))

def c32296 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32296 : Upper (D 7) (R 7) [6,288,192,18,96] 13 := by
  apply FastRouting.sound _ _ [6,288,192,18,96] 13 (by decide) (choices 1) [1,8,128] r32296 c32296
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15460
  · exact u15461
  · exact u15462

def b32297 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 16, targets := 35 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,1),(4,5)], upper := (rows 7 290 196 26 208 41 105 169 297), lower := (rows 7 290 196 26 208 32 64 128 256), losses := [] }

theorem u32297 : Upper (D 7) (R 7) [6,288,192,18,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32297 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32298 : Route 9 := (fun mask => (mask,id))

def c32298 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32298 : Upper (D 7) (R 7) [6,288,192,33,65] 13 := by
  apply FastRouting.sound _ _ [6,288,192,33,65] 13 (by decide) (choices 1) [2,8,16,128] r32298 c32298
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15463
  · exact u15464
  · exact u15465
  · exact u15466

def r32299 : Route 9 := (fun mask => (mask,id))

def c32299 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32299 : Upper (D 7) (R 7) [6,288,192,33,66] 13 := by
  apply FastRouting.sound _ _ [6,288,192,33,66] 13 (by decide) (choices 1) [1,8,16,128] r32299 c32299
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15467
  · exact u15468
  · exact u15469
  · exact u15470

def r32300 : Route 9 := (fun mask => (mask,id))

def c32300 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32300 : Upper (D 7) (R 7) [6,288,192,33,72] 13 := by
  apply FastRouting.sound _ _ [6,288,192,33,72] 13 (by decide) (choices 1) [1,2,16,128] r32300 c32300
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15471
  · exact u15472
  · exact u15473
  · exact u15474

def b32301 : PairBound 9 := { available := 27, camps := [{ cop := 2, region := 16, targets := 35 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,1),(4,5)], upper := (rows 7 290 196 41 208 59 91 155 283), lower := (rows 7 290 196 41 208 32 64 128 256), losses := [] }

theorem u32301 : Upper (D 7) (R 7) [6,288,192,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32301 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32302 : PairBound 9 := { available := 153, camps := [{ cop := 1, region := 8, targets := 193 },{ cop := 3, region := 213, targets := 32 }], pairs := [(0,5),(3,0),(3,6),(3,7)], upper := (rows 7 290 196 42 81 185 217 153 409), lower := (rows 7 290 196 42 81 32 64 128 256), losses := [] }

theorem u32302 : Upper (D 7) (R 7) [6,288,192,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32302 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32303 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 8, targets := 193 },{ cop := 3, region := 213, targets := 32 }], pairs := [(0,5),(3,0),(3,6),(3,7)], upper := (rows 7 290 196 42 88 177 209 145 401), lower := (rows 7 290 196 42 88 32 64 128 256), losses := [] }

theorem u32303 : Upper (D 7) (R 7) [6,288,192,34,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32303 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32304 : Route 9 := (fun mask => (mask,id))

def c32304 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32304 : Upper (D 7) (R 7) [6,288,192,48,65] 13 := by
  apply FastRouting.sound _ _ [6,288,192,48,65] 13 (by decide) (choices 1) [1,2,8,128] r32304 c32304
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15475
  · exact u15476
  · exact u15477
  · exact u15478

def r32305 : Route 9 := (fun mask => (mask,id))

def c32305 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32305 : Upper (D 7) (R 7) [6,288,192,48,66] 13 := by
  apply FastRouting.sound _ _ [6,288,192,48,66] 13 (by decide) (choices 1) [1,8,128] r32305 c32305
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15479
  · exact u15480
  · exact u15481

def b32306 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 197, targets := 32 },{ cop := 2, region := 291, targets := 64 }], pairs := [(0,5),(0,6),(1,6),(2,5)], upper := (rows 7 290 196 56 88 163 195 131 387), lower := (rows 7 290 196 56 88 32 64 128 256), losses := [] }

theorem u32306 : Upper (D 7) (R 7) [6,288,192,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32306 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32307 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 16, targets := 35 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,1),(4,5)], upper := (rows 7 290 196 56 208 43 75 139 267), lower := (rows 7 290 196 56 208 32 64 128 256), losses := [] }

theorem u32307 : Upper (D 7) (R 7) [6,288,192,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32307 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32308 : PairBound 9 := { available := 58, camps := [{ cop := 3, region := 434, targets := 64 },{ cop := 4, region := 362, targets := 128 }], pairs := [(1,6),(1,7),(3,7),(4,6)], upper := (rows 7 290 196 73 145 58 122 186 314), lower := (rows 7 290 196 73 145 32 64 128 256), losses := [] }

theorem u32308 : Upper (D 7) (R 7) [6,288,192,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32308 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32309 : Route 9 := (fun mask => (mask,id))

def c32309 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32309 : Upper (D 7) (R 7) [6,288,192,65,130] 13 := by
  apply FastRouting.sound _ _ [6,288,192,65,130] 13 (by decide) (choices 1) [1,8,16] r32309 c32309
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15482
  · exact u15483
  · exact u15484

def r32310 : Route 9 := (fun mask => (mask,id))

def c32310 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32310 : Upper (D 7) (R 7) [6,288,192,65,136] 13 := by
  apply FastRouting.sound _ _ [6,288,192,65,136] 13 (by decide) (choices 1) [1,2,16] r32310 c32310
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15485
  · exact u15486
  · exact u15487

def r32311 : Route 9 := (fun mask => (mask,id))

def c32311 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32311 : Upper (D 7) (R 7) [6,288,192,65,160] 13 := by
  apply FastRouting.sound _ _ [6,288,192,65,160] 13 (by decide) (choices 1) [1,2,8,16] r32311 c32311
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15488
  · exact u15489
  · exact u15490
  · exact u15491

def r32312 : Route 9 := (fun mask => (mask,id))

def c32312 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32312 : Upper (D 7) (R 7) [6,288,192,66,136] 13 := by
  apply FastRouting.sound _ _ [6,288,192,66,136] 13 (by decide) (choices 1) [1,16] r32312 c32312
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u15492
  · exact u15493

def r32313 : Route 9 := (fun mask => (mask,id))

def c32313 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32313 : Upper (D 7) (R 7) [6,288,192,66,160] 13 := by
  apply FastRouting.sound _ _ [6,288,192,66,160] 13 (by decide) (choices 1) [1,8,16] r32313 c32313
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15494
  · exact u15495
  · exact u15496

def b32314 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 24, targets := 35 }], pairs := [(3,0),(3,1),(3,5),(4,0)], upper := (rows 7 290 196 88 152 35 99 163 291), lower := (rows 7 290 196 88 152 32 64 128 256), losses := [] }

theorem u32314 : Upper (D 7) (R 7) [6,288,192,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32314 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32315 : Route 9 := (fun mask => (mask,id))

def c32315 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32315 : Upper (D 7) (R 7) [6,288,192,80,160] 13 := by
  apply FastRouting.sound _ _ [6,288,192,80,160] 13 (by decide) (choices 1) [1,2,8] r32315 c32315
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15497
  · exact u15498
  · exact u15499

def b32316 : PairBound 9 := { available := 448, camps := [{ cop := 1, region := 20, targets := 192 }], pairs := [(2,6),(2,7),(4,6),(4,7)], upper := (rows 13 35 21 74 50 480 448 448 448), lower := (rows 13 35 21 74 50 32 64 128 256), losses := [] }

theorem u32316 : Upper (D 7) (R 7) [12,33,17,66,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32316 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32317 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 21, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 13 35 21 74 82 416 480 416 416), lower := (rows 13 35 21 74 82 32 64 128 256), losses := [] }

theorem u32317 : Upper (D 7) (R 7) [12,33,17,66,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32317 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32318 : PairBound 9 := { available := 386, camps := [{ cop := 4, region := 15, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 35 21 74 112 418 450 386 386), lower := (rows 13 35 21 74 112 32 64 128 256), losses := [] }

theorem u32318 : Upper (D 7) (R 7) [12,33,17,66,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32318 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32319 : Route 9 := (fun mask => (mask,id))

def c32319 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u32319 : Upper (D 7) (R 7) [12,33,17,66,130] 13 := by
  apply FastRouting.sound _ _ [12,33,17,66,130] 13 (by decide) (choices 1) [64,128,256] r32319 c32319
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15500
  · exact u15501
  · exact u15502

def r32320 : Route 9 := (fun mask => (mask,id))

def c32320 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u32320 : Upper (D 7) (R 7) [12,33,17,66,160] 13 := by
  apply FastRouting.sound _ _ [12,33,17,66,160] 13 (by decide) (choices 1) [2,64,128,256] r32320 c32320
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15503
  · exact u15504
  · exact u15505
  · exact u15506

def r32321 : Route 9 := (fun mask => (mask,id))

def c32321 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u32321 : Upper (D 7) (R 7) [12,33,17,66,192] 13 := by
  apply FastRouting.sound _ _ [12,33,17,66,192] 13 (by decide) (choices 1) [2,128,256] r32321 c32321
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15507
  · exact u15508
  · exact u15509

def r32322 : Route 9 := (fun mask => (mask,id))

def c32322 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32322 : Upper (D 7) (R 7) [12,33,17,66,258] 13 := by
  apply FastRouting.sound _ _ [12,33,17,66,258] 13 (by decide) (choices 1) [64,128] r32322 c32322
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u15510
  · exact u15511

def r32323 : Route 9 := (fun mask => (mask,id))

def c32323 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32323 : Upper (D 7) (R 7) [12,33,17,66,288] 13 := by
  apply FastRouting.sound _ _ [12,33,17,66,288] 13 (by decide) (choices 1) [2,64,128] r32323 c32323
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15512
  · exact u15513
  · exact u15514

def r32324 : Route 9 := (fun mask => (mask,id))

def c32324 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32324 : Upper (D 7) (R 7) [12,33,17,66,320] 13 := by
  apply FastRouting.sound _ _ [12,33,17,66,320] 13 (by decide) (choices 1) [2,128] r32324 c32324
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u15515
  · exact u15516

def r32325 : Route 9 := (fun mask => (mask,id))

def c32325 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32325 : Upper (D 7) (R 7) [12,33,17,66,384] 13 := by
  apply FastRouting.sound _ _ [12,33,17,66,384] 13 (by decide) (choices 1) [2,64,128] r32325 c32325
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15517
  · exact u15518
  · exact u15519

def b32326 : PairBound 9 := { available := 450, camps := [{ cop := 1, region := 20, targets := 192 }], pairs := [(2,6),(2,7),(4,6),(4,7)], upper := (rows 13 35 21 200 50 482 450 450 450), lower := (rows 13 35 21 200 50 32 64 128 256), losses := [] }

theorem u32326 : Upper (D 7) (R 7) [12,33,17,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32326 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32327 : Route 9 := (fun mask => (mask,id))

def c32327 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u32327 : Upper (D 7) (R 7) [12,33,17,192,66] 13 := by
  apply FastRouting.sound _ _ [12,33,17,192,66] 13 (by decide) (choices 1) [2,128,256] r32327 c32327
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15520
  · exact u15521
  · exact u15522

def b32328 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 0, region := 418, targets := 64 },{ cop := 1, region := 456, targets := 32 }], pairs := [(1,6),(3,0),(3,5),(4,0)], upper := (rows 13 35 21 200 112 418 450 386 386), lower := (rows 13 35 21 200 112 32 64 128 256), losses := [] }

theorem u32328 : Upper (D 7) (R 7) [12,33,17,192,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32328 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32329 : PairBound 9 := { available := 290, camps := [{ cop := 3, region := 21, targets := 34 }], pairs := [(0,1),(0,5),(2,1),(2,5)], upper := (rows 13 35 21 200 208 290 354 418 290), lower := (rows 13 35 21 200 208 32 64 128 256), losses := [] }

theorem u32329 : Upper (D 7) (R 7) [12,33,17,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32329 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32330 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c32330 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32330 : Upper (D 7) (R 7) [12,33,17,192,258] 13 := by
  apply FastRouting.sound _ _ [12,33,17,192,258] 13 (by decide) (choices 1) [2,64] r32330 c32330
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u15523
  · exact u15524

def r32331 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c32331 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32331 : Upper (D 7) (R 7) [12,33,17,192,288] 13 := by
  apply FastRouting.sound _ _ [12,33,17,192,288] 13 (by decide) (choices 1) [2,64] r32331 c32331
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u15525
  · exact u15526

def r32332 : Route 9 := (fun mask => (mask,id))

def c32332 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32332 : Upper (D 7) (R 7) [12,33,17,192,320] 13 := by
  apply FastRouting.sound _ _ [12,33,17,192,320] 13 (by decide) (choices 1) [2,128] r32332 c32332
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u15527
  · exact u15528

def b32333 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 20, targets := 192 }], pairs := [(2,6),(2,7),(4,6),(4,7)], upper := (rows 13 35 21 266 50 224 192 192 448), lower := (rows 13 35 21 266 50 32 64 128 256), losses := [] }

theorem u32333 : Upper (D 7) (R 7) [12,33,17,258,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32333 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32334 : Route 9 := (fun mask => (mask,id))

def c32334 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32334 : Upper (D 7) (R 7) [12,33,17,258,66] 13 := by
  apply FastRouting.sound _ _ [12,33,17,258,66] 13 (by decide) (choices 1) [64,128] r32334 c32334
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u15529
  · exact u15530

def r32335 : Route 9 := (fun mask => (mask,id))

def c32335 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32335 : Upper (D 7) (R 7) [12,33,17,258,96] 13 := by
  apply FastRouting.sound _ _ [12,33,17,258,96] 13 (by decide) (choices 1) [2,64,128] r32335 c32335
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15531
  · exact u15532
  · exact u15533

def r32336 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c32336 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32336 : Upper (D 7) (R 7) [12,33,17,258,192] 13 := by
  apply FastRouting.sound _ _ [12,33,17,258,192] 13 (by decide) (choices 1) [2,64] r32336 c32336
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u15534
  · exact u15535

def b32337 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 20, targets := 192 }], pairs := [(2,6),(2,7),(4,6),(4,7)], upper := (rows 13 35 21 328 50 226 194 194 450), lower := (rows 13 35 21 328 50 32 64 128 256), losses := [] }

theorem u32337 : Upper (D 7) (R 7) [12,33,17,320,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32337 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32338 : Route 9 := (fun mask => (mask,id))

def c32338 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32338 : Upper (D 7) (R 7) [12,33,17,320,66] 13 := by
  apply FastRouting.sound _ _ [12,33,17,320,66] 13 (by decide) (choices 1) [2,128] r32338 c32338
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u15536
  · exact u15537

def b32339 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 0, region := 162, targets := 64 },{ cop := 1, region := 456, targets := 32 }], pairs := [(1,6),(3,0),(3,5),(4,0)], upper := (rows 13 35 21 328 112 162 194 130 386), lower := (rows 13 35 21 328 112 32 64 128 256), losses := [] }

theorem u32339 : Upper (D 7) (R 7) [12,33,17,320,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32339 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u32339
end Delivery.IrregularNine14.P07

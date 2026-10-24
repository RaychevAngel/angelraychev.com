import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0089
import IrregularNine14P08C0090

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b15480 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 193 7 268 88 49 162 226 162 418), lower := (rows 193 7 268 88 49 32 64 128 256), losses := [] }

theorem u15480 : Upper (D 8) (R 8) [192,5,264,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15480 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15481 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 193 7 268 88 50 161 225 161 417), lower := (rows 193 7 268 88 50 32 64 128 256), losses := [] }

theorem u15481 : Upper (D 8) (R 8) [192,5,264,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15481 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15482 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 193 7 268 88 146 33 97 161 289), lower := (rows 193 7 268 88 146 32 64 128 256), losses := [] }

theorem u15482 : Upper (D 8) (R 8) [192,5,264,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15482 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15483 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 193 7 268 88 176 35 99 163 291), lower := (rows 193 7 268 88 176 32 64 128 256), losses := [] }

theorem u15483 : Upper (D 8) (R 8) [192,5,264,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15483 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15484 : PairBound 9 := { available := 178, camps := [{ cop := 1, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 193 7 268 104 49 178 242 178 434), lower := (rows 193 7 268 104 49 32 64 128 256), losses := [] }

theorem u15484 : Upper (D 8) (R 8) [192,5,264,96,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15484 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15485 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 193 7 268 104 50 177 241 177 433), lower := (rows 193 7 268 104 50 32 64 128 256), losses := [] }

theorem u15485 : Upper (D 8) (R 8) [192,5,264,96,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15485 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15486 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 193 7 268 104 146 49 113 177 305), lower := (rows 193 7 268 104 146 32 64 128 256), losses := [] }

theorem u15486 : Upper (D 8) (R 8) [192,5,264,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15486 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15487 : PairBound 9 := { available := 51, camps := [{ cop := 1, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 193 7 268 104 176 51 115 179 307), lower := (rows 193 7 268 104 176 32 64 128 256), losses := [] }

theorem u15487 : Upper (D 8) (R 8) [192,5,264,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15487 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15488 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 268 200 49 50 114 178 306), lower := (rows 193 7 268 200 49 32 64 128 256), losses := [] }

theorem u15488 : Upper (D 8) (R 8) [192,5,264,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15488 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15489 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 268 200 50 49 113 177 305), lower := (rows 193 7 268 200 50 32 64 128 256), losses := [] }

theorem u15489 : Upper (D 8) (R 8) [192,5,264,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15489 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15490 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 484, targets := 1 }], pairs := [(2,0)], upper := (rows 193 7 292 26 49 232 232 232 488), lower := (rows 193 7 292 26 49 32 64 128 256), losses := [] }

theorem u15490 : Upper (D 8) (R 8) [192,5,288,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15490 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15491 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c15491 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u15491 : Upper (D 8) (R 8) [192,5,288,18,40] 13 := by
  apply FastRouting.sound _ _ [192,5,288,18,40] 13 (by decide) (choices 1) [1,64] r15491 c15491
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5386
  · exact u5387

def b15492 : PairBound 9 := { available := 168, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 292 26 81 168 232 168 424), lower := (rows 193 7 292 26 81 32 64 128 256), losses := [] }

theorem u15492 : Upper (D 8) (R 8) [192,5,288,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15492 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15493 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 294, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 292 26 88 161 225 161 417), lower := (rows 193 7 292 26 88 32 64 128 256), losses := [] }

theorem u15493 : Upper (D 8) (R 8) [192,5,288,18,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15493 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15494 : Route 9 := (fun mask => (mask,id))

def c15494 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u15494 : Upper (D 8) (R 8) [192,5,288,18,96] 13 := by
  apply FastRouting.sound _ _ [192,5,288,18,96] 13 (by decide) (choices 1) [1,8,128] r15494 c15494
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5388
  · exact u5389
  · exact u5390

def b15495 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 193 7 292 26 208 41 105 169 297), lower := (rows 193 7 292 26 208 32 64 128 256), losses := [] }

theorem u15495 : Upper (D 8) (R 8) [192,5,288,18,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15495 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15496 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c15496 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u15496 : Upper (D 8) (R 8) [192,5,288,33,34] 13 := by
  apply FastRouting.sound _ _ [192,5,288,33,34] 13 (by decide) (choices 1) [8,16,64] r15496 c15496
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5391
  · exact u5392
  · exact u5393

def b15497 : PairBound 9 := { available := 210, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 193 7 292 41 56 242 210 210 466), lower := (rows 193 7 292 41 56 32 64 128 256), losses := [] }

theorem u15497 : Upper (D 8) (R 8) [192,5,288,33,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15497 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15498 : Route 9 := (fun mask => (mask,id))

def c15498 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u15498 : Upper (D 8) (R 8) [192,5,288,33,66] 13 := by
  apply FastRouting.sound _ _ [192,5,288,33,66] 13 (by decide) (choices 1) [8,16,128] r15498 c15498
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5394
  · exact u5395
  · exact u5396

def r15499 : Route 9 := (fun mask => (mask,id))

def c15499 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u15499 : Upper (D 8) (R 8) [192,5,288,33,72] 13 := by
  apply FastRouting.sound _ _ [192,5,288,33,72] 13 (by decide) (choices 1) [2,16,128] r15499 c15499
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5397
  · exact u5398
  · exact u5399

def r15500 : Route 9 := (fun mask => (mask,id))

def c15500 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u15500 : Upper (D 8) (R 8) [192,5,288,33,96] 13 := by
  apply FastRouting.sound _ _ [192,5,288,33,96] 13 (by decide) (choices 1) [2,8,16,128] r15500 c15500
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5400
  · exact u5401
  · exact u5402
  · exact u5403

def b15501 : PairBound 9 := { available := 58, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 193 7 292 41 208 58 122 186 314), lower := (rows 193 7 292 41 208 32 64 128 256), losses := [] }

theorem u15501 : Upper (D 8) (R 8) [192,5,288,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15501 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15502 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 193 7 292 42 56 241 209 209 465), lower := (rows 193 7 292 42 56 32 64 128 256), losses := [] }

theorem u15502 : Upper (D 8) (R 8) [192,5,288,34,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15502 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15503 : PairBound 9 := { available := 184, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 292 42 81 184 248 184 440), lower := (rows 193 7 292 42 81 32 64 128 256), losses := [] }

theorem u15503 : Upper (D 8) (R 8) [192,5,288,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15503 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15504 : Route 9 := (fun mask => (mask,id))

def c15504 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u15504 : Upper (D 8) (R 8) [192,5,288,34,72] 13 := by
  apply FastRouting.sound _ _ [192,5,288,34,72] 13 (by decide) (choices 1) [1,16,128] r15504 c15504
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5404
  · exact u5405
  · exact u5406

def r15505 : Route 9 := (fun mask => (mask,id))

def c15505 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u15505 : Upper (D 8) (R 8) [192,5,288,34,96] 13 := by
  apply FastRouting.sound _ _ [192,5,288,34,96] 13 (by decide) (choices 1) [1,8,16,128] r15505 c15505
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5407
  · exact u5408
  · exact u5409
  · exact u5410

def b15506 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 193 7 292 42 208 57 121 185 313), lower := (rows 193 7 292 42 208 32 64 128 256), losses := [] }

theorem u15506 : Upper (D 8) (R 8) [192,5,288,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15506 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15507 : PairBound 9 := { available := 195, camps := [{ cop := 2, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 292 56 56 227 195 195 451), lower := (rows 193 7 292 56 56 32 64 128 256), losses := [] }

theorem u15507 : Upper (D 8) (R 8) [192,5,288,48,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15507 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15508 : PairBound 9 := { available := 170, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 292 56 81 170 234 170 426), lower := (rows 193 7 292 56 81 32 64 128 256), losses := [] }

theorem u15508 : Upper (D 8) (R 8) [192,5,288,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15508 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15509 : Route 9 := (fun mask => (mask,id))

def c15509 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u15509 : Upper (D 8) (R 8) [192,5,288,48,66] 13 := by
  apply FastRouting.sound _ _ [192,5,288,48,66] 13 (by decide) (choices 1) [1,8,128] r15509 c15509
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5411
  · exact u5412
  · exact u5413

def b15510 : PairBound 9 := { available := 163, camps := [{ cop := 0, region := 294, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 292 56 88 163 227 163 419), lower := (rows 193 7 292 56 88 32 64 128 256), losses := [] }

theorem u15510 : Upper (D 8) (R 8) [192,5,288,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15510 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15511 : PairBound 9 := { available := 139, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 292 56 112 171 203 139 395), lower := (rows 193 7 292 56 112 32 64 128 256), losses := [] }

theorem u15511 : Upper (D 8) (R 8) [192,5,288,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15511 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15512 : PairBound 9 := { available := 43, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 193 7 292 56 208 43 107 171 299), lower := (rows 193 7 292 56 208 32 64 128 256), losses := [] }

theorem u15512 : Upper (D 8) (R 8) [192,5,288,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15512 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15513 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 292 73 146 56 120 184 312), lower := (rows 193 7 292 73 146 32 64 128 256), losses := [] }

theorem u15513 : Upper (D 8) (R 8) [192,5,288,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15513 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15514 : PairBound 9 := { available := 50, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 292 73 152 50 114 178 306), lower := (rows 193 7 292 73 152 32 64 128 256), losses := [] }

theorem u15514 : Upper (D 8) (R 8) [192,5,288,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15514 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15515 : PairBound 9 := { available := 58, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 292 73 176 58 122 186 314), lower := (rows 193 7 292 73 176 32 64 128 256), losses := [] }

theorem u15515 : Upper (D 8) (R 8) [192,5,288,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15515 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15516 : Route 9 := (fun mask => (mask,id))

def c15516 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15516 : Upper (D 8) (R 8) [192,5,288,66,136] 13 := by
  apply FastRouting.sound _ _ [192,5,288,66,136] 13 (by decide) (choices 1) [1,16] r15516 c15516
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5414
  · exact u5415

def r15517 : Route 9 := (fun mask => (mask,id))

def c15517 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15517 : Upper (D 8) (R 8) [192,5,288,66,160] 13 := by
  apply FastRouting.sound _ _ [192,5,288,66,160] 13 (by decide) (choices 1) [1,8,16] r15517 c15517
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5416
  · exact u5417
  · exact u5418

def b15518 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 292 88 152 35 99 163 291), lower := (rows 193 7 292 88 152 32 64 128 256), losses := [] }

theorem u15518 : Upper (D 8) (R 8) [192,5,288,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15518 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15519 : Route 9 := (fun mask => (mask,id))

def c15519 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15519 : Upper (D 8) (R 8) [192,5,288,80,160] 13 := by
  apply FastRouting.sound _ _ [192,5,288,80,160] 13 (by decide) (choices 1) [1,2,8] r15519 c15519
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5419
  · exact u5420
  · exact u5421

theorem m15520_16 : Upper (D 8) (R 8) [192,5,288,96,160,16] 13 :=
  permutation_upper _ _ _ [192,5,288,96,160,8] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5424

def r15520 : Route 9 := (fun mask => (mask,id))

def c15520 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15520 : Upper (D 8) (R 8) [192,5,288,96,160] 13 := by
  apply FastRouting.sound _ _ [192,5,288,96,160] 13 (by decide) (choices 1) [1,2,8,16] r15520 c15520
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5422
  · exact u5423
  · exact u5424
  · exact m15520_16

def b15521 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 324 26 49 168 232 168 424), lower := (rows 193 7 324 26 49 32 64 128 256), losses := [] }

theorem u15521 : Upper (D 8) (R 8) [192,5,320,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15521 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15522 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 324 26 56 161 225 161 417), lower := (rows 193 7 324 26 56 32 64 128 256), losses := [] }

theorem u15522 : Upper (D 8) (R 8) [192,5,320,18,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15522 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15523 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 324 26 176 41 105 169 297), lower := (rows 193 7 324 26 176 32 64 128 256), losses := [] }

theorem u15523 : Upper (D 8) (R 8) [192,5,320,18,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15523 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15524 : PairBound 9 := { available := 184, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 324 41 50 184 248 184 440), lower := (rows 193 7 324 41 50 32 64 128 256), losses := [] }

theorem u15524 : Upper (D 8) (R 8) [192,5,320,33,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15524 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15525 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 324 41 146 56 120 184 312), lower := (rows 193 7 324 41 146 32 64 128 256), losses := [] }

theorem u15525 : Upper (D 8) (R 8) [192,5,320,33,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15525 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15526 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 324 41 152 50 114 178 306), lower := (rows 193 7 324 41 152 32 64 128 256), losses := [] }

theorem u15526 : Upper (D 8) (R 8) [192,5,320,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15526 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15527 : PairBound 9 := { available := 58, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 324 41 176 58 122 186 314), lower := (rows 193 7 324 41 176 32 64 128 256), losses := [] }

theorem u15527 : Upper (D 8) (R 8) [192,5,320,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15527 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15528 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 324 42 152 49 113 177 305), lower := (rows 193 7 324 42 152 32 64 128 256), losses := [] }

theorem u15528 : Upper (D 8) (R 8) [192,5,320,34,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15528 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15529 : PairBound 9 := { available := 57, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 324 42 176 57 121 185 313), lower := (rows 193 7 324 42 176 32 64 128 256), losses := [] }

theorem u15529 : Upper (D 8) (R 8) [192,5,320,34,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15529 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15530 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 324 56 146 41 105 169 297), lower := (rows 193 7 324 56 146 32 64 128 256), losses := [] }

theorem u15530 : Upper (D 8) (R 8) [192,5,320,48,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15530 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15531 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 22, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 22 41 49 480 480 480 480), lower := (rows 193 14 22 41 49 32 64 128 256), losses := [] }

theorem u15531 : Upper (D 8) (R 8) [192,12,18,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15531 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15532 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 22 41 81 416 480 416 416), lower := (rows 193 14 22 41 81 32 64 128 256), losses := [] }

theorem u15532 : Upper (D 8) (R 8) [192,12,18,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15532 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15533 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 296, targets := 64 }], pairs := [(3,6)], upper := (rows 193 14 22 41 112 417 481 417 417), lower := (rows 193 14 22 41 112 32 64 128 256), losses := [] }

theorem u15533 : Upper (D 8) (R 8) [192,12,18,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15533 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15534 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 193 14 22 41 208 289 353 417 289), lower := (rows 193 14 22 41 208 32 64 128 256), losses := [] }

theorem u15534 : Upper (D 8) (R 8) [192,12,18,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15534 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15535 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c15535 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u15535 : Upper (D 8) (R 8) [192,12,18,33,257] 13 := by
  apply FastRouting.sound _ _ [192,12,18,33,257] 13 (by decide) (choices 1) [64] r15535 c15535
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u5425

def r15536 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c15536 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u15536 : Upper (D 8) (R 8) [192,12,18,33,288] 13 := by
  apply FastRouting.sound _ _ [192,12,18,33,288] 13 (by decide) (choices 1) [1,64] r15536 c15536
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5426
  · exact u5427

def b15537 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 193 14 22 41 336 161 225 161 417), lower := (rows 193 14 22 41 336 32 64 128 256), losses := [] }

theorem u15537 : Upper (D 8) (R 8) [192,12,18,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15537 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15538 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 22 73 273 160 224 160 416), lower := (rows 193 14 22 73 273 32 64 128 256), losses := [] }

theorem u15538 : Upper (D 8) (R 8) [192,12,18,65,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15538 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15539 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 22 73 304 161 225 161 417), lower := (rows 193 14 22 73 304 32 64 128 256), losses := [] }

theorem u15539 : Upper (D 8) (R 8) [192,12,18,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15539 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u15539
end Delivery.IrregularNine14.P08

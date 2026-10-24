import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0235
import IrregularNine14P07C0236
import IrregularNine14P07C0237

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b31500 : PairBound 9 := { available := 449, camps := [{ cop := 3, region := 453, targets := 32 },{ cop := 0, region := 496, targets := 2 }], pairs := [(0,5),(2,1),(2,5),(4,1)], upper := (rows 7 98 140 26 49 481 449 449 449), lower := (rows 7 98 140 26 49 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 17 49 81 145 273), good := (rows 501 96 140 508 497 32 64 128 256) }] }

theorem u31500 : Upper (D 7) (R 7) [6,96,136,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31500 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31501 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 24, targets := 129 }], pairs := [(3,0),(3,7),(4,0),(4,7)], upper := (rows 7 98 140 26 112 417 449 385 385), lower := (rows 7 98 140 26 112 32 64 128 256), losses := [] }

theorem u31501 : Upper (D 7) (R 7) [6,96,136,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31501 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31502 : PairBound 9 := { available := 353, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 0, region := 496, targets := 2 },{ cop := 4, region := 362, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,1)], upper := (rows 7 98 140 26 145 353 353 481 353), lower := (rows 7 98 140 26 145 32 64 128 256), losses := [] }

theorem u31502 : Upper (D 7) (R 7) [6,96,136,18,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31502 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31503 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 3, region := 453, targets := 32 }], pairs := [(0,5),(0,7),(1,7),(2,5)], upper := (rows 7 98 140 26 176 353 321 449 321), lower := (rows 7 98 140 26 176 32 64 128 256), losses := [] }

theorem u31503 : Upper (D 7) (R 7) [6,96,136,18,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31503 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31504 : Route 9 := (fun mask => (mask,id))

def c31504 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31504 : Upper (D 7) (R 7) [6,96,136,18,257] 13 := by
  apply FastRouting.sound _ _ [6,96,136,18,257] 13 (by decide) (choices 1) [1,64,128] r31504 c31504
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14135
  · exact u14136
  · exact u14137

def r31505 : Route 9 := (fun mask => (mask,id))

def c31505 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31505 : Upper (D 7) (R 7) [6,96,136,18,288] 13 := by
  apply FastRouting.sound _ _ [6,96,136,18,288] 13 (by decide) (choices 1) [1,64,128] r31505 c31505
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14138
  · exact u14139
  · exact u14140

def r31506 : Route 9 := (fun mask => (mask,id))

def c31506 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31506 : Upper (D 7) (R 7) [6,96,136,18,384] 13 := by
  apply FastRouting.sound _ _ [6,96,136,18,384] 13 (by decide) (choices 1) [1,64] r31506 c31506
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u14141
  · exact u14142

def b31507 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 16, targets := 192 },{ cop := 4, region := 492, targets := 2 }], pairs := [(2,1),(3,1),(4,6),(4,7)], upper := (rows 7 98 140 41 19 496 464 464 464), lower := (rows 7 98 140 41 19 32 64 128 256), losses := [] }

theorem u31507 : Upper (D 7) (R 7) [6,96,136,33,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31507 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31508 : Route 9 := (fun mask => (mask,id))

def c31508 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u31508 : Upper (D 7) (R 7) [6,96,136,33,65] 13 := by
  apply FastRouting.sound _ _ [6,96,136,33,65] 13 (by decide) (choices 1) [2,16,128,256] r31508 c31508
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14143
  · exact u14144
  · exact u14145
  · exact u14146

def b31509 : PairBound 9 := { available := 401, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 7 98 140 41 82 433 465 401 401), lower := (rows 7 98 140 41 82 32 64 128 256), losses := [] }

theorem u31509 : Upper (D 7) (R 7) [6,96,136,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31509 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31510 : PairBound 9 := { available := 338, camps := [{ cop := 4, region := 362, targets := 128 },{ cop := 0, region := 464, targets := 32 },{ cop := 4, region := 354, targets := 1 }], pairs := [(1,0),(1,7),(3,7),(4,5)], upper := (rows 7 98 140 41 145 370 338 466 338), lower := (rows 7 98 140 41 145 32 64 128 256), losses := [] }

theorem u31510 : Upper (D 7) (R 7) [6,96,136,33,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31510 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31511 : Route 9 := (fun mask => (mask,id))

def c31511 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u31511 : Upper (D 7) (R 7) [6,96,136,33,130] 13 := by
  apply FastRouting.sound _ _ [6,96,136,33,130] 13 (by decide) (choices 1) [1,16,64,256] r31511 c31511
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14147
  · exact u14148
  · exact u14149
  · exact u14150

def r31512 : Route 9 := (fun mask => (mask,id))

def c31512 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31512 : Upper (D 7) (R 7) [6,96,136,33,192] 13 := by
  apply FastRouting.sound _ _ [6,96,136,33,192] 13 (by decide) (choices 1) [1,2,16,256] r31512 c31512
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14151
  · exact u14152
  · exact u14153
  · exact u14154

def r31513 : Route 9 := (fun mask => (mask,id))

def c31513 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u31513 : Upper (D 7) (R 7) [6,96,136,33,257] 13 := by
  apply FastRouting.sound _ _ [6,96,136,33,257] 13 (by decide) (choices 1) [2,16,64,128] r31513 c31513
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14155
  · exact u14156
  · exact u14157
  · exact u14158

def r31514 : Route 9 := (fun mask => (mask,id))

def c31514 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u31514 : Upper (D 7) (R 7) [6,96,136,33,258] 13 := by
  apply FastRouting.sound _ _ [6,96,136,33,258] 13 (by decide) (choices 1) [1,16,64,128] r31514 c31514
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14159
  · exact u14160
  · exact u14161
  · exact u14162

def r31515 : Route 9 := (fun mask => (mask,id))

def c31515 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31515 : Upper (D 7) (R 7) [6,96,136,33,320] 13 := by
  apply FastRouting.sound _ _ [6,96,136,33,320] 13 (by decide) (choices 1) [1,2,16,128] r31515 c31515
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14163
  · exact u14164
  · exact u14165
  · exact u14166

def r31516 : Route 9 := (fun mask => (mask,id))

def c31516 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31516 : Upper (D 7) (R 7) [6,96,136,33,384] 13 := by
  apply FastRouting.sound _ _ [6,96,136,33,384] 13 (by decide) (choices 1) [1,2,16,64] r31516 c31516
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14167
  · exact u14168
  · exact u14169
  · exact u14170

def b31517 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 16, targets := 192 },{ cop := 4, region := 492, targets := 2 }], pairs := [(2,1),(3,1),(4,6),(4,7)], upper := (rows 7 98 140 56 19 481 449 449 449), lower := (rows 7 98 140 56 19 32 64 128 256), losses := [] }

theorem u31517 : Upper (D 7) (R 7) [6,96,136,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31517 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31518 : Route 9 := (fun mask => (mask,id))

def c31518 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u31518 : Upper (D 7) (R 7) [6,96,136,48,65] 13 := by
  apply FastRouting.sound _ _ [6,96,136,48,65] 13 (by decide) (choices 1) [1,2,128,256] r31518 c31518
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14171
  · exact u14172
  · exact u14173
  · exact u14174

def b31519 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 24, targets := 129 }], pairs := [(3,0),(3,7),(4,0),(4,7)], upper := (rows 7 98 140 56 82 417 449 385 385), lower := (rows 7 98 140 56 82 32 64 128 256), losses := [] }

theorem u31519 : Upper (D 7) (R 7) [6,96,136,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31519 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31520 : PairBound 9 := { available := 323, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 0, region := 464, targets := 32 },{ cop := 4, region := 362, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,5)], upper := (rows 7 98 140 56 145 355 323 451 323), lower := (rows 7 98 140 56 145 32 64 128 256), losses := [] }

theorem u31520 : Upper (D 7) (R 7) [6,96,136,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31520 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31521 : Route 9 := (fun mask => (mask,id))

def c31521 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u31521 : Upper (D 7) (R 7) [6,96,136,48,130] 13 := by
  apply FastRouting.sound _ _ [6,96,136,48,130] 13 (by decide) (choices 1) [1,64,256] r31521 c31521
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14175
  · exact u14176
  · exact u14177

def r31522 : Route 9 := (fun mask => (mask,id))

def c31522 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31522 : Upper (D 7) (R 7) [6,96,136,48,192] 13 := by
  apply FastRouting.sound _ _ [6,96,136,48,192] 13 (by decide) (choices 1) [1,2,256] r31522 c31522
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14178
  · exact u14179
  · exact u14180

def r31523 : Route 9 := (fun mask => (mask,id))

def c31523 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31523 : Upper (D 7) (R 7) [6,96,136,48,257] 13 := by
  apply FastRouting.sound _ _ [6,96,136,48,257] 13 (by decide) (choices 1) [1,2,64,128] r31523 c31523
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14181
  · exact u14182
  · exact u14183
  · exact u14184

def r31524 : Route 9 := (fun mask => (mask,id))

def c31524 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31524 : Upper (D 7) (R 7) [6,96,136,48,258] 13 := by
  apply FastRouting.sound _ _ [6,96,136,48,258] 13 (by decide) (choices 1) [1,64,128] r31524 c31524
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14185
  · exact u14186
  · exact u14187

def r31525 : Route 9 := (fun mask => (mask,id))

def c31525 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31525 : Upper (D 7) (R 7) [6,96,136,48,320] 13 := by
  apply FastRouting.sound _ _ [6,96,136,48,320] 13 (by decide) (choices 1) [1,2,128] r31525 c31525
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14188
  · exact u14189
  · exact u14190

def r31526 : Route 9 := (fun mask => (mask,id))

def c31526 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31526 : Upper (D 7) (R 7) [6,96,136,48,384] 13 := by
  apply FastRouting.sound _ _ [6,96,136,48,384] 13 (by decide) (choices 1) [1,2,64] r31526 c31526
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14191
  · exact u14192
  · exact u14193

def b31527 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 16, targets := 224 },{ cop := 4, region := 492, targets := 2 }], pairs := [(2,1),(4,5),(4,6),(4,7)], upper := (rows 7 98 140 265 19 240 240 240 496), lower := (rows 7 98 140 265 19 32 64 128 256), losses := [] }

theorem u31527 : Upper (D 7) (R 7) [6,96,136,257,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31527 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31528 : Route 9 := (fun mask => (mask,id))

def c31528 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u31528 : Upper (D 7) (R 7) [6,96,136,257,33] 13 := by
  apply FastRouting.sound _ _ [6,96,136,257,33] 13 (by decide) (choices 1) [2,16,64,128] r31528 c31528
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14194
  · exact u14195
  · exact u14196
  · exact u14197

def b31529 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 461, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 7 98 140 265 50 241 209 209 465), lower := (rows 7 98 140 265 50 32 64 128 256), losses := [] }

theorem u31529 : Upper (D 7) (R 7) [6,96,136,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31529 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31530 : PairBound 9 := { available := 147, camps := [{ cop := 1, region := 16, targets := 129 },{ cop := 4, region := 2, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 7 98 140 265 112 179 211 147 403), lower := (rows 7 98 140 265 112 32 64 128 256), losses := [] }

theorem u31530 : Upper (D 7) (R 7) [6,96,136,257,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31530 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31531 : Route 9 := (fun mask => (mask,id))

def c31531 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31531 : Upper (D 7) (R 7) [6,96,136,257,129] 13 := by
  apply FastRouting.sound _ _ [6,96,136,257,129] 13 (by decide) (choices 1) [2,16,64] r31531 c31531
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14198
  · exact u14199
  · exact u14200

def r31532 : Route 9 := (fun mask => (mask,id))

def c31532 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31532 : Upper (D 7) (R 7) [6,96,136,257,130] 13 := by
  apply FastRouting.sound _ _ [6,96,136,257,130] 13 (by decide) (choices 1) [1,16,64] r31532 c31532
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14201
  · exact u14202
  · exact u14203

def r31533 : Route 9 := (fun mask => (mask,id))

def c31533 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31533 : Upper (D 7) (R 7) [6,96,136,257,160] 13 := by
  apply FastRouting.sound _ _ [6,96,136,257,160] 13 (by decide) (choices 1) [1,2,16,64] r31533 c31533
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14204
  · exact u14205
  · exact u14206
  · exact u14207

def r31534 : Route 9 := (fun mask => (mask,id))

def c31534 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u31534 : Upper (D 7) (R 7) [6,96,136,258,33] 13 := by
  apply FastRouting.sound _ _ [6,96,136,258,33] 13 (by decide) (choices 1) [1,16,64,128] r31534 c31534
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14208
  · exact u14209
  · exact u14210
  · exact u14211

def b31535 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 16, targets := 129 },{ cop := 4, region := 2, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 7 98 140 266 112 177 209 145 401), lower := (rows 7 98 140 266 112 32 64 128 256), losses := [] }

theorem u31535 : Upper (D 7) (R 7) [6,96,136,258,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31535 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31536 : Route 9 := (fun mask => (mask,id))

def c31536 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31536 : Upper (D 7) (R 7) [6,96,136,258,129] 13 := by
  apply FastRouting.sound _ _ [6,96,136,258,129] 13 (by decide) (choices 1) [1,16,64] r31536 c31536
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14212
  · exact u14213
  · exact u14214

def r31537 : Route 9 := (fun mask => (mask,id))

def c31537 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31537 : Upper (D 7) (R 7) [6,96,136,258,160] 13 := by
  apply FastRouting.sound _ _ [6,96,136,258,160] 13 (by decide) (choices 1) [1,16,64] r31537 c31537
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14215
  · exact u14216
  · exact u14217

def b31538 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 16, targets := 224 },{ cop := 4, region := 492, targets := 2 }], pairs := [(2,1),(4,5),(4,6),(4,7)], upper := (rows 7 98 140 280 19 225 225 225 481), lower := (rows 7 98 140 280 19 32 64 128 256), losses := [] }

theorem u31538 : Upper (D 7) (R 7) [6,96,136,272,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31538 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31539 : Route 9 := (fun mask => (mask,id))

def c31539 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31539 : Upper (D 7) (R 7) [6,96,136,272,33] 13 := by
  apply FastRouting.sound _ _ [6,96,136,272,33] 13 (by decide) (choices 1) [1,2,64,128] r31539 c31539
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14218
  · exact u14219
  · exact u14220
  · exact u14221

def b31540 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 461, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 7 98 140 280 50 225 193 193 449), lower := (rows 7 98 140 280 50 32 64 128 256), losses := [] }

theorem u31540 : Upper (D 7) (R 7) [6,96,136,272,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31540 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31541 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 16, targets := 129 },{ cop := 4, region := 2, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 7 98 140 280 112 163 195 131 387), lower := (rows 7 98 140 280 112 32 64 128 256), losses := [] }

theorem u31541 : Upper (D 7) (R 7) [6,96,136,272,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31541 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31542 : Route 9 := (fun mask => (mask,id))

def c31542 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31542 : Upper (D 7) (R 7) [6,96,136,272,129] 13 := by
  apply FastRouting.sound _ _ [6,96,136,272,129] 13 (by decide) (choices 1) [1,2,64] r31542 c31542
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14222
  · exact u14223
  · exact u14224

def r31543 : Route 9 := (fun mask => (mask,id))

def c31543 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31543 : Upper (D 7) (R 7) [6,96,136,272,130] 13 := by
  apply FastRouting.sound _ _ [6,96,136,272,130] 13 (by decide) (choices 1) [1,64] r31543 c31543
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u14225
  · exact u14226

def r31544 : Route 9 := (fun mask => (mask,id))

def c31544 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31544 : Upper (D 7) (R 7) [6,96,136,272,160] 13 := by
  apply FastRouting.sound _ _ [6,96,136,272,160] 13 (by decide) (choices 1) [1,2,64] r31544 c31544
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14227
  · exact u14228
  · exact u14229

def b31545 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 16, targets := 192 },{ cop := 4, region := 492, targets := 2 }], pairs := [(2,1),(3,1),(4,6),(4,7)], upper := (rows 7 98 140 296 19 241 209 209 465), lower := (rows 7 98 140 296 19 32 64 128 256), losses := [] }

theorem u31545 : Upper (D 7) (R 7) [6,96,136,288,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31545 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31546 : Route 9 := (fun mask => (mask,id))

def c31546 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31546 : Upper (D 7) (R 7) [6,96,136,288,65] 13 := by
  apply FastRouting.sound _ _ [6,96,136,288,65] 13 (by decide) (choices 1) [1,2,16,128] r31546 c31546
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14230
  · exact u14231
  · exact u14232
  · exact u14233

def b31547 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 7 98 140 296 82 177 209 145 401), lower := (rows 7 98 140 296 82 32 64 128 256), losses := [] }

theorem u31547 : Upper (D 7) (R 7) [6,96,136,288,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31547 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31548 : Route 9 := (fun mask => (mask,id))

def c31548 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31548 : Upper (D 7) (R 7) [6,96,136,288,129] 13 := by
  apply FastRouting.sound _ _ [6,96,136,288,129] 13 (by decide) (choices 1) [1,2,16,64] r31548 c31548
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14234
  · exact u14235
  · exact u14236
  · exact u14237

def r31549 : Route 9 := (fun mask => (mask,id))

def c31549 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31549 : Upper (D 7) (R 7) [6,96,136,288,130] 13 := by
  apply FastRouting.sound _ _ [6,96,136,288,130] 13 (by decide) (choices 1) [1,16,64] r31549 c31549
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14238
  · exact u14239
  · exact u14240

def r31550 : Route 9 := (fun mask => (mask,id))

def c31550 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31550 : Upper (D 7) (R 7) [6,96,136,288,192] 13 := by
  apply FastRouting.sound _ _ [6,96,136,288,192] 13 (by decide) (choices 1) [1,2,16] r31550 c31550
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14241
  · exact u14242
  · exact u14243

def b31551 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 7 98 164 11 25 496 464 464 464), lower := (rows 7 98 164 11 25 32 64 128 256), losses := [] }

theorem u31551 : Upper (D 7) (R 7) [6,96,160,3,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31551 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31552 : PairBound 9 := { available := 408, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 8, targets := 192 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 7 98 164 11 81 440 472 408 408), lower := (rows 7 98 164 11 81 32 64 128 256), losses := [] }

theorem u31552 : Upper (D 7) (R 7) [6,96,160,3,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31552 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31553 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 8, targets := 192 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 7 98 164 11 88 433 465 401 401), lower := (rows 7 98 164 11 88 32 64 128 256), losses := [] }

theorem u31553 : Upper (D 7) (R 7) [6,96,160,3,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31553 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31554 : PairBound 9 := { available := 337, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 8, targets := 192 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 7 98 164 11 152 369 337 465 337), lower := (rows 7 98 164 11 152 32 64 128 256), losses := [] }

theorem u31554 : Upper (D 7) (R 7) [6,96,160,3,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31554 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31555 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 8, targets := 192 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 7 98 164 11 208 313 345 409 281), lower := (rows 7 98 164 11 208 32 64 128 256), losses := [] }

theorem u31555 : Upper (D 7) (R 7) [6,96,160,3,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31555 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31556 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 8, targets := 192 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 7 98 164 11 273 248 216 216 472), lower := (rows 7 98 164 11 273 32 64 128 256), losses := [] }

theorem u31556 : Upper (D 7) (R 7) [6,96,160,3,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31556 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31557 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 8, targets := 192 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 7 98 164 11 280 241 209 209 465), lower := (rows 7 98 164 11 280 32 64 128 256), losses := [] }

theorem u31557 : Upper (D 7) (R 7) [6,96,160,3,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31557 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31558 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 8, targets := 192 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 7 98 164 11 336 185 217 153 409), lower := (rows 7 98 164 11 336 32 64 128 256), losses := [] }

theorem u31558 : Upper (D 7) (R 7) [6,96,160,3,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31558 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31559 : PairBound 9 := { available := 89, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 8, targets := 192 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 7 98 164 11 400 121 89 217 345), lower := (rows 7 98 164 11 400 32 64 128 256), losses := [] }

theorem u31559 : Upper (D 7) (R 7) [6,96,160,3,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31559 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u31559
end Delivery.IrregularNine14.P07

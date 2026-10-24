import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0402
import IrregularNine14P07C0403
import IrregularNine14P07C0404
import IrregularNine14P07C0405

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r37560 : Route 9 := (fun mask => (mask,id))

def c37560 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37560 : Upper (D 7) (R 7) [36,96,130,65,384] 13 := by
  apply FastRouting.sound _ _ [36,96,130,65,384] 13 (by decide) (choices 1) [1,2,8,16] r37560 c37560
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24172
  · exact u24173
  · exact u24174
  · exact u24175

def b37561 : PairBound 9 := { available := 281, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 37 98 134 74 145 313 345 409 281), lower := (rows 37 98 134 74 145 32 64 128 256), losses := [] }

theorem u37561 : Upper (D 7) (R 7) [36,96,130,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37561 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37562 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 37 98 134 74 152 305 337 401 273), lower := (rows 37 98 134 74 152 32 64 128 256), losses := [] }

theorem u37562 : Upper (D 7) (R 7) [36,96,130,66,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37562 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37563 : PairBound 9 := { available := 153, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 37 98 134 74 273 185 217 153 409), lower := (rows 37 98 134 74 273 32 64 128 256), losses := [] }

theorem u37563 : Upper (D 7) (R 7) [36,96,130,66,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37563 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37564 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 37 98 134 74 280 177 209 145 401), lower := (rows 37 98 134 74 280 32 64 128 256), losses := [] }

theorem u37564 : Upper (D 7) (R 7) [36,96,130,66,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37564 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37565 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 37 98 134 74 400 57 89 153 281), lower := (rows 37 98 134 74 400 32 64 128 256), losses := [] }

theorem u37565 : Upper (D 7) (R 7) [36,96,130,66,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37565 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37566 : Route 9 := (fun mask => (mask,id))

def c37566 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37566 : Upper (D 7) (R 7) [36,96,130,80,129] 13 := by
  apply FastRouting.sound _ _ [36,96,130,80,129] 13 (by decide) (choices 1) [1,2,8,256] r37566 c37566
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24176
  · exact u24177
  · exact u24178
  · exact u24179

def b37567 : PairBound 9 := { available := 265, camps := [{ cop := 2, region := 16, targets := 97 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,5),(4,6)], upper := (rows 37 98 134 88 146 297 329 393 265), lower := (rows 37 98 134 88 146 32 64 128 256), losses := [] }

theorem u37567 : Upper (D 7) (R 7) [36,96,130,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37567 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37568 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 389, targets := 64 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,6),(0,7),(1,7),(2,6)], upper := (rows 37 98 134 88 152 291 323 387 259), lower := (rows 37 98 134 88 152 32 64 128 256), losses := [] }

theorem u37568 : Upper (D 7) (R 7) [36,96,130,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37568 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37569 : Route 9 := (fun mask => (mask,id))

def c37569 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37569 : Upper (D 7) (R 7) [36,96,130,80,257] 13 := by
  apply FastRouting.sound _ _ [36,96,130,80,257] 13 (by decide) (choices 1) [1,2,8,128] r37569 c37569
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24180
  · exact u24181
  · exact u24182
  · exact u24183

def r37570 : Route 9 := (fun mask => (mask,id))

def c37570 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37570 : Upper (D 7) (R 7) [36,96,130,80,258] 13 := by
  apply FastRouting.sound _ _ [36,96,130,80,258] 13 (by decide) (choices 1) [1,8,128] r37570 c37570
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24184
  · exact u24185
  · exact u24186

def r37571 : Route 9 := (fun mask => (mask,id))

def c37571 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37571 : Upper (D 7) (R 7) [36,96,130,80,264] 13 := by
  apply FastRouting.sound _ _ [36,96,130,80,264] 13 (by decide) (choices 1) [1,2,128] r37571 c37571
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24187
  · exact u24188
  · exact u24189

def r37572 : Route 9 := (fun mask => (mask,id))

def c37572 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37572 : Upper (D 7) (R 7) [36,96,130,80,384] 13 := by
  apply FastRouting.sound _ _ [36,96,130,80,384] 13 (by decide) (choices 1) [1,2,8] r37572 c37572
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24190
  · exact u24191
  · exact u24192

def r37573 : Route 9 := (fun mask => (mask,id))

def c37573 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37573 : Upper (D 7) (R 7) [36,96,130,129,257] 13 := by
  apply FastRouting.sound _ _ [36,96,130,129,257] 13 (by decide) (choices 1) [2,8,16,64] r37573 c37573
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24193
  · exact u24194
  · exact u24195
  · exact u24196

def r37574 : Route 9 := (fun mask => (mask,id))

def c37574 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37574 : Upper (D 7) (R 7) [36,96,130,129,258] 13 := by
  apply FastRouting.sound _ _ [36,96,130,129,258] 13 (by decide) (choices 1) [1,8,16,64] r37574 c37574
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24197
  · exact u24198
  · exact u24199
  · exact u24200

def r37575 : Route 9 := (fun mask => (mask,id))

def c37575 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37575 : Upper (D 7) (R 7) [36,96,130,129,264] 13 := by
  apply FastRouting.sound _ _ [36,96,130,129,264] 13 (by decide) (choices 1) [1,2,16,64] r37575 c37575
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24201
  · exact u24202
  · exact u24203
  · exact u24204

def r37576 : Route 9 := (fun mask => (mask,id))

def c37576 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37576 : Upper (D 7) (R 7) [36,96,130,129,320] 13 := by
  apply FastRouting.sound _ _ [36,96,130,129,320] 13 (by decide) (choices 1) [1,2,8,16] r37576 c37576
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24205
  · exact u24206
  · exact u24207
  · exact u24208

def b37577 : PairBound 9 := { available := 89, camps := [{ cop := 2, region := 8, targets := 97 },{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0),(3,0),(3,5),(3,6)], upper := (rows 37 98 134 138 273 121 89 217 345), lower := (rows 37 98 134 138 273 32 64 128 256), losses := [] }

theorem u37577 : Upper (D 7) (R 7) [36,96,130,130,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37577 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37578 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 8, targets := 97 },{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0),(3,0),(3,5),(3,6)], upper := (rows 37 98 134 138 280 113 81 209 337), lower := (rows 37 98 134 138 280 32 64 128 256), losses := [] }

theorem u37578 : Upper (D 7) (R 7) [36,96,130,130,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37578 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37579 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 8, targets := 97 },{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0),(3,0),(3,5),(3,6)], upper := (rows 37 98 134 138 336 57 89 153 281), lower := (rows 37 98 134 138 336 32 64 128 256), losses := [] }

theorem u37579 : Upper (D 7) (R 7) [36,96,130,130,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37579 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37580 : Route 9 := (fun mask => (mask,id))

def c37580 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37580 : Upper (D 7) (R 7) [36,96,130,144,257] 13 := by
  apply FastRouting.sound _ _ [36,96,130,144,257] 13 (by decide) (choices 1) [1,2,8,64] r37580 c37580
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24209
  · exact u24210
  · exact u24211
  · exact u24212

def r37581 : Route 9 := (fun mask => (mask,id))

def c37581 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37581 : Upper (D 7) (R 7) [36,96,130,144,258] 13 := by
  apply FastRouting.sound _ _ [36,96,130,144,258] 13 (by decide) (choices 1) [1,8,64] r37581 c37581
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24213
  · exact u24214
  · exact u24215

def r37582 : Route 9 := (fun mask => (mask,id))

def c37582 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37582 : Upper (D 7) (R 7) [36,96,130,144,264] 13 := by
  apply FastRouting.sound _ _ [36,96,130,144,264] 13 (by decide) (choices 1) [1,2,64] r37582 c37582
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24216
  · exact u24217
  · exact u24218

def r37583 : Route 9 := (fun mask => (mask,id))

def c37583 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37583 : Upper (D 7) (R 7) [36,96,130,144,320] 13 := by
  apply FastRouting.sound _ _ [36,96,130,144,320] 13 (by decide) (choices 1) [1,2,8] r37583 c37583
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24219
  · exact u24220
  · exact u24221

def r37584 : Route 9 := (fun mask => (mask,id))

def c37584 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37584 : Upper (D 7) (R 7) [36,96,130,192,257] 13 := by
  apply FastRouting.sound _ _ [36,96,130,192,257] 13 (by decide) (choices 1) [1,2,8,16] r37584 c37584
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24222
  · exact u24223
  · exact u24224
  · exact u24225

def r37585 : Route 9 := (fun mask => (mask,id))

def c37585 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37585 : Upper (D 7) (R 7) [36,96,130,192,258] 13 := by
  apply FastRouting.sound _ _ [36,96,130,192,258] 13 (by decide) (choices 1) [1,8,16] r37585 c37585
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24226
  · exact u24227
  · exact u24228

def r37586 : Route 9 := (fun mask => (mask,id))

def c37586 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37586 : Upper (D 7) (R 7) [36,96,130,192,264] 13 := by
  apply FastRouting.sound _ _ [36,96,130,192,264] 13 (by decide) (choices 1) [1,2,16] r37586 c37586
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24229
  · exact u24230
  · exact u24231

def b37587 : PairBound 9 := { available := 464, camps := [{ cop := 3, region := 468, targets := 32 },{ cop := 3, region := 16, targets := 192 }], pairs := [(2,5),(4,5),(4,6),(4,7)], upper := (rows 37 98 140 11 19 496 464 464 464), lower := (rows 37 98 140 11 19 32 64 128 256), losses := [] }

theorem u37587 : Upper (D 7) (R 7) [36,96,136,3,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37587 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37588 : Route 9 := (fun mask => (mask,id))

def c37588 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u37588 : Upper (D 7) (R 7) [36,96,136,3,65] 13 := by
  apply FastRouting.sound _ _ [36,96,136,3,65] 13 (by decide) (choices 1) [2,16,128,256] r37588 c37588
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24232
  · exact u24233
  · exact u24234
  · exact u24235

def b37589 : PairBound 9 := { available := 401, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 98 140 11 82 433 465 401 401), lower := (rows 37 98 140 11 82 32 64 128 256), losses := [] }

theorem u37589 : Upper (D 7) (R 7) [36,96,136,3,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37589 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37590 : PairBound 9 := { available := 338, camps := [{ cop := 3, region := 468, targets := 32 },{ cop := 4, region := 362, targets := 128 }], pairs := [(1,7),(2,5),(3,7),(4,5)], upper := (rows 37 98 140 11 145 370 338 466 338), lower := (rows 37 98 140 11 145 32 64 128 256), losses := [] }

theorem u37590 : Upper (D 7) (R 7) [36,96,136,3,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37590 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37591 : Route 9 := (fun mask => (mask,id))

def c37591 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u37591 : Upper (D 7) (R 7) [36,96,136,3,130] 13 := by
  apply FastRouting.sound _ _ [36,96,136,3,130] 13 (by decide) (choices 1) [1,16,64,256] r37591 c37591
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24236
  · exact u24237
  · exact u24238
  · exact u24239

def r37592 : Route 9 := (fun mask => (mask,id))

def c37592 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37592 : Upper (D 7) (R 7) [36,96,136,3,192] 13 := by
  apply FastRouting.sound _ _ [36,96,136,3,192] 13 (by decide) (choices 1) [1,2,16,256] r37592 c37592
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24240
  · exact u24241
  · exact u24242
  · exact u24243

def r37593 : Route 9 := (fun mask => (mask,id))

def c37593 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u37593 : Upper (D 7) (R 7) [36,96,136,3,257] 13 := by
  apply FastRouting.sound _ _ [36,96,136,3,257] 13 (by decide) (choices 1) [2,16,64,128] r37593 c37593
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24244
  · exact u24245
  · exact u24246
  · exact u24247

def r37594 : Route 9 := (fun mask => (mask,id))

def c37594 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u37594 : Upper (D 7) (R 7) [36,96,136,3,258] 13 := by
  apply FastRouting.sound _ _ [36,96,136,3,258] 13 (by decide) (choices 1) [1,16,64,128] r37594 c37594
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24248
  · exact u24249
  · exact u24250
  · exact u24251

def r37595 : Route 9 := (fun mask => (mask,id))

def c37595 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37595 : Upper (D 7) (R 7) [36,96,136,3,320] 13 := by
  apply FastRouting.sound _ _ [36,96,136,3,320] 13 (by decide) (choices 1) [1,2,16,128] r37595 c37595
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24252
  · exact u24253
  · exact u24254
  · exact u24255

def r37596 : Route 9 := (fun mask => (mask,id))

def c37596 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37596 : Upper (D 7) (R 7) [36,96,136,3,384] 13 := by
  apply FastRouting.sound _ _ [36,96,136,3,384] 13 (by decide) (choices 1) [1,2,16,64] r37596 c37596
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24256
  · exact u24257
  · exact u24258
  · exact u24259

def b37597 : PairBound 9 := { available := 450, camps := [{ cop := 4, region := 8, targets := 194 },{ cop := 3, region := 482, targets := 1 }], pairs := [(1,0),(3,1),(3,6),(3,7)], upper := (rows 37 98 140 25 19 482 450 450 450), lower := (rows 37 98 140 25 19 32 64 128 256), losses := [] }

theorem u37597 : Upper (D 7) (R 7) [36,96,136,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37597 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37598 : PairBound 9 := { available := 386, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 37 98 140 25 81 418 450 386 386), lower := (rows 37 98 140 25 81 32 64 128 256), losses := [] }

theorem u37598 : Upper (D 7) (R 7) [36,96,136,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37598 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37599 : PairBound 9 := { available := 387, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 98 140 25 82 419 451 387 387), lower := (rows 37 98 140 25 82 32 64 128 256), losses := [] }

theorem u37599 : Upper (D 7) (R 7) [36,96,136,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37599 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37600 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 12, targets := 98 }], pairs := [(2,1),(2,5),(2,6),(3,1)], upper := (rows 37 98 140 25 145 354 322 450 322), lower := (rows 37 98 140 25 145 32 64 128 256), losses := [] }

theorem u37600 : Upper (D 7) (R 7) [36,96,136,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37600 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37601 : Route 9 := (fun mask => (mask,id))

def c37601 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u37601 : Upper (D 7) (R 7) [36,96,136,17,130] 13 := by
  apply FastRouting.sound _ _ [36,96,136,17,130] 13 (by decide) (choices 1) [1,2,64,256] r37601 c37601
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24260
  · exact u24261
  · exact u24262
  · exact u24263

def r37602 : Route 9 := (fun mask => (mask,id))

def c37602 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37602 : Upper (D 7) (R 7) [36,96,136,17,192] 13 := by
  apply FastRouting.sound _ _ [36,96,136,17,192] 13 (by decide) (choices 1) [1,2,256] r37602 c37602
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24264
  · exact u24265
  · exact u24266

def b37603 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 37 98 140 25 273 226 194 194 450), lower := (rows 37 98 140 25 273 32 64 128 256), losses := [] }

theorem u37603 : Upper (D 7) (R 7) [36,96,136,17,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37603 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37604 : Route 9 := (fun mask => (mask,id))

def c37604 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37604 : Upper (D 7) (R 7) [36,96,136,17,258] 13 := by
  apply FastRouting.sound _ _ [36,96,136,17,258] 13 (by decide) (choices 1) [1,2,64,128] r37604 c37604
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24267
  · exact u24268
  · exact u24269
  · exact u24270

def r37605 : Route 9 := (fun mask => (mask,id))

def c37605 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37605 : Upper (D 7) (R 7) [36,96,136,17,320] 13 := by
  apply FastRouting.sound _ _ [36,96,136,17,320] 13 (by decide) (choices 1) [1,2,128] r37605 c37605
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24271
  · exact u24272
  · exact u24273

def r37606 : Route 9 := (fun mask => (mask,id))

def c37606 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37606 : Upper (D 7) (R 7) [36,96,136,17,384] 13 := by
  apply FastRouting.sound _ _ [36,96,136,17,384] 13 (by decide) (choices 1) [1,2,64] r37606 c37606
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24274
  · exact u24275
  · exact u24276

def b37607 : PairBound 9 := { available := 449, camps := [{ cop := 4, region := 8, targets := 193 },{ cop := 3, region := 485, targets := 2 }], pairs := [(0,1),(3,0),(3,6),(3,7)], upper := (rows 37 98 140 26 19 481 449 449 449), lower := (rows 37 98 140 26 19 32 64 128 256), losses := [] }

theorem u37607 : Upper (D 7) (R 7) [36,96,136,18,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37607 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37608 : Route 9 := (fun mask => (mask,id))

def c37608 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u37608 : Upper (D 7) (R 7) [36,96,136,18,65] 13 := by
  apply FastRouting.sound _ _ [36,96,136,18,65] 13 (by decide) (choices 1) [1,2,128,256] r37608 c37608
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24277
  · exact u24278
  · exact u24279
  · exact u24280

def b37609 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 24, targets := 161 }], pairs := [(3,0),(3,5),(3,7),(4,0)], upper := (rows 37 98 140 26 82 417 449 385 385), lower := (rows 37 98 140 26 82 32 64 128 256), losses := [] }

theorem u37609 : Upper (D 7) (R 7) [36,96,136,18,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37609 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37610 : Route 9 := (fun mask => (mask,id))

def c37610 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u37610 : Upper (D 7) (R 7) [36,96,136,18,129] 13 := by
  apply FastRouting.sound _ _ [36,96,136,18,129] 13 (by decide) (choices 1) [1,2,64,256] r37610 c37610
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24281
  · exact u24282
  · exact u24283
  · exact u24284

def b37611 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 12, targets := 97 }], pairs := [(2,0),(2,5),(2,6),(3,0)], upper := (rows 37 98 140 26 146 353 321 449 321), lower := (rows 37 98 140 26 146 32 64 128 256), losses := [] }

theorem u37611 : Upper (D 7) (R 7) [36,96,136,18,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37611 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37612 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 3, region := 421, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,6)], upper := (rows 37 98 140 26 208 291 323 387 259), lower := (rows 37 98 140 26 208 32 64 128 256), losses := [] }

theorem u37612 : Upper (D 7) (R 7) [36,96,136,18,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37612 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37613 : Route 9 := (fun mask => (mask,id))

def c37613 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37613 : Upper (D 7) (R 7) [36,96,136,18,257] 13 := by
  apply FastRouting.sound _ _ [36,96,136,18,257] 13 (by decide) (choices 1) [1,2,64,128] r37613 c37613
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24285
  · exact u24286
  · exact u24287
  · exact u24288

def b37614 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 37 98 140 26 274 225 193 193 449), lower := (rows 37 98 140 26 274 32 64 128 256), losses := [] }

theorem u37614 : Upper (D 7) (R 7) [36,96,136,18,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37614 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37615 : Route 9 := (fun mask => (mask,id))

def c37615 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37615 : Upper (D 7) (R 7) [36,96,136,18,320] 13 := by
  apply FastRouting.sound _ _ [36,96,136,18,320] 13 (by decide) (choices 1) [1,2,128] r37615 c37615
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24289
  · exact u24290
  · exact u24291

def r37616 : Route 9 := (fun mask => (mask,id))

def c37616 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37616 : Upper (D 7) (R 7) [36,96,136,18,384] 13 := by
  apply FastRouting.sound _ _ [36,96,136,18,384] 13 (by decide) (choices 1) [1,2,64] r37616 c37616
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24292
  · exact u24293
  · exact u24294

def r37617 : Route 9 := (fun mask => (mask,id))

def c37617 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u37617 : Upper (D 7) (R 7) [36,96,136,65,3] 13 := by
  apply FastRouting.sound _ _ [36,96,136,65,3] 13 (by decide) (choices 1) [2,16,128,256] r37617 c37617
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24295
  · exact u24296
  · exact u24297
  · exact u24298

def r37618 : Route 9 := (fun mask => (mask,id))

def c37618 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37618 : Upper (D 7) (R 7) [36,96,136,65,129] 13 := by
  apply FastRouting.sound _ _ [36,96,136,65,129] 13 (by decide) (choices 1) [2,16,256] r37618 c37618
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24299
  · exact u24300
  · exact u24301

def r37619 : Route 9 := (fun mask => (mask,id))

def c37619 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37619 : Upper (D 7) (R 7) [36,96,136,65,130] 13 := by
  apply FastRouting.sound _ _ [36,96,136,65,130] 13 (by decide) (choices 1) [1,2,16,256] r37619 c37619
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24302
  · exact u24303
  · exact u24304
  · exact u24305

#print axioms u37619
end Delivery.IrregularNine14.P07

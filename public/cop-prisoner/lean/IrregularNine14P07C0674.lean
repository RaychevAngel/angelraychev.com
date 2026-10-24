import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0486
import IrregularNine14P07C0487

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b40440 : PairBound 9 := { available := 90, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 97 262 133 41 146 122 90 218 346), lower := (rows 97 262 133 41 146 32 64 128 256), losses := [] }

theorem u40440 : Upper (D 7) (R 7) [96,260,129,33,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40440 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40441 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 97 262 133 41 152 114 82 210 338), lower := (rows 97 262 133 41 152 32 64 128 256), losses := [] }

theorem u40441 : Upper (D 7) (R 7) [96,260,129,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40441 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40442 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 97 262 133 41 208 58 90 154 282), lower := (rows 97 262 133 41 208 32 64 128 256), losses := [] }

theorem u40442 : Upper (D 7) (R 7) [96,260,129,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40442 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40443 : Route 9 := (fun mask => (mask,id))

def c40443 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40443 : Upper (D 7) (R 7) [96,260,129,34,66] 13 := by
  apply FastRouting.sound _ _ [96,260,129,34,66] 13 (by decide) (choices 1) [1,8,16,128] r40443 c40443
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29170
  · exact u29171
  · exact u29172
  · exact u29173

def r40444 : Route 9 := (fun mask => (mask,id))

def c40444 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40444 : Upper (D 7) (R 7) [96,260,129,34,72] 13 := by
  apply FastRouting.sound _ _ [96,260,129,34,72] 13 (by decide) (choices 1) [1,2,16,128] r40444 c40444
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29174
  · exact u29175
  · exact u29176
  · exact u29177

def b40445 : PairBound 9 := { available := 90, camps := [{ cop := 2, region := 16, targets := 98 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,5),(4,6)], upper := (rows 97 262 133 42 145 122 90 218 346), lower := (rows 97 262 133 42 145 32 64 128 256), losses := [] }

theorem u40445 : Upper (D 7) (R 7) [96,260,129,34,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40445 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40446 : Route 9 := (fun mask => (mask,id))

def c40446 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40446 : Upper (D 7) (R 7) [96,260,129,34,130] 13 := by
  apply FastRouting.sound _ _ [96,260,129,34,130] 13 (by decide) (choices 1) [1,8,16,64] r40446 c40446
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29178
  · exact u29179
  · exact u29180
  · exact u29181

def r40447 : Route 9 := (fun mask => (mask,id))

def c40447 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40447 : Upper (D 7) (R 7) [96,260,129,34,136] 13 := by
  apply FastRouting.sound _ _ [96,260,129,34,136] 13 (by decide) (choices 1) [1,2,16,64] r40447 c40447
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29182
  · exact u29183
  · exact u29184
  · exact u29185

def r40448 : Route 9 := (fun mask => (mask,id))

def c40448 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40448 : Upper (D 7) (R 7) [96,260,129,34,192] 13 := by
  apply FastRouting.sound _ _ [96,260,129,34,192] 13 (by decide) (choices 1) [1,2,8,16] r40448 c40448
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29186
  · exact u29187
  · exact u29188
  · exact u29189

def b40449 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 24, targets := 130 }], pairs := [(3,1),(3,7),(4,1),(4,7)], upper := (rows 97 262 133 56 88 163 195 131 387), lower := (rows 97 262 133 56 88 32 64 128 256), losses := [] }

theorem u40449 : Upper (D 7) (R 7) [96,260,129,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40449 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40450 : PairBound 9 := { available := 74, camps := [{ cop := 2, region := 16, targets := 98 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,5),(4,6)], upper := (rows 97 262 133 56 145 106 74 202 330), lower := (rows 97 262 133 56 145 32 64 128 256), losses := [] }

theorem u40450 : Upper (D 7) (R 7) [96,260,129,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40450 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40451 : Route 9 := (fun mask => (mask,id))

def c40451 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40451 : Upper (D 7) (R 7) [96,260,129,48,130] 13 := by
  apply FastRouting.sound _ _ [96,260,129,48,130] 13 (by decide) (choices 1) [1,2,8,64] r40451 c40451
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29190
  · exact u29191
  · exact u29192
  · exact u29193

def b40452 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 390, targets := 32 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,5),(1,7),(2,5)], upper := (rows 97 262 133 56 152 99 67 195 323), lower := (rows 97 262 133 56 152 32 64 128 256), losses := [] }

theorem u40452 : Upper (D 7) (R 7) [96,260,129,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40452 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40453 : Route 9 := (fun mask => (mask,id))

def c40453 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40453 : Upper (D 7) (R 7) [96,260,129,48,192] 13 := by
  apply FastRouting.sound _ _ [96,260,129,48,192] 13 (by decide) (choices 1) [1,2,8] r40453 c40453
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29194
  · exact u29195
  · exact u29196

def b40454 : PairBound 9 := { available := 27, camps := [{ cop := 0, region := 8, targets := 130 },{ cop := 3, region := 1, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 97 262 133 104 146 59 91 155 283), lower := (rows 97 262 133 104 146 32 64 128 256), losses := [] }

theorem u40454 : Upper (D 7) (R 7) [96,260,129,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40454 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40455 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 8, targets := 130 },{ cop := 3, region := 1, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 97 262 133 104 152 51 83 147 275), lower := (rows 97 262 133 104 152 32 64 128 256), losses := [] }

theorem u40455 : Upper (D 7) (R 7) [96,260,129,96,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40455 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40456 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 16, targets := 224 },{ cop := 3, region := 241, targets := 2 }], pairs := [(0,1),(4,5),(4,6),(4,7)], upper := (rows 97 262 134 11 25 240 240 240 496), lower := (rows 97 262 134 11 25 32 64 128 256), losses := [] }

theorem u40456 : Upper (D 7) (R 7) [96,260,130,3,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40456 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40457 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 97 262 134 11 49 248 216 216 472), lower := (rows 97 262 134 11 49 32 64 128 256), losses := [] }

theorem u40457 : Upper (D 7) (R 7) [96,260,130,3,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40457 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40458 : Route 9 := (fun mask => (mask,id))

def c40458 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u40458 : Upper (D 7) (R 7) [96,260,130,3,40] 13 := by
  apply FastRouting.sound _ _ [96,260,130,3,40] 13 (by decide) (choices 1) [1,16,64,128] r40458 c40458
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29197
  · exact u29198
  · exact u29199
  · exact u29200

def b40459 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 16, targets := 130 },{ cop := 4, region := 1, targets := 130 }], pairs := [(0,1),(0,7),(4,1),(4,7)], upper := (rows 97 262 134 11 112 185 217 153 409), lower := (rows 97 262 134 11 112 32 64 128 256), losses := [] }

theorem u40459 : Upper (D 7) (R 7) [96,260,130,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40459 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40460 : Route 9 := (fun mask => (mask,id))

def c40460 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40460 : Upper (D 7) (R 7) [96,260,130,3,129] 13 := by
  apply FastRouting.sound _ _ [96,260,130,3,129] 13 (by decide) (choices 1) [8,16,64] r40460 c40460
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29201
  · exact u29202
  · exact u29203

def r40461 : Route 9 := (fun mask => (mask,id))

def c40461 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40461 : Upper (D 7) (R 7) [96,260,130,3,136] 13 := by
  apply FastRouting.sound _ _ [96,260,130,3,136] 13 (by decide) (choices 1) [1,16,64] r40461 c40461
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29204
  · exact u29205
  · exact u29206

def r40462 : Route 9 := (fun mask => (mask,id))

def c40462 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40462 : Upper (D 7) (R 7) [96,260,130,3,160] 13 := by
  apply FastRouting.sound _ _ [96,260,130,3,160] 13 (by decide) (choices 1) [1,8,16,64] r40462 c40462
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29207
  · exact u29208
  · exact u29209
  · exact u29210

def b40463 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 24, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 97 262 134 25 25 226 226 226 482), lower := (rows 97 262 134 25 25 32 64 128 256), losses := [] }

theorem u40463 : Upper (D 7) (R 7) [96,260,130,17,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40463 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40464 : Route 9 := (fun mask => (mask,id))

def c40464 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40464 : Upper (D 7) (R 7) [96,260,130,17,10] 13 := by
  apply FastRouting.sound _ _ [96,260,130,17,10] 13 (by decide) (choices 1) [1,64,128] r40464 c40464
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29211
  · exact u29212
  · exact u29213

def b40465 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 24, targets := 194 }], pairs := [(3,1),(3,6),(3,7),(4,1)], upper := (rows 97 262 134 25 49 234 202 202 458), lower := (rows 97 262 134 25 49 32 64 128 256), losses := [] }

theorem u40465 : Upper (D 7) (R 7) [96,260,130,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40465 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40466 : PairBound 9 := { available := 201, camps := [{ cop := 3, region := 454, targets := 32 },{ cop := 4, region := 201, targets := 2 }], pairs := [(0,1),(1,5),(2,5),(3,1)], upper := (rows 97 262 134 25 50 233 201 201 457), lower := (rows 97 262 134 25 50 32 64 128 256), losses := [] }

theorem u40466 : Upper (D 7) (R 7) [96,260,130,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40466 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40467 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 24, targets := 194 }], pairs := [(3,1),(3,6),(3,7),(4,1)], upper := (rows 97 262 134 25 56 227 195 195 451), lower := (rows 97 262 134 25 56 32 64 128 256), losses := [] }

theorem u40467 : Upper (D 7) (R 7) [96,260,130,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40467 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40468 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 24, targets := 130 }], pairs := [(3,1),(3,7),(4,1),(4,7)], upper := (rows 97 262 134 25 112 171 203 139 395), lower := (rows 97 262 134 25 112 32 64 128 256), losses := [] }

theorem u40468 : Upper (D 7) (R 7) [96,260,130,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40468 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40469 : PairBound 9 := { available := 106, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 97 262 134 25 145 106 106 234 362), lower := (rows 97 262 134 25 145 32 64 128 256), losses := [] }

theorem u40469 : Upper (D 7) (R 7) [96,260,130,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40469 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40470 : PairBound 9 := { available := 105, camps := [{ cop := 2, region := 16, targets := 97 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,5),(4,6)], upper := (rows 97 262 134 25 146 105 105 233 361), lower := (rows 97 262 134 25 146 32 64 128 256), losses := [] }

theorem u40470 : Upper (D 7) (R 7) [96,260,130,17,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40470 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40471 : Route 9 := (fun mask => (mask,id))

def c40471 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40471 : Upper (D 7) (R 7) [96,260,130,17,136] 13 := by
  apply FastRouting.sound _ _ [96,260,130,17,136] 13 (by decide) (choices 1) [1,2,64] r40471 c40471
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29214
  · exact u29215
  · exact u29216

def r40472 : Route 9 := (fun mask => (mask,id))

def c40472 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40472 : Upper (D 7) (R 7) [96,260,130,17,160] 13 := by
  apply FastRouting.sound _ _ [96,260,130,17,160] 13 (by decide) (choices 1) [1,2,8,64] r40472 c40472
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29217
  · exact u29218
  · exact u29219
  · exact u29220

def b40473 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 97 262 134 26 49 233 201 201 457), lower := (rows 97 262 134 26 49 32 64 128 256), losses := [] }

theorem u40473 : Upper (D 7) (R 7) [96,260,130,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40473 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40474 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 390, targets := 32 },{ cop := 3, region := 241, targets := 2 }], pairs := [(0,1),(1,5),(2,5),(4,1)], upper := (rows 97 262 134 26 56 225 193 193 449), lower := (rows 97 262 134 26 56 32 64 128 256), losses := [] }

theorem u40474 : Upper (D 7) (R 7) [96,260,130,18,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40474 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40475 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 16, targets := 130 },{ cop := 4, region := 1, targets := 130 }], pairs := [(0,1),(0,7),(4,1),(4,7)], upper := (rows 97 262 134 26 112 169 201 137 393), lower := (rows 97 262 134 26 112 32 64 128 256), losses := [] }

theorem u40475 : Upper (D 7) (R 7) [96,260,130,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40475 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40476 : Route 9 := (fun mask => (mask,id))

def c40476 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40476 : Upper (D 7) (R 7) [96,260,130,18,129] 13 := by
  apply FastRouting.sound _ _ [96,260,130,18,129] 13 (by decide) (choices 1) [1,8,64] r40476 c40476
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29221
  · exact u29222
  · exact u29223

def b40477 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 24, targets := 97 }], pairs := [(3,0),(3,5),(3,6),(4,0)], upper := (rows 97 262 134 26 152 97 97 225 353), lower := (rows 97 262 134 26 152 32 64 128 256), losses := [] }

theorem u40477 : Upper (D 7) (R 7) [96,260,130,18,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40477 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40478 : Route 9 := (fun mask => (mask,id))

def c40478 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40478 : Upper (D 7) (R 7) [96,260,130,18,160] 13 := by
  apply FastRouting.sound _ _ [96,260,130,18,160] 13 (by decide) (choices 1) [1,8,64] r40478 c40478
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29224
  · exact u29225
  · exact u29226

def b40479 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 97 262 134 41 82 185 217 153 409), lower := (rows 97 262 134 41 82 32 64 128 256), losses := [] }

theorem u40479 : Upper (D 7) (R 7) [96,260,130,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40479 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40480 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 24, targets := 130 }], pairs := [(3,1),(3,7),(4,1),(4,7)], upper := (rows 97 262 134 41 88 179 211 147 403), lower := (rows 97 262 134 41 88 32 64 128 256), losses := [] }

theorem u40480 : Upper (D 7) (R 7) [96,260,130,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40480 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40481 : PairBound 9 := { available := 90, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 97 262 134 41 145 122 90 218 346), lower := (rows 97 262 134 41 145 32 64 128 256), losses := [] }

theorem u40481 : Upper (D 7) (R 7) [96,260,130,33,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40481 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40482 : PairBound 9 := { available := 83, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 97 262 134 41 152 115 83 211 339), lower := (rows 97 262 134 41 152 32 64 128 256), losses := [] }

theorem u40482 : Upper (D 7) (R 7) [96,260,130,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40482 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40483 : PairBound 9 := { available := 27, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 97 262 134 41 208 59 91 155 283), lower := (rows 97 262 134 41 208 32 64 128 256), losses := [] }

theorem u40483 : Upper (D 7) (R 7) [96,260,130,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40483 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40484 : Route 9 := (fun mask => (mask,id))

def c40484 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40484 : Upper (D 7) (R 7) [96,260,130,34,72] 13 := by
  apply FastRouting.sound _ _ [96,260,130,34,72] 13 (by decide) (choices 1) [1,16,128] r40484 c40484
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29227
  · exact u29228
  · exact u29229

def r40485 : Route 9 := (fun mask => (mask,id))

def c40485 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40485 : Upper (D 7) (R 7) [96,260,130,34,129] 13 := by
  apply FastRouting.sound _ _ [96,260,130,34,129] 13 (by decide) (choices 1) [1,8,16,64] r40485 c40485
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29230
  · exact u29231
  · exact u29232
  · exact u29233

def r40486 : Route 9 := (fun mask => (mask,id))

def c40486 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40486 : Upper (D 7) (R 7) [96,260,130,34,136] 13 := by
  apply FastRouting.sound _ _ [96,260,130,34,136] 13 (by decide) (choices 1) [1,16,64] r40486 c40486
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29234
  · exact u29235
  · exact u29236

def r40487 : Route 9 := (fun mask => (mask,id))

def c40487 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40487 : Upper (D 7) (R 7) [96,260,130,34,192] 13 := by
  apply FastRouting.sound _ _ [96,260,130,34,192] 13 (by decide) (choices 1) [1,8,16] r40487 c40487
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29237
  · exact u29238
  · exact u29239

def b40488 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 24, targets := 130 }], pairs := [(3,1),(3,7),(4,1),(4,7)], upper := (rows 97 262 134 56 88 163 195 131 387), lower := (rows 97 262 134 56 88 32 64 128 256), losses := [] }

theorem u40488 : Upper (D 7) (R 7) [96,260,130,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40488 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40489 : Route 9 := (fun mask => (mask,id))

def c40489 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40489 : Upper (D 7) (R 7) [96,260,130,48,129] 13 := by
  apply FastRouting.sound _ _ [96,260,130,48,129] 13 (by decide) (choices 1) [1,2,8,64] r40489 c40489
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29240
  · exact u29241
  · exact u29242
  · exact u29243

def b40490 : PairBound 9 := { available := 73, camps := [{ cop := 2, region := 16, targets := 97 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,5),(4,6)], upper := (rows 97 262 134 56 146 105 73 201 329), lower := (rows 97 262 134 56 146 32 64 128 256), losses := [] }

theorem u40490 : Upper (D 7) (R 7) [96,260,130,48,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40490 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40491 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 390, targets := 32 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,5),(1,7),(2,5)], upper := (rows 97 262 134 56 152 99 67 195 323), lower := (rows 97 262 134 56 152 32 64 128 256), losses := [] }

theorem u40491 : Upper (D 7) (R 7) [96,260,130,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40491 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40492 : Route 9 := (fun mask => (mask,id))

def c40492 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40492 : Upper (D 7) (R 7) [96,260,130,48,192] 13 := by
  apply FastRouting.sound _ _ [96,260,130,48,192] 13 (by decide) (choices 1) [1,2,8] r40492 c40492
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29244
  · exact u29245
  · exact u29246

def b40493 : PairBound 9 := { available := 27, camps := [{ cop := 0, region := 8, targets := 130 },{ cop := 3, region := 1, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 97 262 134 104 145 59 91 155 283), lower := (rows 97 262 134 104 145 32 64 128 256), losses := [] }

theorem u40493 : Upper (D 7) (R 7) [96,260,130,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40493 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40494 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 8, targets := 130 },{ cop := 3, region := 1, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 97 262 134 104 152 51 83 147 275), lower := (rows 97 262 134 104 152 32 64 128 256), losses := [] }

theorem u40494 : Upper (D 7) (R 7) [96,260,130,96,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40494 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40495 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 16, targets := 224 },{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5),(4,5),(4,6),(4,7)], upper := (rows 97 262 140 11 19 240 240 240 496), lower := (rows 97 262 140 11 19 32 64 128 256), losses := [] }

theorem u40495 : Upper (D 7) (R 7) [96,260,136,3,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40495 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40496 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 97 262 140 11 49 242 210 210 466), lower := (rows 97 262 140 11 49 32 64 128 256), losses := [] }

theorem u40496 : Upper (D 7) (R 7) [96,260,136,3,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40496 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40497 : Route 9 := (fun mask => (mask,id))

def c40497 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u40497 : Upper (D 7) (R 7) [96,260,136,3,34] 13 := by
  apply FastRouting.sound _ _ [96,260,136,3,34] 13 (by decide) (choices 1) [1,16,64,128] r40497 c40497
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29247
  · exact u29248
  · exact u29249
  · exact u29250

def b40498 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 16, targets := 130 },{ cop := 4, region := 1, targets := 130 }], pairs := [(0,1),(0,7),(4,1),(4,7)], upper := (rows 97 262 140 11 112 179 211 147 403), lower := (rows 97 262 140 11 112 32 64 128 256), losses := [] }

theorem u40498 : Upper (D 7) (R 7) [96,260,136,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40498 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40499 : Route 9 := (fun mask => (mask,id))

def c40499 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40499 : Upper (D 7) (R 7) [96,260,136,3,129] 13 := by
  apply FastRouting.sound _ _ [96,260,136,3,129] 13 (by decide) (choices 1) [2,16,64] r40499 c40499
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29251
  · exact u29252
  · exact u29253

#print axioms u40499
end Delivery.IrregularNine14.P07

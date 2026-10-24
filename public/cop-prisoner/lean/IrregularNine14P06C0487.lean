import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0176
import IrregularNine14P06C0177

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b29220 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 4, region := 1, targets := 32 }], pairs := [(0,5),(4,5),(4,6)], upper := (rows 7 42 196 280 22 97 97 225 353), lower := (rows 7 42 196 280 22 32 64 128 256), losses := [] }

theorem u29220 : Upper (D 6) (R 6) [6,40,192,272,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29220
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29221 : PairBound 9 := { available := 71, camps := [{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 42 196 280 49 103 71 199 327), lower := (rows 7 42 196 280 49 32 64 128 256), losses := [{ target := 5, region := (rows 3 2 23 24 16 0 67 131 259), good := (rows 455 463 196 284 477 0 64 128 256) }] }

theorem u29221 : Upper (D 6) (R 6) [6,40,192,272,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29221
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29222 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 7 42 196 280 50 101 69 197 325), lower := (rows 7 42 196 280 50 32 64 128 256), losses := [] }

theorem u29222 : Upper (D 6) (R 6) [6,40,192,272,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29222
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29223 : Route 9 := (fun mask => (mask,id))

def c29223 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29223 : Upper (D 6) (R 6) [6,40,192,272,36] 13 := by
  apply FastRouting.sound _ _ [6,40,192,272,36] 13 (by decide) (choices 1) [1,2,64] r29223 c29223
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10608
  · exact u10609
  · exact u10610

def r29224 : Route 9 := (fun mask => (mask,id))

def c29224 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29224 : Upper (D 6) (R 6) [6,40,192,272,65] 13 := by
  apply FastRouting.sound _ _ [6,40,192,272,65] 13 (by decide) (choices 1) [1,2,4] r29224 c29224
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10611
  · exact u10612
  · exact u10613

def r29225 : Route 9 := (fun mask => (mask,id))

def c29225 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29225 : Upper (D 6) (R 6) [6,40,192,272,66] 13 := by
  apply FastRouting.sound _ _ [6,40,192,272,66] 13 (by decide) (choices 1) [1,4] r29225 c29225
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10614
  · exact u10615

def b29226 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 7 42 196 280 84 35 99 163 291), lower := (rows 7 42 196 280 84 32 64 128 256), losses := [] }

theorem u29226 : Upper (D 6) (R 6) [6,40,192,272,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29226
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29227 : Route 9 := (fun mask => (mask,id))

def c29227 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29227 : Upper (D 6) (R 6) [6,40,192,272,96] 13 := by
  apply FastRouting.sound _ _ [6,40,192,272,96] 13 (by decide) (choices 1) [1,2,4] r29227 c29227
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10616
  · exact u10617
  · exact u10618

def b29228 : PairBound 9 := { available := 53, camps := [{ cop := 0, region := 16, targets := 36 },{ cop := 4, region := 228, targets := 2 }], pairs := [(2,1),(4,2),(4,5)], upper := (rows 7 42 196 328 19 53 117 181 309), lower := (rows 7 42 196 328 19 32 64 128 256), losses := [] }

theorem u29228 : Upper (D 6) (R 6) [6,40,192,320,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29228
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29229 : PairBound 9 := { available := 51, camps := [{ cop := 0, region := 16, targets := 34 },{ cop := 4, region := 362, targets := 4 }], pairs := [(1,2),(4,1),(4,5)], upper := (rows 7 42 196 328 21 51 115 179 307), lower := (rows 7 42 196 328 21 32 64 128 256), losses := [] }

theorem u29229 : Upper (D 6) (R 6) [6,40,192,320,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29229
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29230 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 16, targets := 1 },{ cop := 0, region := 16, targets := 32 },{ cop := 0, region := 16, targets := 64 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 7 42 196 328 22 49 113 177 305), lower := (rows 7 42 196 328 22 32 64 128 256), losses := [] }

theorem u29230 : Upper (D 6) (R 6) [6,40,192,320,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29230
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29231 : Route 9 := (fun mask => (mask,id))

def c29231 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29231 : Upper (D 6) (R 6) [6,40,192,320,33] 13 := by
  apply FastRouting.sound _ _ [6,40,192,320,33] 13 (by decide) (choices 1) [1,2,4,16] r29231 c29231
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10619
  · exact u10620
  · exact u10621
  · exact u10622

def b29232 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 7 42 196 328 50 53 85 149 277), lower := (rows 7 42 196 328 50 32 64 128 256), losses := [] }

theorem u29232 : Upper (D 6) (R 6) [6,40,192,320,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29232
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29233 : Route 9 := (fun mask => (mask,id))

def c29233 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29233 : Upper (D 6) (R 6) [6,40,192,320,36] 13 := by
  apply FastRouting.sound _ _ [6,40,192,320,36] 13 (by decide) (choices 1) [1,2,16] r29233 c29233
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10623
  · exact u10624
  · exact u10625

def b29234 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 24, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 7 42 388 25 19 100 100 228 356), lower := (rows 7 42 388 25 19 32 64 128 256), losses := [] }

theorem u29234 : Upper (D 6) (R 6) [6,40,384,17,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29234
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29235 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 24, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 7 42 388 25 21 98 98 226 354), lower := (rows 7 42 388 25 21 32 64 128 256), losses := [] }

theorem u29235 : Upper (D 6) (R 6) [6,40,384,17,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29235
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29236 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 24, targets := 96 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 7 42 388 25 22 97 97 225 353), lower := (rows 7 42 388 25 22 32 64 128 256), losses := [] }

theorem u29236 : Upper (D 6) (R 6) [6,40,384,17,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29236
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29237 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 10, targets := 68 }], pairs := [(1,2),(1,6),(3,2)], upper := (rows 7 42 388 25 49 102 70 198 326), lower := (rows 7 42 388 25 49 32 64 128 256), losses := [] }

theorem u29237 : Upper (D 6) (R 6) [6,40,384,17,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29237
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29238 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 7 42 388 25 50 101 69 197 325), lower := (rows 7 42 388 25 50 32 64 128 256), losses := [] }

theorem u29238 : Upper (D 6) (R 6) [6,40,384,17,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29238
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29239 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 11, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 42 388 25 52 99 67 195 323), lower := (rows 7 42 388 25 52 32 64 128 256), losses := [] }

theorem u29239 : Upper (D 6) (R 6) [6,40,384,17,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29239
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29240 : PairBound 9 := { available := 102, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 7 42 388 25 81 102 102 230 358), lower := (rows 7 42 388 25 81 32 64 128 256), losses := [] }

theorem u29240 : Upper (D 6) (R 6) [6,40,384,17,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29240
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29241 : Route 9 := (fun mask => (mask,id))

def c29241 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29241 : Upper (D 6) (R 6) [6,40,384,17,66] 13 := by
  apply FastRouting.sound _ _ [6,40,384,17,66] 13 (by decide) (choices 1) [1,4,64] r29241 c29241
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10626
  · exact u10627
  · exact u10628

def r29242 : Route 9 := (fun mask => (mask,id))

def c29242 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29242 : Upper (D 6) (R 6) [6,40,384,17,68] 13 := by
  apply FastRouting.sound _ _ [6,40,384,17,68] 13 (by decide) (choices 1) [1,2,64] r29242 c29242
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10629
  · exact u10630
  · exact u10631

def r29243 : Route 9 := (fun mask => (mask,id))

def c29243 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29243 : Upper (D 6) (R 6) [6,40,384,17,96] 13 := by
  apply FastRouting.sound _ _ [6,40,384,17,96] 13 (by decide) (choices 1) [1,2,4,64] r29243 c29243
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10632
  · exact u10633
  · exact u10634
  · exact u10635

def b29244 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 24, targets := 96 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 7 42 388 26 21 97 97 225 353), lower := (rows 7 42 388 26 21 32 64 128 256), losses := [] }

theorem u29244 : Upper (D 6) (R 6) [6,40,384,18,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29244
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29245 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 10, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 388 26 49 101 69 197 325), lower := (rows 7 42 388 26 49 32 64 128 256), losses := [] }

theorem u29245 : Upper (D 6) (R 6) [6,40,384,18,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29245
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29246 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 10, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 42 388 26 52 97 65 193 321), lower := (rows 7 42 388 26 52 32 64 128 256), losses := [] }

theorem u29246 : Upper (D 6) (R 6) [6,40,384,18,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29246
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29247 : Route 9 := (fun mask => (mask,id))

def c29247 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29247 : Upper (D 6) (R 6) [6,40,384,18,65] 13 := by
  apply FastRouting.sound _ _ [6,40,384,18,65] 13 (by decide) (choices 1) [1,4,64] r29247 c29247
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10636
  · exact u10637
  · exact u10638

def r29248 : Route 9 := (fun mask => (mask,id))

def c29248 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29248 : Upper (D 6) (R 6) [6,40,384,18,68] 13 := by
  apply FastRouting.sound _ _ [6,40,384,18,68] 13 (by decide) (choices 1) [1,64] r29248 c29248
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10639
  · exact u10640

def b29249 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 10, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 388 26 112 101 69 197 325), lower := (rows 7 42 388 26 112 32 64 128 256), losses := [] }

theorem u29249 : Upper (D 6) (R 6) [6,40,384,18,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29249
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29250 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 24, targets := 96 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 7 42 388 28 19 97 97 225 353), lower := (rows 7 42 388 28 19 32 64 128 256), losses := [] }

theorem u29250 : Upper (D 6) (R 6) [6,40,384,20,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29250
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29251 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 453, targets := 32 },{ cop := 0, region := 112, targets := 4 }], pairs := [(0,5),(2,5),(4,2)], upper := (rows 7 42 388 28 49 99 67 195 323), lower := (rows 7 42 388 28 49 32 64 128 256), losses := [] }

theorem u29251 : Upper (D 6) (R 6) [6,40,384,20,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29251
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29252 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 7 42 388 28 50 97 65 193 321), lower := (rows 7 42 388 28 50 32 64 128 256), losses := [] }

theorem u29252 : Upper (D 6) (R 6) [6,40,384,20,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29252
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29253 : Route 9 := (fun mask => (mask,id))

def c29253 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29253 : Upper (D 6) (R 6) [6,40,384,20,65] 13 := by
  apply FastRouting.sound _ _ [6,40,384,20,65] 13 (by decide) (choices 1) [1,2,64] r29253 c29253
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10641
  · exact u10642
  · exact u10643

def r29254 : Route 9 := (fun mask => (mask,id))

def c29254 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29254 : Upper (D 6) (R 6) [6,40,384,20,66] 13 := by
  apply FastRouting.sound _ _ [6,40,384,20,66] 13 (by decide) (choices 1) [1,64] r29254 c29254
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10644
  · exact u10645

def b29255 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 453, targets := 32 },{ cop := 0, region := 112, targets := 4 }], pairs := [(0,5),(2,5),(4,2)], upper := (rows 7 42 388 28 112 99 67 195 323), lower := (rows 7 42 388 28 112 32 64 128 256), losses := [] }

theorem u29255 : Upper (D 6) (R 6) [6,40,384,20,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29255
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29256 : PairBound 9 := { available := 116, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 7 42 388 73 19 116 116 244 372), lower := (rows 7 42 388 73 19 32 64 128 256), losses := [] }

theorem u29256 : Upper (D 6) (R 6) [6,40,384,65,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29256
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29257 : PairBound 9 := { available := 114, camps := [{ cop := 0, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 7 42 388 73 21 114 114 242 370), lower := (rows 7 42 388 73 21 32 64 128 256), losses := [] }

theorem u29257 : Upper (D 6) (R 6) [6,40,384,65,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29257
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29258 : PairBound 9 := { available := 113, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 4, region := 1, targets := 32 }], pairs := [(0,5),(4,5),(4,6)], upper := (rows 7 42 388 73 22 113 113 241 369), lower := (rows 7 42 388 73 22 32 64 128 256), losses := [] }

theorem u29258 : Upper (D 6) (R 6) [6,40,384,65,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29258
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29259 : Route 9 := (fun mask => (mask,id))

def c29259 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29259 : Upper (D 6) (R 6) [6,40,384,65,33] 13 := by
  apply FastRouting.sound _ _ [6,40,384,65,33] 13 (by decide) (choices 1) [2,4,16,64] r29259 c29259
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10646
  · exact u10647
  · exact u10648
  · exact u10649

def b29260 : PairBound 9 := { available := 85, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 7 42 388 73 50 117 85 213 341), lower := (rows 7 42 388 73 50 32 64 128 256), losses := [] }

theorem u29260 : Upper (D 6) (R 6) [6,40,384,65,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29260
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29261 : Route 9 := (fun mask => (mask,id))

def c29261 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29261 : Upper (D 6) (R 6) [6,40,384,65,36] 13 := by
  apply FastRouting.sound _ _ [6,40,384,65,36] 13 (by decide) (choices 1) [1,2,16,64] r29261 c29261
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10650
  · exact u10651
  · exact u10652
  · exact u10653

def b29262 : PairBound 9 := { available := 54, camps := [{ cop := 3, region := 16, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 7 42 388 73 81 54 118 182 310), lower := (rows 7 42 388 73 81 32 64 128 256), losses := [] }

theorem u29262 : Upper (D 6) (R 6) [6,40,384,65,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29262
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29263 : Route 9 := (fun mask => (mask,id))

def c29263 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29263 : Upper (D 6) (R 6) [6,40,384,65,66] 13 := by
  apply FastRouting.sound _ _ [6,40,384,65,66] 13 (by decide) (choices 1) [1,4,16] r29263 c29263
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10654
  · exact u10655
  · exact u10656

def r29264 : Route 9 := (fun mask => (mask,id))

def c29264 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29264 : Upper (D 6) (R 6) [6,40,384,65,68] 13 := by
  apply FastRouting.sound _ _ [6,40,384,65,68] 13 (by decide) (choices 1) [1,2,16] r29264 c29264
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10657
  · exact u10658
  · exact u10659

def r29265 : Route 9 := (fun mask => (mask,id))

def c29265 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29265 : Upper (D 6) (R 6) [6,40,384,65,96] 13 := by
  apply FastRouting.sound _ _ [6,40,384,65,96] 13 (by decide) (choices 1) [1,2,4,16] r29265 c29265
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10660
  · exact u10661
  · exact u10662
  · exact u10663

def b29266 : PairBound 9 := { available := 113, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 16, targets := 32 }], pairs := [(2,1),(4,1),(4,5)], upper := (rows 7 42 388 74 21 113 113 241 369), lower := (rows 7 42 388 74 21 32 64 128 256), losses := [] }

theorem u29266 : Upper (D 6) (R 6) [6,40,384,66,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29266
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29267 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 4, region := 452, targets := 32 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 7 42 388 74 49 117 85 213 341), lower := (rows 7 42 388 74 49 32 64 128 256), losses := [] }

theorem u29267 : Upper (D 6) (R 6) [6,40,384,66,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29267
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29268 : Route 9 := (fun mask => (mask,id))

def c29268 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29268 : Upper (D 6) (R 6) [6,40,384,66,36] 13 := by
  apply FastRouting.sound _ _ [6,40,384,66,36] 13 (by decide) (choices 1) [1,16,64] r29268 c29268
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10664
  · exact u10665
  · exact u10666

def b29269 : PairBound 9 := { available := 53, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 4, region := 420, targets := 64 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 7 42 388 74 81 53 117 181 309), lower := (rows 7 42 388 74 81 32 64 128 256), losses := [] }

theorem u29269 : Upper (D 6) (R 6) [6,40,384,66,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29269
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29270 : Route 9 := (fun mask => (mask,id))

def c29270 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29270 : Upper (D 6) (R 6) [6,40,384,66,68] 13 := by
  apply FastRouting.sound _ _ [6,40,384,66,68] 13 (by decide) (choices 1) [1,16] r29270 c29270
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10667
  · exact u10668

def b29271 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 10, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 42 388 74 112 53 85 149 277), lower := (rows 7 42 388 74 112 32 64 128 256), losses := [] }

theorem u29271 : Upper (D 6) (R 6) [6,40,384,66,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29271
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29272 : PairBound 9 := { available := 113, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 4, region := 484, targets := 2 }], pairs := [(2,1),(4,5),(4,6)], upper := (rows 7 42 388 76 19 113 113 241 369), lower := (rows 7 42 388 76 19 32 64 128 256), losses := [] }

theorem u29272 : Upper (D 6) (R 6) [6,40,384,68,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29272
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29273 : Route 9 := (fun mask => (mask,id))

def c29273 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29273 : Upper (D 6) (R 6) [6,40,384,68,33] 13 := by
  apply FastRouting.sound _ _ [6,40,384,68,33] 13 (by decide) (choices 1) [1,2,16,64] r29273 c29273
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10669
  · exact u10670
  · exact u10671
  · exact u10672

def b29274 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 7 42 388 76 50 113 81 209 337), lower := (rows 7 42 388 76 50 32 64 128 256), losses := [] }

theorem u29274 : Upper (D 6) (R 6) [6,40,384,68,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29274
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29275 : Route 9 := (fun mask => (mask,id))

def c29275 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29275 : Upper (D 6) (R 6) [6,40,384,68,65] 13 := by
  apply FastRouting.sound _ _ [6,40,384,68,65] 13 (by decide) (choices 1) [1,2,16] r29275 c29275
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10673
  · exact u10674
  · exact u10675

def b29276 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 421, targets := 64 },{ cop := 0, region := 112, targets := 4 }], pairs := [(0,6),(2,6),(4,2)], upper := (rows 7 42 388 76 82 49 113 177 305), lower := (rows 7 42 388 76 82 32 64 128 256), losses := [] }

theorem u29276 : Upper (D 6) (R 6) [6,40,384,68,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29276
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29277 : Route 9 := (fun mask => (mask,id))

def c29277 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29277 : Upper (D 6) (R 6) [6,40,384,68,96] 13 := by
  apply FastRouting.sound _ _ [6,40,384,68,96] 13 (by decide) (choices 1) [1,2,16] r29277 c29277
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10676
  · exact u10677
  · exact u10678

def b29278 : PairBound 9 := { available := 101, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 7 42 388 88 19 101 101 229 357), lower := (rows 7 42 388 88 19 32 64 128 256), losses := [] }

theorem u29278 : Upper (D 6) (R 6) [6,40,384,80,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29278
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29279 : PairBound 9 := { available := 99, camps := [{ cop := 0, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 7 42 388 88 21 99 99 227 355), lower := (rows 7 42 388 88 21 32 64 128 256), losses := [] }

theorem u29279 : Upper (D 6) (R 6) [6,40,384,80,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29279
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u29279
end Delivery.IrregularNine14.P06

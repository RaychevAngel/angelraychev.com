import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0425
import IrregularNine14P06C0426

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r39240 : Route 9 := (fun mask => (mask,id))

def c39240 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39240 : Upper (D 6) (R 6) [40,48,192,65,260] 13 := by
  apply FastRouting.sound _ _ [40,48,192,65,260] 13 (by decide) (choices 1) [1,2,4] r39240 c39240
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25534
  · exact u25535
  · exact u25536

def r39241 : Route 9 := (fun mask => (mask,id))

def c39241 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39241 : Upper (D 6) (R 6) [40,48,192,66,257] 13 := by
  apply FastRouting.sound _ _ [40,48,192,66,257] 13 (by decide) (choices 1) [1,2,4] r39241 c39241
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25537
  · exact u25538
  · exact u25539

def b39242 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 165, targets := 2 },{ cop := 0, region := 196, targets := 32 }], pairs := [(0,1),(2,1),(2,5)], upper := (rows 41 50 196 74 274 37 69 133 261), lower := (rows 41 50 196 74 274 32 64 128 256), losses := [] }

theorem u39242 : Upper (D 6) (R 6) [40,48,192,66,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39242 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39243 : Route 9 := (fun mask => (mask,id))

def c39243 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39243 : Upper (D 6) (R 6) [40,48,192,66,260] 13 := by
  apply FastRouting.sound _ _ [40,48,192,66,260] 13 (by decide) (choices 1) [1,2,4] r39243 c39243
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25540
  · exact u25541
  · exact u25542

def b39244 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 41 50 196 76 273 39 71 135 263), lower := (rows 41 50 196 76 273 32 64 128 256), losses := [] }

theorem u39244 : Upper (D 6) (R 6) [40,48,192,68,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39244 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39245 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 41 50 196 76 274 39 71 135 263), lower := (rows 41 50 196 76 274 32 64 128 256), losses := [] }

theorem u39245 : Upper (D 6) (R 6) [40,48,192,68,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39245 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39246 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 41 50 196 76 276 35 67 131 259), lower := (rows 41 50 196 76 276 32 64 128 256), losses := [] }

theorem u39246 : Upper (D 6) (R 6) [40,48,192,68,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39246 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39247 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 50 388 11 21 102 70 198 326), lower := (rows 41 50 388 11 21 32 64 128 256), losses := [] }

theorem u39247 : Upper (D 6) (R 6) [40,48,384,3,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39247 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39248 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 50 388 11 22 101 69 197 325), lower := (rows 41 50 388 11 22 32 64 128 256), losses := [] }

theorem u39248 : Upper (D 6) (R 6) [40,48,384,3,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39248 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39249 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 50 388 11 81 102 70 198 326), lower := (rows 41 50 388 11 81 32 64 128 256), losses := [] }

theorem u39249 : Upper (D 6) (R 6) [40,48,384,3,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39249 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39250 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 50 388 11 82 101 69 197 325), lower := (rows 41 50 388 11 82 32 64 128 256), losses := [] }

theorem u39250 : Upper (D 6) (R 6) [40,48,384,3,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39250 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39251 : PairBound 9 := { available := 71, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 50 388 11 84 103 71 199 327), lower := (rows 41 50 388 11 84 32 64 128 256), losses := [] }

theorem u39251 : Upper (D 6) (R 6) [40,48,384,3,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39251 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39252 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 41 50 388 13 21 98 66 194 322), lower := (rows 41 50 388 13 21 32 64 128 256), losses := [] }

theorem u39252 : Upper (D 6) (R 6) [40,48,384,5,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39252 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39253 : PairBound 9 := { available := 67, camps := [], pairs := [(0,1),(1,0),(4,0)], upper := (rows 41 50 388 13 22 99 67 195 323), lower := (rows 41 50 388 13 22 32 64 128 256), losses := [{ target := 0, region := (rows 0 3 4 8 24 32 64 128 256), good := (rows 58 50 388 30 22 32 64 128 256) },{ target := 1, region := (rows 3 0 4 24 16 32 64 128 256), good := (rows 41 57 388 13 29 32 64 128 256) }] }

theorem u39253 : Upper (D 6) (R 6) [40,48,384,5,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39253 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39254 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 422, targets := 1 },{ cop := 1, region := 452, targets := 32 }], pairs := [(1,0),(2,0),(2,5)], upper := (rows 41 50 388 13 81 102 70 198 326), lower := (rows 41 50 388 13 81 32 64 128 256), losses := [] }

theorem u39254 : Upper (D 6) (R 6) [40,48,384,5,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39254 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39255 : Route 9 := (fun mask => (mask,id))

def c39255 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39255 : Upper (D 6) (R 6) [40,48,384,5,66] 13 := by
  apply FastRouting.sound _ _ [40,48,384,5,66] 13 (by decide) (choices 1) [1,2,4,64] r39255 c39255
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25543
  · exact u25544
  · exact u25545
  · exact u25546

def r39256 : Route 9 := (fun mask => (mask,id))

def c39256 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39256 : Upper (D 6) (R 6) [40,48,384,5,68] 13 := by
  apply FastRouting.sound _ _ [40,48,384,5,68] 13 (by decide) (choices 1) [1,2,64] r39256 c39256
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25547
  · exact u25548
  · exact u25549

def b39257 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 97, targets := 4 },{ cop := 4, region := 98, targets := 4 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 41 50 388 14 21 99 67 195 323), lower := (rows 41 50 388 14 21 32 64 128 256), losses := [{ target := 6, region := (rows 3 3 4 24 24 32 0 128 256), good := (rows 59 59 388 31 31 32 0 128 256) }] }

theorem u39257 : Upper (D 6) (R 6) [40,48,384,6,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39257 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39258 : Route 9 := (fun mask => (mask,id))

def c39258 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39258 : Upper (D 6) (R 6) [40,48,384,6,65] 13 := by
  apply FastRouting.sound _ _ [40,48,384,6,65] 13 (by decide) (choices 1) [1,2,4,64] r39258 c39258
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25550
  · exact u25551
  · exact u25552
  · exact u25553

def b39259 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 485, targets := 2 },{ cop := 0, region := 452, targets := 32 }], pairs := [(0,1),(2,1),(2,5)], upper := (rows 41 50 388 14 82 101 69 197 325), lower := (rows 41 50 388 14 82 32 64 128 256), losses := [] }

theorem u39259 : Upper (D 6) (R 6) [40,48,384,6,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39259 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39260 : Route 9 := (fun mask => (mask,id))

def c39260 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39260 : Upper (D 6) (R 6) [40,48,384,6,68] 13 := by
  apply FastRouting.sound _ _ [40,48,384,6,68] 13 (by decide) (choices 1) [1,2,64] r39260 c39260
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25554
  · exact u25555
  · exact u25556

def b39261 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 16, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 41 50 388 73 81 38 70 134 262), lower := (rows 41 50 388 73 81 32 64 128 256), losses := [] }

theorem u39261 : Upper (D 6) (R 6) [40,48,384,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39261 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39262 : PairBound 9 := { available := 7, camps := [], pairs := [(0,1),(1,0),(4,0)], upper := (rows 41 50 388 73 82 39 71 135 263), lower := (rows 41 50 388 73 82 32 64 128 256), losses := [{ target := 0, region := (rows 0 3 4 8 24 32 64 128 256), good := (rows 58 50 388 90 82 32 64 128 256) },{ target := 1, region := (rows 3 0 4 24 16 32 64 128 256), good := (rows 41 57 388 73 89 32 64 128 256) }] }

theorem u39262 : Upper (D 6) (R 6) [40,48,384,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39262 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39263 : Route 9 := (fun mask => (mask,id))

def c39263 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39263 : Upper (D 6) (R 6) [40,48,384,65,68] 13 := by
  apply FastRouting.sound _ _ [40,48,384,65,68] 13 (by decide) (choices 1) [1,2,4] r39263 c39263
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25557
  · exact u25558
  · exact u25559

def b39264 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 421, targets := 64 },{ cop := 4, region := 422, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 41 50 388 74 81 39 71 135 263), lower := (rows 41 50 388 74 81 32 64 128 256), losses := [] }

theorem u39264 : Upper (D 6) (R 6) [40,48,384,66,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39264 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39265 : Route 9 := (fun mask => (mask,id))

def c39265 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39265 : Upper (D 6) (R 6) [40,48,384,66,68] 13 := by
  apply FastRouting.sound _ _ [40,48,384,66,68] 13 (by decide) (choices 1) [1,2,4] r39265 c39265
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25560
  · exact u25561
  · exact u25562

def b39266 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 41 50 388 76 84 35 67 131 259), lower := (rows 41 50 388 76 84 32 64 128 256), losses := [] }

theorem u39266 : Upper (D 6) (R 6) [40,48,384,68,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39266 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39267 : PairBound 9 := { available := 388, camps := [{ cop := 2, region := 27, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 41 82 100 11 19 420 452 388 388), lower := (rows 41 82 100 11 19 32 64 128 256), losses := [] }

theorem u39267 : Upper (D 6) (R 6) [40,80,96,3,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39267 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39268 : PairBound 9 := { available := 390, camps := [{ cop := 4, region := 486, targets := 1 },{ cop := 4, region := 450, targets := 32 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 41 82 100 11 21 422 454 390 390), lower := (rows 41 82 100 11 21 32 64 128 256), losses := [] }

theorem u39268 : Upper (D 6) (R 6) [40,80,96,3,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39268 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39269 : PairBound 9 := { available := 389, camps := [{ cop := 2, region := 18, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 41 82 100 11 22 421 453 389 389), lower := (rows 41 82 100 11 22 32 64 128 256), losses := [] }

theorem u39269 : Upper (D 6) (R 6) [40,80,96,3,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39269 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39270 : Route 9 := (fun mask => (mask,id))

def c39270 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u39270 : Upper (D 6) (R 6) [40,80,96,3,129] 13 := by
  apply FastRouting.sound _ _ [40,80,96,3,129] 13 (by decide) (choices 1) [2,4,256] r39270 c39270
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25563
  · exact u25564
  · exact u25565

def r39271 : Route 9 := (fun mask => (mask,id))

def c39271 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u39271 : Upper (D 6) (R 6) [40,80,96,3,130] 13 := by
  apply FastRouting.sound _ _ [40,80,96,3,130] 13 (by decide) (choices 1) [1,4,256] r39271 c39271
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25566
  · exact u25567
  · exact u25568

def r39272 : Route 9 := (fun mask => (mask,id))

def c39272 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u39272 : Upper (D 6) (R 6) [40,80,96,3,132] 13 := by
  apply FastRouting.sound _ _ [40,80,96,3,132] 13 (by decide) (choices 1) [1,2,4,256] r39272 c39272
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25569
  · exact u25570
  · exact u25571
  · exact u25572

def r39273 : Route 9 := (fun mask => (mask,id))

def c39273 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39273 : Upper (D 6) (R 6) [40,80,96,3,384] 13 := by
  apply FastRouting.sound _ _ [40,80,96,3,384] 13 (by decide) (choices 1) [1,2,4] r39273 c39273
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25573
  · exact u25574
  · exact u25575

def b39274 : PairBound 9 := { available := 386, camps := [{ cop := 2, region := 9, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 82 100 13 21 418 450 386 386), lower := (rows 41 82 100 13 21 32 64 128 256), losses := [] }

theorem u39274 : Upper (D 6) (R 6) [40,80,96,5,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39274 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39275 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 9, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 82 100 13 145 294 326 390 262), lower := (rows 41 82 100 13 145 32 64 128 256), losses := [] }

theorem u39275 : Upper (D 6) (R 6) [40,80,96,5,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39275 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39276 : PairBound 9 := { available := 263, camps := [{ cop := 2, region := 9, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 82 100 13 146 295 327 391 263), lower := (rows 41 82 100 13 146 32 64 128 256), losses := [] }

theorem u39276 : Upper (D 6) (R 6) [40,80,96,5,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39276 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39277 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 9, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 82 100 13 148 291 323 387 259), lower := (rows 41 82 100 13 148 32 64 128 256), losses := [] }

theorem u39277 : Upper (D 6) (R 6) [40,80,96,5,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39277 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39278 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 9, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 82 100 13 400 39 71 135 263), lower := (rows 41 82 100 13 400 32 64 128 256), losses := [] }

theorem u39278 : Upper (D 6) (R 6) [40,80,96,5,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39278 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39279 : PairBound 9 := { available := 387, camps := [{ cop := 3, region := 433, targets := 64 },{ cop := 4, region := 450, targets := 32 }], pairs := [(0,6),(1,5),(4,6)], upper := (rows 41 82 100 14 21 419 451 387 387), lower := (rows 41 82 100 14 21 32 64 128 256), losses := [] }

theorem u39279 : Upper (D 6) (R 6) [40,80,96,6,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39279 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39280 : Route 9 := (fun mask => (mask,id))

def c39280 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u39280 : Upper (D 6) (R 6) [40,80,96,6,129] 13 := by
  apply FastRouting.sound _ _ [40,80,96,6,129] 13 (by decide) (choices 1) [1,2,4,256] r39280 c39280
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25576
  · exact u25577
  · exact u25578
  · exact u25579

def b39281 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 357, targets := 2 },{ cop := 3, region := 289, targets := 64 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 41 82 100 14 146 293 325 389 261), lower := (rows 41 82 100 14 146 32 64 128 256), losses := [] }

theorem u39281 : Upper (D 6) (R 6) [40,80,96,6,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39281 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39282 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 433, targets := 64 },{ cop := 3, region := 289, targets := 4 }], pairs := [(0,2),(0,6),(4,6)], upper := (rows 41 82 100 14 148 291 323 387 259), lower := (rows 41 82 100 14 148 32 64 128 256), losses := [] }

theorem u39282 : Upper (D 6) (R 6) [40,80,96,6,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39282 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39283 : Route 9 := (fun mask => (mask,id))

def c39283 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39283 : Upper (D 6) (R 6) [40,80,96,6,384] 13 := by
  apply FastRouting.sound _ _ [40,80,96,6,384] 13 (by decide) (choices 1) [1,2,4] r39283 c39283
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25580
  · exact u25581
  · exact u25582

def r39284 : Route 9 := (fun mask => (mask,id))

def c39284 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39284 : Upper (D 6) (R 6) [40,80,96,129,257] 13 := by
  apply FastRouting.sound _ _ [40,80,96,129,257] 13 (by decide) (choices 1) [2,4] r39284 c39284
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25583
  · exact u25584

def r39285 : Route 9 := (fun mask => (mask,id))

def c39285 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39285 : Upper (D 6) (R 6) [40,80,96,129,258] 13 := by
  apply FastRouting.sound _ _ [40,80,96,129,258] 13 (by decide) (choices 1) [1,2,4] r39285 c39285
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25585
  · exact u25586
  · exact u25587

def r39286 : Route 9 := (fun mask => (mask,id))

def c39286 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39286 : Upper (D 6) (R 6) [40,80,96,129,260] 13 := by
  apply FastRouting.sound _ _ [40,80,96,129,260] 13 (by decide) (choices 1) [1,2,4] r39286 c39286
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25588
  · exact u25589
  · exact u25590

def r39287 : Route 9 := (fun mask => (mask,id))

def c39287 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39287 : Upper (D 6) (R 6) [40,80,96,130,257] 13 := by
  apply FastRouting.sound _ _ [40,80,96,130,257] 13 (by decide) (choices 1) [1,2,4] r39287 c39287
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25591
  · exact u25592
  · exact u25593

def r39288 : Route 9 := (fun mask => (mask,id))

def c39288 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39288 : Upper (D 6) (R 6) [40,80,96,130,260] 13 := by
  apply FastRouting.sound _ _ [40,80,96,130,260] 13 (by decide) (choices 1) [1,2,4] r39288 c39288
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25594
  · exact u25595
  · exact u25596

def r39289 : Route 9 := (fun mask => (mask,id))

def c39289 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39289 : Upper (D 6) (R 6) [40,80,96,132,260] 13 := by
  apply FastRouting.sound _ _ [40,80,96,132,260] 13 (by decide) (choices 1) [1,2] r39289 c39289
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25597
  · exact u25598

def b39290 : PairBound 9 := { available := 356, camps := [{ cop := 2, region := 370, targets := 1 },{ cop := 3, region := 485, targets := 2 }], pairs := [(0,1),(1,0),(4,0)], upper := (rows 41 82 133 11 22 356 356 484 356), lower := (rows 41 82 133 11 22 32 64 128 256), losses := [] }

theorem u39290 : Upper (D 6) (R 6) [40,80,129,3,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39290 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39291 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 82 133 11 50 356 324 452 324), lower := (rows 41 82 133 11 50 32 64 128 256), losses := [] }

theorem u39291 : Upper (D 6) (R 6) [40,80,129,3,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39291 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39292 : PairBound 9 := { available := 326, camps := [{ cop := 2, region := 370, targets := 1 },{ cop := 3, region := 452, targets := 32 }], pairs := [(1,0),(2,5),(4,0)], upper := (rows 41 82 133 11 52 358 326 454 326), lower := (rows 41 82 133 11 52 32 64 128 256), losses := [] }

theorem u39292 : Upper (D 6) (R 6) [40,80,129,3,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39292 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39293 : PairBound 9 := { available := 292, camps := [{ cop := 6, region := 18, targets := 37 }], pairs := [(1,0),(1,2),(1,5)], upper := (rows 41 82 133 11 82 292 356 420 292), lower := (rows 41 82 133 11 82 32 64 128 256), losses := [] }

theorem u39293 : Upper (D 6) (R 6) [40,80,129,3,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39293 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39294 : PairBound 9 := { available := 294, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 82 133 11 84 294 358 422 294), lower := (rows 41 82 133 11 84 32 64 128 256), losses := [] }

theorem u39294 : Upper (D 6) (R 6) [40,80,129,3,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39294 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39295 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 82 133 11 112 294 326 390 262), lower := (rows 41 82 133 11 112 32 64 128 256), losses := [] }

theorem u39295 : Upper (D 6) (R 6) [40,80,129,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39295 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39296 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 370, targets := 1 },{ cop := 3, region := 229, targets := 2 }], pairs := [(0,1),(1,0),(4,0)], upper := (rows 41 82 133 11 274 100 100 228 356), lower := (rows 41 82 133 11 274 32 64 128 256), losses := [] }

theorem u39296 : Upper (D 6) (R 6) [40,80,129,3,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39296 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39297 : Route 9 := (fun mask => (mask,id))

def c39297 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39297 : Upper (D 6) (R 6) [40,80,129,3,260] 13 := by
  apply FastRouting.sound _ _ [40,80,129,3,260] 13 (by decide) (choices 1) [2,4,64] r39297 c39297
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25599
  · exact u25600
  · exact u25601

def b39298 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 370, targets := 1 },{ cop := 3, region := 196, targets := 32 }], pairs := [(1,0),(2,5),(4,0)], upper := (rows 41 82 133 11 304 102 70 198 326), lower := (rows 41 82 133 11 304 32 64 128 256), losses := [] }

theorem u39298 : Upper (D 6) (R 6) [40,80,129,3,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39298 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39299 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 173, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 82 133 11 336 38 102 166 294), lower := (rows 41 82 133 11 336 32 64 128 256), losses := [] }

theorem u39299 : Upper (D 6) (R 6) [40,80,129,3,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39299 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u39299
end Delivery.IrregularNine14.P06

import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0426
import IrregularNine14P07C0427

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r38340 : Route 9 := (fun mask => (mask,id))

def c38340 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38340 : Upper (D 7) (R 7) [36,192,264,96,129] 13 := by
  apply FastRouting.sound _ _ [36,192,264,96,129] 13 (by decide) (choices 1) [1,2,16] r38340 c38340
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25565
  · exact u25566
  · exact u25567

def b38341 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 16, targets := 97 },{ cop := 4, region := 365, targets := 128 }], pairs := [(0,7),(4,0),(4,5),(4,6)], upper := (rows 37 194 268 104 146 51 83 147 275), lower := (rows 37 194 268 104 146 32 64 128 256), losses := [] }

theorem u38341 : Upper (D 7) (R 7) [36,192,264,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38341 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38342 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 16, targets := 160 },{ cop := 4, region := 8, targets := 160 }], pairs := [(3,5),(3,7),(4,5),(4,7)], upper := (rows 37 194 324 11 19 184 248 184 440), lower := (rows 37 194 324 11 19 32 64 128 256), losses := [] }

theorem u38342 : Upper (D 7) (R 7) [36,192,320,3,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38342 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38343 : PairBound 9 := { available := 178, camps := [{ cop := 3, region := 16, targets := 162 },{ cop := 4, region := 226, targets := 1 }], pairs := [(1,0),(4,1),(4,5),(4,7)], upper := (rows 37 194 324 11 25 178 242 178 434), lower := (rows 37 194 324 11 25 32 64 128 256), losses := [] }

theorem u38343 : Upper (D 7) (R 7) [36,192,320,3,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38343 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38344 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 16, targets := 161 },{ cop := 4, region := 485, targets := 2 }], pairs := [(0,1),(4,0),(4,5),(4,7)], upper := (rows 37 194 324 11 26 177 241 177 433), lower := (rows 37 194 324 11 26 32 64 128 256), losses := [] }

theorem u38344 : Upper (D 7) (R 7) [36,192,320,3,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38344 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38345 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 202, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 194 324 11 49 186 218 154 410), lower := (rows 37 194 324 11 49 32 64 128 256), losses := [] }

theorem u38345 : Upper (D 7) (R 7) [36,192,320,3,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38345 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38346 : Route 9 := (fun mask => (mask,id))

def c38346 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38346 : Upper (D 7) (R 7) [36,192,320,3,34] 13 := by
  apply FastRouting.sound _ _ [36,192,320,3,34] 13 (by decide) (choices 1) [1,8,16,128] r38346 c38346
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25568
  · exact u25569
  · exact u25570
  · exact u25571

def r38347 : Route 9 := (fun mask => (mask,id))

def c38347 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38347 : Upper (D 7) (R 7) [36,192,320,3,40] 13 := by
  apply FastRouting.sound _ _ [36,192,320,3,40] 13 (by decide) (choices 1) [1,2,16,128] r38347 c38347
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25572
  · exact u25573
  · exact u25574
  · exact u25575

def r38348 : Route 9 := (fun mask => (mask,id))

def c38348 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38348 : Upper (D 7) (R 7) [36,192,320,3,129] 13 := by
  apply FastRouting.sound _ _ [36,192,320,3,129] 13 (by decide) (choices 1) [2,8,16] r38348 c38348
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25576
  · exact u25577
  · exact u25578

def b38349 : PairBound 9 := { available := 57, camps := [{ cop := 1, region := 16, targets := 97 },{ cop := 4, region := 365, targets := 128 }], pairs := [(0,7),(4,0),(4,5),(4,6)], upper := (rows 37 194 324 11 146 57 121 185 313), lower := (rows 37 194 324 11 146 32 64 128 256), losses := [] }

theorem u38349 : Upper (D 7) (R 7) [36,192,320,3,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38349 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38350 : Route 9 := (fun mask => (mask,id))

def c38350 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38350 : Upper (D 7) (R 7) [36,192,320,3,136] 13 := by
  apply FastRouting.sound _ _ [36,192,320,3,136] 13 (by decide) (choices 1) [1,2,16] r38350 c38350
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25579
  · exact u25580
  · exact u25581

def r38351 : Route 9 := (fun mask => (mask,id))

def c38351 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38351 : Upper (D 7) (R 7) [36,192,320,3,160] 13 := by
  apply FastRouting.sound _ _ [36,192,320,3,160] 13 (by decide) (choices 1) [1,2,8,16] r38351 c38351
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25582
  · exact u25583
  · exact u25584
  · exact u25585

def b38352 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 24, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 37 194 324 25 25 162 226 162 418), lower := (rows 37 194 324 25 25 32 64 128 256), losses := [] }

theorem u38352 : Upper (D 7) (R 7) [36,192,320,17,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38352 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38353 : Route 9 := (fun mask => (mask,id))

def c38353 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38353 : Upper (D 7) (R 7) [36,192,320,17,10] 13 := by
  apply FastRouting.sound _ _ [36,192,320,17,10] 13 (by decide) (choices 1) [1,2,128] r38353 c38353
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25586
  · exact u25587
  · exact u25588

def b38354 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 24, targets := 194 }], pairs := [(3,1),(3,6),(3,7),(4,1)], upper := (rows 37 194 324 25 49 170 202 138 394), lower := (rows 37 194 324 25 49 32 64 128 256), losses := [] }

theorem u38354 : Upper (D 7) (R 7) [36,192,320,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38354 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38355 : Route 9 := (fun mask => (mask,id))

def c38355 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38355 : Upper (D 7) (R 7) [36,192,320,17,34] 13 := by
  apply FastRouting.sound _ _ [36,192,320,17,34] 13 (by decide) (choices 1) [1,2,8,128] r38355 c38355
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25589
  · exact u25590
  · exact u25591
  · exact u25592

def b38356 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 24, targets := 194 }], pairs := [(3,1),(3,6),(3,7),(4,1)], upper := (rows 37 194 324 25 56 163 195 131 387), lower := (rows 37 194 324 25 56 32 64 128 256), losses := [] }

theorem u38356 : Upper (D 7) (R 7) [36,192,320,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38356 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38357 : PairBound 9 := { available := 42, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 37 194 324 25 145 42 106 170 298), lower := (rows 37 194 324 25 145 32 64 128 256), losses := [] }

theorem u38357 : Upper (D 7) (R 7) [36,192,320,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38357 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38358 : PairBound 9 := { available := 43, camps := [{ cop := 1, region := 16, targets := 97 },{ cop := 4, region := 365, targets := 128 }], pairs := [(0,7),(4,0),(4,5),(4,6)], upper := (rows 37 194 324 25 146 43 107 171 299), lower := (rows 37 194 324 25 146 32 64 128 256), losses := [] }

theorem u38358 : Upper (D 7) (R 7) [36,192,320,17,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38358 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38359 : Route 9 := (fun mask => (mask,id))

def c38359 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38359 : Upper (D 7) (R 7) [36,192,320,17,136] 13 := by
  apply FastRouting.sound _ _ [36,192,320,17,136] 13 (by decide) (choices 1) [1,2] r38359 c38359
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25593
  · exact u25594

def r38360 : Route 9 := (fun mask => (mask,id))

def c38360 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38360 : Upper (D 7) (R 7) [36,192,320,17,160] 13 := by
  apply FastRouting.sound _ _ [36,192,320,17,160] 13 (by decide) (choices 1) [1,2,8] r38360 c38360
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25595
  · exact u25596
  · exact u25597

def b38361 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 24, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 37 194 324 26 26 161 225 161 417), lower := (rows 37 194 324 26 26 32 64 128 256), losses := [] }

theorem u38361 : Upper (D 7) (R 7) [36,192,320,18,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38361 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38362 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 202, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 194 324 26 49 171 203 139 395), lower := (rows 37 194 324 26 49 32 64 128 256), losses := [] }

theorem u38362 : Upper (D 7) (R 7) [36,192,320,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38362 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38363 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 37 194 324 26 50 169 201 137 393), lower := (rows 37 194 324 26 50 32 64 128 256), losses := [] }

theorem u38363 : Upper (D 7) (R 7) [36,192,320,18,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38363 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38364 : Route 9 := (fun mask => (mask,id))

def c38364 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38364 : Upper (D 7) (R 7) [36,192,320,18,40] 13 := by
  apply FastRouting.sound _ _ [36,192,320,18,40] 13 (by decide) (choices 1) [1,2,128] r38364 c38364
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25598
  · exact u25599
  · exact u25600

def r38365 : Route 9 := (fun mask => (mask,id))

def c38365 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38365 : Upper (D 7) (R 7) [36,192,320,18,129] 13 := by
  apply FastRouting.sound _ _ [36,192,320,18,129] 13 (by decide) (choices 1) [1,2,8] r38365 c38365
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25601
  · exact u25602
  · exact u25603

def b38366 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 24, targets := 97 }], pairs := [(3,0),(3,5),(3,6),(4,0)], upper := (rows 37 194 324 26 146 41 105 169 297), lower := (rows 37 194 324 26 146 32 64 128 256), losses := [] }

theorem u38366 : Upper (D 7) (R 7) [36,192,320,18,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38366 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38367 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 24, targets := 97 }], pairs := [(3,0),(3,5),(3,6),(4,0)], upper := (rows 37 194 324 26 152 35 99 163 291), lower := (rows 37 194 324 26 152 32 64 128 256), losses := [] }

theorem u38367 : Upper (D 7) (R 7) [36,192,320,18,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38367 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38368 : Route 9 := (fun mask => (mask,id))

def c38368 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38368 : Upper (D 7) (R 7) [36,192,320,18,160] 13 := by
  apply FastRouting.sound _ _ [36,192,320,18,160] 13 (by decide) (choices 1) [1,2,8] r38368 c38368
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25604
  · exact u25605
  · exact u25606

def b38369 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 210, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 194 324 41 145 58 90 154 282), lower := (rows 37 194 324 41 145 32 64 128 256), losses := [] }

theorem u38369 : Upper (D 7) (R 7) [36,192,320,33,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38369 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38370 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 210, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 194 324 41 152 51 83 147 275), lower := (rows 37 194 324 41 152 32 64 128 256), losses := [] }

theorem u38370 : Upper (D 7) (R 7) [36,192,320,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38370 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38371 : Route 9 := (fun mask => (mask,id))

def c38371 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38371 : Upper (D 7) (R 7) [36,192,320,34,129] 13 := by
  apply FastRouting.sound _ _ [36,192,320,34,129] 13 (by decide) (choices 1) [1,2,8,16] r38371 c38371
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25607
  · exact u25608
  · exact u25609
  · exact u25610

def b38372 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 16, targets := 97 },{ cop := 4, region := 365, targets := 128 }], pairs := [(0,7),(4,0),(4,5),(4,6)], upper := (rows 37 194 324 42 146 57 89 153 281), lower := (rows 37 194 324 42 146 32 64 128 256), losses := [] }

theorem u38372 : Upper (D 7) (R 7) [36,192,320,34,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38372 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38373 : Route 9 := (fun mask => (mask,id))

def c38373 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38373 : Upper (D 7) (R 7) [36,192,320,34,136] 13 := by
  apply FastRouting.sound _ _ [36,192,320,34,136] 13 (by decide) (choices 1) [1,2,16] r38373 c38373
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25611
  · exact u25612
  · exact u25613

def r38374 : Route 9 := (fun mask => (mask,id))

def c38374 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38374 : Upper (D 7) (R 7) [36,192,320,48,129] 13 := by
  apply FastRouting.sound _ _ [36,192,320,48,129] 13 (by decide) (choices 1) [1,2,8] r38374 c38374
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25614
  · exact u25615
  · exact u25616

def b38375 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 16, targets := 97 },{ cop := 4, region := 365, targets := 128 }], pairs := [(0,7),(4,0),(4,5),(4,6)], upper := (rows 37 194 324 56 146 43 75 139 267), lower := (rows 37 194 324 56 146 32 64 128 256), losses := [] }

theorem u38375 : Upper (D 7) (R 7) [36,192,320,48,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38375 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38376 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 1, region := 293, targets := 128 }], pairs := [(0,7),(1,5),(2,5),(2,7)], upper := (rows 37 194 324 56 152 35 67 131 259), lower := (rows 37 194 324 56 152 32 64 128 256), losses := [] }

theorem u38376 : Upper (D 7) (R 7) [36,192,320,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38376 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38377 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 13, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 259 13 26 50 224 192 192 448), lower := (rows 37 259 13 26 50 32 64 128 256), losses := [] }

theorem u38377 : Upper (D 7) (R 7) [36,257,9,18,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38377 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38378 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 8, targets := 224 },{ cop := 1, region := 248, targets := 1 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 37 259 13 26 82 224 224 224 480), lower := (rows 37 259 13 26 82 32 64 128 256), losses := [] }

theorem u38378 : Upper (D 7) (R 7) [36,257,9,18,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38378 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38379 : Route 9 := (fun mask => (mask,id))

def c38379 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38379 : Upper (D 7) (R 7) [36,257,9,18,96] 13 := by
  apply FastRouting.sound _ _ [36,257,9,18,96] 13 (by decide) (choices 1) [2,64,128] r38379 c38379
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25617
  · exact u25618
  · exact u25619

def r38380 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c38380 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38380 : Upper (D 7) (R 7) [36,257,9,18,192] 13 := by
  apply FastRouting.sound _ _ [36,257,9,18,192] 13 (by decide) (choices 1) [2,64] r38380 c38380
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25620
  · exact u25621

def r38381 : Route 9 := (fun mask => (mask,id))

def c38381 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u38381 : Upper (D 7) (R 7) [36,257,9,66,34] 13 := by
  apply FastRouting.sound _ _ [36,257,9,66,34] 13 (by decide) (choices 1) [16,64,128] r38381 c38381
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25622
  · exact u25623
  · exact u25624

def b38382 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 248, targets := 1 },{ cop := 3, region := 16, targets := 160 }], pairs := [(3,0),(4,0),(4,5),(4,7)], upper := (rows 37 259 13 74 82 176 240 176 432), lower := (rows 37 259 13 74 82 32 64 128 256), losses := [] }

theorem u38382 : Upper (D 7) (R 7) [36,257,9,66,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38382 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38383 : Route 9 := (fun mask => (mask,id))

def c38383 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38383 : Upper (D 7) (R 7) [36,257,9,66,96] 13 := by
  apply FastRouting.sound _ _ [36,257,9,66,96] 13 (by decide) (choices 1) [2,16,128] r38383 c38383
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25625
  · exact u25626
  · exact u25627

def r38384 : Route 9 := (fun mask => (mask,id))

def c38384 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u38384 : Upper (D 7) (R 7) [36,257,9,66,130] 13 := by
  apply FastRouting.sound _ _ [36,257,9,66,130] 13 (by decide) (choices 1) [16,64,128] r38384 c38384
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25628
  · exact u25629
  · exact u25630

def r38385 : Route 9 := (fun mask => (mask,id))

def c38385 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u38385 : Upper (D 7) (R 7) [36,257,9,66,160] 13 := by
  apply FastRouting.sound _ _ [36,257,9,66,160] 13 (by decide) (choices 1) [2,16,64,128] r38385 c38385
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25631
  · exact u25632
  · exact u25633
  · exact u25634

def r38386 : Route 9 := (fun mask => (mask,id))

def c38386 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38386 : Upper (D 7) (R 7) [36,257,9,66,192] 13 := by
  apply FastRouting.sound _ _ [36,257,9,66,192] 13 (by decide) (choices 1) [2,16,128] r38386 c38386
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25635
  · exact u25636
  · exact u25637

def b38387 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 248, targets := 1 },{ cop := 0, region := 450, targets := 32 },{ cop := 4, region := 200, targets := 32 }], pairs := [(1,5),(3,0),(3,5),(4,0)], upper := (rows 37 259 13 88 50 226 194 194 450), lower := (rows 37 259 13 88 50 32 64 128 256), losses := [] }

theorem u38387 : Upper (D 7) (R 7) [36,257,9,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38387 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38388 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 423, targets := 64 },{ cop := 4, region := 8, targets := 2 }], pairs := [(0,6),(1,6),(2,6),(3,1)], upper := (rows 37 259 13 88 82 162 226 162 418), lower := (rows 37 259 13 88 82 32 64 128 256), losses := [] }

theorem u38388 : Upper (D 7) (R 7) [36,257,9,80,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38388 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38389 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 13, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 259 13 88 112 162 194 130 386), lower := (rows 37 259 13 88 112 32 64 128 256), losses := [] }

theorem u38389 : Upper (D 7) (R 7) [36,257,9,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38389 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38390 : Route 9 := (fun mask => (mask,id))

def c38390 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38390 : Upper (D 7) (R 7) [36,257,9,80,130] 13 := by
  apply FastRouting.sound _ _ [36,257,9,80,130] 13 (by decide) (choices 1) [2,64,128] r38390 c38390
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25638
  · exact u25639
  · exact u25640

def r38391 : Route 9 := (fun mask => (mask,id))

def c38391 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38391 : Upper (D 7) (R 7) [36,257,9,80,160] 13 := by
  apply FastRouting.sound _ _ [36,257,9,80,160] 13 (by decide) (choices 1) [2,64,128] r38391 c38391
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25641
  · exact u25642
  · exact u25643

def b38392 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 37 259 13 88 208 162 226 162 418), lower := (rows 37 259 13 88 208 32 64 128 256), losses := [] }

theorem u38392 : Upper (D 7) (R 7) [36,257,9,80,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38392 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38393 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c38393 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u38393 : Upper (D 7) (R 7) [36,257,9,192,34] 13 := by
  apply FastRouting.sound _ _ [36,257,9,192,34] 13 (by decide) (choices 1) [2,16,64] r38393 c38393
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25644
  · exact u25645
  · exact u25646

def r38394 : Route 9 := (fun mask => (mask,id))

def c38394 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38394 : Upper (D 7) (R 7) [36,257,9,192,66] 13 := by
  apply FastRouting.sound _ _ [36,257,9,192,66] 13 (by decide) (choices 1) [2,16,128] r38394 c38394
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25647
  · exact u25648
  · exact u25649

def r38395 : Route 9 := (fun mask => (mask,id))

def c38395 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38395 : Upper (D 7) (R 7) [36,257,9,192,96] 13 := by
  apply FastRouting.sound _ _ [36,257,9,192,96] 13 (by decide) (choices 1) [2,16,128] r38395 c38395
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25650
  · exact u25651
  · exact u25652

def b38396 : PairBound 9 := { available := 50, camps := [{ cop := 3, region := 16, targets := 35 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,1),(4,5)], upper := (rows 37 259 13 200 208 50 114 178 306), lower := (rows 37 259 13 200 208 32 64 128 256), losses := [] }

theorem u38396 : Upper (D 7) (R 7) [36,257,9,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38396 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38397 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 13, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 259 14 25 50 224 192 192 448), lower := (rows 37 259 14 25 50 32 64 128 256), losses := [] }

theorem u38397 : Upper (D 7) (R 7) [36,257,10,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38397 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38398 : Route 9 := (fun mask => (mask,id))

def c38398 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38398 : Upper (D 7) (R 7) [36,257,10,17,66] 13 := by
  apply FastRouting.sound _ _ [36,257,10,17,66] 13 (by decide) (choices 1) [64,128] r38398 c38398
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25653
  · exact u25654

def r38399 : Route 9 := (fun mask => (mask,id))

def c38399 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38399 : Upper (D 7) (R 7) [36,257,10,17,96] 13 := by
  apply FastRouting.sound _ _ [36,257,10,17,96] 13 (by decide) (choices 1) [2,64,128] r38399 c38399
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25655
  · exact u25656
  · exact u25657

#print axioms u38399
end Delivery.IrregularNine14.P07

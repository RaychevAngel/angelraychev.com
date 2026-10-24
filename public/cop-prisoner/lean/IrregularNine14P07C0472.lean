import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0176
import IrregularNine14P07C0177

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r28320 : Route 9 := (fun mask => (mask,id))

def c28320 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28320 : Upper (D 7) (R 7) [96,160,24,66,384,2] 13 := by
  apply FastRouting.sound _ _ [96,160,24,66,384,2] 13 (by decide) (choices 1) [1,4] r28320 c28320
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10594
  · exact u10595

def b28321 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 402, targets := 64 },{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7),(1,6),(4,6)], upper := (rows 97 162 28 74 400 36 67 131 259), lower := (rows 97 162 28 74 400 36 64 128 256), losses := [] }

theorem u28321 : Upper (D 7) (R 7) [96,160,24,66,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28321 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28322 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 402, targets := 64 },{ cop := 3, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(1,6),(4,6)], upper := (rows 97 162 28 76 273 33 194 130 386), lower := (rows 97 162 28 76 273 33 64 128 256), losses := [] }

theorem u28322 : Upper (D 7) (R 7) [96,160,24,68,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28322 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28323 : Route 9 := (fun mask => (mask,id))

def c28323 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28323 : Upper (D 7) (R 7) [96,160,24,68,257,2] 13 := by
  apply FastRouting.sound _ _ [96,160,24,68,257,2] 13 (by decide) (choices 1) [1,2,128] r28323 c28323
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10596
  · exact u10597
  · exact u10598

def b28324 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 97 162 28 76 273 160 67 131 259), lower := (rows 97 162 28 76 273 160 64 128 256), losses := [] }

theorem u28324 : Upper (D 7) (R 7) [96,160,24,68,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28324 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28325 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 402, targets := 64 },{ cop := 3, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(1,6),(4,6)], upper := (rows 97 162 28 76 274 33 195 131 387), lower := (rows 97 162 28 76 274 33 64 128 256), losses := [] }

theorem u28325 : Upper (D 7) (R 7) [96,160,24,68,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28325 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28326 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 402, targets := 64 },{ cop := 1, region := 65, targets := 2 },{ cop := 7, region := 34, targets := 1 }], pairs := [(0,1),(1,0),(1,6),(4,6)], upper := (rows 97 162 28 76 274 34 193 129 385), lower := (rows 97 162 28 76 274 34 64 128 256), losses := [] }

theorem u28326 : Upper (D 7) (R 7) [96,160,24,68,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28326 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28327 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 97 162 28 76 274 160 67 131 259), lower := (rows 97 162 28 76 274 160 64 128 256), losses := [] }

theorem u28327 : Upper (D 7) (R 7) [96,160,24,68,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28327 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28328 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 402, targets := 64 },{ cop := 3, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(1,6),(4,6)], upper := (rows 97 162 28 76 400 33 67 131 259), lower := (rows 97 162 28 76 400 33 64 128 256), losses := [] }

theorem u28328 : Upper (D 7) (R 7) [96,160,24,68,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28328 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28329 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 402, targets := 64 },{ cop := 1, region := 65, targets := 128 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,6),(4,6)], upper := (rows 97 162 28 76 400 34 67 131 259), lower := (rows 97 162 28 76 400 34 64 128 256), losses := [] }

theorem u28329 : Upper (D 7) (R 7) [96,160,24,68,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28329 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28330 : Route 9 := (fun mask => (mask,id))

def c28330 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28330 : Upper (D 7) (R 7) [96,160,24,192,257,1] 13 := by
  apply FastRouting.sound _ _ [96,160,24,192,257,1] 13 (by decide) (choices 1) [2,4] r28330 c28330
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10599
  · exact u10600

def r28331 : Route 9 := (fun mask => (mask,id))

def c28331 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28331 : Upper (D 7) (R 7) [96,160,24,192,257,2] 13 := by
  apply FastRouting.sound _ _ [96,160,24,192,257,2] 13 (by decide) (choices 1) [1,2,4] r28331 c28331
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10601
  · exact u10602
  · exact u10603

def b28332 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 402, targets := 64 },{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7),(1,6),(4,6)], upper := (rows 97 162 28 200 273 36 67 131 259), lower := (rows 97 162 28 200 273 36 64 128 256), losses := [] }

theorem u28332 : Upper (D 7) (R 7) [96,160,24,192,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28332 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28333 : Route 9 := (fun mask => (mask,id))

def c28333 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28333 : Upper (D 7) (R 7) [96,160,24,192,260,1] 13 := by
  apply FastRouting.sound _ _ [96,160,24,192,260,1] 13 (by decide) (choices 1) [1,2] r28333 c28333
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10604
  · exact u10605

def r28334 : Route 9 := (fun mask => (mask,id))

def c28334 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28334 : Upper (D 7) (R 7) [96,160,66,129,257,2] 13 := by
  apply FastRouting.sound _ _ [96,160,66,129,257,2] 13 (by decide) (choices 1) [4,8,16] r28334 c28334
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10606
  · exact u10607
  · exact u10608

def b28335 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 410, targets := 64 }], pairs := [(1,6),(3,6),(4,6)], upper := (rows 97 162 70 137 273 36 90 154 282), lower := (rows 97 162 70 137 273 36 64 128 256), losses := [] }

theorem u28335 : Upper (D 7) (R 7) [96,160,66,129,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28335 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28336 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 341, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 97 162 70 137 273 40 86 150 278), lower := (rows 97 162 70 137 273 40 64 128 256), losses := [] }

theorem u28336 : Upper (D 7) (R 7) [96,160,66,129,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28336 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28337 : Route 9 := (fun mask => (mask,id))

def c28337 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28337 : Upper (D 7) (R 7) [96,160,66,129,257,16] 13 := by
  apply FastRouting.sound _ _ [96,160,66,129,257,16] 13 (by decide) (choices 1) [2,4,8] r28337 c28337
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10609
  · exact u10610
  · exact u10611

def r28338 : Route 9 := (fun mask => (mask,id))

def c28338 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28338 : Upper (D 7) (R 7) [96,160,66,129,260,1] 13 := by
  apply FastRouting.sound _ _ [96,160,66,129,260,1] 13 (by decide) (choices 1) [2,8,16] r28338 c28338
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10612
  · exact u10613
  · exact u10614

def r28339 : Route 9 := (fun mask => (mask,id))

def c28339 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28339 : Upper (D 7) (R 7) [96,160,66,129,260,2] 13 := by
  apply FastRouting.sound _ _ [96,160,66,129,260,2] 13 (by decide) (choices 1) [1,8,16] r28339 c28339
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10615
  · exact u10616
  · exact u10617

def b28340 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 341, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 97 162 70 137 276 40 83 147 275), lower := (rows 97 162 70 137 276 40 64 128 256), losses := [] }

theorem u28340 : Upper (D 7) (R 7) [96,160,66,129,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28340 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28341 : Route 9 := (fun mask => (mask,id))

def c28341 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28341 : Upper (D 7) (R 7) [96,160,66,129,260,16] 13 := by
  apply FastRouting.sound _ _ [96,160,66,129,260,16] 13 (by decide) (choices 1) [1,2,8] r28341 c28341
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10618
  · exact u10619
  · exact u10620

def r28342 : Route 9 := (fun mask => (mask,id))

def c28342 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28342 : Upper (D 7) (R 7) [96,160,66,132,257,1] 13 := by
  apply FastRouting.sound _ _ [96,160,66,132,257,1] 13 (by decide) (choices 1) [2,8,16] r28342 c28342
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10621
  · exact u10622
  · exact u10623

def b28343 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 34, targets := 65 },{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7),(1,0),(1,6),(4,7)], upper := (rows 97 162 70 140 273 34 89 153 281), lower := (rows 97 162 70 140 273 34 64 128 256), losses := [{ target := 7, region := (rows 13 2 4 8 24 38 72 0 264), good := (rows 97 34 103 381 273 34 64 0 256) }] }

theorem u28343 : Upper (D 7) (R 7) [96,160,66,132,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28343 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28344 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 341, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 97 162 70 140 273 40 83 147 275), lower := (rows 97 162 70 140 273 40 64 128 256), losses := [] }

theorem u28344 : Upper (D 7) (R 7) [96,160,66,132,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28344 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28345 : Route 9 := (fun mask => (mask,id))

def c28345 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28345 : Upper (D 7) (R 7) [96,160,66,132,257,16] 13 := by
  apply FastRouting.sound _ _ [96,160,66,132,257,16] 13 (by decide) (choices 1) [1,2,8] r28345 c28345
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10624
  · exact u10625
  · exact u10626

def r28346 : Route 9 := (fun mask => (mask,id))

def c28346 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28346 : Upper (D 7) (R 7) [96,160,66,132,258,1] 13 := by
  apply FastRouting.sound _ _ [96,160,66,132,258,1] 13 (by decide) (choices 1) [1,8,16] r28346 c28346
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10627
  · exact u10628
  · exact u10629

def b28347 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 341, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 97 162 70 140 274 40 81 145 273), lower := (rows 97 162 70 140 274 40 64 128 256), losses := [] }

theorem u28347 : Upper (D 7) (R 7) [96,160,66,132,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28347 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28348 : Route 9 := (fun mask => (mask,id))

def c28348 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28348 : Upper (D 7) (R 7) [96,160,66,132,258,16] 13 := by
  apply FastRouting.sound _ _ [96,160,66,132,258,16] 13 (by decide) (choices 1) [1,8] r28348 c28348
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10630
  · exact u10631

def r28349 : Route 9 := (fun mask => (mask,id))

def c28349 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28349 : Upper (D 7) (R 7) [96,160,66,132,264,1] 13 := by
  apply FastRouting.sound _ _ [96,160,66,132,264,1] 13 (by decide) (choices 1) [1,2,16] r28349 c28349
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10632
  · exact u10633
  · exact u10634

def b28350 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 34, targets := 65 },{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7),(1,0),(1,6),(4,7)], upper := (rows 97 162 70 140 280 34 81 145 273), lower := (rows 97 162 70 140 280 34 64 128 256), losses := [{ target := 7, region := (rows 13 2 4 8 24 38 88 0 280), good := (rows 97 34 103 381 345 34 64 0 256) }] }

theorem u28350 : Upper (D 7) (R 7) [96,160,66,132,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28350 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28351 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 0, region := 130, targets := 64 }], pairs := [(0,7),(1,6),(2,7)], upper := (rows 97 162 70 140 280 48 67 131 259), lower := (rows 97 162 70 140 280 48 64 128 256), losses := [] }

theorem u28351 : Upper (D 7) (R 7) [96,160,66,132,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28351 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28352 : Route 9 := (fun mask => (mask,id))

def c28352 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28352 : Upper (D 7) (R 7) [96,160,66,144,257,1] 13 := by
  apply FastRouting.sound _ _ [96,160,66,144,257,1] 13 (by decide) (choices 1) [2,4,8] r28352 c28352
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10635
  · exact u10636
  · exact u10637

def r28353 : Route 9 := (fun mask => (mask,id))

def c28353 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28353 : Upper (D 7) (R 7) [96,160,66,144,257,2] 13 := by
  apply FastRouting.sound _ _ [96,160,66,144,257,2] 13 (by decide) (choices 1) [1,4,8] r28353 c28353
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10638
  · exact u10639
  · exact u10640

def b28354 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 410, targets := 64 }], pairs := [(1,6),(3,6),(4,6)], upper := (rows 97 162 70 152 273 36 75 139 267), lower := (rows 97 162 70 152 273 36 64 128 256), losses := [] }

theorem u28354 : Upper (D 7) (R 7) [96,160,66,144,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28354 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28355 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 341, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 97 162 70 152 273 40 71 135 263), lower := (rows 97 162 70 152 273 40 64 128 256), losses := [] }

theorem u28355 : Upper (D 7) (R 7) [96,160,66,144,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28355 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28356 : Route 9 := (fun mask => (mask,id))

def c28356 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28356 : Upper (D 7) (R 7) [96,160,66,144,258,1] 13 := by
  apply FastRouting.sound _ _ [96,160,66,144,258,1] 13 (by decide) (choices 1) [1,4,8] r28356 c28356
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10641
  · exact u10642
  · exact u10643

def b28357 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 410, targets := 64 }], pairs := [(1,6),(3,6),(4,6)], upper := (rows 97 162 70 152 274 36 73 137 265), lower := (rows 97 162 70 152 274 36 64 128 256), losses := [] }

theorem u28357 : Upper (D 7) (R 7) [96,160,66,144,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28357 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28358 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 341, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 97 162 70 152 274 40 69 133 261), lower := (rows 97 162 70 152 274 40 64 128 256), losses := [] }

theorem u28358 : Upper (D 7) (R 7) [96,160,66,144,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28358 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28359 : Route 9 := (fun mask => (mask,id))

def c28359 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28359 : Upper (D 7) (R 7) [96,160,66,144,260,1] 13 := by
  apply FastRouting.sound _ _ [96,160,66,144,260,1] 13 (by decide) (choices 1) [1,2,8] r28359 c28359
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10644
  · exact u10645
  · exact u10646

def r28360 : Route 9 := (fun mask => (mask,id))

def c28360 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28360 : Upper (D 7) (R 7) [96,160,66,144,260,2] 13 := by
  apply FastRouting.sound _ _ [96,160,66,144,260,2] 13 (by decide) (choices 1) [1,8] r28360 c28360
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10647
  · exact u10648

def b28361 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 341, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 97 162 70 152 276 40 67 131 259), lower := (rows 97 162 70 152 276 40 64 128 256), losses := [] }

theorem u28361 : Upper (D 7) (R 7) [96,160,66,144,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28361 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28362 : Route 9 := (fun mask => (mask,id))

def c28362 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28362 : Upper (D 7) (R 7) [96,160,66,144,264,1] 13 := by
  apply FastRouting.sound _ _ [96,160,66,144,264,1] 13 (by decide) (choices 1) [1,2,4] r28362 c28362
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10649
  · exact u10650
  · exact u10651

def b28363 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 3, region := 34, targets := 65 }], pairs := [(0,7),(1,0),(1,6),(2,7)], upper := (rows 97 162 70 152 280 34 69 133 261), lower := (rows 97 162 70 152 280 34 64 128 256), losses := [] }

theorem u28363 : Upper (D 7) (R 7) [96,160,66,144,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28363 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28364 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 410, targets := 64 }], pairs := [(1,6),(3,6),(4,6)], upper := (rows 97 162 70 152 280 36 67 131 259), lower := (rows 97 162 70 152 280 36 64 128 256), losses := [] }

theorem u28364 : Upper (D 7) (R 7) [96,160,66,144,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28364 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28365 : Route 9 := (fun mask => (mask,id))

def c28365 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28365 : Upper (D 7) (R 7) [96,160,72,144,257,1] 13 := by
  apply FastRouting.sound _ _ [96,160,72,144,257,1] 13 (by decide) (choices 1) [2,4] r28365 c28365
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10652
  · exact u10653

def r28366 : Route 9 := (fun mask => (mask,id))

def c28366 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28366 : Upper (D 7) (R 7) [96,160,72,144,257,2] 13 := by
  apply FastRouting.sound _ _ [96,160,72,144,257,2] 13 (by decide) (choices 1) [1,2,4] r28366 c28366
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10654
  · exact u10655
  · exact u10656

def b28367 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 410, targets := 64 }], pairs := [(1,6),(3,6),(4,6)], upper := (rows 97 162 76 152 273 36 67 131 259), lower := (rows 97 162 76 152 273 36 64 128 256), losses := [] }

theorem u28367 : Upper (D 7) (R 7) [96,160,72,144,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28367 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28368 : Route 9 := (fun mask => (mask,id))

def c28368 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28368 : Upper (D 7) (R 7) [96,160,72,144,258,1] 13 := by
  apply FastRouting.sound _ _ [96,160,72,144,258,1] 13 (by decide) (choices 1) [1,2,4] r28368 c28368
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10657
  · exact u10658
  · exact u10659

def b28369 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 34, targets := 65 }], pairs := [(0,7),(1,0),(1,6),(2,7)], upper := (rows 97 162 76 152 274 34 69 133 261), lower := (rows 97 162 76 152 274 34 64 128 256), losses := [{ target := 7, region := (rows 9 2 12 8 16 50 76 0 268), good := (rows 97 34 333 381 306 34 64 0 256) }] }

theorem u28369 : Upper (D 7) (R 7) [96,160,72,144,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28369 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28370 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 410, targets := 64 }], pairs := [(1,6),(3,6),(4,6)], upper := (rows 97 162 76 152 274 36 67 131 259), lower := (rows 97 162 76 152 274 36 64 128 256), losses := [] }

theorem u28370 : Upper (D 7) (R 7) [96,160,72,144,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28370 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28371 : Route 9 := (fun mask => (mask,id))

def c28371 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28371 : Upper (D 7) (R 7) [96,160,72,144,260,1] 13 := by
  apply FastRouting.sound _ _ [96,160,72,144,260,1] 13 (by decide) (choices 1) [1,2] r28371 c28371
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10660
  · exact u10661

def r28372 : Route 9 := (fun mask => (mask,id))

def c28372 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28372 : Upper (D 7) (R 7) [96,160,72,144,260,2] 13 := by
  apply FastRouting.sound _ _ [96,160,72,144,260,2] 13 (by decide) (choices 1) [1,2] r28372 c28372
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10662
  · exact u10663

def b28373 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 60, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 97 259 13 26 52 34 192 192 448), lower := (rows 97 259 13 26 52 34 64 128 256), losses := [] }

theorem u28373 : Upper (D 7) (R 7) [96,257,9,18,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28373 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28374 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 259 13 26 52 96 194 130 386), lower := (rows 97 259 13 26 52 96 64 128 256), losses := [] }

theorem u28374 : Upper (D 7) (R 7) [96,257,9,18,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28374 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28375 : Route 9 := (fun mask => (mask,id))

def c28375 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28375 : Upper (D 7) (R 7) [96,257,9,18,36,128] 13 := by
  apply FastRouting.sound _ _ [96,257,9,18,36,128] 13 (by decide) (choices 1) [2,128] r28375 c28375
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10664
  · exact u10665

def r28376 : Route 9 := (fun mask => (mask,id))

def c28376 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u28376 : Upper (D 7) (R 7) [96,257,9,18,132,2] 13 := by
  apply FastRouting.sound _ _ [96,257,9,18,132,2] 13 (by decide) (choices 1) [32,128] r28376 c28376
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10666
  · exact u10667

def b28377 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 259 13 26 148 96 226 162 418), lower := (rows 97 259 13 26 148 96 64 128 256), losses := [] }

theorem u28377 : Upper (D 7) (R 7) [96,257,9,18,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28377 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28378 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 323, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,0)], upper := (rows 97 259 13 26 148 160 98 226 354), lower := (rows 97 259 13 26 148 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 190 74 138 266), good := (rows 96 482 508 506 180 160 64 160 256) },{ target := 7, region := (rows 33 39 4 24 16 32 97 0 289), good := (rows 355 323 335 26 30 355 64 0 256) }] }

theorem u28378 : Upper (D 7) (R 7) [96,257,9,18,132,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28378 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28379 : Route 9 := (fun mask => (mask,id))

def c28379 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28379 : Upper (D 7) (R 7) [96,257,9,18,160,2] 13 := by
  apply FastRouting.sound _ _ [96,257,9,18,160,2] 13 (by decide) (choices 1) [4,128] r28379 c28379
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10668
  · exact u10669

#print axioms u28379
end Delivery.IrregularNine14.P07

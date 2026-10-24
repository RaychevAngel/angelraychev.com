import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0426
import IrregularNine14P06C0427
import IrregularNine14P06C0428

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r39300 : Route 9 := (fun mask => (mask,id))

def c39300 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u39300 : Upper (D 6) (R 6) [40,80,129,6,3] 13 := by
  apply FastRouting.sound _ _ [40,80,129,6,3] 13 (by decide) (choices 1) [4,64,256] r39300 c39300
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25602
  · exact u25603
  · exact u25604

def b39301 : PairBound 9 := { available := 354, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 41 82 133 14 21 354 354 482 354), lower := (rows 41 82 133 14 21 32 64 128 256), losses := [] }

theorem u39301 : Upper (D 6) (R 6) [40,80,129,6,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39301 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39302 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 41 82 133 14 22 353 353 481 353), lower := (rows 41 82 133 14 22 32 64 128 256), losses := [] }

theorem u39302 : Upper (D 6) (R 6) [40,80,129,6,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39302 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39303 : PairBound 9 := { available := 326, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 41 82 133 14 49 358 326 454 326), lower := (rows 41 82 133 14 49 32 64 128 256), losses := [] }

theorem u39303 : Upper (D 6) (R 6) [40,80,129,6,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39303 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39304 : PairBound 9 := { available := 325, camps := [{ cop := 3, region := 485, targets := 2 },{ cop := 0, region := 452, targets := 32 }], pairs := [(0,1),(2,1),(2,5)], upper := (rows 41 82 133 14 50 357 325 453 325), lower := (rows 41 82 133 14 50 32 64 128 256), losses := [] }

theorem u39304 : Upper (D 6) (R 6) [40,80,129,6,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39304 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39305 : Route 9 := (fun mask => (mask,id))

def c39305 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u39305 : Upper (D 6) (R 6) [40,80,129,6,36] 13 := by
  apply FastRouting.sound _ _ [40,80,129,6,36] 13 (by decide) (choices 1) [1,2,64,256] r39305 c39305
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25605
  · exact u25606
  · exact u25607
  · exact u25608

def b39306 : PairBound 9 := { available := 294, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 82 133 14 81 294 358 422 294), lower := (rows 41 82 133 14 81 32 64 128 256), losses := [] }

theorem u39306 : Upper (D 6) (R 6) [40,80,129,6,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39306 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39307 : PairBound 9 := { available := 293, camps := [{ cop := 6, region := 18, targets := 37 }], pairs := [(1,0),(1,2),(1,5)], upper := (rows 41 82 133 14 82 293 357 421 293), lower := (rows 41 82 133 14 82 32 64 128 256), losses := [] }

theorem u39307 : Upper (D 6) (R 6) [40,80,129,6,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39307 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39308 : PairBound 9 := { available := 291, camps := [{ cop := 4, region := 10, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 41 82 133 14 84 291 355 419 291), lower := (rows 41 82 133 14 84 32 64 128 256), losses := [] }

theorem u39308 : Upper (D 6) (R 6) [40,80,129,6,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39308 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39309 : PairBound 9 := { available := 263, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 82 133 14 112 295 327 391 263), lower := (rows 41 82 133 14 112 32 64 128 256), losses := [] }

theorem u39309 : Upper (D 6) (R 6) [40,80,129,6,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39309 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39310 : Route 9 := (fun mask => (mask,id))

def c39310 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39310 : Upper (D 6) (R 6) [40,80,129,6,257] 13 := by
  apply FastRouting.sound _ _ [40,80,129,6,257] 13 (by decide) (choices 1) [2,4,64] r39310 c39310
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25609
  · exact u25610
  · exact u25611

def r39311 : Route 9 := (fun mask => (mask,id))

def c39311 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39311 : Upper (D 6) (R 6) [40,80,129,6,258] 13 := by
  apply FastRouting.sound _ _ [40,80,129,6,258] 13 (by decide) (choices 1) [1,4,64] r39311 c39311
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25612
  · exact u25613
  · exact u25614

def r39312 : Route 9 := (fun mask => (mask,id))

def c39312 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39312 : Upper (D 6) (R 6) [40,80,129,6,260] 13 := by
  apply FastRouting.sound _ _ [40,80,129,6,260] 13 (by decide) (choices 1) [1,2,64] r39312 c39312
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25615
  · exact u25616
  · exact u25617

def r39313 : Route 9 := (fun mask => (mask,id))

def c39313 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39313 : Upper (D 6) (R 6) [40,80,129,6,288] 13 := by
  apply FastRouting.sound _ _ [40,80,129,6,288] 13 (by decide) (choices 1) [1,2,4,64] r39313 c39313
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25618
  · exact u25619
  · exact u25620
  · exact u25621

def b39314 : PairBound 9 := { available := 39, camps := [{ cop := 1, region := 173, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 82 133 14 336 39 103 167 295), lower := (rows 41 82 133 14 336 32 64 128 256), losses := [] }

theorem u39314 : Upper (D 6) (R 6) [40,80,129,6,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39314 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39315 : Route 9 := (fun mask => (mask,id))

def c39315 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u39315 : Upper (D 6) (R 6) [40,80,129,65,6] 13 := by
  apply FastRouting.sound _ _ [40,80,129,65,6] 13 (by decide) (choices 1) [2,4,256] r39315 c39315
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25622
  · exact u25623
  · exact u25624

def b39316 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 370, targets := 1 }], pairs := [(0,1),(1,0),(4,0)], upper := (rows 41 82 133 73 50 294 326 390 262), lower := (rows 41 82 133 73 50 32 64 128 256), losses := [{ target := 1, region := (rows 17 0 4 10 16 32 64 128 256), good := (rows 41 89 133 73 57 32 64 128 256) }] }

theorem u39316 : Upper (D 6) (R 6) [40,80,129,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39316 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39317 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 370, targets := 1 },{ cop := 4, region := 322, targets := 32 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 41 82 133 73 52 294 326 390 262), lower := (rows 41 82 133 73 52 32 64 128 256), losses := [] }

theorem u39317 : Upper (D 6) (R 6) [40,80,129,65,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39317 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39318 : Route 9 := (fun mask => (mask,id))

def c39318 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39318 : Upper (D 6) (R 6) [40,80,129,65,258] 13 := by
  apply FastRouting.sound _ _ [40,80,129,65,258] 13 (by decide) (choices 1) [2,4] r39318 c39318
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25625
  · exact u25626

def r39319 : Route 9 := (fun mask => (mask,id))

def c39319 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39319 : Upper (D 6) (R 6) [40,80,129,65,260] 13 := by
  apply FastRouting.sound _ _ [40,80,129,65,260] 13 (by decide) (choices 1) [2,4] r39319 c39319
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25627
  · exact u25628

def r39320 : Route 9 := (fun mask => (mask,id))

def c39320 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39320 : Upper (D 6) (R 6) [40,80,129,65,288] 13 := by
  apply FastRouting.sound _ _ [40,80,129,65,288] 13 (by decide) (choices 1) [2,4] r39320 c39320
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25629
  · exact u25630

def r39321 : Route 9 := (fun mask => (mask,id))

def c39321 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u39321 : Upper (D 6) (R 6) [40,80,129,68,3] 13 := by
  apply FastRouting.sound _ _ [40,80,129,68,3] 13 (by decide) (choices 1) [2,4,256] r39321 c39321
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25631
  · exact u25632
  · exact u25633

def b39322 : PairBound 9 := { available := 290, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 41 82 133 76 21 290 354 418 290), lower := (rows 41 82 133 76 21 32 64 128 256), losses := [] }

theorem u39322 : Upper (D 6) (R 6) [40,80,129,68,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39322 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39323 : PairBound 9 := { available := 291, camps := [{ cop := 3, region := 18, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 41 82 133 76 22 291 355 419 291), lower := (rows 41 82 133 76 22 32 64 128 256), losses := [] }

theorem u39323 : Upper (D 6) (R 6) [40,80,129,68,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39323 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39324 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 41 82 133 76 49 294 326 390 262), lower := (rows 41 82 133 76 49 32 64 128 256), losses := [] }

theorem u39324 : Upper (D 6) (R 6) [40,80,129,68,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39324 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39325 : Route 9 := (fun mask => (mask,id))

def c39325 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u39325 : Upper (D 6) (R 6) [40,80,129,68,34] 13 := by
  apply FastRouting.sound _ _ [40,80,129,68,34] 13 (by decide) (choices 1) [1,2,4,256] r39325 c39325
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25634
  · exact u25635
  · exact u25636
  · exact u25637

def r39326 : Route 9 := (fun mask => (mask,id))

def c39326 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u39326 : Upper (D 6) (R 6) [40,80,129,68,36] 13 := by
  apply FastRouting.sound _ _ [40,80,129,68,36] 13 (by decide) (choices 1) [1,2,256] r39326 c39326
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25638
  · exact u25639
  · exact u25640

def r39327 : Route 9 := (fun mask => (mask,id))

def c39327 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39327 : Upper (D 6) (R 6) [40,80,129,68,257] 13 := by
  apply FastRouting.sound _ _ [40,80,129,68,257] 13 (by decide) (choices 1) [2,4] r39327 c39327
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25641
  · exact u25642

def r39328 : Route 9 := (fun mask => (mask,id))

def c39328 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39328 : Upper (D 6) (R 6) [40,80,129,68,258] 13 := by
  apply FastRouting.sound _ _ [40,80,129,68,258] 13 (by decide) (choices 1) [1,2,4] r39328 c39328
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25643
  · exact u25644
  · exact u25645

def r39329 : Route 9 := (fun mask => (mask,id))

def c39329 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39329 : Upper (D 6) (R 6) [40,80,129,68,260] 13 := by
  apply FastRouting.sound _ _ [40,80,129,68,260] 13 (by decide) (choices 1) [1,2] r39329 c39329
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25646
  · exact u25647

def r39330 : Route 9 := (fun mask => (mask,id))

def c39330 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39330 : Upper (D 6) (R 6) [40,80,129,68,288] 13 := by
  apply FastRouting.sound _ _ [40,80,129,68,288] 13 (by decide) (choices 1) [1,2,4] r39330 c39330
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25648
  · exact u25649
  · exact u25650

def r39331 : Route 9 := (fun mask => (mask,id))

def c39331 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39331 : Upper (D 6) (R 6) [40,80,129,257,6] 13 := by
  apply FastRouting.sound _ _ [40,80,129,257,6] 13 (by decide) (choices 1) [2,4,64] r39331 c39331
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25651
  · exact u25652
  · exact u25653

def r39332 : Route 9 := (fun mask => (mask,id))

def c39332 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39332 : Upper (D 6) (R 6) [40,80,129,257,34] 13 := by
  apply FastRouting.sound _ _ [40,80,129,257,34] 13 (by decide) (choices 1) [2,4,64] r39332 c39332
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25654
  · exact u25655
  · exact u25656

def b39333 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 114, targets := 1 },{ cop := 4, region := 66, targets := 32 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 41 82 133 265 52 102 70 198 326), lower := (rows 41 82 133 265 52 32 64 128 256), losses := [] }

theorem u39333 : Upper (D 6) (R 6) [40,80,129,257,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39333 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39334 : PairBound 9 := { available := 38, camps := [{ cop := 6, region := 18, targets := 37 }], pairs := [(1,0),(1,2),(1,5)], upper := (rows 41 82 133 265 82 38 102 166 294), lower := (rows 41 82 133 265 82 32 64 128 256), losses := [] }

theorem u39334 : Upper (D 6) (R 6) [40,80,129,257,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39334 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39335 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 82 133 265 84 38 102 166 294), lower := (rows 41 82 133 265 84 32 64 128 256), losses := [] }

theorem u39335 : Upper (D 6) (R 6) [40,80,129,257,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39335 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39336 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 82 133 265 112 38 70 134 262), lower := (rows 41 82 133 265 112 32 64 128 256), losses := [] }

theorem u39336 : Upper (D 6) (R 6) [40,80,129,257,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39336 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39337 : Route 9 := (fun mask => (mask,id))

def c39337 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39337 : Upper (D 6) (R 6) [40,80,129,258,3] 13 := by
  apply FastRouting.sound _ _ [40,80,129,258,3] 13 (by decide) (choices 1) [4,64] r39337 c39337
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25657
  · exact u25658

def b39338 : PairBound 9 := { available := 102, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 41 82 133 266 21 102 102 230 358), lower := (rows 41 82 133 266 21 32 64 128 256), losses := [] }

theorem u39338 : Upper (D 6) (R 6) [40,80,129,258,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39338 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39339 : Route 9 := (fun mask => (mask,id))

def c39339 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39339 : Upper (D 6) (R 6) [40,80,129,258,6] 13 := by
  apply FastRouting.sound _ _ [40,80,129,258,6] 13 (by decide) (choices 1) [1,4,64] r39339 c39339
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25659
  · exact u25660
  · exact u25661

def b39340 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 41 82 133 266 49 102 70 198 326), lower := (rows 41 82 133 266 49 32 64 128 256), losses := [] }

theorem u39340 : Upper (D 6) (R 6) [40,80,129,258,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39340 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39341 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 229, targets := 2 },{ cop := 0, region := 196, targets := 32 }], pairs := [(0,1),(2,1),(2,5)], upper := (rows 41 82 133 266 50 101 69 197 325), lower := (rows 41 82 133 266 50 32 64 128 256), losses := [] }

theorem u39341 : Upper (D 6) (R 6) [40,80,129,258,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39341 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39342 : Route 9 := (fun mask => (mask,id))

def c39342 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39342 : Upper (D 6) (R 6) [40,80,129,258,36] 13 := by
  apply FastRouting.sound _ _ [40,80,129,258,36] 13 (by decide) (choices 1) [1,2,4,64] r39342 c39342
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25662
  · exact u25663
  · exact u25664
  · exact u25665

def b39343 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 82 133 266 81 38 102 166 294), lower := (rows 41 82 133 266 81 32 64 128 256), losses := [] }

theorem u39343 : Upper (D 6) (R 6) [40,80,129,258,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39343 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39344 : PairBound 9 := { available := 37, camps := [{ cop := 6, region := 18, targets := 37 }], pairs := [(1,0),(1,2),(1,5)], upper := (rows 41 82 133 266 82 37 101 165 293), lower := (rows 41 82 133 266 82 32 64 128 256), losses := [] }

theorem u39344 : Upper (D 6) (R 6) [40,80,129,258,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39344 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39345 : PairBound 9 := { available := 39, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 82 133 266 84 39 103 167 295), lower := (rows 41 82 133 266 84 32 64 128 256), losses := [] }

theorem u39345 : Upper (D 6) (R 6) [40,80,129,258,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39345 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39346 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 82 133 266 112 39 71 135 263), lower := (rows 41 82 133 266 112 32 64 128 256), losses := [] }

theorem u39346 : Upper (D 6) (R 6) [40,80,129,258,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39346 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39347 : Route 9 := (fun mask => (mask,id))

def c39347 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39347 : Upper (D 6) (R 6) [40,80,129,260,3] 13 := by
  apply FastRouting.sound _ _ [40,80,129,260,3] 13 (by decide) (choices 1) [2,4,64] r39347 c39347
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25666
  · exact u25667
  · exact u25668

def b39348 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 41 82 133 268 21 98 98 226 354), lower := (rows 41 82 133 268 21 32 64 128 256), losses := [] }

theorem u39348 : Upper (D 6) (R 6) [40,80,129,260,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39348 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39349 : Route 9 := (fun mask => (mask,id))

def c39349 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39349 : Upper (D 6) (R 6) [40,80,129,260,6] 13 := by
  apply FastRouting.sound _ _ [40,80,129,260,6] 13 (by decide) (choices 1) [1,2,64] r39349 c39349
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25669
  · exact u25670
  · exact u25671

def b39350 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 41 82 133 268 49 102 70 198 326), lower := (rows 41 82 133 268 49 32 64 128 256), losses := [] }

theorem u39350 : Upper (D 6) (R 6) [40,80,129,260,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39350 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39351 : Route 9 := (fun mask => (mask,id))

def c39351 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39351 : Upper (D 6) (R 6) [40,80,129,260,34] 13 := by
  apply FastRouting.sound _ _ [40,80,129,260,34] 13 (by decide) (choices 1) [1,2,4,64] r39351 c39351
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25672
  · exact u25673
  · exact u25674
  · exact u25675

def r39352 : Route 9 := (fun mask => (mask,id))

def c39352 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39352 : Upper (D 6) (R 6) [40,80,129,260,36] 13 := by
  apply FastRouting.sound _ _ [40,80,129,260,36] 13 (by decide) (choices 1) [1,2,64] r39352 c39352
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25676
  · exact u25677
  · exact u25678

def b39353 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 82 133 268 81 38 102 166 294), lower := (rows 41 82 133 268 81 32 64 128 256), losses := [] }

theorem u39353 : Upper (D 6) (R 6) [40,80,129,260,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39353 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39354 : PairBound 9 := { available := 39, camps := [{ cop := 6, region := 18, targets := 37 }], pairs := [(1,0),(1,2),(1,5)], upper := (rows 41 82 133 268 82 39 103 167 295), lower := (rows 41 82 133 268 82 32 64 128 256), losses := [] }

theorem u39354 : Upper (D 6) (R 6) [40,80,129,260,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39354 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39355 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 82 133 268 84 35 99 163 291), lower := (rows 41 82 133 268 84 32 64 128 256), losses := [] }

theorem u39355 : Upper (D 6) (R 6) [40,80,129,260,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39355 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39356 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 82 133 268 112 39 71 135 263), lower := (rows 41 82 133 268 112 32 64 128 256), losses := [] }

theorem u39356 : Upper (D 6) (R 6) [40,80,129,260,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39356 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39357 : Route 9 := (fun mask => (mask,id))

def c39357 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39357 : Upper (D 6) (R 6) [40,80,129,320,3] 13 := by
  apply FastRouting.sound _ _ [40,80,129,320,3] 13 (by decide) (choices 1) [2,4] r39357 c39357
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25679
  · exact u25680

def b39358 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 41 82 133 328 21 38 102 166 294), lower := (rows 41 82 133 328 21 32 64 128 256), losses := [] }

theorem u39358 : Upper (D 6) (R 6) [40,80,129,320,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39358 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39359 : Route 9 := (fun mask => (mask,id))

def c39359 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39359 : Upper (D 6) (R 6) [40,80,129,320,6] 13 := by
  apply FastRouting.sound _ _ [40,80,129,320,6] 13 (by decide) (choices 1) [1,2,4] r39359 c39359
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25681
  · exact u25682
  · exact u25683

#print axioms u39359
end Delivery.IrregularNine14.P06

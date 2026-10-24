import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0347
import IrregularNine14P06C0348

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r36420 : Route 9 := (fun mask => (mask,id))

def c36420 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36420 : Upper (D 6) (R 6) [34,72,48,384,65] 13 := by
  apply FastRouting.sound _ _ [34,72,48,384,65] 13 (by decide) (choices 1) [1,2,4] r36420 c36420
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20828
  · exact u20829
  · exact u20830

def b36421 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 74 52 392 82 37 69 133 261), lower := (rows 35 74 52 392 82 32 64 128 256), losses := [] }

theorem u36421 : Upper (D 6) (R 6) [34,72,48,384,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36421 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36422 : Route 9 := (fun mask => (mask,id))

def c36422 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36422 : Upper (D 6) (R 6) [34,72,48,384,68] 13 := by
  apply FastRouting.sound _ _ [34,72,48,384,68] 13 (by decide) (choices 1) [1,2,4] r36422 c36422
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20831
  · exact u20832
  · exact u20833

def b36423 : PairBound 9 := { available := 420, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 74 84 13 19 420 484 420 420), lower := (rows 35 74 84 13 19 32 64 128 256), losses := [] }

theorem u36423 : Upper (D 6) (R 6) [34,72,80,5,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36423 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36424 : PairBound 9 := { available := 418, camps := [{ cop := 3, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 35 74 84 13 21 418 482 418 418), lower := (rows 35 74 84 13 21 32 64 128 256), losses := [] }

theorem u36424 : Upper (D 6) (R 6) [34,72,80,5,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36424 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36425 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 20, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 35 74 84 13 22 417 481 417 417), lower := (rows 35 74 84 13 22 32 64 128 256), losses := [] }

theorem u36425 : Upper (D 6) (R 6) [34,72,80,5,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36425 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36426 : PairBound 9 := { available := 390, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 74 84 13 49 422 454 390 390), lower := (rows 35 74 84 13 49 32 64 128 256), losses := [] }

theorem u36426 : Upper (D 6) (R 6) [34,72,80,5,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36426 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36427 : PairBound 9 := { available := 389, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 74 84 13 50 421 453 389 389), lower := (rows 35 74 84 13 50 32 64 128 256), losses := [] }

theorem u36427 : Upper (D 6) (R 6) [34,72,80,5,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36427 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36428 : PairBound 9 := { available := 387, camps := [{ cop := 3, region := 483, targets := 4 },{ cop := 1, region := 417, targets := 64 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 74 84 13 52 419 451 387 387), lower := (rows 35 74 84 13 52 32 64 128 256), losses := [] }

theorem u36428 : Upper (D 6) (R 6) [34,72,80,5,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36428 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36429 : Route 9 := (fun mask => (mask,id))

def c36429 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36429 : Upper (D 6) (R 6) [34,72,80,5,129] 13 := by
  apply FastRouting.sound _ _ [34,72,80,5,129] 13 (by decide) (choices 1) [2,4,256] r36429 c36429
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20834
  · exact u20835
  · exact u20836

def r36430 : Route 9 := (fun mask => (mask,id))

def c36430 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36430 : Upper (D 6) (R 6) [34,72,80,5,130] 13 := by
  apply FastRouting.sound _ _ [34,72,80,5,130] 13 (by decide) (choices 1) [1,4,256] r36430 c36430
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20837
  · exact u20838
  · exact u20839

def b36431 : PairBound 9 := { available := 291, camps := [{ cop := 3, region := 355, targets := 4 },{ cop := 1, region := 289, targets := 64 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 74 84 13 148 291 355 419 291), lower := (rows 35 74 84 13 148 32 64 128 256), losses := [] }

theorem u36431 : Upper (D 6) (R 6) [34,72,80,5,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36431 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36432 : Route 9 := (fun mask => (mask,id))

def c36432 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36432 : Upper (D 6) (R 6) [34,72,80,5,160] 13 := by
  apply FastRouting.sound _ _ [34,72,80,5,160] 13 (by decide) (choices 1) [1,2,4,256] r36432 c36432
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20840
  · exact u20841
  · exact u20842
  · exact u20843

def r36433 : Route 9 := (fun mask => (mask,id))

def c36433 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36433 : Upper (D 6) (R 6) [34,72,80,5,384] 13 := by
  apply FastRouting.sound _ _ [34,72,80,5,384] 13 (by decide) (choices 1) [1,2,4] r36433 c36433
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20844
  · exact u20845
  · exact u20846

def b36434 : PairBound 9 := { available := 389, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 0, region := 468, targets := 32 }], pairs := [(2,5),(4,2),(4,6)], upper := (rows 35 74 84 44 19 421 453 389 389), lower := (rows 35 74 84 44 19 32 64 128 256), losses := [] }

theorem u36434 : Upper (D 6) (R 6) [34,72,80,36,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36434 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36435 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 3, region := 451, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 74 84 44 21 419 451 387 387), lower := (rows 35 74 84 44 21 32 64 128 256), losses := [] }

theorem u36435 : Upper (D 6) (R 6) [34,72,80,36,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36435 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36436 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 20, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 35 74 84 44 22 417 449 385 385), lower := (rows 35 74 84 44 22 32 64 128 256), losses := [] }

theorem u36436 : Upper (D 6) (R 6) [34,72,80,36,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36436 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36437 : Route 9 := (fun mask => (mask,id))

def c36437 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36437 : Upper (D 6) (R 6) [34,72,80,36,129] 13 := by
  apply FastRouting.sound _ _ [34,72,80,36,129] 13 (by decide) (choices 1) [1,2,4,256] r36437 c36437
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20847
  · exact u20848
  · exact u20849
  · exact u20850

def r36438 : Route 9 := (fun mask => (mask,id))

def c36438 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36438 : Upper (D 6) (R 6) [34,72,80,36,130] 13 := by
  apply FastRouting.sound _ _ [34,72,80,36,130] 13 (by decide) (choices 1) [1,4,256] r36438 c36438
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20851
  · exact u20852
  · exact u20853

def b36439 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 3, region := 323, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 74 84 44 148 291 323 387 259), lower := (rows 35 74 84 44 148 32 64 128 256), losses := [] }

theorem u36439 : Upper (D 6) (R 6) [34,72,80,36,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36439 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36440 : Route 9 := (fun mask => (mask,id))

def c36440 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36440 : Upper (D 6) (R 6) [34,72,80,36,384] 13 := by
  apply FastRouting.sound _ _ [34,72,80,36,384] 13 (by decide) (choices 1) [1,2,4] r36440 c36440
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20854
  · exact u20855
  · exact u20856

def b36441 : PairBound 9 := { available := 292, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 74 84 137 19 292 356 420 292), lower := (rows 35 74 84 137 19 32 64 128 256), losses := [] }

theorem u36441 : Upper (D 6) (R 6) [34,72,80,129,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36441 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36442 : Route 9 := (fun mask => (mask,id))

def c36442 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36442 : Upper (D 6) (R 6) [34,72,80,129,5] 13 := by
  apply FastRouting.sound _ _ [34,72,80,129,5] 13 (by decide) (choices 1) [2,4,256] r36442 c36442
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20857
  · exact u20858
  · exact u20859

def b36443 : PairBound 9 := { available := 293, camps := [{ cop := 1, region := 20, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 35 74 84 137 22 293 357 421 293), lower := (rows 35 74 84 137 22 32 64 128 256), losses := [] }

theorem u36443 : Upper (D 6) (R 6) [34,72,80,129,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36443 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36444 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 74 84 137 49 294 326 390 262), lower := (rows 35 74 84 137 49 32 64 128 256), losses := [] }

theorem u36444 : Upper (D 6) (R 6) [34,72,80,129,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36444 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36445 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 74 84 137 50 293 325 389 261), lower := (rows 35 74 84 137 50 32 64 128 256), losses := [] }

theorem u36445 : Upper (D 6) (R 6) [34,72,80,129,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36445 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36446 : Route 9 := (fun mask => (mask,id))

def c36446 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36446 : Upper (D 6) (R 6) [34,72,80,129,36] 13 := by
  apply FastRouting.sound _ _ [34,72,80,129,36] 13 (by decide) (choices 1) [1,2,4,256] r36446 c36446
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20860
  · exact u20861
  · exact u20862
  · exact u20863

def r36447 : Route 9 := (fun mask => (mask,id))

def c36447 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36447 : Upper (D 6) (R 6) [34,72,80,129,257] 13 := by
  apply FastRouting.sound _ _ [34,72,80,129,257] 13 (by decide) (choices 1) [2,4] r36447 c36447
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u20864
  · exact u20865

def r36448 : Route 9 := (fun mask => (mask,id))

def c36448 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36448 : Upper (D 6) (R 6) [34,72,80,129,258] 13 := by
  apply FastRouting.sound _ _ [34,72,80,129,258] 13 (by decide) (choices 1) [1,4] r36448 c36448
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u20866
  · exact u20867

def r36449 : Route 9 := (fun mask => (mask,id))

def c36449 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36449 : Upper (D 6) (R 6) [34,72,80,129,260] 13 := by
  apply FastRouting.sound _ _ [34,72,80,129,260] 13 (by decide) (choices 1) [1,2,4] r36449 c36449
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20868
  · exact u20869
  · exact u20870

def r36450 : Route 9 := (fun mask => (mask,id))

def c36450 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36450 : Upper (D 6) (R 6) [34,72,80,129,288] 13 := by
  apply FastRouting.sound _ _ [34,72,80,129,288] 13 (by decide) (choices 1) [1,2,4] r36450 c36450
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20871
  · exact u20872
  · exact u20873

def r36451 : Route 9 := (fun mask => (mask,id))

def c36451 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36451 : Upper (D 6) (R 6) [34,72,80,130,5] 13 := by
  apply FastRouting.sound _ _ [34,72,80,130,5] 13 (by decide) (choices 1) [1,4,256] r36451 c36451
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20874
  · exact u20875
  · exact u20876

def b36452 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 74 84 138 49 293 325 389 261), lower := (rows 35 74 84 138 49 32 64 128 256), losses := [] }

theorem u36452 : Upper (D 6) (R 6) [34,72,80,130,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36452 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36453 : Route 9 := (fun mask => (mask,id))

def c36453 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36453 : Upper (D 6) (R 6) [34,72,80,130,36] 13 := by
  apply FastRouting.sound _ _ [34,72,80,130,36] 13 (by decide) (choices 1) [1,4,256] r36453 c36453
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20877
  · exact u20878
  · exact u20879

def r36454 : Route 9 := (fun mask => (mask,id))

def c36454 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36454 : Upper (D 6) (R 6) [34,72,80,130,257] 13 := by
  apply FastRouting.sound _ _ [34,72,80,130,257] 13 (by decide) (choices 1) [1,4] r36454 c36454
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u20880
  · exact u20881

def r36455 : Route 9 := (fun mask => (mask,id))

def c36455 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36455 : Upper (D 6) (R 6) [34,72,80,130,260] 13 := by
  apply FastRouting.sound _ _ [34,72,80,130,260] 13 (by decide) (choices 1) [1,4] r36455 c36455
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u20882
  · exact u20883

def r36456 : Route 9 := (fun mask => (mask,id))

def c36456 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36456 : Upper (D 6) (R 6) [34,72,80,130,288] 13 := by
  apply FastRouting.sound _ _ [34,72,80,130,288] 13 (by decide) (choices 1) [1,4] r36456 c36456
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u20884
  · exact u20885

def b36457 : PairBound 9 := { available := 293, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 74 84 140 19 293 357 421 293), lower := (rows 35 74 84 140 19 32 64 128 256), losses := [] }

theorem u36457 : Upper (D 6) (R 6) [34,72,80,132,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36457 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36458 : PairBound 9 := { available := 291, camps := [{ cop := 3, region := 355, targets := 4 },{ cop := 1, region := 289, targets := 64 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 74 84 140 21 291 355 419 291), lower := (rows 35 74 84 140 21 32 64 128 256), losses := [] }

theorem u36458 : Upper (D 6) (R 6) [34,72,80,132,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36458 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36459 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 20, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 35 74 84 140 22 289 353 417 289), lower := (rows 35 74 84 140 22 32 64 128 256), losses := [] }

theorem u36459 : Upper (D 6) (R 6) [34,72,80,132,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36459 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36460 : PairBound 9 := { available := 263, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 74 84 140 49 295 327 391 263), lower := (rows 35 74 84 140 49 32 64 128 256), losses := [] }

theorem u36460 : Upper (D 6) (R 6) [34,72,80,132,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36460 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36461 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 74 84 140 50 293 325 389 261), lower := (rows 35 74 84 140 50 32 64 128 256), losses := [] }

theorem u36461 : Upper (D 6) (R 6) [34,72,80,132,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36461 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36462 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 355, targets := 4 },{ cop := 1, region := 289, targets := 64 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 74 84 140 52 291 323 387 259), lower := (rows 35 74 84 140 52 32 64 128 256), losses := [] }

theorem u36462 : Upper (D 6) (R 6) [34,72,80,132,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36462 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36463 : Route 9 := (fun mask => (mask,id))

def c36463 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36463 : Upper (D 6) (R 6) [34,72,80,132,257] 13 := by
  apply FastRouting.sound _ _ [34,72,80,132,257] 13 (by decide) (choices 1) [1,2,4] r36463 c36463
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20886
  · exact u20887
  · exact u20888

def r36464 : Route 9 := (fun mask => (mask,id))

def c36464 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36464 : Upper (D 6) (R 6) [34,72,80,132,258] 13 := by
  apply FastRouting.sound _ _ [34,72,80,132,258] 13 (by decide) (choices 1) [1,4] r36464 c36464
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u20889
  · exact u20890

def b36465 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 99, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 74 84 140 276 35 99 163 291), lower := (rows 35 74 84 140 276 32 64 128 256), losses := [] }

theorem u36465 : Upper (D 6) (R 6) [34,72,80,132,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36465 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36466 : Route 9 := (fun mask => (mask,id))

def c36466 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36466 : Upper (D 6) (R 6) [34,72,80,132,288] 13 := by
  apply FastRouting.sound _ _ [34,72,80,132,288] 13 (by decide) (choices 1) [1,2,4] r36466 c36466
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20891
  · exact u20892
  · exact u20893

def b36467 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(4,2),(4,6)], upper := (rows 35 74 84 168 19 293 325 389 261), lower := (rows 35 74 84 168 19 32 64 128 256), losses := [] }

theorem u36467 : Upper (D 6) (R 6) [34,72,80,160,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36467 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36468 : Route 9 := (fun mask => (mask,id))

def c36468 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36468 : Upper (D 6) (R 6) [34,72,80,160,5] 13 := by
  apply FastRouting.sound _ _ [34,72,80,160,5] 13 (by decide) (choices 1) [1,2,4,256] r36468 c36468
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20894
  · exact u20895
  · exact u20896
  · exact u20897

def b36469 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 20, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 35 74 84 168 22 293 325 389 261), lower := (rows 35 74 84 168 22 32 64 128 256), losses := [] }

theorem u36469 : Upper (D 6) (R 6) [34,72,80,160,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36469 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36470 : Route 9 := (fun mask => (mask,id))

def c36470 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36470 : Upper (D 6) (R 6) [34,72,80,160,257] 13 := by
  apply FastRouting.sound _ _ [34,72,80,160,257] 13 (by decide) (choices 1) [1,2,4] r36470 c36470
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20898
  · exact u20899
  · exact u20900

def r36471 : Route 9 := (fun mask => (mask,id))

def c36471 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36471 : Upper (D 6) (R 6) [34,72,80,160,258] 13 := by
  apply FastRouting.sound _ _ [34,72,80,160,258] 13 (by decide) (choices 1) [1,4] r36471 c36471
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u20901
  · exact u20902

def r36472 : Route 9 := (fun mask => (mask,id))

def c36472 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36472 : Upper (D 6) (R 6) [34,72,80,160,260] 13 := by
  apply FastRouting.sound _ _ [34,72,80,160,260] 13 (by decide) (choices 1) [1,2,4] r36472 c36472
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20903
  · exact u20904
  · exact u20905

def b36473 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 74 84 392 19 37 101 165 293), lower := (rows 35 74 84 392 19 32 64 128 256), losses := [] }

theorem u36473 : Upper (D 6) (R 6) [34,72,80,384,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36473 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36474 : Route 9 := (fun mask => (mask,id))

def c36474 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36474 : Upper (D 6) (R 6) [34,72,80,384,5] 13 := by
  apply FastRouting.sound _ _ [34,72,80,384,5] 13 (by decide) (choices 1) [1,2,4] r36474 c36474
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20906
  · exact u20907
  · exact u20908

def b36475 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 20, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 35 74 84 392 22 37 101 165 293), lower := (rows 35 74 84 392 22 32 64 128 256), losses := [] }

theorem u36475 : Upper (D 6) (R 6) [34,72,80,384,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36475 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36476 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 74 84 392 49 39 71 135 263), lower := (rows 35 74 84 392 49 32 64 128 256), losses := [] }

theorem u36476 : Upper (D 6) (R 6) [34,72,80,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36476 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36477 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 74 84 392 50 37 69 133 261), lower := (rows 35 74 84 392 50 32 64 128 256), losses := [] }

theorem u36477 : Upper (D 6) (R 6) [34,72,80,384,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36477 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36478 : Route 9 := (fun mask => (mask,id))

def c36478 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36478 : Upper (D 6) (R 6) [34,72,80,384,36] 13 := by
  apply FastRouting.sound _ _ [34,72,80,384,36] 13 (by decide) (choices 1) [1,2,4] r36478 c36478
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20909
  · exact u20910
  · exact u20911

def b36479 : PairBound 9 := { available := 404, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 74 100 13 19 436 468 404 404), lower := (rows 35 74 100 13 19 32 64 128 256), losses := [] }

theorem u36479 : Upper (D 6) (R 6) [34,72,96,5,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36479 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u36479
end Delivery.IrregularNine14.P06

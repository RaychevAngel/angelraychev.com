import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0396
import IrregularNine14P07C0397
import IrregularNine14P07C0398

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b37380 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 29, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 98 28 11 81 418 450 386 386), lower := (rows 37 98 28 11 81 32 64 128 256), losses := [] }

theorem u37380 : Upper (D 7) (R 7) [36,96,24,3,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37380 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37381 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 29, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 98 28 11 82 417 449 385 385), lower := (rows 37 98 28 11 82 32 64 128 256), losses := [] }

theorem u37381 : Upper (D 7) (R 7) [36,96,24,3,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37381 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37382 : Route 9 := (fun mask => (mask,id))

def c37382 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u37382 : Upper (D 7) (R 7) [36,96,24,3,129] 13 := by
  apply FastRouting.sound _ _ [36,96,24,3,129] 13 (by decide) (choices 1) [2,64,128,256] r37382 c37382
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23761
  · exact u23762
  · exact u23763
  · exact u23764

def r37383 : Route 9 := (fun mask => (mask,id))

def c37383 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u37383 : Upper (D 7) (R 7) [36,96,24,3,130] 13 := by
  apply FastRouting.sound _ _ [36,96,24,3,130] 13 (by decide) (choices 1) [1,64,128,256] r37383 c37383
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23765
  · exact u23766
  · exact u23767
  · exact u23768

def r37384 : Route 9 := (fun mask => (mask,id))

def c37384 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u37384 : Upper (D 7) (R 7) [36,96,24,3,192] 13 := by
  apply FastRouting.sound _ _ [36,96,24,3,192] 13 (by decide) (choices 1) [1,2,128,256] r37384 c37384
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23769
  · exact u23770
  · exact u23771
  · exact u23772

def r37385 : Route 9 := (fun mask => (mask,id))

def c37385 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37385 : Upper (D 7) (R 7) [36,96,24,3,257] 13 := by
  apply FastRouting.sound _ _ [36,96,24,3,257] 13 (by decide) (choices 1) [2,64,128] r37385 c37385
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23773
  · exact u23774
  · exact u23775

def r37386 : Route 9 := (fun mask => (mask,id))

def c37386 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37386 : Upper (D 7) (R 7) [36,96,24,3,258] 13 := by
  apply FastRouting.sound _ _ [36,96,24,3,258] 13 (by decide) (choices 1) [1,64,128] r37386 c37386
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23776
  · exact u23777
  · exact u23778

def r37387 : Route 9 := (fun mask => (mask,id))

def c37387 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37387 : Upper (D 7) (R 7) [36,96,24,3,320] 13 := by
  apply FastRouting.sound _ _ [36,96,24,3,320] 13 (by decide) (choices 1) [1,2,128] r37387 c37387
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23779
  · exact u23780
  · exact u23781

def r37388 : Route 9 := (fun mask => (mask,id))

def c37388 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37388 : Upper (D 7) (R 7) [36,96,24,3,384] 13 := by
  apply FastRouting.sound _ _ [36,96,24,3,384] 13 (by decide) (choices 1) [1,2,64,128] r37388 c37388
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23782
  · exact u23783
  · exact u23784
  · exact u23785

def r37389 : Route 9 := (fun mask => (mask,id))

def c37389 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u37389 : Upper (D 7) (R 7) [36,96,24,65,129] 13 := by
  apply FastRouting.sound _ _ [36,96,24,65,129] 13 (by decide) (choices 1) [2,128,256] r37389 c37389
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23786
  · exact u23787
  · exact u23788

def r37390 : Route 9 := (fun mask => (mask,id))

def c37390 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u37390 : Upper (D 7) (R 7) [36,96,24,65,130] 13 := by
  apply FastRouting.sound _ _ [36,96,24,65,130] 13 (by decide) (choices 1) [1,2,128,256] r37390 c37390
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23789
  · exact u23790
  · exact u23791
  · exact u23792

def r37391 : Route 9 := (fun mask => (mask,id))

def c37391 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37391 : Upper (D 7) (R 7) [36,96,24,65,257] 13 := by
  apply FastRouting.sound _ _ [36,96,24,65,257] 13 (by decide) (choices 1) [2,128] r37391 c37391
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u23793
  · exact u23794

def r37392 : Route 9 := (fun mask => (mask,id))

def c37392 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37392 : Upper (D 7) (R 7) [36,96,24,65,258] 13 := by
  apply FastRouting.sound _ _ [36,96,24,65,258] 13 (by decide) (choices 1) [1,2,128] r37392 c37392
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23795
  · exact u23796
  · exact u23797

def r37393 : Route 9 := (fun mask => (mask,id))

def c37393 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37393 : Upper (D 7) (R 7) [36,96,24,65,384] 13 := by
  apply FastRouting.sound _ _ [36,96,24,65,384] 13 (by decide) (choices 1) [1,2,128] r37393 c37393
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23798
  · exact u23799
  · exact u23800

def b37394 : PairBound 9 := { available := 387, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 37 98 28 74 145 419 451 387 387), lower := (rows 37 98 28 74 145 32 64 128 256), losses := [] }

theorem u37394 : Upper (D 7) (R 7) [36,96,24,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37394 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37395 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 37 98 28 74 146 417 449 385 385), lower := (rows 37 98 28 74 146 32 64 128 256), losses := [] }

theorem u37395 : Upper (D 7) (R 7) [36,96,24,66,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37395 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37396 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 37 98 28 74 273 163 195 131 387), lower := (rows 37 98 28 74 273 32 64 128 256), losses := [] }

theorem u37396 : Upper (D 7) (R 7) [36,96,24,66,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37396 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37397 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 37 98 28 74 274 161 193 129 385), lower := (rows 37 98 28 74 274 32 64 128 256), losses := [] }

theorem u37397 : Upper (D 7) (R 7) [36,96,24,66,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37397 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37398 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 37 98 28 74 400 163 195 131 387), lower := (rows 37 98 28 74 400 32 64 128 256), losses := [] }

theorem u37398 : Upper (D 7) (R 7) [36,96,24,66,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37398 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37399 : PairBound 9 := { available := 322, camps := [{ cop := 3, region := 20, targets := 98 }], pairs := [(2,1),(2,5),(2,6),(4,1)], upper := (rows 37 98 28 137 145 354 322 450 322), lower := (rows 37 98 28 137 145 32 64 128 256), losses := [] }

theorem u37399 : Upper (D 7) (R 7) [36,96,24,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37399 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37400 : Route 9 := (fun mask => (mask,id))

def c37400 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u37400 : Upper (D 7) (R 7) [36,96,24,129,130] 13 := by
  apply FastRouting.sound _ _ [36,96,24,129,130] 13 (by decide) (choices 1) [1,2,64,256] r37400 c37400
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23801
  · exact u23802
  · exact u23803
  · exact u23804

def r37401 : Route 9 := (fun mask => (mask,id))

def c37401 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37401 : Upper (D 7) (R 7) [36,96,24,129,192] 13 := by
  apply FastRouting.sound _ _ [36,96,24,129,192] 13 (by decide) (choices 1) [1,2,256] r37401 c37401
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23805
  · exact u23806
  · exact u23807

def r37402 : Route 9 := (fun mask => (mask,id))

def c37402 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37402 : Upper (D 7) (R 7) [36,96,24,129,257] 13 := by
  apply FastRouting.sound _ _ [36,96,24,129,257] 13 (by decide) (choices 1) [2,64,128] r37402 c37402
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23808
  · exact u23809
  · exact u23810

def r37403 : Route 9 := (fun mask => (mask,id))

def c37403 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37403 : Upper (D 7) (R 7) [36,96,24,129,258] 13 := by
  apply FastRouting.sound _ _ [36,96,24,129,258] 13 (by decide) (choices 1) [1,2,64,128] r37403 c37403
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23811
  · exact u23812
  · exact u23813
  · exact u23814

def r37404 : Route 9 := (fun mask => (mask,id))

def c37404 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37404 : Upper (D 7) (R 7) [36,96,24,129,320] 13 := by
  apply FastRouting.sound _ _ [36,96,24,129,320] 13 (by decide) (choices 1) [1,2,128] r37404 c37404
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23815
  · exact u23816
  · exact u23817

def r37405 : Route 9 := (fun mask => (mask,id))

def c37405 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37405 : Upper (D 7) (R 7) [36,96,24,129,384] 13 := by
  apply FastRouting.sound _ _ [36,96,24,129,384] 13 (by decide) (choices 1) [1,2,64] r37405 c37405
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23818
  · exact u23819
  · exact u23820

def b37406 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 20, targets := 97 }], pairs := [(2,0),(2,5),(2,6),(4,0)], upper := (rows 37 98 28 138 146 353 321 449 321), lower := (rows 37 98 28 138 146 32 64 128 256), losses := [] }

theorem u37406 : Upper (D 7) (R 7) [36,96,24,130,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37406 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37407 : Route 9 := (fun mask => (mask,id))

def c37407 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37407 : Upper (D 7) (R 7) [36,96,24,130,192] 13 := by
  apply FastRouting.sound _ _ [36,96,24,130,192] 13 (by decide) (choices 1) [1,2,256] r37407 c37407
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23821
  · exact u23822
  · exact u23823

def r37408 : Route 9 := (fun mask => (mask,id))

def c37408 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37408 : Upper (D 7) (R 7) [36,96,24,130,257] 13 := by
  apply FastRouting.sound _ _ [36,96,24,130,257] 13 (by decide) (choices 1) [1,2,64,128] r37408 c37408
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23824
  · exact u23825
  · exact u23826
  · exact u23827

def r37409 : Route 9 := (fun mask => (mask,id))

def c37409 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37409 : Upper (D 7) (R 7) [36,96,24,130,258] 13 := by
  apply FastRouting.sound _ _ [36,96,24,130,258] 13 (by decide) (choices 1) [1,64,128] r37409 c37409
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23828
  · exact u23829
  · exact u23830

def r37410 : Route 9 := (fun mask => (mask,id))

def c37410 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37410 : Upper (D 7) (R 7) [36,96,24,130,320] 13 := by
  apply FastRouting.sound _ _ [36,96,24,130,320] 13 (by decide) (choices 1) [1,2,128] r37410 c37410
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23831
  · exact u23832
  · exact u23833

def r37411 : Route 9 := (fun mask => (mask,id))

def c37411 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37411 : Upper (D 7) (R 7) [36,96,24,130,384] 13 := by
  apply FastRouting.sound _ _ [36,96,24,130,384] 13 (by decide) (choices 1) [1,2,64] r37411 c37411
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23834
  · exact u23835
  · exact u23836

def r37412 : Route 9 := (fun mask => (mask,id))

def c37412 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37412 : Upper (D 7) (R 7) [36,96,24,192,257] 13 := by
  apply FastRouting.sound _ _ [36,96,24,192,257] 13 (by decide) (choices 1) [1,2,128] r37412 c37412
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23837
  · exact u23838
  · exact u23839

def r37413 : Route 9 := (fun mask => (mask,id))

def c37413 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37413 : Upper (D 7) (R 7) [36,96,24,192,258] 13 := by
  apply FastRouting.sound _ _ [36,96,24,192,258] 13 (by decide) (choices 1) [1,2,128] r37413 c37413
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23840
  · exact u23841
  · exact u23842

def r37414 : Route 9 := (fun mask => (mask,id))

def c37414 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37414 : Upper (D 7) (R 7) [36,96,24,192,384] 13 := by
  apply FastRouting.sound _ _ [36,96,24,192,384] 13 (by decide) (choices 1) [1,2] r37414 c37414
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u23843
  · exact u23844

def b37415 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 29, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 98 76 25 19 418 450 386 386), lower := (rows 37 98 76 25 19 32 64 128 256), losses := [] }

theorem u37415 : Upper (D 7) (R 7) [36,96,72,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37415 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37416 : PairBound 9 := { available := 386, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 37 98 76 25 145 418 450 386 386), lower := (rows 37 98 76 25 145 32 64 128 256), losses := [] }

theorem u37416 : Upper (D 7) (R 7) [36,96,72,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37416 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37417 : Route 9 := (fun mask => (mask,id))

def c37417 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u37417 : Upper (D 7) (R 7) [36,96,72,17,130] 13 := by
  apply FastRouting.sound _ _ [36,96,72,17,130] 13 (by decide) (choices 1) [1,2,128,256] r37417 c37417
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23845
  · exact u23846
  · exact u23847
  · exact u23848

def b37418 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 37 98 76 25 273 162 194 130 386), lower := (rows 37 98 76 25 273 32 64 128 256), losses := [] }

theorem u37418 : Upper (D 7) (R 7) [36,96,72,17,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37418 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37419 : Route 9 := (fun mask => (mask,id))

def c37419 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37419 : Upper (D 7) (R 7) [36,96,72,17,258] 13 := by
  apply FastRouting.sound _ _ [36,96,72,17,258] 13 (by decide) (choices 1) [1,2,128] r37419 c37419
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23849
  · exact u23850
  · exact u23851

def r37420 : Route 9 := (fun mask => (mask,id))

def c37420 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37420 : Upper (D 7) (R 7) [36,96,72,17,384] 13 := by
  apply FastRouting.sound _ _ [36,96,72,17,384] 13 (by decide) (choices 1) [1,2,128] r37420 c37420
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23852
  · exact u23853
  · exact u23854

def b37421 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 29, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 98 76 26 19 417 449 385 385), lower := (rows 37 98 76 26 19 32 64 128 256), losses := [] }

theorem u37421 : Upper (D 7) (R 7) [36,96,72,18,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37421 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37422 : Route 9 := (fun mask => (mask,id))

def c37422 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u37422 : Upper (D 7) (R 7) [36,96,72,18,129] 13 := by
  apply FastRouting.sound _ _ [36,96,72,18,129] 13 (by decide) (choices 1) [1,2,128,256] r37422 c37422
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23855
  · exact u23856
  · exact u23857
  · exact u23858

def b37423 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 37 98 76 26 146 417 449 385 385), lower := (rows 37 98 76 26 146 32 64 128 256), losses := [] }

theorem u37423 : Upper (D 7) (R 7) [36,96,72,18,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37423 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37424 : Route 9 := (fun mask => (mask,id))

def c37424 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37424 : Upper (D 7) (R 7) [36,96,72,18,257] 13 := by
  apply FastRouting.sound _ _ [36,96,72,18,257] 13 (by decide) (choices 1) [1,2,128] r37424 c37424
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23859
  · exact u23860
  · exact u23861

def b37425 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 37 98 76 26 274 161 193 129 385), lower := (rows 37 98 76 26 274 32 64 128 256), losses := [] }

theorem u37425 : Upper (D 7) (R 7) [36,96,72,18,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37425 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37426 : Route 9 := (fun mask => (mask,id))

def c37426 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37426 : Upper (D 7) (R 7) [36,96,72,18,384] 13 := by
  apply FastRouting.sound _ _ [36,96,72,18,384] 13 (by decide) (choices 1) [1,2,128] r37426 c37426
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23862
  · exact u23863
  · exact u23864

def b37427 : PairBound 9 := { available := 402, camps := [{ cop := 4, region := 460, targets := 32 },{ cop := 4, region := 482, targets := 1 },{ cop := 4, region := 392, targets := 64 }], pairs := [(1,0),(2,5),(3,5),(3,6)], upper := (rows 37 98 76 137 19 434 466 402 402), lower := (rows 37 98 76 137 19 32 64 128 256), losses := [] }

theorem u37427 : Upper (D 7) (R 7) [36,96,72,129,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37427 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37428 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 16, targets := 98 },{ cop := 4, region := 8, targets := 2 }], pairs := [(3,1),(4,1),(4,5),(4,6)], upper := (rows 37 98 76 137 145 306 338 402 274), lower := (rows 37 98 76 137 145 32 64 128 256), losses := [] }

theorem u37428 : Upper (D 7) (R 7) [36,96,72,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37428 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37429 : Route 9 := (fun mask => (mask,id))

def c37429 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37429 : Upper (D 7) (R 7) [36,96,72,129,130] 13 := by
  apply FastRouting.sound _ _ [36,96,72,129,130] 13 (by decide) (choices 1) [1,2,16,256] r37429 c37429
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23865
  · exact u23866
  · exact u23867
  · exact u23868

def r37430 : Route 9 := (fun mask => (mask,id))

def c37430 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37430 : Upper (D 7) (R 7) [36,96,72,129,257] 13 := by
  apply FastRouting.sound _ _ [36,96,72,129,257] 13 (by decide) (choices 1) [2,16,128] r37430 c37430
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23869
  · exact u23870
  · exact u23871

def r37431 : Route 9 := (fun mask => (mask,id))

def c37431 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37431 : Upper (D 7) (R 7) [36,96,72,129,258] 13 := by
  apply FastRouting.sound _ _ [36,96,72,129,258] 13 (by decide) (choices 1) [1,2,16,128] r37431 c37431
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23872
  · exact u23873
  · exact u23874
  · exact u23875

def r37432 : Route 9 := (fun mask => (mask,id))

def c37432 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37432 : Upper (D 7) (R 7) [36,96,72,129,384] 13 := by
  apply FastRouting.sound _ _ [36,96,72,129,384] 13 (by decide) (choices 1) [1,2,16] r37432 c37432
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23876
  · exact u23877
  · exact u23878

def r37433 : Route 9 := (fun mask => (mask,id))

def c37433 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u37433 : Upper (D 7) (R 7) [36,96,72,130,3] 13 := by
  apply FastRouting.sound _ _ [36,96,72,130,3] 13 (by decide) (choices 1) [1,16,128,256] r37433 c37433
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23879
  · exact u23880
  · exact u23881
  · exact u23882

def r37434 : Route 9 := (fun mask => (mask,id))

def c37434 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37434 : Upper (D 7) (R 7) [36,96,72,130,129] 13 := by
  apply FastRouting.sound _ _ [36,96,72,130,129] 13 (by decide) (choices 1) [1,2,16,256] r37434 c37434
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23883
  · exact u23884
  · exact u23885
  · exact u23886

def b37435 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 16, targets := 97 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,5),(4,6)], upper := (rows 37 98 76 138 146 305 337 401 273), lower := (rows 37 98 76 138 146 32 64 128 256), losses := [] }

theorem u37435 : Upper (D 7) (R 7) [36,96,72,130,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37435 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37436 : Route 9 := (fun mask => (mask,id))

def c37436 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37436 : Upper (D 7) (R 7) [36,96,72,130,257] 13 := by
  apply FastRouting.sound _ _ [36,96,72,130,257] 13 (by decide) (choices 1) [1,2,16,128] r37436 c37436
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23887
  · exact u23888
  · exact u23889
  · exact u23890

def r37437 : Route 9 := (fun mask => (mask,id))

def c37437 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37437 : Upper (D 7) (R 7) [36,96,72,130,258] 13 := by
  apply FastRouting.sound _ _ [36,96,72,130,258] 13 (by decide) (choices 1) [1,16,128] r37437 c37437
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23891
  · exact u23892
  · exact u23893

def r37438 : Route 9 := (fun mask => (mask,id))

def c37438 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37438 : Upper (D 7) (R 7) [36,96,72,130,384] 13 := by
  apply FastRouting.sound _ _ [36,96,72,130,384] 13 (by decide) (choices 1) [1,2,16] r37438 c37438
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23894
  · exact u23895
  · exact u23896

def r37439 : Route 9 := (fun mask => (mask,id))

def c37439 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u37439 : Upper (D 7) (R 7) [36,96,72,144,3] 13 := by
  apply FastRouting.sound _ _ [36,96,72,144,3] 13 (by decide) (choices 1) [1,2,128,256] r37439 c37439
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23897
  · exact u23898
  · exact u23899
  · exact u23900

#print axioms u37439
end Delivery.IrregularNine14.P07

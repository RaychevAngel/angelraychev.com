import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0530
import IrregularNine14P07C0531
import IrregularNine14P07C0532
import IrregularNine14P07C0533
import IrregularNine14P07C0534

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r41460 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41460 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41460 : Upper (D 7) (R 7) [6,257,40,17] 13 := by
  apply FastRouting.sound _ _ [6,257,40,17] 13 (by decide) (choices 2) [34,66,96,192] r41460 c41460
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u31818
  · exact u31819
  · exact u31820
  · exact u31821

def r41461 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41461 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41461 : Upper (D 7) (R 7) [6,257,40,18] 13 := by
  apply FastRouting.sound _ _ [6,257,40,18] 13 (by decide) (choices 2) [33,65,96,192] r41461 c41461
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u31822
  · exact u31823
  · exact u31824
  · exact u31825

def b41462 : PairBound 9 := { available := 210, camps := [{ cop := 3, region := 4, targets := 195 }], pairs := [(2,0),(2,1),(2,6),(2,7)], upper := (rows 7 259 44 41 210 242 210 210 466), lower := (rows 7 259 44 41 16 32 64 128 256), losses := [] }

theorem u41462 : Upper (D 7) (R 7) [6,257,40,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41462 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41463 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 259 44 42 209 241 209 209 465), lower := (rows 7 259 44 42 16 32 64 128 256), losses := [] }

theorem u41463 : Upper (D 7) (R 7) [6,257,40,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41463 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41464 : PairBound 9 := { available := 195, camps := [{ cop := 3, region := 4, targets := 195 }], pairs := [(2,0),(2,1),(2,6),(2,7)], upper := (rows 7 259 44 56 211 227 195 195 451), lower := (rows 7 259 44 56 16 32 64 128 256), losses := [] }

theorem u41464 : Upper (D 7) (R 7) [6,257,40,48] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41464 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41465 : Route 9 := (fun mask => (mask,id))

def c41465 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41465 : Upper (D 7) (R 7) [6,257,40,65] 13 := by
  apply FastRouting.sound _ _ [6,257,40,65] 13 (by decide) (choices 2) [34,66,96,130,160,192] r41465 c41465
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31826
  · exact u31827
  · exact u31828
  · exact u31829
  · exact u31830
  · exact u31831

def r41466 : Route 9 := (fun mask => (mask,id))

def c41466 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41466 : Upper (D 7) (R 7) [6,257,40,66] 13 := by
  apply FastRouting.sound _ _ [6,257,40,66] 13 (by decide) (choices 2) [33,65,96,129,160,192] r41466 c41466
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31832
  · exact u31833
  · exact u31834
  · exact u31835
  · exact u31836
  · exact u31837

def r41467 : Route 9 := (fun mask => (mask,id))

def c41467 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41467 : Upper (D 7) (R 7) [6,257,40,80] 13 := by
  apply FastRouting.sound _ _ [6,257,40,80] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r41467 c41467
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31838
  · exact u31839
  · exact u31840
  · exact u31841
  · exact u31842
  · exact u31843
  · exact u31844
  · exact u31845
  · exact u31846
  · exact u31847

def b41468 : PairBound 9 := { available := 211, camps := [{ cop := 3, region := 4, targets := 195 }], pairs := [(2,0),(2,1),(2,6),(2,7)], upper := (rows 7 259 44 104 211 243 211 211 467), lower := (rows 7 259 44 104 16 32 64 128 256), losses := [] }

theorem u41468 : Upper (D 7) (R 7) [6,257,40,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41468 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41469 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41469 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41469 : Upper (D 7) (R 7) [6,257,40,192] 13 := by
  apply FastRouting.sound _ _ [6,257,40,192] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r41469 c41469
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31848
  · exact u31849
  · exact u31850
  · exact u31851
  · exact u31852
  · exact u31853
  · exact u31854

def b41470 : PairBound 9 := { available := 248, camps := [{ cop := 3, region := 244, targets := 3 }], pairs := [(2,0),(2,1),(4,0),(4,1)], upper := (rows 7 259 100 11 248 248 248 248 504), lower := (rows 7 259 100 11 16 32 64 128 256), losses := [] }

theorem u41470 : Upper (D 7) (R 7) [6,257,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41470 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41471 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41471 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41471 : Upper (D 7) (R 7) [6,257,96,17] 13 := by
  apply FastRouting.sound _ _ [6,257,96,17] 13 (by decide) (choices 2) [10,34,40,96,130,136,160] r41471 c41471
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31858
  · exact u31859
  · exact u31860
  · exact u31861
  · exact u31862
  · exact u31863
  · exact u31864

theorem m41472_9 : Upper (D 7) (R 7) [6,257,96,18,9] 13 :=
  permutation_upper _ _ _ [6,257,96,17,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31858

def r41472 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41472 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41472 : Upper (D 7) (R 7) [6,257,96,18] 13 := by
  apply FastRouting.sound _ _ [6,257,96,18] 13 (by decide) (choices 2) [9,33,40,96,129,136,160] r41472 c41472
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41472_9
  · exact u31865
  · exact u31866
  · exact u31867
  · exact u31868
  · exact u31869
  · exact u31870

theorem m41473_10 : Upper (D 7) (R 7) [6,257,96,33,10] 13 :=
  permutation_upper _ _ _ [6,257,96,18,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31865

def r41473 : Route 9 := (fun mask => (mask,id))

def c41473 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41473 : Upper (D 7) (R 7) [6,257,96,33] 13 := by
  apply FastRouting.sound _ _ [6,257,96,33] 13 (by decide) (choices 2) [10,66,72,130,136,192] r41473 c41473
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41473_10
  · exact u31871
  · exact u31872
  · exact u31873
  · exact u31874
  · exact u31875

theorem m41474_9 : Upper (D 7) (R 7) [6,257,96,34,9] 13 :=
  permutation_upper _ _ _ [6,257,96,17,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31859

theorem m41474_65 : Upper (D 7) (R 7) [6,257,96,34,65] 13 :=
  permutation_upper _ _ _ [6,257,96,33,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31871

def r41474 : Route 9 := (fun mask => (mask,id))

def c41474 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41474 : Upper (D 7) (R 7) [6,257,96,34] 13 := by
  apply FastRouting.sound _ _ [6,257,96,34] 13 (by decide) (choices 2) [9,65,72,129,136,192] r41474 c41474
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41474_9
  · exact m41474_65
  · exact u31876
  · exact u31877
  · exact u31878
  · exact u31879

theorem m41475_3 : Upper (D 7) (R 7) [6,257,96,48,3] 13 :=
  permutation_upper _ _ _ [6,257,96,3,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31855

theorem m41475_9 : Upper (D 7) (R 7) [6,257,96,48,9] 13 :=
  permutation_upper _ _ _ [6,257,96,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31860

theorem m41475_10 : Upper (D 7) (R 7) [6,257,96,48,10] 13 :=
  permutation_upper _ _ _ [6,257,96,18,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31866

theorem m41475_65 : Upper (D 7) (R 7) [6,257,96,48,65] 13 :=
  permutation_upper _ _ _ [6,257,96,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31872

theorem m41475_66 : Upper (D 7) (R 7) [6,257,96,48,66] 13 :=
  permutation_upper _ _ _ [6,257,96,34,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31876

def r41475 : Route 9 := (fun mask => (mask,id))

def c41475 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41475 : Upper (D 7) (R 7) [6,257,96,48] 13 := by
  apply FastRouting.sound _ _ [6,257,96,48] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192] r41475 c41475
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41475_3
  · exact m41475_9
  · exact m41475_10
  · exact m41475_65
  · exact m41475_66
  · exact u31880
  · exact u31881
  · exact u31882
  · exact u31883
  · exact u31884

def b41476 : PairBound 9 := { available := 155, camps := [{ cop := 2, region := 8, targets := 131 },{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0),(3,0),(3,1),(3,7)], upper := (rows 7 259 100 104 155 187 219 155 411), lower := (rows 7 259 100 104 16 32 64 128 256), losses := [] }

theorem u41476 : Upper (D 7) (R 7) [6,257,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41476 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m41477_10 : Upper (D 7) (R 7) [6,257,96,129,10] 13 :=
  permutation_upper _ _ _ [6,257,96,18,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31868

theorem m41477_34 : Upper (D 7) (R 7) [6,257,96,129,34] 13 :=
  permutation_upper _ _ _ [6,257,96,34,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31877

theorem m41477_40 : Upper (D 7) (R 7) [6,257,96,129,40] 13 :=
  permutation_upper _ _ _ [6,257,96,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31881

theorem m41477_96 : Upper (D 7) (R 7) [6,257,96,129,96] 13 :=
  permutation_upper _ _ _ [6,257,96,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31885

def r41477 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41477 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41477 : Upper (D 7) (R 7) [6,257,96,129] 13 := by
  apply FastRouting.sound _ _ [6,257,96,129] 13 (by decide) (choices 2) [10,34,40,96,130,136,160] r41477 c41477
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41477_10
  · exact m41477_34
  · exact m41477_40
  · exact m41477_96
  · exact u31888
  · exact u31889
  · exact u31890

theorem m41478_9 : Upper (D 7) (R 7) [6,257,96,130,9] 13 :=
  permutation_upper _ _ _ [6,257,96,17,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31862

theorem m41478_33 : Upper (D 7) (R 7) [6,257,96,130,33] 13 :=
  permutation_upper _ _ _ [6,257,96,33,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31873

theorem m41478_40 : Upper (D 7) (R 7) [6,257,96,130,40] 13 :=
  permutation_upper _ _ _ [6,257,96,48,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31882

theorem m41478_96 : Upper (D 7) (R 7) [6,257,96,130,96] 13 :=
  permutation_upper _ _ _ [6,257,96,96,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31886

theorem m41478_129 : Upper (D 7) (R 7) [6,257,96,130,129] 13 :=
  permutation_upper _ _ _ [6,257,96,129,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31888

def r41478 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41478 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41478 : Upper (D 7) (R 7) [6,257,96,130] 13 := by
  apply FastRouting.sound _ _ [6,257,96,130] 13 (by decide) (choices 2) [9,33,40,96,129,136,160] r41478 c41478
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41478_9
  · exact m41478_33
  · exact m41478_40
  · exact m41478_96
  · exact m41478_129
  · exact u31891
  · exact u31892

theorem m41479_3 : Upper (D 7) (R 7) [6,257,96,144,3] 13 :=
  permutation_upper _ _ _ [6,257,96,3,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31856

theorem m41479_9 : Upper (D 7) (R 7) [6,257,96,144,9] 13 :=
  permutation_upper _ _ _ [6,257,96,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31863

theorem m41479_10 : Upper (D 7) (R 7) [6,257,96,144,10] 13 :=
  permutation_upper _ _ _ [6,257,96,18,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31869

theorem m41479_33 : Upper (D 7) (R 7) [6,257,96,144,33] 13 :=
  permutation_upper _ _ _ [6,257,96,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31874

theorem m41479_34 : Upper (D 7) (R 7) [6,257,96,144,34] 13 :=
  permutation_upper _ _ _ [6,257,96,34,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31878

theorem m41479_40 : Upper (D 7) (R 7) [6,257,96,144,40] 13 :=
  permutation_upper _ _ _ [6,257,96,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31883

theorem m41479_96 : Upper (D 7) (R 7) [6,257,96,144,96] 13 :=
  permutation_upper _ _ _ [6,257,96,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31887

theorem m41479_129 : Upper (D 7) (R 7) [6,257,96,144,129] 13 :=
  permutation_upper _ _ _ [6,257,96,129,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31889

theorem m41479_130 : Upper (D 7) (R 7) [6,257,96,144,130] 13 :=
  permutation_upper _ _ _ [6,257,96,130,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31891

def r41479 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41479 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41479 : Upper (D 7) (R 7) [6,257,96,144] 13 := by
  apply FastRouting.sound _ _ [6,257,96,144] 13 (by decide) (choices 2) [3,9,10,33,34,40,96,129,130,136,160] r41479 c41479
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41479_3
  · exact m41479_9
  · exact m41479_10
  · exact m41479_33
  · exact m41479_34
  · exact m41479_40
  · exact m41479_96
  · exact m41479_129
  · exact m41479_130
  · exact u31893
  · exact u31894

theorem m41480_3 : Upper (D 7) (R 7) [6,257,96,160,3] 13 :=
  permutation_upper _ _ _ [6,257,96,3,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31857

theorem m41480_9 : Upper (D 7) (R 7) [6,257,96,160,9] 13 :=
  permutation_upper _ _ _ [6,257,96,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31864

theorem m41480_10 : Upper (D 7) (R 7) [6,257,96,160,10] 13 :=
  permutation_upper _ _ _ [6,257,96,18,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31870

theorem m41480_65 : Upper (D 7) (R 7) [6,257,96,160,65] 13 :=
  permutation_upper _ _ _ [6,257,96,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31875

theorem m41480_66 : Upper (D 7) (R 7) [6,257,96,160,66] 13 :=
  permutation_upper _ _ _ [6,257,96,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31879

theorem m41480_72 : Upper (D 7) (R 7) [6,257,96,160,72] 13 :=
  permutation_upper _ _ _ [6,257,96,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31884

theorem m41480_129 : Upper (D 7) (R 7) [6,257,96,160,129] 13 :=
  permutation_upper _ _ _ [6,257,96,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31890

theorem m41480_130 : Upper (D 7) (R 7) [6,257,96,160,130] 13 :=
  permutation_upper _ _ _ [6,257,96,130,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31892

theorem m41480_136 : Upper (D 7) (R 7) [6,257,96,160,136] 13 :=
  permutation_upper _ _ _ [6,257,96,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31894

def r41480 : Route 9 := (fun mask => (mask,id))

def c41480 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41480 : Upper (D 7) (R 7) [6,257,96,160] 13 := by
  apply FastRouting.sound _ _ [6,257,96,160] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192] r41480 c41480
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41480_3
  · exact m41480_9
  · exact m41480_10
  · exact m41480_65
  · exact m41480_66
  · exact m41480_72
  · exact m41480_129
  · exact m41480_130
  · exact m41480_136
  · exact u31895

def b41481 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 0, region := 244, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 7 266 21 11 240 224 224 224 480), lower := (rows 7 266 21 11 16 32 64 128 256), losses := [] }

theorem u41481 : Upper (D 7) (R 7) [6,264,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41481 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41482 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41482 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41482 : Upper (D 7) (R 7) [6,264,17,33] 13 := by
  apply FastRouting.sound _ _ [6,264,17,33] 13 (by decide) (choices 2) [34,66,96,192] r41482 c41482
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u31896
  · exact u31897
  · exact u31898
  · exact u31899

def r41483 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41483 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41483 : Upper (D 7) (R 7) [6,264,17,34] 13 := by
  apply FastRouting.sound _ _ [6,264,17,34] 13 (by decide) (choices 2) [33,65,96,192] r41483 c41483
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u31900
  · exact u31901
  · exact u31902
  · exact u31903

def r41484 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41484 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41484 : Upper (D 7) (R 7) [6,264,17,96] 13 := by
  apply FastRouting.sound _ _ [6,264,17,96] 13 (by decide) (choices 2) [3,33,34,96,129,130,160] r41484 c41484
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31904
  · exact u31905
  · exact u31906
  · exact u31907
  · exact u31908
  · exact u31909
  · exact u31910

def b41485 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 0, region := 244, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 7 266 37 11 240 240 240 240 496), lower := (rows 7 266 37 11 16 32 64 128 256), losses := [] }

theorem u41485 : Upper (D 7) (R 7) [6,264,33,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41485 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41486 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41486 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41486 : Upper (D 7) (R 7) [6,264,33,17] 13 := by
  apply FastRouting.sound _ _ [6,264,33,17] 13 (by decide) (choices 2) [34,66,96,192] r41486 c41486
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u31911
  · exact u31912
  · exact u31913
  · exact u31914

def r41487 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41487 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41487 : Upper (D 7) (R 7) [6,264,33,18] 13 := by
  apply FastRouting.sound _ _ [6,264,33,18] 13 (by decide) (choices 2) [33,65,96,192] r41487 c41487
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u31915
  · exact u31916
  · exact u31917
  · exact u31918

def b41488 : PairBound 9 := { available := 210, camps := [{ cop := 2, region := 8, targets := 194 },{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1),(3,1),(3,6),(3,7)], upper := (rows 7 266 37 41 210 242 210 210 466), lower := (rows 7 266 37 41 16 32 64 128 256), losses := [] }

theorem u41488 : Upper (D 7) (R 7) [6,264,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41488 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41489 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 266 37 42 209 241 209 209 465), lower := (rows 7 266 37 42 16 32 64 128 256), losses := [] }

theorem u41489 : Upper (D 7) (R 7) [6,264,33,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41489 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41490 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41490 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41490 : Upper (D 7) (R 7) [6,264,33,48] 13 := by
  apply FastRouting.sound _ _ [6,264,33,48] 13 (by decide) (choices 2) [3,65,66,192] r41490 c41490
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u31919
  · exact u31920
  · exact u31921
  · exact u31922

def r41491 : Route 9 := (fun mask => (mask,id))

def c41491 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41491 : Upper (D 7) (R 7) [6,264,33,65] 13 := by
  apply FastRouting.sound _ _ [6,264,33,65] 13 (by decide) (choices 2) [34,66,96,130,160,192] r41491 c41491
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31923
  · exact u31924
  · exact u31925
  · exact u31926
  · exact u31927
  · exact u31928

def r41492 : Route 9 := (fun mask => (mask,id))

def c41492 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41492 : Upper (D 7) (R 7) [6,264,33,66] 13 := by
  apply FastRouting.sound _ _ [6,264,33,66] 13 (by decide) (choices 2) [33,65,96,129,160,192] r41492 c41492
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31929
  · exact u31930
  · exact u31931
  · exact u31932
  · exact u31933
  · exact u31934

def r41493 : Route 9 := (fun mask => (mask,id))

def c41493 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41493 : Upper (D 7) (R 7) [6,264,33,80] 13 := by
  apply FastRouting.sound _ _ [6,264,33,80] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r41493 c41493
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31935
  · exact u31936
  · exact u31937
  · exact u31938
  · exact u31939
  · exact u31940
  · exact u31941
  · exact u31942
  · exact u31943
  · exact u31944

def r41494 : Route 9 := (fun mask => (mask,id))

def c41494 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41494 : Upper (D 7) (R 7) [6,264,33,96] 13 := by
  apply FastRouting.sound _ _ [6,264,33,96] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41494 c41494
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31945
  · exact u31946
  · exact u31947
  · exact u31948
  · exact u31949
  · exact u31950

def r41495 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41495 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41495 : Upper (D 7) (R 7) [6,264,33,192] 13 := by
  apply FastRouting.sound _ _ [6,264,33,192] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r41495 c41495
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31951
  · exact u31952
  · exact u31953
  · exact u31954
  · exact u31955
  · exact u31956
  · exact u31957

def b41496 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 0, region := 244, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 7 266 52 11 241 225 225 225 481), lower := (rows 7 266 52 11 16 32 64 128 256), losses := [] }

theorem u41496 : Upper (D 7) (R 7) [6,264,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41496 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41497 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41497 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41497 : Upper (D 7) (R 7) [6,264,48,33] 13 := by
  apply FastRouting.sound _ _ [6,264,48,33] 13 (by decide) (choices 2) [3,65,66,192] r41497 c41497
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u31958
  · exact u31959
  · exact u31960
  · exact u31961

def r41498 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41498 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41498 : Upper (D 7) (R 7) [6,264,48,34] 13 := by
  apply FastRouting.sound _ _ [6,264,48,34] 13 (by decide) (choices 2) [65,192] r41498 c41498
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u31962
  · exact u31963

def r41499 : Route 9 := (fun mask => (mask,id))

def c41499 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41499 : Upper (D 7) (R 7) [6,264,48,65] 13 := by
  apply FastRouting.sound _ _ [6,264,48,65] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r41499 c41499
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31964
  · exact u31965
  · exact u31966
  · exact u31967
  · exact u31968
  · exact u31969
  · exact u31970
  · exact u31971
  · exact u31972
  · exact u31973

def r41500 : Route 9 := (fun mask => (mask,id))

def c41500 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41500 : Upper (D 7) (R 7) [6,264,48,66] 13 := by
  apply FastRouting.sound _ _ [6,264,48,66] 13 (by decide) (choices 2) [33,65,96,129,160,192] r41500 c41500
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31974
  · exact u31975
  · exact u31976
  · exact u31977
  · exact u31978
  · exact u31979

def r41501 : Route 9 := (fun mask => (mask,id))

def c41501 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41501 : Upper (D 7) (R 7) [6,264,48,96] 13 := by
  apply FastRouting.sound _ _ [6,264,48,96] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41501 c41501
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31980
  · exact u31981
  · exact u31982
  · exact u31983
  · exact u31984
  · exact u31985

def r41502 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41502 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41502 : Upper (D 7) (R 7) [6,264,48,192] 13 := by
  apply FastRouting.sound _ _ [6,264,48,192] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r41502 c41502
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31986
  · exact u31987
  · exact u31988
  · exact u31989
  · exact u31990
  · exact u31991
  · exact u31992

def b41503 : PairBound 9 := { available := 241, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 0, region := 244, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 7 266 100 11 241 241 241 241 497), lower := (rows 7 266 100 11 16 32 64 128 256), losses := [] }

theorem u41503 : Upper (D 7) (R 7) [6,264,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41503 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41504 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41504 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41504 : Upper (D 7) (R 7) [6,264,96,17] 13 := by
  apply FastRouting.sound _ _ [6,264,96,17] 13 (by decide) (choices 2) [3,33,34,96,129,130,160] r41504 c41504
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31993
  · exact u31994
  · exact u31995
  · exact u31996
  · exact u31997
  · exact u31998
  · exact u31999

def r41505 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41505 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41505 : Upper (D 7) (R 7) [6,264,96,18] 13 := by
  apply FastRouting.sound _ _ [6,264,96,18] 13 (by decide) (choices 2) [33,96,129,160] r41505 c41505
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u32000
  · exact u32001
  · exact u32002
  · exact u32003

def r41506 : Route 9 := (fun mask => (mask,id))

def c41506 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41506 : Upper (D 7) (R 7) [6,264,96,33] 13 := by
  apply FastRouting.sound _ _ [6,264,96,33] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41506 c41506
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32004
  · exact u32005
  · exact u32006
  · exact u32007
  · exact u32008
  · exact u32009

def r41507 : Route 9 := (fun mask => (mask,id))

def c41507 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41507 : Upper (D 7) (R 7) [6,264,96,34] 13 := by
  apply FastRouting.sound _ _ [6,264,96,34] 13 (by decide) (choices 2) [65,129,192] r41507 c41507
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u32010
  · exact u32011
  · exact u32012

def r41508 : Route 9 := (fun mask => (mask,id))

def c41508 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41508 : Upper (D 7) (R 7) [6,264,96,48] 13 := by
  apply FastRouting.sound _ _ [6,264,96,48] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41508 c41508
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32013
  · exact u32014
  · exact u32015
  · exact u32016
  · exact u32017
  · exact u32018

def b41509 : PairBound 9 := { available := 147, camps := [{ cop := 2, region := 8, targets := 131 },{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0),(3,0),(3,1),(3,7)], upper := (rows 7 266 100 104 147 179 211 147 403), lower := (rows 7 266 100 104 16 32 64 128 256), losses := [] }

theorem u41509 : Upper (D 7) (R 7) [6,264,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41509 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41510 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41510 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41510 : Upper (D 7) (R 7) [6,264,96,129] 13 := by
  apply FastRouting.sound _ _ [6,264,96,129] 13 (by decide) (choices 2) [3,33,34,96,129,130,160] r41510 c41510
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32019
  · exact u32020
  · exact u32021
  · exact u32022
  · exact u32023
  · exact u32024
  · exact u32025

def r41511 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41511 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41511 : Upper (D 7) (R 7) [6,264,96,130] 13 := by
  apply FastRouting.sound _ _ [6,264,96,130] 13 (by decide) (choices 2) [33,96,129,160] r41511 c41511
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u32026
  · exact u32027
  · exact u32028
  · exact u32029

def r41512 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41512 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41512 : Upper (D 7) (R 7) [6,264,96,144] 13 := by
  apply FastRouting.sound _ _ [6,264,96,144] 13 (by decide) (choices 2) [3,33,34,96,129,130,160] r41512 c41512
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32030
  · exact u32031
  · exact u32032
  · exact u32033
  · exact u32034
  · exact u32035
  · exact u32036

def r41513 : Route 9 := (fun mask => (mask,id))

def c41513 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41513 : Upper (D 7) (R 7) [6,264,96,160] 13 := by
  apply FastRouting.sound _ _ [6,264,96,160] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41513 c41513
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32037
  · exact u32038
  · exact u32039
  · exact u32040
  · exact u32041
  · exact u32042

def b41514 : PairBound 9 := { available := 240, camps := [{ cop := 1, region := 13, targets := 224 }], pairs := [(0,5),(0,6),(0,7),(2,5)], upper := (rows 7 290 13 11 240 240 240 240 496), lower := (rows 7 290 13 11 16 32 64 128 256), losses := [] }

theorem u41514 : Upper (D 7) (R 7) [6,288,9,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41514 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41515 : PairBound 9 := { available := 226, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 7 290 13 25 242 226 226 226 482), lower := (rows 7 290 13 25 16 32 64 128 256), losses := [] }

theorem u41515 : Upper (D 7) (R 7) [6,288,9,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41515 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41516 : PairBound 9 := { available := 225, camps := [{ cop := 3, region := 5, targets := 224 }], pairs := [(0,5),(0,6),(0,7),(2,5)], upper := (rows 7 290 13 26 241 225 225 225 481), lower := (rows 7 290 13 26 16 32 64 128 256), losses := [] }

theorem u41516 : Upper (D 7) (R 7) [6,288,9,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41516 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41517 : PairBound 9 := { available := 210, camps := [{ cop := 1, region := 13, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 290 13 41 210 242 210 210 466), lower := (rows 7 290 13 41 16 32 64 128 256), losses := [] }

theorem u41517 : Upper (D 7) (R 7) [6,288,9,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41517 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41518 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 13, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 290 13 42 209 241 209 209 465), lower := (rows 7 290 13 42 16 32 64 128 256), losses := [] }

theorem u41518 : Upper (D 7) (R 7) [6,288,9,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41518 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41519 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41519 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41519 : Upper (D 7) (R 7) [6,288,9,48] 13 := by
  apply FastRouting.sound _ _ [6,288,9,48] 13 (by decide) (choices 2) [3,65,66,192] r41519 c41519
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u32043
  · exact u32044
  · exact u32045
  · exact u32046

#print axioms u41519
end Delivery.IrregularNine14.P07

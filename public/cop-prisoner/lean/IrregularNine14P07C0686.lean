import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0509
import IrregularNine14P07C0510
import IrregularNine14P07C0511
import IrregularNine14P07C0512
import IrregularNine14P07C0513
import IrregularNine14P07C0514

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m41160_10 : Upper (D 7) (R 7) [6,33,257,192,10] 13 :=
  permutation_upper _ _ _ [6,33,257,18,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30570

theorem m41160_34 : Upper (D 7) (R 7) [6,33,257,192,34] 13 :=
  permutation_upper _ _ _ [6,33,257,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30572

theorem m41160_40 : Upper (D 7) (R 7) [6,33,257,192,40] 13 :=
  permutation_upper _ _ _ [6,33,257,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30575

theorem m41160_66 : Upper (D 7) (R 7) [6,33,257,192,66] 13 :=
  permutation_upper _ _ _ [6,33,257,66,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30580

theorem m41160_72 : Upper (D 7) (R 7) [6,33,257,192,72] 13 :=
  permutation_upper _ _ _ [6,33,257,80,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30585

theorem m41160_96 : Upper (D 7) (R 7) [6,33,257,192,96] 13 :=
  permutation_upper _ _ _ [6,33,257,96,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30586

def r41160 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41160 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41160 : Upper (D 7) (R 7) [6,33,257,192] 13 := by
  apply FastRouting.sound _ _ [6,33,257,192] 13 (by decide) (choices 2) [10,34,40,66,72,96,192] r41160 c41160
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41160_10
  · exact m41160_34
  · exact m41160_40
  · exact m41160_66
  · exact m41160_72
  · exact m41160_96
  · exact u30587

def b41161 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 500, targets := 3 }], pairs := [(2,0),(2,1),(4,0),(4,1)], upper := (rows 7 35 268 11 240 240 240 240 496), lower := (rows 7 35 268 11 16 32 64 128 256), losses := [] }

theorem u41161 : Upper (D 7) (R 7) [6,33,264,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41161 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41162 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41162 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41162 : Upper (D 7) (R 7) [6,33,264,17] 13 := by
  apply FastRouting.sound _ _ [6,33,264,17] 13 (by decide) (choices 2) [34,66,96,192] r41162 c41162
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u30588
  · exact u30589
  · exact u30590
  · exact u30591

def r41163 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41163 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41163 : Upper (D 7) (R 7) [6,33,264,18] 13 := by
  apply FastRouting.sound _ _ [6,33,264,18] 13 (by decide) (choices 2) [33,65,96,192] r41163 c41163
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u30592
  · exact u30593
  · exact u30594
  · exact u30595

def b41164 : PairBound 9 := { available := 210, camps := [{ cop := 1, region := 8, targets := 192 },{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7),(3,6),(3,7)], upper := (rows 7 35 268 41 210 242 210 210 466), lower := (rows 7 35 268 41 16 32 64 128 256), losses := [] }

theorem u41164 : Upper (D 7) (R 7) [6,33,264,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41164 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41165 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 8, targets := 193 },{ cop := 3, region := 469, targets := 32 }], pairs := [(0,5),(3,0),(3,6),(3,7)], upper := (rows 7 35 268 42 209 241 209 209 465), lower := (rows 7 35 268 42 16 32 64 128 256), losses := [] }

theorem u41165 : Upper (D 7) (R 7) [6,33,264,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41165 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41166 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41166 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41166 : Upper (D 7) (R 7) [6,33,264,48] 13 := by
  apply FastRouting.sound _ _ [6,33,264,48] 13 (by decide) (choices 2) [3,65,66,192] r41166 c41166
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u30596
  · exact u30597
  · exact u30598
  · exact u30599

def r41167 : Route 9 := (fun mask => (mask,id))

def c41167 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41167 : Upper (D 7) (R 7) [6,33,264,65] 13 := by
  apply FastRouting.sound _ _ [6,33,264,65] 13 (by decide) (choices 2) [34,66,96,130,160,192] r41167 c41167
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30600
  · exact u30601
  · exact u30602
  · exact u30603
  · exact u30604
  · exact u30605

def r41168 : Route 9 := (fun mask => (mask,id))

def c41168 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41168 : Upper (D 7) (R 7) [6,33,264,66] 13 := by
  apply FastRouting.sound _ _ [6,33,264,66] 13 (by decide) (choices 2) [33,65,96,129,160,192] r41168 c41168
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30606
  · exact u30607
  · exact u30608
  · exact u30609
  · exact u30610
  · exact u30611

def r41169 : Route 9 := (fun mask => (mask,id))

def c41169 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41169 : Upper (D 7) (R 7) [6,33,264,80] 13 := by
  apply FastRouting.sound _ _ [6,33,264,80] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r41169 c41169
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30612
  · exact u30613
  · exact u30614
  · exact u30615
  · exact u30616
  · exact u30617
  · exact u30618
  · exact u30619
  · exact u30620
  · exact u30621

def r41170 : Route 9 := (fun mask => (mask,id))

def c41170 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41170 : Upper (D 7) (R 7) [6,33,264,96] 13 := by
  apply FastRouting.sound _ _ [6,33,264,96] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41170 c41170
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30622
  · exact u30623
  · exact u30624
  · exact u30625
  · exact u30626
  · exact u30627

def r41171 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41171 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41171 : Upper (D 7) (R 7) [6,33,264,192] 13 := by
  apply FastRouting.sound _ _ [6,33,264,192] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r41171 c41171
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30628
  · exact u30629
  · exact u30630
  · exact u30631
  · exact u30632
  · exact u30633
  · exact u30634

def b41172 : PairBound 9 := { available := 248, camps := [{ cop := 3, region := 500, targets := 3 }], pairs := [(2,0),(2,1),(4,0),(4,1)], upper := (rows 7 35 324 11 248 248 248 248 504), lower := (rows 7 35 324 11 16 32 64 128 256), losses := [] }

theorem u41172 : Upper (D 7) (R 7) [6,33,320,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41172 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41173 : Route 9 := (fun mask => (mask,id))

def c41173 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41173 : Upper (D 7) (R 7) [6,33,320,17] 13 := by
  apply FastRouting.sound _ _ [6,33,320,17] 13 (by decide) (choices 2) [10,34,40,66,72,96,130,136,160,192] r41173 c41173
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30641
  · exact u30642
  · exact u30643
  · exact u30644
  · exact u30645
  · exact u30646
  · exact u30647
  · exact u30648
  · exact u30649
  · exact u30650

theorem m41174_9 : Upper (D 7) (R 7) [6,33,320,18,9] 13 :=
  permutation_upper _ _ _ [6,33,320,17,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30641

def r41174 : Route 9 := (fun mask => (mask,id))

def c41174 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41174 : Upper (D 7) (R 7) [6,33,320,18] 13 := by
  apply FastRouting.sound _ _ [6,33,320,18] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r41174 c41174
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41174_9
  · exact u30651
  · exact u30652
  · exact u30653
  · exact u30654
  · exact u30655
  · exact u30656
  · exact u30657
  · exact u30658
  · exact u30659

def b41175 : PairBound 9 := { available := 218, camps := [{ cop := 1, region := 8, targets := 192 },{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7),(3,6),(3,7)], upper := (rows 7 35 324 41 218 250 218 218 474), lower := (rows 7 35 324 41 16 32 64 128 256), losses := [] }

theorem u41175 : Upper (D 7) (R 7) [6,33,320,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41175 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41176 : PairBound 9 := { available := 217, camps := [{ cop := 1, region := 8, targets := 193 },{ cop := 3, region := 469, targets := 32 }], pairs := [(0,5),(3,0),(3,6),(3,7)], upper := (rows 7 35 324 42 217 249 217 217 473), lower := (rows 7 35 324 42 16 32 64 128 256), losses := [] }

theorem u41176 : Upper (D 7) (R 7) [6,33,320,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41176 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m41177_3 : Upper (D 7) (R 7) [6,33,320,48,3] 13 :=
  permutation_upper _ _ _ [6,33,320,3,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30635

theorem m41177_9 : Upper (D 7) (R 7) [6,33,320,48,9] 13 :=
  permutation_upper _ _ _ [6,33,320,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30643

theorem m41177_10 : Upper (D 7) (R 7) [6,33,320,48,10] 13 :=
  permutation_upper _ _ _ [6,33,320,18,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30652

def r41177 : Route 9 := (fun mask => (mask,id))

def c41177 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41177 : Upper (D 7) (R 7) [6,33,320,48] 13 := by
  apply FastRouting.sound _ _ [6,33,320,48] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192] r41177 c41177
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41177_3
  · exact m41177_9
  · exact m41177_10
  · exact u30670
  · exact u30671
  · exact u30672
  · exact u30673
  · exact u30674
  · exact u30675
  · exact u30676

theorem m41178_10 : Upper (D 7) (R 7) [6,33,320,65,10] 13 :=
  permutation_upper _ _ _ [6,33,320,18,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30653

theorem m41178_34 : Upper (D 7) (R 7) [6,33,320,65,34] 13 :=
  permutation_upper _ _ _ [6,33,320,34,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30665

theorem m41178_40 : Upper (D 7) (R 7) [6,33,320,65,40] 13 :=
  permutation_upper _ _ _ [6,33,320,48,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30670

def r41178 : Route 9 := (fun mask => (mask,id))

def c41178 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u41178 : Upper (D 7) (R 7) [6,33,320,65] 13 := by
  apply FastRouting.sound _ _ [6,33,320,65] 13 (by decide) (choices 2) [10,34,40,130,136,160] r41178 c41178
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41178_10
  · exact m41178_34
  · exact m41178_40
  · exact u30677
  · exact u30678
  · exact u30679

theorem m41179_9 : Upper (D 7) (R 7) [6,33,320,66,9] 13 :=
  permutation_upper _ _ _ [6,33,320,17,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30644

theorem m41179_33 : Upper (D 7) (R 7) [6,33,320,66,33] 13 :=
  permutation_upper _ _ _ [6,33,320,33,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30660

theorem m41179_40 : Upper (D 7) (R 7) [6,33,320,66,40] 13 :=
  permutation_upper _ _ _ [6,33,320,48,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30671

def r41179 : Route 9 := (fun mask => (mask,id))

def c41179 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u41179 : Upper (D 7) (R 7) [6,33,320,66] 13 := by
  apply FastRouting.sound _ _ [6,33,320,66] 13 (by decide) (choices 2) [9,33,40,129,136,160] r41179 c41179
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41179_9
  · exact m41179_33
  · exact m41179_40
  · exact u30680
  · exact u30681
  · exact u30682

theorem m41180_3 : Upper (D 7) (R 7) [6,33,320,80,3] 13 :=
  permutation_upper _ _ _ [6,33,320,3,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30636

theorem m41180_9 : Upper (D 7) (R 7) [6,33,320,80,9] 13 :=
  permutation_upper _ _ _ [6,33,320,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30645

theorem m41180_10 : Upper (D 7) (R 7) [6,33,320,80,10] 13 :=
  permutation_upper _ _ _ [6,33,320,18,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30654

theorem m41180_33 : Upper (D 7) (R 7) [6,33,320,80,33] 13 :=
  permutation_upper _ _ _ [6,33,320,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30661

theorem m41180_34 : Upper (D 7) (R 7) [6,33,320,80,34] 13 :=
  permutation_upper _ _ _ [6,33,320,34,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30666

theorem m41180_40 : Upper (D 7) (R 7) [6,33,320,80,40] 13 :=
  permutation_upper _ _ _ [6,33,320,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30672

def r41180 : Route 9 := (fun mask => (mask,id))

def c41180 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u41180 : Upper (D 7) (R 7) [6,33,320,80] 13 := by
  apply FastRouting.sound _ _ [6,33,320,80] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r41180 c41180
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41180_3
  · exact m41180_9
  · exact m41180_10
  · exact m41180_33
  · exact m41180_34
  · exact m41180_40
  · exact u30683
  · exact u30684
  · exact u30685
  · exact u30686

theorem m41181_3 : Upper (D 7) (R 7) [6,33,320,96,3] 13 :=
  permutation_upper _ _ _ [6,33,320,3,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30637

theorem m41181_9 : Upper (D 7) (R 7) [6,33,320,96,9] 13 :=
  permutation_upper _ _ _ [6,33,320,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30646

theorem m41181_10 : Upper (D 7) (R 7) [6,33,320,96,10] 13 :=
  permutation_upper _ _ _ [6,33,320,18,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30655

def r41181 : Route 9 := (fun mask => (mask,id))

def c41181 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u41181 : Upper (D 7) (R 7) [6,33,320,96] 13 := by
  apply FastRouting.sound _ _ [6,33,320,96] 13 (by decide) (choices 2) [3,9,10,129,130,136] r41181 c41181
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41181_3
  · exact m41181_9
  · exact m41181_10
  · exact u30687
  · exact u30688
  · exact u30689

theorem m41182_10 : Upper (D 7) (R 7) [6,33,320,129,10] 13 :=
  permutation_upper _ _ _ [6,33,320,18,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30656

theorem m41182_34 : Upper (D 7) (R 7) [6,33,320,129,34] 13 :=
  permutation_upper _ _ _ [6,33,320,34,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30667

theorem m41182_40 : Upper (D 7) (R 7) [6,33,320,129,40] 13 :=
  permutation_upper _ _ _ [6,33,320,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30673

theorem m41182_66 : Upper (D 7) (R 7) [6,33,320,129,66] 13 :=
  permutation_upper _ _ _ [6,33,320,66,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30680

theorem m41182_72 : Upper (D 7) (R 7) [6,33,320,129,72] 13 :=
  permutation_upper _ _ _ [6,33,320,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30683

theorem m41182_96 : Upper (D 7) (R 7) [6,33,320,129,96] 13 :=
  permutation_upper _ _ _ [6,33,320,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30687

def r41182 : Route 9 := (fun mask => (mask,id))

def c41182 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41182 : Upper (D 7) (R 7) [6,33,320,129] 13 := by
  apply FastRouting.sound _ _ [6,33,320,129] 13 (by decide) (choices 2) [10,34,40,66,72,96,130,136,160,192] r41182 c41182
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41182_10
  · exact m41182_34
  · exact m41182_40
  · exact m41182_66
  · exact m41182_72
  · exact m41182_96
  · exact u30690
  · exact u30691
  · exact u30692
  · exact u30693

theorem m41183_9 : Upper (D 7) (R 7) [6,33,320,130,9] 13 :=
  permutation_upper _ _ _ [6,33,320,17,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30647

theorem m41183_33 : Upper (D 7) (R 7) [6,33,320,130,33] 13 :=
  permutation_upper _ _ _ [6,33,320,33,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30662

theorem m41183_40 : Upper (D 7) (R 7) [6,33,320,130,40] 13 :=
  permutation_upper _ _ _ [6,33,320,48,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30674

theorem m41183_65 : Upper (D 7) (R 7) [6,33,320,130,65] 13 :=
  permutation_upper _ _ _ [6,33,320,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30677

theorem m41183_72 : Upper (D 7) (R 7) [6,33,320,130,72] 13 :=
  permutation_upper _ _ _ [6,33,320,80,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30684

theorem m41183_96 : Upper (D 7) (R 7) [6,33,320,130,96] 13 :=
  permutation_upper _ _ _ [6,33,320,96,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30688

theorem m41183_129 : Upper (D 7) (R 7) [6,33,320,130,129] 13 :=
  permutation_upper _ _ _ [6,33,320,129,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30690

def r41183 : Route 9 := (fun mask => (mask,id))

def c41183 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41183 : Upper (D 7) (R 7) [6,33,320,130] 13 := by
  apply FastRouting.sound _ _ [6,33,320,130] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r41183 c41183
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41183_9
  · exact m41183_33
  · exact m41183_40
  · exact m41183_65
  · exact m41183_72
  · exact m41183_96
  · exact m41183_129
  · exact u30694
  · exact u30695
  · exact u30696

theorem m41184_3 : Upper (D 7) (R 7) [6,33,320,144,3] 13 :=
  permutation_upper _ _ _ [6,33,320,3,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30638

theorem m41184_9 : Upper (D 7) (R 7) [6,33,320,144,9] 13 :=
  permutation_upper _ _ _ [6,33,320,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30648

theorem m41184_10 : Upper (D 7) (R 7) [6,33,320,144,10] 13 :=
  permutation_upper _ _ _ [6,33,320,18,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30657

theorem m41184_33 : Upper (D 7) (R 7) [6,33,320,144,33] 13 :=
  permutation_upper _ _ _ [6,33,320,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30663

theorem m41184_34 : Upper (D 7) (R 7) [6,33,320,144,34] 13 :=
  permutation_upper _ _ _ [6,33,320,34,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30668

theorem m41184_40 : Upper (D 7) (R 7) [6,33,320,144,40] 13 :=
  permutation_upper _ _ _ [6,33,320,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30675

theorem m41184_65 : Upper (D 7) (R 7) [6,33,320,144,65] 13 :=
  permutation_upper _ _ _ [6,33,320,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30678

theorem m41184_66 : Upper (D 7) (R 7) [6,33,320,144,66] 13 :=
  permutation_upper _ _ _ [6,33,320,66,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30681

theorem m41184_72 : Upper (D 7) (R 7) [6,33,320,144,72] 13 :=
  permutation_upper _ _ _ [6,33,320,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30685

theorem m41184_96 : Upper (D 7) (R 7) [6,33,320,144,96] 13 :=
  permutation_upper _ _ _ [6,33,320,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30689

theorem m41184_129 : Upper (D 7) (R 7) [6,33,320,144,129] 13 :=
  permutation_upper _ _ _ [6,33,320,129,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30691

theorem m41184_130 : Upper (D 7) (R 7) [6,33,320,144,130] 13 :=
  permutation_upper _ _ _ [6,33,320,130,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30694

def r41184 : Route 9 := (fun mask => (mask,id))

def c41184 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41184 : Upper (D 7) (R 7) [6,33,320,144] 13 := by
  apply FastRouting.sound _ _ [6,33,320,144] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96,129,130,136,160,192] r41184 c41184
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41184_3
  · exact m41184_9
  · exact m41184_10
  · exact m41184_33
  · exact m41184_34
  · exact m41184_40
  · exact m41184_65
  · exact m41184_66
  · exact m41184_72
  · exact m41184_96
  · exact m41184_129
  · exact m41184_130
  · exact u30697
  · exact u30698
  · exact u30699

theorem m41185_3 : Upper (D 7) (R 7) [6,33,320,160,3] 13 :=
  permutation_upper _ _ _ [6,33,320,3,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30639

theorem m41185_9 : Upper (D 7) (R 7) [6,33,320,160,9] 13 :=
  permutation_upper _ _ _ [6,33,320,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30649

theorem m41185_10 : Upper (D 7) (R 7) [6,33,320,160,10] 13 :=
  permutation_upper _ _ _ [6,33,320,18,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30658

theorem m41185_65 : Upper (D 7) (R 7) [6,33,320,160,65] 13 :=
  permutation_upper _ _ _ [6,33,320,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30679

theorem m41185_66 : Upper (D 7) (R 7) [6,33,320,160,66] 13 :=
  permutation_upper _ _ _ [6,33,320,66,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30682

theorem m41185_72 : Upper (D 7) (R 7) [6,33,320,160,72] 13 :=
  permutation_upper _ _ _ [6,33,320,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30686

theorem m41185_129 : Upper (D 7) (R 7) [6,33,320,160,129] 13 :=
  permutation_upper _ _ _ [6,33,320,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30692

theorem m41185_130 : Upper (D 7) (R 7) [6,33,320,160,130] 13 :=
  permutation_upper _ _ _ [6,33,320,130,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30695

theorem m41185_136 : Upper (D 7) (R 7) [6,33,320,160,136] 13 :=
  permutation_upper _ _ _ [6,33,320,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30698

def r41185 : Route 9 := (fun mask => (mask,id))

def c41185 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41185 : Upper (D 7) (R 7) [6,33,320,160] 13 := by
  apply FastRouting.sound _ _ [6,33,320,160] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192] r41185 c41185
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41185_3
  · exact m41185_9
  · exact m41185_10
  · exact m41185_65
  · exact m41185_66
  · exact m41185_72
  · exact m41185_129
  · exact m41185_130
  · exact m41185_136
  · exact u30700

theorem m41186_3 : Upper (D 7) (R 7) [6,33,320,192,3] 13 :=
  permutation_upper _ _ _ [6,33,320,3,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30640

theorem m41186_9 : Upper (D 7) (R 7) [6,33,320,192,9] 13 :=
  permutation_upper _ _ _ [6,33,320,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30650

theorem m41186_10 : Upper (D 7) (R 7) [6,33,320,192,10] 13 :=
  permutation_upper _ _ _ [6,33,320,18,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30659

theorem m41186_33 : Upper (D 7) (R 7) [6,33,320,192,33] 13 :=
  permutation_upper _ _ _ [6,33,320,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30664

theorem m41186_34 : Upper (D 7) (R 7) [6,33,320,192,34] 13 :=
  permutation_upper _ _ _ [6,33,320,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30669

theorem m41186_40 : Upper (D 7) (R 7) [6,33,320,192,40] 13 :=
  permutation_upper _ _ _ [6,33,320,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30676

theorem m41186_129 : Upper (D 7) (R 7) [6,33,320,192,129] 13 :=
  permutation_upper _ _ _ [6,33,320,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30693

theorem m41186_130 : Upper (D 7) (R 7) [6,33,320,192,130] 13 :=
  permutation_upper _ _ _ [6,33,320,130,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30696

theorem m41186_136 : Upper (D 7) (R 7) [6,33,320,192,136] 13 :=
  permutation_upper _ _ _ [6,33,320,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30699

theorem m41186_160 : Upper (D 7) (R 7) [6,33,320,192,160] 13 :=
  permutation_upper _ _ _ [6,33,320,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30700

def r41186 : Route 9 := (fun mask => (mask,id))

def c41186 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u41186 : Upper (D 7) (R 7) [6,33,320,192] 13 := by
  apply FastRouting.sound _ _ [6,33,320,192] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r41186 c41186
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41186_3
  · exact m41186_9
  · exact m41186_10
  · exact m41186_33
  · exact m41186_34
  · exact m41186_40
  · exact m41186_129
  · exact m41186_130
  · exact m41186_136
  · exact m41186_160

def b41187 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 0, region := 500, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 7 42 21 11 496 480 480 480 480), lower := (rows 7 42 21 11 16 32 64 128 256), losses := [] }

theorem u41187 : Upper (D 7) (R 7) [6,40,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41187 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41188 : PairBound 9 := { available := 450, camps := [{ cop := 1, region := 469, targets := 32 },{ cop := 3, region := 2, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(4,5)], upper := (rows 7 42 21 41 466 482 450 450 450), lower := (rows 7 42 21 41 16 32 64 128 256), losses := [] }

theorem u41188 : Upper (D 7) (R 7) [6,40,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41188 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41189 : PairBound 9 := { available := 449, camps := [{ cop := 5, region := 10, targets := 193 }], pairs := [(1,0),(1,6),(1,7),(3,0)], upper := (rows 7 42 21 42 465 481 449 449 449), lower := (rows 7 42 21 42 16 32 64 128 256), losses := [] }

theorem u41189 : Upper (D 7) (R 7) [6,40,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41189 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41190 : Route 9 := (fun mask => (mask,id))

def c41190 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41190 : Upper (D 7) (R 7) [6,40,17,65] 13 := by
  apply FastRouting.sound _ _ [6,40,17,65] 13 (by decide) (choices 2) [34,66,96,130,160,192,258,288,320,384] r41190 c41190
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30701
  · exact u30702
  · exact u30703
  · exact u30704
  · exact u30705
  · exact u30706
  · exact u30707
  · exact u30708
  · exact u30709
  · exact u30710

def r41191 : Route 9 := (fun mask => (mask,id))

def c41191 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41191 : Upper (D 7) (R 7) [6,40,17,66] 13 := by
  apply FastRouting.sound _ _ [6,40,17,66] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r41191 c41191
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30711
  · exact u30712
  · exact u30713
  · exact u30714
  · exact u30715
  · exact u30716
  · exact u30717
  · exact u30718
  · exact u30719
  · exact u30720

def b41192 : PairBound 9 := { available := 451, camps := [{ cop := 1, region := 469, targets := 32 },{ cop := 3, region := 2, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(4,5)], upper := (rows 7 42 21 104 467 483 451 451 451), lower := (rows 7 42 21 104 16 32 64 128 256), losses := [] }

theorem u41192 : Upper (D 7) (R 7) [6,40,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41192 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41193 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41193 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41193 : Upper (D 7) (R 7) [6,40,17,192] 13 := by
  apply FastRouting.sound _ _ [6,40,17,192] 13 (by decide) (choices 2) [3,33,34,65,66,96,192,257,258,288,320] r41193 c41193
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30721
  · exact u30722
  · exact u30723
  · exact u30724
  · exact u30725
  · exact u30726
  · exact u30727
  · exact u30728
  · exact u30729
  · exact u30730
  · exact u30731

def r41194 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41194 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41194 : Upper (D 7) (R 7) [6,40,17,257] 13 := by
  apply FastRouting.sound _ _ [6,40,17,257] 13 (by decide) (choices 2) [34,66,96,192] r41194 c41194
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u30732
  · exact u30733
  · exact u30734
  · exact u30735

def r41195 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41195 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41195 : Upper (D 7) (R 7) [6,40,17,258] 13 := by
  apply FastRouting.sound _ _ [6,40,17,258] 13 (by decide) (choices 2) [33,65,96,192] r41195 c41195
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u30736
  · exact u30737
  · exact u30738
  · exact u30739

def b41196 : PairBound 9 := { available := 195, camps := [{ cop := 1, region := 213, targets := 32 },{ cop := 3, region := 2, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(4,5)], upper := (rows 7 42 21 296 211 227 195 195 451), lower := (rows 7 42 21 296 16 32 64 128 256), losses := [] }

theorem u41196 : Upper (D 7) (R 7) [6,40,17,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41196 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41197 : Route 9 := (fun mask => (mask,id))

def c41197 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41197 : Upper (D 7) (R 7) [6,40,17,320] 13 := by
  apply FastRouting.sound _ _ [6,40,17,320] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r41197 c41197
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30740
  · exact u30741
  · exact u30742
  · exact u30743
  · exact u30744
  · exact u30745
  · exact u30746
  · exact u30747
  · exact u30748
  · exact u30749

def b41198 : PairBound 9 := { available := 449, camps := [{ cop := 2, region := 11, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 42 52 11 465 481 449 449 449), lower := (rows 7 42 52 11 16 32 64 128 256), losses := [] }

theorem u41198 : Upper (D 7) (R 7) [6,40,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41198 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41199 : Route 9 := (fun mask => (mask,id))

def c41199 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41199 : Upper (D 7) (R 7) [6,40,48,65] 13 := by
  apply FastRouting.sound _ _ [6,40,48,65] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r41199 c41199
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30750
  · exact u30751
  · exact u30752
  · exact u30753
  · exact u30754
  · exact u30755
  · exact u30756
  · exact u30757
  · exact u30758
  · exact u30759

def b41200 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 472, targets := 32 }], pairs := [(2,1),(3,5),(4,1),(4,5)], upper := (rows 7 42 52 74 465 481 449 449 449), lower := (rows 7 42 52 74 16 32 64 128 256), losses := [] }

theorem u41200 : Upper (D 7) (R 7) [6,40,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41200 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41201 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41201 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41201 : Upper (D 7) (R 7) [6,40,48,192] 13 := by
  apply FastRouting.sound _ _ [6,40,48,192] 13 (by decide) (choices 2) [3,65,66,192,257,258,320] r41201 c41201
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30760
  · exact u30761
  · exact u30762
  · exact u30763
  · exact u30764
  · exact u30765
  · exact u30766

def r41202 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41202 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41202 : Upper (D 7) (R 7) [6,40,48,257] 13 := by
  apply FastRouting.sound _ _ [6,40,48,257] 13 (by decide) (choices 2) [3,65,66,192] r41202 c41202
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u30767
  · exact u30768
  · exact u30769
  · exact u30770

def b41203 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 0, region := 472, targets := 32 }], pairs := [(2,1),(3,5),(4,1),(4,5)], upper := (rows 7 42 52 266 209 225 193 193 449), lower := (rows 7 42 52 266 16 32 64 128 256), losses := [] }

theorem u41203 : Upper (D 7) (R 7) [6,40,48,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41203 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41204 : Route 9 := (fun mask => (mask,id))

def c41204 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41204 : Upper (D 7) (R 7) [6,40,48,320] 13 := by
  apply FastRouting.sound _ _ [6,40,48,320] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41204 c41204
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30771
  · exact u30772
  · exact u30773
  · exact u30774
  · exact u30775
  · exact u30776

def b41205 : PairBound 9 := { available := 496, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 0, region := 500, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 7 42 69 11 496 496 496 496 496), lower := (rows 7 42 69 11 16 32 64 128 256), losses := [] }

theorem u41205 : Upper (D 7) (R 7) [6,40,65,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41205 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41206 : Route 9 := (fun mask => (mask,id))

def c41206 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41206 : Upper (D 7) (R 7) [6,40,65,17] 13 := by
  apply FastRouting.sound _ _ [6,40,65,17] 13 (by decide) (choices 2) [34,66,96,130,160,192,258,288,320,384] r41206 c41206
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30777
  · exact u30778
  · exact u30779
  · exact u30780
  · exact u30781
  · exact u30782
  · exact u30783
  · exact u30784
  · exact u30785
  · exact u30786

def r41207 : Route 9 := (fun mask => (mask,id))

def c41207 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41207 : Upper (D 7) (R 7) [6,40,65,18] 13 := by
  apply FastRouting.sound _ _ [6,40,65,18] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r41207 c41207
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30787
  · exact u30788
  · exact u30789
  · exact u30790
  · exact u30791
  · exact u30792
  · exact u30793
  · exact u30794
  · exact u30795
  · exact u30796

def b41208 : PairBound 9 := { available := 466, camps := [{ cop := 1, region := 469, targets := 32 },{ cop := 3, region := 2, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(4,5)], upper := (rows 7 42 69 41 466 498 466 466 466), lower := (rows 7 42 69 41 16 32 64 128 256), losses := [] }

theorem u41208 : Upper (D 7) (R 7) [6,40,65,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41208 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41209 : PairBound 9 := { available := 465, camps := [{ cop := 5, region := 10, targets := 193 }], pairs := [(1,0),(1,6),(1,7),(3,0)], upper := (rows 7 42 69 42 465 497 465 465 465), lower := (rows 7 42 69 42 16 32 64 128 256), losses := [] }

theorem u41209 : Upper (D 7) (R 7) [6,40,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41209 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41210 : PairBound 9 := { available := 451, camps := [{ cop := 1, region := 469, targets := 32 },{ cop := 3, region := 2, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(4,5)], upper := (rows 7 42 69 56 467 483 451 451 451), lower := (rows 7 42 69 56 16 32 64 128 256), losses := [] }

theorem u41210 : Upper (D 7) (R 7) [6,40,65,48] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41210 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41211 : PairBound 9 := { available := 434, camps := [{ cop := 2, region := 8, targets := 162 },{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1),(3,1),(3,5),(3,7)], upper := (rows 7 42 69 73 434 434 498 434 434), lower := (rows 7 42 69 73 16 32 64 128 256), losses := [] }

theorem u41211 : Upper (D 7) (R 7) [6,40,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41211 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41212 : PairBound 9 := { available := 433, camps := [{ cop := 3, region := 5, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 42 69 74 433 433 497 433 433), lower := (rows 7 42 69 74 16 32 64 128 256), losses := [] }

theorem u41212 : Upper (D 7) (R 7) [6,40,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41212 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41213 : Route 9 := (fun mask => (mask,id))

def c41213 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 6 => 2 | 10 => 3 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u41213 : Upper (D 7) (R 7) [6,40,65,80] 13 := by
  apply FastRouting.sound _ _ [6,40,65,80] 13 (by decide) (choices 2) [3,33,34,129,130,160,257,258,288,384] r41213 c41213
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30797
  · exact u30798
  · exact u30799
  · exact u30800
  · exact u30801
  · exact u30802
  · exact u30803
  · exact u30804
  · exact u30805
  · exact u30806

def b41214 : PairBound 9 := { available := 403, camps := [{ cop := 1, region := 469, targets := 32 },{ cop := 3, region := 7, targets := 128 }], pairs := [(0,5),(0,7),(2,5),(4,5)], upper := (rows 7 42 69 104 403 435 467 403 403), lower := (rows 7 42 69 104 16 32 64 128 256), losses := [] }

theorem u41214 : Upper (D 7) (R 7) [6,40,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41214 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41215 : Route 9 := (fun mask => (mask,id))

def c41215 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41215 : Upper (D 7) (R 7) [6,40,65,129] 13 := by
  apply FastRouting.sound _ _ [6,40,65,129] 13 (by decide) (choices 2) [34,66,96,130,160,192,258,288,320,384] r41215 c41215
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30807
  · exact u30808
  · exact u30809
  · exact u30810
  · exact u30811
  · exact u30812
  · exact u30813
  · exact u30814
  · exact u30815
  · exact u30816

def r41216 : Route 9 := (fun mask => (mask,id))

def c41216 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41216 : Upper (D 7) (R 7) [6,40,65,130] 13 := by
  apply FastRouting.sound _ _ [6,40,65,130] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r41216 c41216
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30817
  · exact u30818
  · exact u30819
  · exact u30820
  · exact u30821
  · exact u30822
  · exact u30823
  · exact u30824
  · exact u30825
  · exact u30826

def r41217 : Route 9 := (fun mask => (mask,id))

def c41217 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41217 : Upper (D 7) (R 7) [6,40,65,144] 13 := by
  apply FastRouting.sound _ _ [6,40,65,144] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192,257,258,288,320,384] r41217 c41217
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30827
  · exact u30828
  · exact u30829
  · exact u30830
  · exact u30831
  · exact u30832
  · exact u30833
  · exact u30834
  · exact u30835
  · exact u30836
  · exact u30837
  · exact u30838
  · exact u30839
  · exact u30840
  · exact u30841

def b41218 : PairBound 9 := { available := 467, camps := [{ cop := 1, region := 469, targets := 32 },{ cop := 3, region := 2, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(4,5)], upper := (rows 7 42 69 168 467 499 467 467 467), lower := (rows 7 42 69 168 16 32 64 128 256), losses := [] }

theorem u41218 : Upper (D 7) (R 7) [6,40,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41218 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41219 : Route 9 := (fun mask => (mask,id))

def c41219 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 6 => 2 | 10 => 3 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u41219 : Upper (D 7) (R 7) [6,40,65,192] 13 := by
  apply FastRouting.sound _ _ [6,40,65,192] 13 (by decide) (choices 2) [3,33,34,129,130,160,257,258,288,384] r41219 c41219
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30842
  · exact u30843
  · exact u30844
  · exact u30845
  · exact u30846
  · exact u30847
  · exact u30848
  · exact u30849
  · exact u30850
  · exact u30851

#print axioms u41219
end Delivery.IrregularNine14.P07

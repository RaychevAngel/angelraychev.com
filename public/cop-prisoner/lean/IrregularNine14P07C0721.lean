import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0643
import IrregularNine14P07C0644
import IrregularNine14P07C0645
import IrregularNine14P07C0646
import IrregularNine14P07C0647

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b43260 : PairBound 9 := { available := 178, camps := [{ cop := 3, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 37 259 76 73 178 178 242 178 434), lower := (rows 37 259 76 73 16 32 64 128 256), losses := [] }

theorem u43260 : Upper (D 7) (R 7) [36,257,72,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43260 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b43261 : PairBound 9 := { available := 179, camps := [{ cop := 3, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 37 259 76 74 179 179 243 179 435), lower := (rows 37 259 76 74 16 32 64 128 256), losses := [] }

theorem u43261 : Upper (D 7) (R 7) [36,257,72,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43261 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b43262 : PairBound 9 := { available := 163, camps := [{ cop := 3, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 37 259 76 88 179 163 227 163 419), lower := (rows 37 259 76 88 16 32 64 128 256), losses := [] }

theorem u43262 : Upper (D 7) (R 7) [36,257,72,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43262 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b43263 : PairBound 9 := { available := 147, camps := [{ cop := 3, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 259 76 104 147 179 211 147 403), lower := (rows 37 259 76 104 16 32 64 128 256), losses := [] }

theorem u43263 : Upper (D 7) (R 7) [36,257,72,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43263 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r43264 : Route 9 := (fun mask => (mask,id))

def c43264 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43264 : Upper (D 7) (R 7) [36,257,72,129] 13 := by
  apply FastRouting.sound _ _ [36,257,72,129] 13 (by decide) (choices 2) [34,66,96,130,160,192] r43264 c43264
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38584
  · exact u38585
  · exact u38586
  · exact u38587
  · exact u38588
  · exact u38589

def r43265 : Route 9 := (fun mask => (mask,id))

def c43265 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43265 : Upper (D 7) (R 7) [36,257,72,130] 13 := by
  apply FastRouting.sound _ _ [36,257,72,130] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r43265 c43265
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38590
  · exact u38591
  · exact u38592
  · exact u38593
  · exact u38594
  · exact u38595
  · exact u38596
  · exact u38597
  · exact u38598
  · exact u38599

def r43266 : Route 9 := (fun mask => (mask,id))

def c43266 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43266 : Upper (D 7) (R 7) [36,257,72,144] 13 := by
  apply FastRouting.sound _ _ [36,257,72,144] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r43266 c43266
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38600
  · exact u38601
  · exact u38602
  · exact u38603
  · exact u38604
  · exact u38605
  · exact u38606
  · exact u38607
  · exact u38608
  · exact u38609

def r43267 : Route 9 := (fun mask => (mask,id))

def c43267 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43267 : Upper (D 7) (R 7) [36,257,72,160] 13 := by
  apply FastRouting.sound _ _ [36,257,72,160] 13 (by decide) (choices 2) [3,65,66,129,130,192] r43267 c43267
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38610
  · exact u38611
  · exact u38612
  · exact u38613
  · exact u38614
  · exact u38615

def b43268 : PairBound 9 := { available := 179, camps := [{ cop := 3, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 37 259 76 200 179 179 243 179 435), lower := (rows 37 259 76 200 16 32 64 128 256), losses := [] }

theorem u43268 : Upper (D 7) (R 7) [36,257,72,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43268 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b43269 : PairBound 9 := { available := 250, camps := [{ cop := 1, region := 8, targets := 224 },{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0),(3,5),(3,6),(3,7)], upper := (rows 37 259 196 11 250 250 250 250 506), lower := (rows 37 259 196 11 16 32 64 128 256), losses := [] }

theorem u43269 : Upper (D 7) (R 7) [36,257,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43269 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r43270 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c43270 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43270 : Upper (D 7) (R 7) [36,257,192,17] 13 := by
  apply FastRouting.sound _ _ [36,257,192,17] 13 (by decide) (choices 2) [10,34,40,66,72,96,192] r43270 c43270
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38622
  · exact u38623
  · exact u38624
  · exact u38625
  · exact u38626
  · exact u38627
  · exact u38628

theorem m43271_3 : Upper (D 7) (R 7) [36,257,192,18,3] 13 :=
  permutation_upper _ _ _ [36,257,192,3,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38616

theorem m43271_9 : Upper (D 7) (R 7) [36,257,192,18,9] 13 :=
  permutation_upper _ _ _ [36,257,192,17,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38622

def r43271 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c43271 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43271 : Upper (D 7) (R 7) [36,257,192,18] 13 := by
  apply FastRouting.sound _ _ [36,257,192,18] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96,192] r43271 c43271
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43271_3
  · exact m43271_9
  · exact u38629
  · exact u38630
  · exact u38631
  · exact u38632
  · exact u38633
  · exact u38634
  · exact u38635
  · exact u38636
  · exact u38637

def b43272 : PairBound 9 := { available := 218, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 259 196 41 218 250 218 218 474), lower := (rows 37 259 196 41 16 32 64 128 256), losses := [] }

theorem u43272 : Upper (D 7) (R 7) [36,257,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43272 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m43273_3 : Upper (D 7) (R 7) [36,257,192,34,3] 13 :=
  permutation_upper _ _ _ [36,257,192,3,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38617

theorem m43273_9 : Upper (D 7) (R 7) [36,257,192,34,9] 13 :=
  permutation_upper _ _ _ [36,257,192,17,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38623

theorem m43273_10 : Upper (D 7) (R 7) [36,257,192,34,10] 13 :=
  permutation_upper _ _ _ [36,257,192,18,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38631

def r43273 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c43273 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43273 : Upper (D 7) (R 7) [36,257,192,34] 13 := by
  apply FastRouting.sound _ _ [36,257,192,34] 13 (by decide) (choices 2) [3,9,10,65,66,72,192] r43273 c43273
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43273_3
  · exact m43273_9
  · exact m43273_10
  · exact u38640
  · exact u38641
  · exact u38642
  · exact u38643

theorem m43274_3 : Upper (D 7) (R 7) [36,257,192,48,3] 13 :=
  permutation_upper _ _ _ [36,257,192,3,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38618

theorem m43274_9 : Upper (D 7) (R 7) [36,257,192,48,9] 13 :=
  permutation_upper _ _ _ [36,257,192,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38624

theorem m43274_10 : Upper (D 7) (R 7) [36,257,192,48,10] 13 :=
  permutation_upper _ _ _ [36,257,192,18,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38632

def r43274 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c43274 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43274 : Upper (D 7) (R 7) [36,257,192,48] 13 := by
  apply FastRouting.sound _ _ [36,257,192,48] 13 (by decide) (choices 2) [3,9,10,65,66,72,192] r43274 c43274
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43274_3
  · exact m43274_9
  · exact m43274_10
  · exact u38644
  · exact u38645
  · exact u38646
  · exact u38647

theorem m43275_10 : Upper (D 7) (R 7) [36,257,192,65,10] 13 :=
  permutation_upper _ _ _ [36,257,192,18,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38633

theorem m43275_34 : Upper (D 7) (R 7) [36,257,192,65,34] 13 :=
  permutation_upper _ _ _ [36,257,192,34,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38640

theorem m43275_40 : Upper (D 7) (R 7) [36,257,192,65,40] 13 :=
  permutation_upper _ _ _ [36,257,192,48,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38644

def r43275 : Route 9 := (fun mask => (mask,id))

def c43275 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43275 : Upper (D 7) (R 7) [36,257,192,65] 13 := by
  apply FastRouting.sound _ _ [36,257,192,65] 13 (by decide) (choices 2) [10,34,40,130,136,160] r43275 c43275
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43275_10
  · exact m43275_34
  · exact m43275_40
  · exact u38648
  · exact u38649
  · exact u38650

theorem m43276_3 : Upper (D 7) (R 7) [36,257,192,66,3] 13 :=
  permutation_upper _ _ _ [36,257,192,3,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38619

theorem m43276_9 : Upper (D 7) (R 7) [36,257,192,66,9] 13 :=
  permutation_upper _ _ _ [36,257,192,17,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38625

theorem m43276_10 : Upper (D 7) (R 7) [36,257,192,66,10] 13 :=
  permutation_upper _ _ _ [36,257,192,18,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38634

theorem m43276_33 : Upper (D 7) (R 7) [36,257,192,66,33] 13 :=
  permutation_upper _ _ _ [36,257,192,33,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38638

theorem m43276_34 : Upper (D 7) (R 7) [36,257,192,66,34] 13 :=
  permutation_upper _ _ _ [36,257,192,34,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38641

theorem m43276_40 : Upper (D 7) (R 7) [36,257,192,66,40] 13 :=
  permutation_upper _ _ _ [36,257,192,48,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38645

theorem m43276_129 : Upper (D 7) (R 7) [36,257,192,66,129] 13 :=
  permutation_upper _ _ _ [36,257,192,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38648

def r43276 : Route 9 := (fun mask => (mask,id))

def c43276 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43276 : Upper (D 7) (R 7) [36,257,192,66] 13 := by
  apply FastRouting.sound _ _ [36,257,192,66] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r43276 c43276
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43276_3
  · exact m43276_9
  · exact m43276_10
  · exact m43276_33
  · exact m43276_34
  · exact m43276_40
  · exact m43276_129
  · exact u38651
  · exact u38652
  · exact u38653

theorem m43277_3 : Upper (D 7) (R 7) [36,257,192,80,3] 13 :=
  permutation_upper _ _ _ [36,257,192,3,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38620

theorem m43277_9 : Upper (D 7) (R 7) [36,257,192,80,9] 13 :=
  permutation_upper _ _ _ [36,257,192,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38626

theorem m43277_10 : Upper (D 7) (R 7) [36,257,192,80,10] 13 :=
  permutation_upper _ _ _ [36,257,192,18,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38635

theorem m43277_33 : Upper (D 7) (R 7) [36,257,192,80,33] 13 :=
  permutation_upper _ _ _ [36,257,192,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38639

theorem m43277_34 : Upper (D 7) (R 7) [36,257,192,80,34] 13 :=
  permutation_upper _ _ _ [36,257,192,34,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38642

theorem m43277_40 : Upper (D 7) (R 7) [36,257,192,80,40] 13 :=
  permutation_upper _ _ _ [36,257,192,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38646

theorem m43277_129 : Upper (D 7) (R 7) [36,257,192,80,129] 13 :=
  permutation_upper _ _ _ [36,257,192,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38649

theorem m43277_130 : Upper (D 7) (R 7) [36,257,192,80,130] 13 :=
  permutation_upper _ _ _ [36,257,192,66,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38652

def r43277 : Route 9 := (fun mask => (mask,id))

def c43277 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43277 : Upper (D 7) (R 7) [36,257,192,80] 13 := by
  apply FastRouting.sound _ _ [36,257,192,80] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r43277 c43277
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43277_3
  · exact m43277_9
  · exact m43277_10
  · exact m43277_33
  · exact m43277_34
  · exact m43277_40
  · exact m43277_129
  · exact m43277_130
  · exact u38654
  · exact u38655

theorem m43278_3 : Upper (D 7) (R 7) [36,257,192,96,3] 13 :=
  permutation_upper _ _ _ [36,257,192,3,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38621

theorem m43278_9 : Upper (D 7) (R 7) [36,257,192,96,9] 13 :=
  permutation_upper _ _ _ [36,257,192,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38627

theorem m43278_10 : Upper (D 7) (R 7) [36,257,192,96,10] 13 :=
  permutation_upper _ _ _ [36,257,192,18,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38636

theorem m43278_129 : Upper (D 7) (R 7) [36,257,192,96,129] 13 :=
  permutation_upper _ _ _ [36,257,192,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38650

theorem m43278_130 : Upper (D 7) (R 7) [36,257,192,96,130] 13 :=
  permutation_upper _ _ _ [36,257,192,66,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38653

theorem m43278_136 : Upper (D 7) (R 7) [36,257,192,96,136] 13 :=
  permutation_upper _ _ _ [36,257,192,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38655

def r43278 : Route 9 := (fun mask => (mask,id))

def c43278 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43278 : Upper (D 7) (R 7) [36,257,192,96] 13 := by
  apply FastRouting.sound _ _ [36,257,192,96] 13 (by decide) (choices 2) [3,9,10,129,130,136] r43278 c43278
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43278_3
  · exact m43278_9
  · exact m43278_10
  · exact m43278_129
  · exact m43278_130
  · exact m43278_136

def b43279 : PairBound 9 := { available := 59, camps := [{ cop := 2, region := 8, targets := 35 },{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0),(3,0),(3,1),(3,5)], upper := (rows 37 259 196 200 59 59 123 187 315), lower := (rows 37 259 196 200 16 32 64 128 256), losses := [] }

theorem u43279 : Upper (D 7) (R 7) [36,257,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43279 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b43280 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 8, targets := 224 },{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5),(3,5),(3,6),(3,7)], upper := (rows 37 266 7 11 240 240 240 240 496), lower := (rows 37 266 7 11 16 32 64 128 256), losses := [] }

theorem u43280 : Upper (D 7) (R 7) [36,264,3,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43280 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r43281 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c43281 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43281 : Upper (D 7) (R 7) [36,264,3,17] 13 := by
  apply FastRouting.sound _ _ [36,264,3,17] 13 (by decide) (choices 2) [34,66,96,192] r43281 c43281
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u38656
  · exact u38657
  · exact u38658
  · exact u38659

def r43282 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c43282 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43282 : Upper (D 7) (R 7) [36,264,3,18] 13 := by
  apply FastRouting.sound _ _ [36,264,3,18] 13 (by decide) (choices 2) [33,65,96,192] r43282 c43282
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u38660
  · exact u38661
  · exact u38662
  · exact u38663

def b43283 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 266 7 41 210 242 210 210 466), lower := (rows 37 266 7 41 16 32 64 128 256), losses := [] }

theorem u43283 : Upper (D 7) (R 7) [36,264,3,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43283 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b43284 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 266 7 42 209 241 209 209 465), lower := (rows 37 266 7 42 16 32 64 128 256), losses := [] }

theorem u43284 : Upper (D 7) (R 7) [36,264,3,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43284 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r43285 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c43285 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43285 : Upper (D 7) (R 7) [36,264,3,48] 13 := by
  apply FastRouting.sound _ _ [36,264,3,48] 13 (by decide) (choices 2) [3,65,66,192] r43285 c43285
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u38664
  · exact u38665
  · exact u38666
  · exact u38667

def r43286 : Route 9 := (fun mask => (mask,id))

def c43286 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43286 : Upper (D 7) (R 7) [36,264,3,65] 13 := by
  apply FastRouting.sound _ _ [36,264,3,65] 13 (by decide) (choices 2) [34,66,96,130,160,192] r43286 c43286
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38668
  · exact u38669
  · exact u38670
  · exact u38671
  · exact u38672
  · exact u38673

def r43287 : Route 9 := (fun mask => (mask,id))

def c43287 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43287 : Upper (D 7) (R 7) [36,264,3,66] 13 := by
  apply FastRouting.sound _ _ [36,264,3,66] 13 (by decide) (choices 2) [33,65,96,129,160,192] r43287 c43287
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38674
  · exact u38675
  · exact u38676
  · exact u38677
  · exact u38678
  · exact u38679

def r43288 : Route 9 := (fun mask => (mask,id))

def c43288 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43288 : Upper (D 7) (R 7) [36,264,3,80] 13 := by
  apply FastRouting.sound _ _ [36,264,3,80] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r43288 c43288
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38680
  · exact u38681
  · exact u38682
  · exact u38683
  · exact u38684
  · exact u38685
  · exact u38686
  · exact u38687
  · exact u38688
  · exact u38689

def r43289 : Route 9 := (fun mask => (mask,id))

def c43289 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43289 : Upper (D 7) (R 7) [36,264,3,96] 13 := by
  apply FastRouting.sound _ _ [36,264,3,96] 13 (by decide) (choices 2) [3,65,66,129,130,192] r43289 c43289
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38690
  · exact u38691
  · exact u38692
  · exact u38693
  · exact u38694
  · exact u38695

def r43290 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c43290 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43290 : Upper (D 7) (R 7) [36,264,3,192] 13 := by
  apply FastRouting.sound _ _ [36,264,3,192] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r43290 c43290
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38696
  · exact u38697
  · exact u38698
  · exact u38699
  · exact u38700
  · exact u38701
  · exact u38702

def r43291 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c43291 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43291 : Upper (D 7) (R 7) [36,264,17,3] 13 := by
  apply FastRouting.sound _ _ [36,264,17,3] 13 (by decide) (choices 2) [34,66,96,192] r43291 c43291
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u38703
  · exact u38704
  · exact u38705
  · exact u38706

def b43292 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 450, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 266 21 41 210 226 194 194 450), lower := (rows 37 266 21 41 16 32 64 128 256), losses := [] }

theorem u43292 : Upper (D 7) (R 7) [36,264,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43292 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r43293 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c43293 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43293 : Upper (D 7) (R 7) [36,264,17,34] 13 := by
  apply FastRouting.sound _ _ [36,264,17,34] 13 (by decide) (choices 2) [3,65,66,192] r43293 c43293
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u38707
  · exact u38708
  · exact u38709
  · exact u38710

def r43294 : Route 9 := (fun mask => (mask,id))

def c43294 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43294 : Upper (D 7) (R 7) [36,264,17,65] 13 := by
  apply FastRouting.sound _ _ [36,264,17,65] 13 (by decide) (choices 2) [34,66,96,130,160,192] r43294 c43294
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38711
  · exact u38712
  · exact u38713
  · exact u38714
  · exact u38715
  · exact u38716

def r43295 : Route 9 := (fun mask => (mask,id))

def c43295 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43295 : Upper (D 7) (R 7) [36,264,17,66] 13 := by
  apply FastRouting.sound _ _ [36,264,17,66] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r43295 c43295
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38717
  · exact u38718
  · exact u38719
  · exact u38720
  · exact u38721
  · exact u38722
  · exact u38723
  · exact u38724
  · exact u38725
  · exact u38726

def r43296 : Route 9 := (fun mask => (mask,id))

def c43296 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43296 : Upper (D 7) (R 7) [36,264,17,96] 13 := by
  apply FastRouting.sound _ _ [36,264,17,96] 13 (by decide) (choices 2) [3,65,66,129,130,192] r43296 c43296
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38727
  · exact u38728
  · exact u38729
  · exact u38730
  · exact u38731
  · exact u38732

def r43297 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c43297 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43297 : Upper (D 7) (R 7) [36,264,17,192] 13 := by
  apply FastRouting.sound _ _ [36,264,17,192] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r43297 c43297
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38733
  · exact u38734
  · exact u38735
  · exact u38736
  · exact u38737
  · exact u38738
  · exact u38739

def r43298 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c43298 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43298 : Upper (D 7) (R 7) [36,264,18,3] 13 := by
  apply FastRouting.sound _ _ [36,264,18,3] 13 (by decide) (choices 2) [33,65,96,192] r43298 c43298
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u38740
  · exact u38741
  · exact u38742
  · exact u38743

def b43299 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 450, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 266 22 41 211 227 195 195 451), lower := (rows 37 266 22 41 16 32 64 128 256), losses := [] }

theorem u43299 : Upper (D 7) (R 7) [36,264,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43299 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r43300 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c43300 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43300 : Upper (D 7) (R 7) [36,264,18,34] 13 := by
  apply FastRouting.sound _ _ [36,264,18,34] 13 (by decide) (choices 2) [65,192] r43300 c43300
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u38744
  · exact u38745

def r43301 : Route 9 := (fun mask => (mask,id))

def c43301 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43301 : Upper (D 7) (R 7) [36,264,18,65] 13 := by
  apply FastRouting.sound _ _ [36,264,18,65] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r43301 c43301
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38746
  · exact u38747
  · exact u38748
  · exact u38749
  · exact u38750
  · exact u38751
  · exact u38752
  · exact u38753
  · exact u38754
  · exact u38755

def r43302 : Route 9 := (fun mask => (mask,id))

def c43302 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43302 : Upper (D 7) (R 7) [36,264,18,66] 13 := by
  apply FastRouting.sound _ _ [36,264,18,66] 13 (by decide) (choices 2) [33,65,96,129,160,192] r43302 c43302
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38756
  · exact u38757
  · exact u38758
  · exact u38759
  · exact u38760
  · exact u38761

def r43303 : Route 9 := (fun mask => (mask,id))

def c43303 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43303 : Upper (D 7) (R 7) [36,264,18,96] 13 := by
  apply FastRouting.sound _ _ [36,264,18,96] 13 (by decide) (choices 2) [3,65,66,129,130,192] r43303 c43303
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38762
  · exact u38763
  · exact u38764
  · exact u38765
  · exact u38766
  · exact u38767

def r43304 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c43304 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43304 : Upper (D 7) (R 7) [36,264,18,192] 13 := by
  apply FastRouting.sound _ _ [36,264,18,192] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r43304 c43304
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38768
  · exact u38769
  · exact u38770
  · exact u38771
  · exact u38772
  · exact u38773
  · exact u38774

def r43305 : Route 9 := (fun mask => (mask,id))

def c43305 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43305 : Upper (D 7) (R 7) [36,264,65,3] 13 := by
  apply FastRouting.sound _ _ [36,264,65,3] 13 (by decide) (choices 2) [34,66,96,130,160,192] r43305 c43305
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38775
  · exact u38776
  · exact u38777
  · exact u38778
  · exact u38779
  · exact u38780

def r43306 : Route 9 := (fun mask => (mask,id))

def c43306 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43306 : Upper (D 7) (R 7) [36,264,65,17] 13 := by
  apply FastRouting.sound _ _ [36,264,65,17] 13 (by decide) (choices 2) [34,66,96,130,160,192] r43306 c43306
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38781
  · exact u38782
  · exact u38783
  · exact u38784
  · exact u38785
  · exact u38786

def r43307 : Route 9 := (fun mask => (mask,id))

def c43307 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43307 : Upper (D 7) (R 7) [36,264,65,18] 13 := by
  apply FastRouting.sound _ _ [36,264,65,18] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r43307 c43307
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38787
  · exact u38788
  · exact u38789
  · exact u38790
  · exact u38791
  · exact u38792
  · exact u38793
  · exact u38794
  · exact u38795
  · exact u38796

def b43308 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 266 69 41 210 242 210 210 466), lower := (rows 37 266 69 41 16 32 64 128 256), losses := [] }

theorem u43308 : Upper (D 7) (R 7) [36,264,65,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43308 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r43309 : Route 9 := (fun mask => (mask,id))

def c43309 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43309 : Upper (D 7) (R 7) [36,264,65,34] 13 := by
  apply FastRouting.sound _ _ [36,264,65,34] 13 (by decide) (choices 2) [3,65,66,129,130,192] r43309 c43309
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38797
  · exact u38798
  · exact u38799
  · exact u38800
  · exact u38801
  · exact u38802

def r43310 : Route 9 := (fun mask => (mask,id))

def c43310 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43310 : Upper (D 7) (R 7) [36,264,65,48] 13 := by
  apply FastRouting.sound _ _ [36,264,65,48] 13 (by decide) (choices 2) [3,65,66,129,130,192] r43310 c43310
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38803
  · exact u38804
  · exact u38805
  · exact u38806
  · exact u38807
  · exact u38808

def b43311 : PairBound 9 := { available := 178, camps := [{ cop := 2, region := 8, targets := 162 },{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1),(3,1),(3,5),(3,7)], upper := (rows 37 266 69 73 178 178 242 178 434), lower := (rows 37 266 69 73 16 32 64 128 256), losses := [] }

theorem u43311 : Upper (D 7) (R 7) [36,264,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43311 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r43312 : Route 9 := (fun mask => (mask,id))

def c43312 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43312 : Upper (D 7) (R 7) [36,264,65,66] 13 := by
  apply FastRouting.sound _ _ [36,264,65,66] 13 (by decide) (choices 2) [3,33,34,129,130,160] r43312 c43312
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38809
  · exact u38810
  · exact u38811
  · exact u38812
  · exact u38813
  · exact u38814

def r43313 : Route 9 := (fun mask => (mask,id))

def c43313 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43313 : Upper (D 7) (R 7) [36,264,65,80] 13 := by
  apply FastRouting.sound _ _ [36,264,65,80] 13 (by decide) (choices 2) [3,33,34,129,130,160] r43313 c43313
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38815
  · exact u38816
  · exact u38817
  · exact u38818
  · exact u38819
  · exact u38820

def b43314 : PairBound 9 := { available := 147, camps := [{ cop := 3, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 69 104 147 179 211 147 403), lower := (rows 37 266 69 104 16 32 64 128 256), losses := [] }

theorem u43314 : Upper (D 7) (R 7) [36,264,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43314 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r43315 : Route 9 := (fun mask => (mask,id))

def c43315 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43315 : Upper (D 7) (R 7) [36,264,65,129] 13 := by
  apply FastRouting.sound _ _ [36,264,65,129] 13 (by decide) (choices 2) [34,66,96,130,160,192] r43315 c43315
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38821
  · exact u38822
  · exact u38823
  · exact u38824
  · exact u38825
  · exact u38826

def r43316 : Route 9 := (fun mask => (mask,id))

def c43316 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43316 : Upper (D 7) (R 7) [36,264,65,130] 13 := by
  apply FastRouting.sound _ _ [36,264,65,130] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r43316 c43316
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38827
  · exact u38828
  · exact u38829
  · exact u38830
  · exact u38831
  · exact u38832
  · exact u38833
  · exact u38834
  · exact u38835
  · exact u38836

def r43317 : Route 9 := (fun mask => (mask,id))

def c43317 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43317 : Upper (D 7) (R 7) [36,264,65,144] 13 := by
  apply FastRouting.sound _ _ [36,264,65,144] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r43317 c43317
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38837
  · exact u38838
  · exact u38839
  · exact u38840
  · exact u38841
  · exact u38842
  · exact u38843
  · exact u38844
  · exact u38845
  · exact u38846

def r43318 : Route 9 := (fun mask => (mask,id))

def c43318 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43318 : Upper (D 7) (R 7) [36,264,65,160] 13 := by
  apply FastRouting.sound _ _ [36,264,65,160] 13 (by decide) (choices 2) [3,65,66,129,130,192] r43318 c43318
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38847
  · exact u38848
  · exact u38849
  · exact u38850
  · exact u38851
  · exact u38852

def r43319 : Route 9 := (fun mask => (mask,id))

def c43319 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43319 : Upper (D 7) (R 7) [36,264,65,192] 13 := by
  apply FastRouting.sound _ _ [36,264,65,192] 13 (by decide) (choices 2) [3,33,34,129,130,160] r43319 c43319
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38853
  · exact u38854
  · exact u38855
  · exact u38856
  · exact u38857
  · exact u38858

#print axioms u43319
end Delivery.IrregularNine14.P07

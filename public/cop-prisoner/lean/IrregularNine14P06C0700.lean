import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0560
import IrregularNine14P06C0561
import IrregularNine14P06C0562
import IrregularNine14P06C0563

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r42000 : Route 9 := (fun mask => (mask,id))

def c42000 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42000 : Upper (D 6) (R 6) [10,144,34,96] 13 := by
  apply FastRouting.sound _ _ [10,144,34,96] 13 (by decide) (choices 2) [5,65,68,257,260,320] r42000 c42000
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33603
  · exact u33604
  · exact u33605
  · exact u33606
  · exact u33607
  · exact u33608

def r42001 : Route 9 := (fun mask => (mask,id))

def c42001 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42001 : Upper (D 6) (R 6) [10,144,34,257] 13 := by
  apply FastRouting.sound _ _ [10,144,34,257] 13 (by decide) (choices 2) [5,33,36,65,68,96] r42001 c42001
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33609
  · exact u33610
  · exact u33611
  · exact u33612
  · exact u33613
  · exact u33614

def r42002 : Route 9 := (fun mask => (mask,id))

def c42002 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42002 : Upper (D 6) (R 6) [10,144,34,260] 13 := by
  apply FastRouting.sound _ _ [10,144,34,260] 13 (by decide) (choices 2) [5,33,36,65,68,96] r42002 c42002
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33615
  · exact u33616
  · exact u33617
  · exact u33618
  · exact u33619
  · exact u33620

def r42003 : Route 9 := (fun mask => (mask,id))

def c42003 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42003 : Upper (D 6) (R 6) [10,144,34,288] 13 := by
  apply FastRouting.sound _ _ [10,144,34,288] 13 (by decide) (choices 2) [5,65,68] r42003 c42003
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u33621
  · exact u33622
  · exact u33623

def r42004 : Route 9 := (fun mask => (mask,id))

def c42004 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42004 : Upper (D 6) (R 6) [10,144,34,320] 13 := by
  apply FastRouting.sound _ _ [10,144,34,320] 13 (by decide) (choices 2) [5,33,36,65,68,96] r42004 c42004
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33624
  · exact u33625
  · exact u33626
  · exact u33627
  · exact u33628
  · exact u33629

def b42005 : PairBound 9 := { available := 357, camps := [{ cop := 1, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 146 100 11 373 357 357 485 357), lower := (rows 11 146 100 11 16 32 64 128 256), losses := [] }

theorem u42005 : Upper (D 6) (R 6) [10,144,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42005 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42006 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c42006 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42006 : Upper (D 6) (R 6) [10,144,96,5] 13 := by
  apply FastRouting.sound _ _ [10,144,96,5] 13 (by decide) (choices 2) [3,5,6,33,34,36,96,257,258,260,288] r42006 c42006
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33630
  · exact u33631
  · exact u33632
  · exact u33633
  · exact u33634
  · exact u33635
  · exact u33636
  · exact u33637
  · exact u33638
  · exact u33639
  · exact u33640

def b42007 : PairBound 9 := { available := 357, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 146 100 14 373 357 357 485 357), lower := (rows 11 146 100 14 16 32 64 128 256), losses := [] }

theorem u42007 : Upper (D 6) (R 6) [10,144,96,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42007 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42008 : Route 9 := (fun mask => (mask,id))

def c42008 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42008 : Upper (D 6) (R 6) [10,144,96,33] 13 := by
  apply FastRouting.sound _ _ [10,144,96,33] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r42008 c42008
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33641
  · exact u33642
  · exact u33643
  · exact u33644
  · exact u33645
  · exact u33646
  · exact u33647
  · exact u33648
  · exact u33649
  · exact u33650

def b42009 : PairBound 9 := { available := 325, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 146 100 42 341 357 325 453 325), lower := (rows 11 146 100 42 16 32 64 128 256), losses := [] }

theorem u42009 : Upper (D 6) (R 6) [10,144,96,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42009 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42010 : PairBound 9 := { available := 327, camps := [{ cop := 2, region := 8, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 146 100 44 343 359 327 455 327), lower := (rows 11 146 100 44 16 32 64 128 256), losses := [] }

theorem u42010 : Upper (D 6) (R 6) [10,144,96,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42010 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42011 : PairBound 9 := { available := 263, camps := [{ cop := 2, region := 8, targets := 3 },{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0),(3,0),(3,1)], upper := (rows 11 146 100 104 279 295 327 391 263), lower := (rows 11 146 100 104 16 32 64 128 256), losses := [] }

theorem u42011 : Upper (D 6) (R 6) [10,144,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42011 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42012 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c42012 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42012 : Upper (D 6) (R 6) [10,144,96,257] 13 := by
  apply FastRouting.sound _ _ [10,144,96,257] 13 (by decide) (choices 2) [3,5,6,33,34,36,96] r42012 c42012
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33651
  · exact u33652
  · exact u33653
  · exact u33654
  · exact u33655
  · exact u33656
  · exact u33657

def b42013 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 146 100 266 117 101 101 229 357), lower := (rows 11 146 100 266 16 32 64 128 256), losses := [] }

theorem u42013 : Upper (D 6) (R 6) [10,144,96,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42013 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42014 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c42014 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42014 : Upper (D 6) (R 6) [10,144,96,260] 13 := by
  apply FastRouting.sound _ _ [10,144,96,260] 13 (by decide) (choices 2) [3,5,6,33,34,36,96] r42014 c42014
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33658
  · exact u33659
  · exact u33660
  · exact u33661
  · exact u33662
  · exact u33663
  · exact u33664

def r42015 : Route 9 := (fun mask => (mask,id))

def c42015 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42015 : Upper (D 6) (R 6) [10,144,96,288] 13 := by
  apply FastRouting.sound _ _ [10,144,96,288] 13 (by decide) (choices 2) [3,5,6,65,66,68] r42015 c42015
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33665
  · exact u33666
  · exact u33667
  · exact u33668
  · exact u33669
  · exact u33670

def b42016 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 146 261 11 116 100 100 228 356), lower := (rows 11 146 261 11 16 32 64 128 256), losses := [] }

theorem u42016 : Upper (D 6) (R 6) [10,144,257,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42016 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42017 : PairBound 9 := { available := 102, camps := [{ cop := 2, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 11 146 261 13 118 102 102 230 358), lower := (rows 11 146 261 13 16 32 64 128 256), losses := [] }

theorem u42017 : Upper (D 6) (R 6) [10,144,257,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42017 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42018 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 146 261 14 117 101 101 229 357), lower := (rows 11 146 261 14 16 32 64 128 256), losses := [] }

theorem u42018 : Upper (D 6) (R 6) [10,144,257,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42018 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42019 : Route 9 := (fun mask => (mask,id))

def c42019 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42019 : Upper (D 6) (R 6) [10,144,257,33] 13 := by
  apply FastRouting.sound _ _ [10,144,257,33] 13 (by decide) (choices 2) [6,34,36,66,68,96] r42019 c42019
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33671
  · exact u33672
  · exact u33673
  · exact u33674
  · exact u33675
  · exact u33676

def b42020 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 146 261 42 117 101 101 229 357), lower := (rows 11 146 261 42 16 32 64 128 256), losses := [] }

theorem u42020 : Upper (D 6) (R 6) [10,144,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42020 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42021 : Route 9 := (fun mask => (mask,id))

def c42021 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42021 : Upper (D 6) (R 6) [10,144,257,36] 13 := by
  apply FastRouting.sound _ _ [10,144,257,36] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r42021 c42021
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33677
  · exact u33678
  · exact u33679
  · exact u33680
  · exact u33681
  · exact u33682
  · exact u33683
  · exact u33684
  · exact u33685
  · exact u33686

def r42022 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c42022 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42022 : Upper (D 6) (R 6) [10,144,257,96] 13 := by
  apply FastRouting.sound _ _ [10,144,257,96] 13 (by decide) (choices 2) [3,5,6,33,34,36,96] r42022 c42022
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33687
  · exact u33688
  · exact u33689
  · exact u33690
  · exact u33691
  · exact u33692
  · exact u33693

def b42023 : PairBound 9 := { available := 101, camps := [{ cop := 2, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 146 262 13 117 101 101 229 357), lower := (rows 11 146 262 13 16 32 64 128 256), losses := [] }

theorem u42023 : Upper (D 6) (R 6) [10,144,258,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42023 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42024 : Route 9 := (fun mask => (mask,id))

def c42024 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42024 : Upper (D 6) (R 6) [10,144,258,33] 13 := by
  apply FastRouting.sound _ _ [10,144,258,33] 13 (by decide) (choices 2) [5,33,36,65,68,96] r42024 c42024
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33694
  · exact u33695
  · exact u33696
  · exact u33697
  · exact u33698
  · exact u33699

def r42025 : Route 9 := (fun mask => (mask,id))

def c42025 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42025 : Upper (D 6) (R 6) [10,144,258,36] 13 := by
  apply FastRouting.sound _ _ [10,144,258,36] 13 (by decide) (choices 2) [5,33,36,65,68,96] r42025 c42025
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33700
  · exact u33701
  · exact u33702
  · exact u33703
  · exact u33704
  · exact u33705

def r42026 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c42026 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42026 : Upper (D 6) (R 6) [10,144,258,96] 13 := by
  apply FastRouting.sound _ _ [10,144,258,96] 13 (by decide) (choices 2) [5,33,36,96] r42026 c42026
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u33706
  · exact u33707
  · exact u33708
  · exact u33709

def b42027 : PairBound 9 := { available := 101, camps := [{ cop := 1, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 146 292 11 117 101 101 229 357), lower := (rows 11 146 292 11 16 32 64 128 256), losses := [] }

theorem u42027 : Upper (D 6) (R 6) [10,144,288,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42027 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42028 : Route 9 := (fun mask => (mask,id))

def c42028 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42028 : Upper (D 6) (R 6) [10,144,288,5] 13 := by
  apply FastRouting.sound _ _ [10,144,288,5] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r42028 c42028
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33710
  · exact u33711
  · exact u33712
  · exact u33713
  · exact u33714
  · exact u33715
  · exact u33716
  · exact u33717
  · exact u33718
  · exact u33719

def b42029 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 146 292 14 117 101 101 229 357), lower := (rows 11 146 292 14 16 32 64 128 256), losses := [] }

theorem u42029 : Upper (D 6) (R 6) [10,144,288,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42029 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42030 : Route 9 := (fun mask => (mask,id))

def c42030 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42030 : Upper (D 6) (R 6) [10,144,288,33] 13 := by
  apply FastRouting.sound _ _ [10,144,288,33] 13 (by decide) (choices 2) [3,5,6,65,66,68] r42030 c42030
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33720
  · exact u33721
  · exact u33722
  · exact u33723
  · exact u33724
  · exact u33725

def b42031 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 146 292 42 85 101 69 197 325), lower := (rows 11 146 292 42 16 32 64 128 256), losses := [] }

theorem u42031 : Upper (D 6) (R 6) [10,144,288,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42031 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42032 : PairBound 9 := { available := 71, camps := [{ cop := 2, region := 8, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 146 292 44 87 103 71 199 327), lower := (rows 11 146 292 44 16 32 64 128 256), losses := [] }

theorem u42032 : Upper (D 6) (R 6) [10,144,288,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42032 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42033 : Route 9 := (fun mask => (mask,id))

def c42033 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42033 : Upper (D 6) (R 6) [10,144,288,65] 13 := by
  apply FastRouting.sound _ _ [10,144,288,65] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r42033 c42033
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33726
  · exact u33727
  · exact u33728
  · exact u33729
  · exact u33730
  · exact u33731
  · exact u33732
  · exact u33733
  · exact u33734
  · exact u33735

def b42034 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 146 292 74 117 101 101 229 357), lower := (rows 11 146 292 74 16 32 64 128 256), losses := [] }

theorem u42034 : Upper (D 6) (R 6) [10,144,288,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42034 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42035 : Route 9 := (fun mask => (mask,id))

def c42035 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42035 : Upper (D 6) (R 6) [10,144,288,68] 13 := by
  apply FastRouting.sound _ _ [10,144,288,68] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r42035 c42035
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33736
  · exact u33737
  · exact u33738
  · exact u33739
  · exact u33740
  · exact u33741
  · exact u33742
  · exact u33743
  · exact u33744
  · exact u33745

def r42036 : Route 9 := (fun mask => (mask,id))

def c42036 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42036 : Upper (D 6) (R 6) [10,144,288,96] 13 := by
  apply FastRouting.sound _ _ [10,144,288,96] 13 (by decide) (choices 2) [3,5,6,65,66,68] r42036 c42036
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33746
  · exact u33747
  · exact u33748
  · exact u33749
  · exact u33750
  · exact u33751

def b42037 : PairBound 9 := { available := 357, camps := [{ cop := 2, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 162 22 13 373 357 357 485 357), lower := (rows 11 162 22 13 16 32 64 128 256), losses := [] }

theorem u42037 : Upper (D 6) (R 6) [10,160,18,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42037 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42038 : PairBound 9 := { available := 325, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 162 22 41 341 357 325 453 325), lower := (rows 11 162 22 41 16 32 64 128 256), losses := [] }

theorem u42038 : Upper (D 6) (R 6) [10,160,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42038 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m42039_5 : Upper (D 6) (R 6) [10,160,18,36,5] 13 :=
  permutation_upper _ _ _ [10,160,18,5,33] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33752

def r42039 : Route 9 := (fun mask => (mask,id))

def c42039 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42039 : Upper (D 6) (R 6) [10,160,18,36] 13 := by
  apply FastRouting.sound _ _ [10,160,18,36] 13 (by decide) (choices 2) [5,65,68,257,260,320] r42039 c42039
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42039_5
  · exact u33765
  · exact u33766
  · exact u33767
  · exact u33768
  · exact u33769

theorem m42040_5 : Upper (D 6) (R 6) [10,160,18,65,5] 13 :=
  permutation_upper _ _ _ [10,160,18,5,68] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33754

theorem m42040_33 : Upper (D 6) (R 6) [10,160,18,65,33] 13 :=
  permutation_upper _ _ _ [10,160,18,36,68] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33766

theorem m42040_36 : Upper (D 6) (R 6) [10,160,18,65,36] 13 :=
  permutation_upper _ _ _ [10,160,18,33,68] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33761

def r42040 : Route 9 := (fun mask => (mask,id))

def c42040 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42040 : Upper (D 6) (R 6) [10,160,18,65] 13 := by
  apply FastRouting.sound _ _ [10,160,18,65] 13 (by decide) (choices 2) [5,33,36,65,68,96,257,260,288,320] r42040 c42040
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42040_5
  · exact m42040_33
  · exact m42040_36
  · exact u33770
  · exact u33771
  · exact u33772
  · exact u33773
  · exact u33774
  · exact u33775
  · exact u33776

theorem m42041_5 : Upper (D 6) (R 6) [10,160,18,68,5] 13 :=
  permutation_upper _ _ _ [10,160,18,5,65] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33753

theorem m42041_33 : Upper (D 6) (R 6) [10,160,18,68,33] 13 :=
  permutation_upper _ _ _ [10,160,18,36,65] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33765

theorem m42041_36 : Upper (D 6) (R 6) [10,160,18,68,36] 13 :=
  permutation_upper _ _ _ [10,160,18,33,65] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33760

theorem m42041_68 : Upper (D 6) (R 6) [10,160,18,68,68] 13 :=
  permutation_upper _ _ _ [10,160,18,65,65] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33770

def r42041 : Route 9 := (fun mask => (mask,id))

def c42041 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42041 : Upper (D 6) (R 6) [10,160,18,68] 13 := by
  apply FastRouting.sound _ _ [10,160,18,68] 13 (by decide) (choices 2) [5,33,36,65,68,96,257,260,288,320] r42041 c42041
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42041_5
  · exact m42041_33
  · exact m42041_36
  · exact u33777
  · exact m42041_68
  · exact u33778
  · exact u33779
  · exact u33780
  · exact u33781
  · exact u33782

theorem m42042_5 : Upper (D 6) (R 6) [10,160,18,96,5] 13 :=
  permutation_upper _ _ _ [10,160,18,5,96] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33755

theorem m42042_65 : Upper (D 6) (R 6) [10,160,18,96,65] 13 :=
  permutation_upper _ _ _ [10,160,18,68,96] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33778

theorem m42042_68 : Upper (D 6) (R 6) [10,160,18,96,68] 13 :=
  permutation_upper _ _ _ [10,160,18,65,96] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33772

def r42042 : Route 9 := (fun mask => (mask,id))

def c42042 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42042 : Upper (D 6) (R 6) [10,160,18,96] 13 := by
  apply FastRouting.sound _ _ [10,160,18,96] 13 (by decide) (choices 2) [5,65,68,257,260,320] r42042 c42042
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42042_5
  · exact m42042_65
  · exact m42042_68
  · exact u33783
  · exact u33784
  · exact u33785

theorem m42043_5 : Upper (D 6) (R 6) [10,160,18,257,5] 13 :=
  permutation_upper _ _ _ [10,160,18,5,260] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33757

theorem m42043_33 : Upper (D 6) (R 6) [10,160,18,257,33] 13 :=
  permutation_upper _ _ _ [10,160,18,36,260] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33768

theorem m42043_36 : Upper (D 6) (R 6) [10,160,18,257,36] 13 :=
  permutation_upper _ _ _ [10,160,18,33,260] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33763

theorem m42043_65 : Upper (D 6) (R 6) [10,160,18,257,65] 13 :=
  permutation_upper _ _ _ [10,160,18,68,260] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33780

theorem m42043_68 : Upper (D 6) (R 6) [10,160,18,257,68] 13 :=
  permutation_upper _ _ _ [10,160,18,65,260] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33774

theorem m42043_96 : Upper (D 6) (R 6) [10,160,18,257,96] 13 :=
  permutation_upper _ _ _ [10,160,18,96,260] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33784

def r42043 : Route 9 := (fun mask => (mask,id))

def c42043 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42043 : Upper (D 6) (R 6) [10,160,18,257] 13 := by
  apply FastRouting.sound _ _ [10,160,18,257] 13 (by decide) (choices 2) [5,33,36,65,68,96] r42043 c42043
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42043_5
  · exact m42043_33
  · exact m42043_36
  · exact m42043_65
  · exact m42043_68
  · exact m42043_96

theorem m42044_5 : Upper (D 6) (R 6) [10,160,18,260,5] 13 :=
  permutation_upper _ _ _ [10,160,18,5,257] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33756

theorem m42044_33 : Upper (D 6) (R 6) [10,160,18,260,33] 13 :=
  permutation_upper _ _ _ [10,160,18,36,257] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33767

theorem m42044_36 : Upper (D 6) (R 6) [10,160,18,260,36] 13 :=
  permutation_upper _ _ _ [10,160,18,33,257] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33762

theorem m42044_65 : Upper (D 6) (R 6) [10,160,18,260,65] 13 :=
  permutation_upper _ _ _ [10,160,18,68,257] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33779

theorem m42044_68 : Upper (D 6) (R 6) [10,160,18,260,68] 13 :=
  permutation_upper _ _ _ [10,160,18,65,257] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33773

theorem m42044_96 : Upper (D 6) (R 6) [10,160,18,260,96] 13 :=
  permutation_upper _ _ _ [10,160,18,96,257] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33783

def r42044 : Route 9 := (fun mask => (mask,id))

def c42044 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42044 : Upper (D 6) (R 6) [10,160,18,260] 13 := by
  apply FastRouting.sound _ _ [10,160,18,260] 13 (by decide) (choices 2) [5,33,36,65,68,96] r42044 c42044
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42044_5
  · exact m42044_33
  · exact m42044_36
  · exact m42044_65
  · exact m42044_68
  · exact m42044_96

theorem m42045_5 : Upper (D 6) (R 6) [10,160,18,288,5] 13 :=
  permutation_upper _ _ _ [10,160,18,5,288] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33758

theorem m42045_65 : Upper (D 6) (R 6) [10,160,18,288,65] 13 :=
  permutation_upper _ _ _ [10,160,18,68,288] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33781

theorem m42045_68 : Upper (D 6) (R 6) [10,160,18,288,68] 13 :=
  permutation_upper _ _ _ [10,160,18,65,288] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33775

def r42045 : Route 9 := (fun mask => (mask,id))

def c42045 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42045 : Upper (D 6) (R 6) [10,160,18,288] 13 := by
  apply FastRouting.sound _ _ [10,160,18,288] 13 (by decide) (choices 2) [5,65,68] r42045 c42045
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m42045_5
  · exact m42045_65
  · exact m42045_68

theorem m42046_5 : Upper (D 6) (R 6) [10,160,18,320,5] 13 :=
  permutation_upper _ _ _ [10,160,18,5,320] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33759

theorem m42046_33 : Upper (D 6) (R 6) [10,160,18,320,33] 13 :=
  permutation_upper _ _ _ [10,160,18,36,320] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33769

theorem m42046_36 : Upper (D 6) (R 6) [10,160,18,320,36] 13 :=
  permutation_upper _ _ _ [10,160,18,33,320] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33764

theorem m42046_65 : Upper (D 6) (R 6) [10,160,18,320,65] 13 :=
  permutation_upper _ _ _ [10,160,18,68,320] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33782

theorem m42046_68 : Upper (D 6) (R 6) [10,160,18,320,68] 13 :=
  permutation_upper _ _ _ [10,160,18,65,320] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33776

theorem m42046_96 : Upper (D 6) (R 6) [10,160,18,320,96] 13 :=
  permutation_upper _ _ _ [10,160,18,96,320] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33785

def r42046 : Route 9 := (fun mask => (mask,id))

def c42046 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42046 : Upper (D 6) (R 6) [10,160,18,320] 13 := by
  apply FastRouting.sound _ _ [10,160,18,320] 13 (by decide) (choices 2) [5,33,36,65,68,96] r42046 c42046
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42046_5
  · exact m42046_33
  · exact m42046_36
  · exact m42046_65
  · exact m42046_68
  · exact m42046_96

def b42047 : PairBound 9 := { available := 340, camps := [{ cop := 1, region := 9, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 162 37 11 340 372 340 468 340), lower := (rows 11 162 37 11 16 32 64 128 256), losses := [] }

theorem u42047 : Upper (D 6) (R 6) [10,160,33,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42047 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42048 : PairBound 9 := { available := 342, camps := [{ cop := 1, region := 13, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 162 37 13 342 374 342 470 342), lower := (rows 11 162 37 13 16 32 64 128 256), losses := [] }

theorem u42048 : Upper (D 6) (R 6) [10,160,33,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42048 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42049 : PairBound 9 := { available := 341, camps := [{ cop := 1, region := 13, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 162 37 14 341 373 341 469 341), lower := (rows 11 162 37 14 16 32 64 128 256), losses := [] }

theorem u42049 : Upper (D 6) (R 6) [10,160,33,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42049 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42050 : Route 9 := (fun mask => (mask,id))

def c42050 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42050 : Upper (D 6) (R 6) [10,160,33,17] 13 := by
  apply FastRouting.sound _ _ [10,160,33,17] 13 (by decide) (choices 2) [6,66,68,258,260,320] r42050 c42050
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33786
  · exact u33787
  · exact u33788
  · exact u33789
  · exact u33790
  · exact u33791

def b42051 : PairBound 9 := { available := 325, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 162 37 26 341 357 325 453 325), lower := (rows 11 162 37 26 16 32 64 128 256), losses := [] }

theorem u42051 : Upper (D 6) (R 6) [10,160,33,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42051 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42052 : Route 9 := (fun mask => (mask,id))

def c42052 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42052 : Upper (D 6) (R 6) [10,160,33,20] 13 := by
  apply FastRouting.sound _ _ [10,160,33,20] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r42052 c42052
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33792
  · exact u33793
  · exact u33794
  · exact u33795
  · exact u33796
  · exact u33797
  · exact u33798
  · exact u33799
  · exact u33800
  · exact u33801

def r42053 : Route 9 := (fun mask => (mask,id))

def c42053 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42053 : Upper (D 6) (R 6) [10,160,33,65] 13 := by
  apply FastRouting.sound _ _ [10,160,33,65] 13 (by decide) (choices 2) [6,66,68,258,260,320] r42053 c42053
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33802
  · exact u33803
  · exact u33804
  · exact u33805
  · exact u33806
  · exact u33807

def b42054 : PairBound 9 := { available := 341, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 162 37 74 341 373 341 469 341), lower := (rows 11 162 37 74 16 32 64 128 256), losses := [] }

theorem u42054 : Upper (D 6) (R 6) [10,160,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42054 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42055 : Route 9 := (fun mask => (mask,id))

def c42055 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42055 : Upper (D 6) (R 6) [10,160,33,68] 13 := by
  apply FastRouting.sound _ _ [10,160,33,68] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r42055 c42055
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33808
  · exact u33809
  · exact u33810
  · exact u33811
  · exact u33812
  · exact u33813
  · exact u33814
  · exact u33815
  · exact u33816
  · exact u33817

def r42056 : Route 9 := (fun mask => (mask,id))

def c42056 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42056 : Upper (D 6) (R 6) [10,160,33,80] 13 := by
  apply FastRouting.sound _ _ [10,160,33,80] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r42056 c42056
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33818
  · exact u33819
  · exact u33820
  · exact u33821
  · exact u33822
  · exact u33823
  · exact u33824
  · exact u33825
  · exact u33826
  · exact u33827

def r42057 : Route 9 := (fun mask => (mask,id))

def c42057 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42057 : Upper (D 6) (R 6) [10,160,33,257] 13 := by
  apply FastRouting.sound _ _ [10,160,33,257] 13 (by decide) (choices 2) [6,66,68] r42057 c42057
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u33828
  · exact u33829
  · exact u33830

def b42058 : PairBound 9 := { available := 85, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 162 37 266 85 117 85 213 341), lower := (rows 11 162 37 266 16 32 64 128 256), losses := [] }

theorem u42058 : Upper (D 6) (R 6) [10,160,33,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42058 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42059 : Route 9 := (fun mask => (mask,id))

def c42059 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42059 : Upper (D 6) (R 6) [10,160,33,260] 13 := by
  apply FastRouting.sound _ _ [10,160,33,260] 13 (by decide) (choices 2) [3,5,6,65,66,68] r42059 c42059
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33831
  · exact u33832
  · exact u33833
  · exact u33834
  · exact u33835
  · exact u33836

#print axioms u42059
end Delivery.IrregularNine14.P06

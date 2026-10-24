import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0642
import IrregularNine14P06C0643
import IrregularNine14P06C0644
import IrregularNine14P06C0645
import IrregularNine14P06C0646
import IrregularNine14P06C0647

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r43140 : Route 9 := (fun mask => (mask,id))

def c43140 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43140 : Upper (D 6) (R 6) [34,136,320,20] 13 := by
  apply FastRouting.sound _ _ [34,136,320,20] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r43140 c43140
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38550
  · exact u38551
  · exact u38552
  · exact u38553
  · exact u38554
  · exact u38555
  · exact u38556
  · exact u38557
  · exact u38558
  · exact u38559

def b43141 : PairBound 9 := { available := 87, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 138 324 41 87 119 87 215 343), lower := (rows 35 138 324 41 16 32 64 128 256), losses := [] }

theorem u43141 : Upper (D 6) (R 6) [34,136,320,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43141 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43142 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 0, region := 8, targets := 4 }], pairs := [(2,1),(3,2),(4,1)], upper := (rows 35 138 324 42 85 117 85 213 341), lower := (rows 35 138 324 42 16 32 64 128 256), losses := [] }

theorem u43142 : Upper (D 6) (R 6) [34,136,320,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43142 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43143 : Route 9 := (fun mask => (mask,id))

def c43143 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43143 : Upper (D 6) (R 6) [34,136,320,36] 13 := by
  apply FastRouting.sound _ _ [34,136,320,36] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43143 c43143
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38560
  · exact u38561
  · exact u38562
  · exact u38563
  · exact u38564
  · exact u38565

def r43144 : Route 9 := (fun mask => (mask,id))

def c43144 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43144 : Upper (D 6) (R 6) [34,136,320,48] 13 := by
  apply FastRouting.sound _ _ [34,136,320,48] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43144 c43144
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38566
  · exact u38567
  · exact u38568
  · exact u38569
  · exact u38570
  · exact u38571

def r43145 : Route 9 := (fun mask => (mask,id))

def c43145 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43145 : Upper (D 6) (R 6) [34,136,320,65] 13 := by
  apply FastRouting.sound _ _ [34,136,320,65] 13 (by decide) (choices 2) [3,5,6,33,34,36] r43145 c43145
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38572
  · exact u38573
  · exact u38574
  · exact u38575
  · exact u38576
  · exact u38577

def r43146 : Route 9 := (fun mask => (mask,id))

def c43146 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43146 : Upper (D 6) (R 6) [34,136,320,66] 13 := by
  apply FastRouting.sound _ _ [34,136,320,66] 13 (by decide) (choices 2) [5,33,36] r43146 c43146
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u38578
  · exact u38579
  · exact u38580

def b43147 : PairBound 9 := { available := 55, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 138 324 76 55 55 119 183 311), lower := (rows 35 138 324 76 16 32 64 128 256), losses := [] }

theorem u43147 : Upper (D 6) (R 6) [34,136,320,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43147 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43148 : Route 9 := (fun mask => (mask,id))

def c43148 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43148 : Upper (D 6) (R 6) [34,136,320,80] 13 := by
  apply FastRouting.sound _ _ [34,136,320,80] 13 (by decide) (choices 2) [3,5,6,33,34,36] r43148 c43148
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38581
  · exact u38582
  · exact u38583
  · exact u38584
  · exact u38585
  · exact u38586

def r43149 : Route 9 := (fun mask => (mask,id))

def c43149 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43149 : Upper (D 6) (R 6) [34,136,320,96] 13 := by
  apply FastRouting.sound _ _ [34,136,320,96] 13 (by decide) (choices 2) [3,5,6] r43149 c43149
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u38587
  · exact u38588
  · exact u38589

def b43150 : PairBound 9 := { available := 341, camps := [{ cop := 0, region := 8, targets := 36 },{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6),(3,2),(3,5)], upper := (rows 35 194 44 11 341 373 341 469 341), lower := (rows 35 194 44 11 16 32 64 128 256), losses := [] }

theorem u43150 : Upper (D 6) (R 6) [34,192,40,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43150 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43151 : PairBound 9 := { available := 343, camps := [{ cop := 0, region := 12, targets := 66 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 35 194 44 13 343 375 343 471 343), lower := (rows 35 194 44 13 16 32 64 128 256), losses := [] }

theorem u43151 : Upper (D 6) (R 6) [34,192,40,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43151 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43152 : PairBound 9 := { available := 341, camps := [{ cop := 0, region := 12, targets := 1 },{ cop := 0, region := 12, targets := 64 }], pairs := [(2,0),(2,6),(3,0)], upper := (rows 35 194 44 14 341 373 341 469 341), lower := (rows 35 194 44 14 16 32 64 128 256), losses := [] }

theorem u43152 : Upper (D 6) (R 6) [34,192,40,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43152 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43153 : Route 9 := (fun mask => (mask,id))

def c43153 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43153 : Upper (D 6) (R 6) [34,192,40,17] 13 := by
  apply FastRouting.sound _ _ [34,192,40,17] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r43153 c43153
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

def r43154 : Route 9 := (fun mask => (mask,id))

def c43154 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43154 : Upper (D 6) (R 6) [34,192,40,18] 13 := by
  apply FastRouting.sound _ _ [34,192,40,18] 13 (by decide) (choices 2) [5,65,68,257,260,320] r43154 c43154
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38600
  · exact u38601
  · exact u38602
  · exact u38603
  · exact u38604
  · exact u38605

def r43155 : Route 9 := (fun mask => (mask,id))

def c43155 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43155 : Upper (D 6) (R 6) [34,192,40,20] 13 := by
  apply FastRouting.sound _ _ [34,192,40,20] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r43155 c43155
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38606
  · exact u38607
  · exact u38608
  · exact u38609
  · exact u38610
  · exact u38611
  · exact u38612
  · exact u38613
  · exact u38614
  · exact u38615

def r43156 : Route 9 := (fun mask => (mask,id))

def c43156 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43156 : Upper (D 6) (R 6) [34,192,40,65] 13 := by
  apply FastRouting.sound _ _ [34,192,40,65] 13 (by decide) (choices 2) [3,5,6,257,258,260] r43156 c43156
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38616
  · exact u38617
  · exact u38618
  · exact u38619
  · exact u38620
  · exact u38621

def b43157 : PairBound 9 := { available := 277, camps := [{ cop := 1, region := 8, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 35 194 44 74 277 309 341 405 277), lower := (rows 35 194 44 74 16 32 64 128 256), losses := [] }

theorem u43157 : Upper (D 6) (R 6) [34,192,40,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43157 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43158 : Route 9 := (fun mask => (mask,id))

def c43158 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43158 : Upper (D 6) (R 6) [34,192,40,68] 13 := by
  apply FastRouting.sound _ _ [34,192,40,68] 13 (by decide) (choices 2) [3,5,6,257,258,260] r43158 c43158
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38622
  · exact u38623
  · exact u38624
  · exact u38625
  · exact u38626
  · exact u38627

def r43159 : Route 9 := (fun mask => (mask,id))

def c43159 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43159 : Upper (D 6) (R 6) [34,192,40,80] 13 := by
  apply FastRouting.sound _ _ [34,192,40,80] 13 (by decide) (choices 2) [3,5,6,257,258,260] r43159 c43159
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38628
  · exact u38629
  · exact u38630
  · exact u38631
  · exact u38632
  · exact u38633

def r43160 : Route 9 := (fun mask => (mask,id))

def c43160 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43160 : Upper (D 6) (R 6) [34,192,40,257] 13 := by
  apply FastRouting.sound _ _ [34,192,40,257] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43160 c43160
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38634
  · exact u38635
  · exact u38636
  · exact u38637
  · exact u38638
  · exact u38639

def r43161 : Route 9 := (fun mask => (mask,id))

def c43161 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43161 : Upper (D 6) (R 6) [34,192,40,258] 13 := by
  apply FastRouting.sound _ _ [34,192,40,258] 13 (by decide) (choices 2) [5,65,68] r43161 c43161
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u38640
  · exact u38641
  · exact u38642

def r43162 : Route 9 := (fun mask => (mask,id))

def c43162 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43162 : Upper (D 6) (R 6) [34,192,40,260] 13 := by
  apply FastRouting.sound _ _ [34,192,40,260] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43162 c43162
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38643
  · exact u38644
  · exact u38645
  · exact u38646
  · exact u38647
  · exact u38648

def r43163 : Route 9 := (fun mask => (mask,id))

def c43163 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43163 : Upper (D 6) (R 6) [34,192,40,272] 13 := by
  apply FastRouting.sound _ _ [34,192,40,272] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43163 c43163
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38649
  · exact u38650
  · exact u38651
  · exact u38652
  · exact u38653
  · exact u38654

def r43164 : Route 9 := (fun mask => (mask,id))

def c43164 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43164 : Upper (D 6) (R 6) [34,192,40,320] 13 := by
  apply FastRouting.sound _ _ [34,192,40,320] 13 (by decide) (choices 2) [3,5,6] r43164 c43164
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u38655
  · exact u38656
  · exact u38657

def b43165 : PairBound 9 := { available := 309, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 194 76 11 309 309 373 437 309), lower := (rows 35 194 76 11 16 32 64 128 256), losses := [] }

theorem u43165 : Upper (D 6) (R 6) [34,192,72,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43165 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43166 : Route 9 := (fun mask => (mask,id))

def c43166 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 10 => 3 | 66 => 6 | 130 => 7 | 12 => 3 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43166 : Upper (D 6) (R 6) [34,192,72,5] 13 := by
  apply FastRouting.sound _ _ [34,192,72,5] 13 (by decide) (choices 2) [3,5,6,33,34,36,257,258,260,288] r43166 c43166
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38658
  · exact u38659
  · exact u38660
  · exact u38661
  · exact u38662
  · exact u38663
  · exact u38664
  · exact u38665
  · exact u38666
  · exact u38667

def b43167 : PairBound 9 := { available := 309, camps := [{ cop := 1, region := 12, targets := 33 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 35 194 76 14 309 309 373 437 309), lower := (rows 35 194 76 14 16 32 64 128 256), losses := [] }

theorem u43167 : Upper (D 6) (R 6) [34,192,72,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43167 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43168 : Route 9 := (fun mask => (mask,id))

def c43168 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 10 => 3 | 66 => 6 | 130 => 7 | 12 => 3 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43168 : Upper (D 6) (R 6) [34,192,72,17] 13 := by
  apply FastRouting.sound _ _ [34,192,72,17] 13 (by decide) (choices 2) [3,5,6,33,34,36,257,258,260,288] r43168 c43168
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38668
  · exact u38669
  · exact u38670
  · exact u38671
  · exact u38672
  · exact u38673
  · exact u38674
  · exact u38675
  · exact u38676
  · exact u38677

def r43169 : Route 9 := (fun mask => (mask,id))

def c43169 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43169 : Upper (D 6) (R 6) [34,192,72,18] 13 := by
  apply FastRouting.sound _ _ [34,192,72,18] 13 (by decide) (choices 2) [5,33,36,257,260,288] r43169 c43169
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38678
  · exact u38679
  · exact u38680
  · exact u38681
  · exact u38682
  · exact u38683

def r43170 : Route 9 := (fun mask => (mask,id))

def c43170 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 10 => 3 | 66 => 6 | 130 => 7 | 12 => 3 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43170 : Upper (D 6) (R 6) [34,192,72,20] 13 := by
  apply FastRouting.sound _ _ [34,192,72,20] 13 (by decide) (choices 2) [3,5,6,33,34,36,257,258,260,288] r43170 c43170
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38684
  · exact u38685
  · exact u38686
  · exact u38687
  · exact u38688
  · exact u38689
  · exact u38690
  · exact u38691
  · exact u38692
  · exact u38693

def b43171 : PairBound 9 := { available := 279, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 194 76 41 279 311 343 407 279), lower := (rows 35 194 76 41 16 32 64 128 256), losses := [] }

theorem u43171 : Upper (D 6) (R 6) [34,192,72,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43171 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43172 : PairBound 9 := { available := 277, camps := [{ cop := 0, region := 8, targets := 68 },{ cop := 3, region := 1, targets := 4 }], pairs := [(0,2),(3,2),(3,6)], upper := (rows 35 194 76 42 277 309 341 405 277), lower := (rows 35 194 76 42 16 32 64 128 256), losses := [] }

theorem u43172 : Upper (D 6) (R 6) [34,192,72,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43172 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43173 : Route 9 := (fun mask => (mask,id))

def c43173 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43173 : Upper (D 6) (R 6) [34,192,72,36] 13 := by
  apply FastRouting.sound _ _ [34,192,72,36] 13 (by decide) (choices 2) [3,5,6,257,258,260] r43173 c43173
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38694
  · exact u38695
  · exact u38696
  · exact u38697
  · exact u38698
  · exact u38699

def r43174 : Route 9 := (fun mask => (mask,id))

def c43174 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43174 : Upper (D 6) (R 6) [34,192,72,48] 13 := by
  apply FastRouting.sound _ _ [34,192,72,48] 13 (by decide) (choices 2) [3,5,6,257,258,260] r43174 c43174
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38700
  · exact u38701
  · exact u38702
  · exact u38703
  · exact u38704
  · exact u38705

def r43175 : Route 9 := (fun mask => (mask,id))

def c43175 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43175 : Upper (D 6) (R 6) [34,192,72,257] 13 := by
  apply FastRouting.sound _ _ [34,192,72,257] 13 (by decide) (choices 2) [3,5,6,33,34,36] r43175 c43175
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38706
  · exact u38707
  · exact u38708
  · exact u38709
  · exact u38710
  · exact u38711

def r43176 : Route 9 := (fun mask => (mask,id))

def c43176 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43176 : Upper (D 6) (R 6) [34,192,72,258] 13 := by
  apply FastRouting.sound _ _ [34,192,72,258] 13 (by decide) (choices 2) [5,33,36] r43176 c43176
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u38712
  · exact u38713
  · exact u38714

def r43177 : Route 9 := (fun mask => (mask,id))

def c43177 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43177 : Upper (D 6) (R 6) [34,192,72,260] 13 := by
  apply FastRouting.sound _ _ [34,192,72,260] 13 (by decide) (choices 2) [3,5,6,33,34,36] r43177 c43177
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38715
  · exact u38716
  · exact u38717
  · exact u38718
  · exact u38719
  · exact u38720

def r43178 : Route 9 := (fun mask => (mask,id))

def c43178 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43178 : Upper (D 6) (R 6) [34,192,72,272] 13 := by
  apply FastRouting.sound _ _ [34,192,72,272] 13 (by decide) (choices 2) [3,5,6,33,34,36] r43178 c43178
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u38721
  · exact u38722
  · exact u38723
  · exact u38724
  · exact u38725
  · exact u38726

def r43179 : Route 9 := (fun mask => (mask,id))

def c43179 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43179 : Upper (D 6) (R 6) [34,192,72,288] 13 := by
  apply FastRouting.sound _ _ [34,192,72,288] 13 (by decide) (choices 2) [3,5,6] r43179 c43179
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u38727
  · exact u38728
  · exact u38729

def b43180 : PairBound 9 := { available := 285, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 194 100 11 285 317 349 413 285), lower := (rows 35 194 100 11 16 32 64 128 256), losses := [] }

theorem u43180 : Upper (D 6) (R 6) [34,192,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43180 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m43181_3 : Upper (D 6) (R 6) [34,192,96,5,3] 13 :=
  permutation_upper _ _ _ [34,192,96,3,5] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38730

def r43181 : Route 9 := (fun mask => (mask,id))

def c43181 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43181 : Upper (D 6) (R 6) [34,192,96,5] 13 := by
  apply FastRouting.sound _ _ [34,192,96,5] 13 (by decide) (choices 2) [3,5,6,9,10,12,257,258,260,264] r43181 c43181
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43181_3
  · exact u38736
  · exact u38737
  · exact u38738
  · exact u38739
  · exact u38740
  · exact u38741
  · exact u38742
  · exact u38743
  · exact u38744

theorem m43182_5 : Upper (D 6) (R 6) [34,192,96,6,5] 13 :=
  permutation_upper _ _ _ [34,192,96,5,6] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38737

def r43182 : Route 9 := (fun mask => (mask,id))

def c43182 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43182 : Upper (D 6) (R 6) [34,192,96,6] 13 := by
  apply FastRouting.sound _ _ [34,192,96,6] 13 (by decide) (choices 2) [5,9,12,257,260,264] r43182 c43182
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43182_5
  · exact u38745
  · exact u38746
  · exact u38747
  · exact u38748
  · exact u38749

theorem m43183_3 : Upper (D 6) (R 6) [34,192,96,17,3] 13 :=
  permutation_upper _ _ _ [34,192,96,3,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38731

theorem m43183_5 : Upper (D 6) (R 6) [34,192,96,17,5] 13 :=
  permutation_upper _ _ _ [34,192,96,5,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38738

theorem m43183_6 : Upper (D 6) (R 6) [34,192,96,17,6] 13 :=
  permutation_upper _ _ _ [34,192,96,6,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38745

def r43183 : Route 9 := (fun mask => (mask,id))

def c43183 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43183 : Upper (D 6) (R 6) [34,192,96,17] 13 := by
  apply FastRouting.sound _ _ [34,192,96,17] 13 (by decide) (choices 2) [3,5,6,9,10,12,257,258,260,264] r43183 c43183
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43183_3
  · exact m43183_5
  · exact m43183_6
  · exact u38750
  · exact u38751
  · exact u38752
  · exact u38753
  · exact u38754
  · exact u38755
  · exact u38756

theorem m43184_5 : Upper (D 6) (R 6) [34,192,96,18,5] 13 :=
  permutation_upper _ _ _ [34,192,96,5,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38739

theorem m43184_9 : Upper (D 6) (R 6) [34,192,96,18,9] 13 :=
  permutation_upper _ _ _ [34,192,96,17,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38751

def r43184 : Route 9 := (fun mask => (mask,id))

def c43184 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43184 : Upper (D 6) (R 6) [34,192,96,18] 13 := by
  apply FastRouting.sound _ _ [34,192,96,18] 13 (by decide) (choices 2) [5,9,12,257,260,264] r43184 c43184
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43184_5
  · exact m43184_9
  · exact u38757
  · exact u38758
  · exact u38759
  · exact u38760

theorem m43185_3 : Upper (D 6) (R 6) [34,192,96,20,3] 13 :=
  permutation_upper _ _ _ [34,192,96,3,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38732

theorem m43185_5 : Upper (D 6) (R 6) [34,192,96,20,5] 13 :=
  permutation_upper _ _ _ [34,192,96,5,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38740

theorem m43185_6 : Upper (D 6) (R 6) [34,192,96,20,6] 13 :=
  permutation_upper _ _ _ [34,192,96,6,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38746

theorem m43185_9 : Upper (D 6) (R 6) [34,192,96,20,9] 13 :=
  permutation_upper _ _ _ [34,192,96,17,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38752

theorem m43185_10 : Upper (D 6) (R 6) [34,192,96,20,10] 13 :=
  permutation_upper _ _ _ [34,192,96,18,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38757

def r43185 : Route 9 := (fun mask => (mask,id))

def c43185 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43185 : Upper (D 6) (R 6) [34,192,96,20] 13 := by
  apply FastRouting.sound _ _ [34,192,96,20] 13 (by decide) (choices 2) [3,5,6,9,10,12,257,258,260,264] r43185 c43185
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43185_3
  · exact m43185_5
  · exact m43185_6
  · exact m43185_9
  · exact m43185_10
  · exact u38761
  · exact u38762
  · exact u38763
  · exact u38764
  · exact u38765

theorem m43186_3 : Upper (D 6) (R 6) [34,192,96,257,3] 13 :=
  permutation_upper _ _ _ [34,192,96,3,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38733

theorem m43186_5 : Upper (D 6) (R 6) [34,192,96,257,5] 13 :=
  permutation_upper _ _ _ [34,192,96,5,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38741

theorem m43186_6 : Upper (D 6) (R 6) [34,192,96,257,6] 13 :=
  permutation_upper _ _ _ [34,192,96,6,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38747

theorem m43186_9 : Upper (D 6) (R 6) [34,192,96,257,9] 13 :=
  permutation_upper _ _ _ [34,192,96,17,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38753

theorem m43186_10 : Upper (D 6) (R 6) [34,192,96,257,10] 13 :=
  permutation_upper _ _ _ [34,192,96,18,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38758

theorem m43186_12 : Upper (D 6) (R 6) [34,192,96,257,12] 13 :=
  permutation_upper _ _ _ [34,192,96,20,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38762

def r43186 : Route 9 := (fun mask => (mask,id))

def c43186 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43186 : Upper (D 6) (R 6) [34,192,96,257] 13 := by
  apply FastRouting.sound _ _ [34,192,96,257] 13 (by decide) (choices 2) [3,5,6,9,10,12] r43186 c43186
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43186_3
  · exact m43186_5
  · exact m43186_6
  · exact m43186_9
  · exact m43186_10
  · exact m43186_12

theorem m43187_5 : Upper (D 6) (R 6) [34,192,96,258,5] 13 :=
  permutation_upper _ _ _ [34,192,96,5,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38742

theorem m43187_9 : Upper (D 6) (R 6) [34,192,96,258,9] 13 :=
  permutation_upper _ _ _ [34,192,96,17,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38754

theorem m43187_12 : Upper (D 6) (R 6) [34,192,96,258,12] 13 :=
  permutation_upper _ _ _ [34,192,96,20,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38763

def r43187 : Route 9 := (fun mask => (mask,id))

def c43187 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43187 : Upper (D 6) (R 6) [34,192,96,258] 13 := by
  apply FastRouting.sound _ _ [34,192,96,258] 13 (by decide) (choices 2) [5,9,12] r43187 c43187
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m43187_5
  · exact m43187_9
  · exact m43187_12

theorem m43188_3 : Upper (D 6) (R 6) [34,192,96,260,3] 13 :=
  permutation_upper _ _ _ [34,192,96,3,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38734

theorem m43188_5 : Upper (D 6) (R 6) [34,192,96,260,5] 13 :=
  permutation_upper _ _ _ [34,192,96,5,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38743

theorem m43188_6 : Upper (D 6) (R 6) [34,192,96,260,6] 13 :=
  permutation_upper _ _ _ [34,192,96,6,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38748

theorem m43188_9 : Upper (D 6) (R 6) [34,192,96,260,9] 13 :=
  permutation_upper _ _ _ [34,192,96,17,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38755

theorem m43188_10 : Upper (D 6) (R 6) [34,192,96,260,10] 13 :=
  permutation_upper _ _ _ [34,192,96,18,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38759

theorem m43188_12 : Upper (D 6) (R 6) [34,192,96,260,12] 13 :=
  permutation_upper _ _ _ [34,192,96,20,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38764

def r43188 : Route 9 := (fun mask => (mask,id))

def c43188 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43188 : Upper (D 6) (R 6) [34,192,96,260] 13 := by
  apply FastRouting.sound _ _ [34,192,96,260] 13 (by decide) (choices 2) [3,5,6,9,10,12] r43188 c43188
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43188_3
  · exact m43188_5
  · exact m43188_6
  · exact m43188_9
  · exact m43188_10
  · exact m43188_12

theorem m43189_3 : Upper (D 6) (R 6) [34,192,96,272,3] 13 :=
  permutation_upper _ _ _ [34,192,96,3,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38735

theorem m43189_5 : Upper (D 6) (R 6) [34,192,96,272,5] 13 :=
  permutation_upper _ _ _ [34,192,96,5,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38744

theorem m43189_6 : Upper (D 6) (R 6) [34,192,96,272,6] 13 :=
  permutation_upper _ _ _ [34,192,96,6,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38749

theorem m43189_9 : Upper (D 6) (R 6) [34,192,96,272,9] 13 :=
  permutation_upper _ _ _ [34,192,96,17,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38756

theorem m43189_10 : Upper (D 6) (R 6) [34,192,96,272,10] 13 :=
  permutation_upper _ _ _ [34,192,96,18,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38760

theorem m43189_12 : Upper (D 6) (R 6) [34,192,96,272,12] 13 :=
  permutation_upper _ _ _ [34,192,96,20,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38765

def r43189 : Route 9 := (fun mask => (mask,id))

def c43189 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43189 : Upper (D 6) (R 6) [34,192,96,272] 13 := by
  apply FastRouting.sound _ _ [34,192,96,272] 13 (by decide) (choices 2) [3,5,6,9,10,12] r43189 c43189
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43189_3
  · exact m43189_5
  · exact m43189_6
  · exact m43189_9
  · exact m43189_10
  · exact m43189_12

def b43190 : PairBound 9 := { available := 124, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 194 261 11 124 124 124 252 380), lower := (rows 35 194 261 11 16 32 64 128 256), losses := [] }

theorem u43190 : Upper (D 6) (R 6) [34,192,257,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43190 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43191 : PairBound 9 := { available := 126, camps := [{ cop := 2, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 35 194 261 13 126 126 126 254 382), lower := (rows 35 194 261 13 16 32 64 128 256), losses := [] }

theorem u43191 : Upper (D 6) (R 6) [34,192,257,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43191 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m43192_5 : Upper (D 6) (R 6) [34,192,257,6,5] 13 :=
  permutation_upper _ _ _ [34,192,257,5,6] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38772

def r43192 : Route 9 := (fun mask => (mask,id))

def c43192 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43192 : Upper (D 6) (R 6) [34,192,257,6] 13 := by
  apply FastRouting.sound _ _ [34,192,257,6] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96] r43192 c43192
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43192_5
  · exact u38780
  · exact u38781
  · exact u38782
  · exact u38783
  · exact u38784
  · exact u38785
  · exact u38786
  · exact u38787
  · exact u38788

theorem m43193_6 : Upper (D 6) (R 6) [34,192,257,17,6] 13 :=
  permutation_upper _ _ _ [34,192,257,6,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38780

def r43193 : Route 9 := (fun mask => (mask,id))

def c43193 : Nat → Fin 9 := (fun mask => match mask with | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43193 : Upper (D 6) (R 6) [34,192,257,17] 13 := by
  apply FastRouting.sound _ _ [34,192,257,17] 13 (by decide) (choices 2) [6,10,12,34,36,40,66,68,72,96] r43193 c43193
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43193_6
  · exact u38789
  · exact u38790
  · exact u38791
  · exact u38792
  · exact u38793
  · exact u38794
  · exact u38795
  · exact u38796
  · exact u38797

theorem m43194_5 : Upper (D 6) (R 6) [34,192,257,18,5] 13 :=
  permutation_upper _ _ _ [34,192,257,5,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38773

theorem m43194_9 : Upper (D 6) (R 6) [34,192,257,18,9] 13 :=
  permutation_upper _ _ _ [34,192,257,17,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38789

def r43194 : Route 9 := (fun mask => (mask,id))

def c43194 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43194 : Upper (D 6) (R 6) [34,192,257,18] 13 := by
  apply FastRouting.sound _ _ [34,192,257,18] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96] r43194 c43194
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43194_5
  · exact m43194_9
  · exact u38798
  · exact u38799
  · exact u38800
  · exact u38801
  · exact u38802
  · exact u38803
  · exact u38804
  · exact u38805

theorem m43195_3 : Upper (D 6) (R 6) [34,192,257,20,3] 13 :=
  permutation_upper _ _ _ [34,192,257,3,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38766

theorem m43195_5 : Upper (D 6) (R 6) [34,192,257,20,5] 13 :=
  permutation_upper _ _ _ [34,192,257,5,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38774

theorem m43195_6 : Upper (D 6) (R 6) [34,192,257,20,6] 13 :=
  permutation_upper _ _ _ [34,192,257,6,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38781

theorem m43195_9 : Upper (D 6) (R 6) [34,192,257,20,9] 13 :=
  permutation_upper _ _ _ [34,192,257,17,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38790

theorem m43195_10 : Upper (D 6) (R 6) [34,192,257,20,10] 13 :=
  permutation_upper _ _ _ [34,192,257,18,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38798

def r43195 : Route 9 := (fun mask => (mask,id))

def c43195 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 257 => 8 | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43195 : Upper (D 6) (R 6) [34,192,257,20] 13 := by
  apply FastRouting.sound _ _ [34,192,257,20] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40,65,66,68,72,96] r43195 c43195
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43195_3
  · exact m43195_5
  · exact m43195_6
  · exact m43195_9
  · exact m43195_10
  · exact u38806
  · exact u38807
  · exact u38808
  · exact u38809
  · exact u38810
  · exact u38811
  · exact u38812
  · exact u38813
  · exact u38814
  · exact u38815

def b43196 : PairBound 9 := { available := 94, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 194 261 41 94 126 94 222 350), lower := (rows 35 194 261 41 16 32 64 128 256), losses := [] }

theorem u43196 : Upper (D 6) (R 6) [34,192,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43196 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43197 : PairBound 9 := { available := 93, camps := [{ cop := 0, region := 8, targets := 68 },{ cop := 3, region := 1, targets := 4 }], pairs := [(0,2),(3,2),(3,6)], upper := (rows 35 194 261 42 93 125 93 221 349), lower := (rows 35 194 261 42 16 32 64 128 256), losses := [] }

theorem u43197 : Upper (D 6) (R 6) [34,192,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43197 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m43198_3 : Upper (D 6) (R 6) [34,192,257,36,3] 13 :=
  permutation_upper _ _ _ [34,192,257,3,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38767

theorem m43198_5 : Upper (D 6) (R 6) [34,192,257,36,5] 13 :=
  permutation_upper _ _ _ [34,192,257,5,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38775

theorem m43198_6 : Upper (D 6) (R 6) [34,192,257,36,6] 13 :=
  permutation_upper _ _ _ [34,192,257,6,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38783

theorem m43198_9 : Upper (D 6) (R 6) [34,192,257,36,9] 13 :=
  permutation_upper _ _ _ [34,192,257,17,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38792

theorem m43198_10 : Upper (D 6) (R 6) [34,192,257,36,10] 13 :=
  permutation_upper _ _ _ [34,192,257,18,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38800

theorem m43198_12 : Upper (D 6) (R 6) [34,192,257,36,12] 13 :=
  permutation_upper _ _ _ [34,192,257,20,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38809

def r43198 : Route 9 := (fun mask => (mask,id))

def c43198 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43198 : Upper (D 6) (R 6) [34,192,257,36] 13 := by
  apply FastRouting.sound _ _ [34,192,257,36] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72] r43198 c43198
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43198_3
  · exact m43198_5
  · exact m43198_6
  · exact m43198_9
  · exact m43198_10
  · exact m43198_12
  · exact u38821
  · exact u38822
  · exact u38823
  · exact u38824

theorem m43199_3 : Upper (D 6) (R 6) [34,192,257,48,3] 13 :=
  permutation_upper _ _ _ [34,192,257,3,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38768

theorem m43199_5 : Upper (D 6) (R 6) [34,192,257,48,5] 13 :=
  permutation_upper _ _ _ [34,192,257,5,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38776

theorem m43199_6 : Upper (D 6) (R 6) [34,192,257,48,6] 13 :=
  permutation_upper _ _ _ [34,192,257,6,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38784

theorem m43199_9 : Upper (D 6) (R 6) [34,192,257,48,9] 13 :=
  permutation_upper _ _ _ [34,192,257,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38793

theorem m43199_10 : Upper (D 6) (R 6) [34,192,257,48,10] 13 :=
  permutation_upper _ _ _ [34,192,257,18,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38801

theorem m43199_12 : Upper (D 6) (R 6) [34,192,257,48,12] 13 :=
  permutation_upper _ _ _ [34,192,257,20,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38810

def r43199 : Route 9 := (fun mask => (mask,id))

def c43199 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43199 : Upper (D 6) (R 6) [34,192,257,48] 13 := by
  apply FastRouting.sound _ _ [34,192,257,48] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72] r43199 c43199
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43199_3
  · exact m43199_5
  · exact m43199_6
  · exact m43199_9
  · exact m43199_10
  · exact m43199_12
  · exact u38825
  · exact u38826
  · exact u38827
  · exact u38828

#print axioms u43199
end Delivery.IrregularNine14.P06

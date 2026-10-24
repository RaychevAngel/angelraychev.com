import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0610
import IrregularNine14P06C0611
import IrregularNine14P06C0612
import IrregularNine14P06C0613
import IrregularNine14P06C0614

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r42720 : Route 9 := (fun mask => (mask,id))

def c42720 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42720 : Upper (D 6) (R 6) [34,72,129,260] 13 := by
  apply FastRouting.sound _ _ [34,72,129,260] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r42720 c42720
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36605
  · exact u36606
  · exact u36607
  · exact u36608
  · exact u36609
  · exact u36610
  · exact u36611
  · exact u36612
  · exact u36613
  · exact u36614

def r42721 : Route 9 := (fun mask => (mask,id))

def c42721 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42721 : Upper (D 6) (R 6) [34,72,129,272] 13 := by
  apply FastRouting.sound _ _ [34,72,129,272] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r42721 c42721
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36615
  · exact u36616
  · exact u36617
  · exact u36618
  · exact u36619
  · exact u36620
  · exact u36621
  · exact u36622
  · exact u36623
  · exact u36624

def r42722 : Route 9 := (fun mask => (mask,id))

def c42722 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42722 : Upper (D 6) (R 6) [34,72,129,288] 13 := by
  apply FastRouting.sound _ _ [34,72,129,288] 13 (by decide) (choices 2) [3,5,6,65,66,68] r42722 c42722
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36625
  · exact u36626
  · exact u36627
  · exact u36628
  · exact u36629
  · exact u36630

def b42723 : PairBound 9 := { available := 55, camps := [{ cop := 1, region := 181, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 74 133 328 55 55 119 183 311), lower := (rows 35 74 133 328 16 32 64 128 256), losses := [] }

theorem u42723 : Upper (D 6) (R 6) [34,72,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42723 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42724 : Route 9 := (fun mask => (mask,id))

def c42724 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42724 : Upper (D 6) (R 6) [34,72,130,5] 13 := by
  apply FastRouting.sound _ _ [34,72,130,5] 13 (by decide) (choices 2) [5,33,36,65,68,96,257,260,288,320] r42724 c42724
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36631
  · exact u36632
  · exact u36633
  · exact u36634
  · exact u36635
  · exact u36636
  · exact u36637
  · exact u36638
  · exact u36639
  · exact u36640

def r42725 : Route 9 := (fun mask => (mask,id))

def c42725 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42725 : Upper (D 6) (R 6) [34,72,130,17] 13 := by
  apply FastRouting.sound _ _ [34,72,130,17] 13 (by decide) (choices 2) [5,33,36,65,68,96,257,260,288,320] r42725 c42725
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36641
  · exact u36642
  · exact u36643
  · exact u36644
  · exact u36645
  · exact u36646
  · exact u36647
  · exact u36648
  · exact u36649
  · exact u36650

def r42726 : Route 9 := (fun mask => (mask,id))

def c42726 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42726 : Upper (D 6) (R 6) [34,72,130,20] 13 := by
  apply FastRouting.sound _ _ [34,72,130,20] 13 (by decide) (choices 2) [5,33,36,65,68,96,257,260,288,320] r42726 c42726
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36651
  · exact u36652
  · exact u36653
  · exact u36654
  · exact u36655
  · exact u36656
  · exact u36657
  · exact u36658
  · exact u36659
  · exact u36660

def b42727 : PairBound 9 := { available := 341, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 74 134 41 341 373 341 469 341), lower := (rows 35 74 134 41 16 32 64 128 256), losses := [] }

theorem u42727 : Upper (D 6) (R 6) [34,72,130,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42727 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42728 : Route 9 := (fun mask => (mask,id))

def c42728 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42728 : Upper (D 6) (R 6) [34,72,130,36] 13 := by
  apply FastRouting.sound _ _ [34,72,130,36] 13 (by decide) (choices 2) [5,65,68,257,260,320] r42728 c42728
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36661
  · exact u36662
  · exact u36663
  · exact u36664
  · exact u36665
  · exact u36666

def r42729 : Route 9 := (fun mask => (mask,id))

def c42729 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42729 : Upper (D 6) (R 6) [34,72,130,48] 13 := by
  apply FastRouting.sound _ _ [34,72,130,48] 13 (by decide) (choices 2) [5,65,68,257,260,320] r42729 c42729
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36667
  · exact u36668
  · exact u36669
  · exact u36670
  · exact u36671
  · exact u36672

def b42730 : PairBound 9 := { available := 309, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 74 134 73 309 309 373 437 309), lower := (rows 35 74 134 73 16 32 64 128 256), losses := [] }

theorem u42730 : Upper (D 6) (R 6) [34,72,130,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42730 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42731 : PairBound 9 := { available := 309, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 74 134 76 309 309 373 437 309), lower := (rows 35 74 134 76 16 32 64 128 256), losses := [] }

theorem u42731 : Upper (D 6) (R 6) [34,72,130,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42731 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42732 : PairBound 9 := { available := 293, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 74 134 88 309 293 357 421 293), lower := (rows 35 74 134 88 16 32 64 128 256), losses := [] }

theorem u42732 : Upper (D 6) (R 6) [34,72,130,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42732 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42733 : PairBound 9 := { available := 277, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 74 134 104 277 309 341 405 277), lower := (rows 35 74 134 104 16 32 64 128 256), losses := [] }

theorem u42733 : Upper (D 6) (R 6) [34,72,130,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42733 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42734 : Route 9 := (fun mask => (mask,id))

def c42734 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42734 : Upper (D 6) (R 6) [34,72,130,257] 13 := by
  apply FastRouting.sound _ _ [34,72,130,257] 13 (by decide) (choices 2) [5,33,36,65,68,96] r42734 c42734
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36673
  · exact u36674
  · exact u36675
  · exact u36676
  · exact u36677
  · exact u36678

def r42735 : Route 9 := (fun mask => (mask,id))

def c42735 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42735 : Upper (D 6) (R 6) [34,72,130,260] 13 := by
  apply FastRouting.sound _ _ [34,72,130,260] 13 (by decide) (choices 2) [5,33,36,65,68,96] r42735 c42735
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36679
  · exact u36680
  · exact u36681
  · exact u36682
  · exact u36683
  · exact u36684

def r42736 : Route 9 := (fun mask => (mask,id))

def c42736 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42736 : Upper (D 6) (R 6) [34,72,130,272] 13 := by
  apply FastRouting.sound _ _ [34,72,130,272] 13 (by decide) (choices 2) [5,33,36,65,68,96] r42736 c42736
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36685
  · exact u36686
  · exact u36687
  · exact u36688
  · exact u36689
  · exact u36690

def r42737 : Route 9 := (fun mask => (mask,id))

def c42737 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42737 : Upper (D 6) (R 6) [34,72,130,288] 13 := by
  apply FastRouting.sound _ _ [34,72,130,288] 13 (by decide) (choices 2) [5,65,68] r42737 c42737
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u36691
  · exact u36692
  · exact u36693

def b42738 : PairBound 9 := { available := 53, camps := [{ cop := 1, region := 181, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 74 134 328 53 53 117 181 309), lower := (rows 35 74 134 328 16 32 64 128 256), losses := [] }

theorem u42738 : Upper (D 6) (R 6) [34,72,130,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42738 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42739 : PairBound 9 := { available := 357, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 74 148 11 373 357 357 485 357), lower := (rows 35 74 148 11 16 32 64 128 256), losses := [] }

theorem u42739 : Upper (D 6) (R 6) [34,72,144,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42739 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42740 : Route 9 := (fun mask => (mask,id))

def c42740 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42740 : Upper (D 6) (R 6) [34,72,144,5] 13 := by
  apply FastRouting.sound _ _ [34,72,144,5] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,257,258,260,288,320] r42740 c42740
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36694
  · exact u36695
  · exact u36696
  · exact u36697
  · exact u36698
  · exact u36699
  · exact u36700
  · exact u36701
  · exact u36702
  · exact u36703
  · exact u36704
  · exact u36705
  · exact u36706
  · exact u36707
  · exact u36708

def r42741 : Route 9 := (fun mask => (mask,id))

def c42741 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42741 : Upper (D 6) (R 6) [34,72,144,6] 13 := by
  apply FastRouting.sound _ _ [34,72,144,6] 13 (by decide) (choices 2) [5,33,36,65,68,96,257,260,288,320] r42741 c42741
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36709
  · exact u36710
  · exact u36711
  · exact u36712
  · exact u36713
  · exact u36714
  · exact u36715
  · exact u36716
  · exact u36717
  · exact u36718

def b42742 : PairBound 9 := { available := 327, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 74 148 41 343 359 327 455 327), lower := (rows 35 74 148 41 16 32 64 128 256), losses := [] }

theorem u42742 : Upper (D 6) (R 6) [34,72,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42742 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42743 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 0, region := 8, targets := 4 }], pairs := [(2,1),(3,2),(4,1)], upper := (rows 35 74 148 42 341 357 325 453 325), lower := (rows 35 74 148 42 16 32 64 128 256), losses := [] }

theorem u42743 : Upper (D 6) (R 6) [34,72,144,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42743 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42744 : Route 9 := (fun mask => (mask,id))

def c42744 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42744 : Upper (D 6) (R 6) [34,72,144,36] 13 := by
  apply FastRouting.sound _ _ [34,72,144,36] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r42744 c42744
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36719
  · exact u36720
  · exact u36721
  · exact u36722
  · exact u36723
  · exact u36724
  · exact u36725
  · exact u36726
  · exact u36727
  · exact u36728

def b42745 : PairBound 9 := { available := 295, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 74 148 73 311 295 359 423 295), lower := (rows 35 74 148 73 16 32 64 128 256), losses := [] }

theorem u42745 : Upper (D 6) (R 6) [34,72,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42745 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42746 : PairBound 9 := { available := 293, camps := [{ cop := 6, region := 10, targets := 37 }], pairs := [(1,0),(1,2),(1,5)], upper := (rows 35 74 148 74 309 293 357 421 293), lower := (rows 35 74 148 74 16 32 64 128 256), losses := [] }

theorem u42746 : Upper (D 6) (R 6) [34,72,144,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42746 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42747 : PairBound 9 := { available := 295, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 74 148 76 311 295 359 423 295), lower := (rows 35 74 148 76 16 32 64 128 256), losses := [] }

theorem u42747 : Upper (D 6) (R 6) [34,72,144,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42747 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42748 : PairBound 9 := { available := 263, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 74 148 104 279 295 327 391 263), lower := (rows 35 74 148 104 16 32 64 128 256), losses := [] }

theorem u42748 : Upper (D 6) (R 6) [34,72,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42748 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42749 : Route 9 := (fun mask => (mask,id))

def c42749 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42749 : Upper (D 6) (R 6) [34,72,144,257] 13 := by
  apply FastRouting.sound _ _ [34,72,144,257] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r42749 c42749
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36729
  · exact u36730
  · exact u36731
  · exact u36732
  · exact u36733
  · exact u36734
  · exact u36735
  · exact u36736
  · exact u36737
  · exact u36738

def r42750 : Route 9 := (fun mask => (mask,id))

def c42750 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42750 : Upper (D 6) (R 6) [34,72,144,258] 13 := by
  apply FastRouting.sound _ _ [34,72,144,258] 13 (by decide) (choices 2) [5,33,36,65,68,96] r42750 c42750
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36739
  · exact u36740
  · exact u36741
  · exact u36742
  · exact u36743
  · exact u36744

def r42751 : Route 9 := (fun mask => (mask,id))

def c42751 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42751 : Upper (D 6) (R 6) [34,72,144,260] 13 := by
  apply FastRouting.sound _ _ [34,72,144,260] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r42751 c42751
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36745
  · exact u36746
  · exact u36747
  · exact u36748
  · exact u36749
  · exact u36750
  · exact u36751
  · exact u36752
  · exact u36753
  · exact u36754

def r42752 : Route 9 := (fun mask => (mask,id))

def c42752 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42752 : Upper (D 6) (R 6) [34,72,144,288] 13 := by
  apply FastRouting.sound _ _ [34,72,144,288] 13 (by decide) (choices 2) [3,5,6,65,66,68] r42752 c42752
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36755
  · exact u36756
  · exact u36757
  · exact u36758
  · exact u36759
  · exact u36760

def b42753 : PairBound 9 := { available := 39, camps := [{ cop := 1, region := 181, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 74 148 328 55 39 103 167 295), lower := (rows 35 74 148 328 16 32 64 128 256), losses := [] }

theorem u42753 : Upper (D 6) (R 6) [34,72,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42753 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42754 : PairBound 9 := { available := 341, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 74 164 11 341 373 341 469 341), lower := (rows 35 74 164 11 16 32 64 128 256), losses := [] }

theorem u42754 : Upper (D 6) (R 6) [34,72,160,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42754 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42755 : Route 9 := (fun mask => (mask,id))

def c42755 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42755 : Upper (D 6) (R 6) [34,72,160,5] 13 := by
  apply FastRouting.sound _ _ [34,72,160,5] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r42755 c42755
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36761
  · exact u36762
  · exact u36763
  · exact u36764
  · exact u36765
  · exact u36766
  · exact u36767
  · exact u36768
  · exact u36769
  · exact u36770

def r42756 : Route 9 := (fun mask => (mask,id))

def c42756 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42756 : Upper (D 6) (R 6) [34,72,160,6] 13 := by
  apply FastRouting.sound _ _ [34,72,160,6] 13 (by decide) (choices 2) [5,65,68,257,260,320] r42756 c42756
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36771
  · exact u36772
  · exact u36773
  · exact u36774
  · exact u36775
  · exact u36776

def r42757 : Route 9 := (fun mask => (mask,id))

def c42757 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42757 : Upper (D 6) (R 6) [34,72,160,17] 13 := by
  apply FastRouting.sound _ _ [34,72,160,17] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r42757 c42757
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36777
  · exact u36778
  · exact u36779
  · exact u36780
  · exact u36781
  · exact u36782
  · exact u36783
  · exact u36784
  · exact u36785
  · exact u36786

def r42758 : Route 9 := (fun mask => (mask,id))

def c42758 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42758 : Upper (D 6) (R 6) [34,72,160,18] 13 := by
  apply FastRouting.sound _ _ [34,72,160,18] 13 (by decide) (choices 2) [5,65,68,257,260,320] r42758 c42758
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36787
  · exact u36788
  · exact u36789
  · exact u36790
  · exact u36791
  · exact u36792

def r42759 : Route 9 := (fun mask => (mask,id))

def c42759 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42759 : Upper (D 6) (R 6) [34,72,160,20] 13 := by
  apply FastRouting.sound _ _ [34,72,160,20] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r42759 c42759
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36793
  · exact u36794
  · exact u36795
  · exact u36796
  · exact u36797
  · exact u36798
  · exact u36799
  · exact u36800
  · exact u36801
  · exact u36802

def b42760 : PairBound 9 := { available := 279, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 74 164 73 279 311 343 407 279), lower := (rows 35 74 164 73 16 32 64 128 256), losses := [] }

theorem u42760 : Upper (D 6) (R 6) [34,72,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42760 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42761 : PairBound 9 := { available := 277, camps := [{ cop := 6, region := 10, targets := 37 }], pairs := [(1,0),(1,2),(1,5)], upper := (rows 35 74 164 74 277 309 341 405 277), lower := (rows 35 74 164 74 16 32 64 128 256), losses := [] }

theorem u42761 : Upper (D 6) (R 6) [34,72,160,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42761 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42762 : PairBound 9 := { available := 279, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 74 164 76 279 311 343 407 279), lower := (rows 35 74 164 76 16 32 64 128 256), losses := [] }

theorem u42762 : Upper (D 6) (R 6) [34,72,160,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42762 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42763 : PairBound 9 := { available := 263, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 74 164 88 279 295 327 391 263), lower := (rows 35 74 164 88 16 32 64 128 256), losses := [] }

theorem u42763 : Upper (D 6) (R 6) [34,72,160,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42763 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42764 : Route 9 := (fun mask => (mask,id))

def c42764 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42764 : Upper (D 6) (R 6) [34,72,160,257] 13 := by
  apply FastRouting.sound _ _ [34,72,160,257] 13 (by decide) (choices 2) [3,5,6,65,66,68] r42764 c42764
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36803
  · exact u36804
  · exact u36805
  · exact u36806
  · exact u36807
  · exact u36808

def r42765 : Route 9 := (fun mask => (mask,id))

def c42765 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42765 : Upper (D 6) (R 6) [34,72,160,258] 13 := by
  apply FastRouting.sound _ _ [34,72,160,258] 13 (by decide) (choices 2) [5,65,68] r42765 c42765
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u36809
  · exact u36810
  · exact u36811

def r42766 : Route 9 := (fun mask => (mask,id))

def c42766 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42766 : Upper (D 6) (R 6) [34,72,160,260] 13 := by
  apply FastRouting.sound _ _ [34,72,160,260] 13 (by decide) (choices 2) [3,5,6,65,66,68] r42766 c42766
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36812
  · exact u36813
  · exact u36814
  · exact u36815
  · exact u36816
  · exact u36817

def r42767 : Route 9 := (fun mask => (mask,id))

def c42767 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42767 : Upper (D 6) (R 6) [34,72,160,272] 13 := by
  apply FastRouting.sound _ _ [34,72,160,272] 13 (by decide) (choices 2) [3,5,6,65,66,68] r42767 c42767
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36818
  · exact u36819
  · exact u36820
  · exact u36821
  · exact u36822
  · exact u36823

def b42768 : PairBound 9 := { available := 23, camps := [{ cop := 1, region := 181, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 74 164 328 23 55 87 151 279), lower := (rows 35 74 164 328 16 32 64 128 256), losses := [] }

theorem u42768 : Upper (D 6) (R 6) [34,72,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42768 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42769 : PairBound 9 := { available := 309, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 74 196 11 309 309 373 437 309), lower := (rows 35 74 196 11 16 32 64 128 256), losses := [] }

theorem u42769 : Upper (D 6) (R 6) [34,72,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42769 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42770 : Route 9 := (fun mask => (mask,id))

def c42770 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 10 => 3 | 66 => 6 | 130 => 7 | 12 => 3 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42770 : Upper (D 6) (R 6) [34,72,192,5] 13 := by
  apply FastRouting.sound _ _ [34,72,192,5] 13 (by decide) (choices 2) [3,5,6,33,34,36,257,258,260,288] r42770 c42770
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36824
  · exact u36825
  · exact u36826
  · exact u36827
  · exact u36828
  · exact u36829
  · exact u36830
  · exact u36831
  · exact u36832
  · exact u36833

def b42771 : PairBound 9 := { available := 309, camps := [{ cop := 2, region := 10, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 74 196 14 309 309 373 437 309), lower := (rows 35 74 196 14 16 32 64 128 256), losses := [] }

theorem u42771 : Upper (D 6) (R 6) [34,72,192,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42771 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42772 : Route 9 := (fun mask => (mask,id))

def c42772 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 10 => 3 | 66 => 6 | 130 => 7 | 12 => 3 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42772 : Upper (D 6) (R 6) [34,72,192,17] 13 := by
  apply FastRouting.sound _ _ [34,72,192,17] 13 (by decide) (choices 2) [3,5,6,33,34,36,257,258,260,288] r42772 c42772
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36834
  · exact u36835
  · exact u36836
  · exact u36837
  · exact u36838
  · exact u36839
  · exact u36840
  · exact u36841
  · exact u36842
  · exact u36843

def r42773 : Route 9 := (fun mask => (mask,id))

def c42773 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42773 : Upper (D 6) (R 6) [34,72,192,18] 13 := by
  apply FastRouting.sound _ _ [34,72,192,18] 13 (by decide) (choices 2) [5,33,36,257,260,288] r42773 c42773
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36844
  · exact u36845
  · exact u36846
  · exact u36847
  · exact u36848
  · exact u36849

def r42774 : Route 9 := (fun mask => (mask,id))

def c42774 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 10 => 3 | 66 => 6 | 130 => 7 | 12 => 3 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42774 : Upper (D 6) (R 6) [34,72,192,20] 13 := by
  apply FastRouting.sound _ _ [34,72,192,20] 13 (by decide) (choices 2) [3,5,6,33,34,36,257,258,260,288] r42774 c42774
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36850
  · exact u36851
  · exact u36852
  · exact u36853
  · exact u36854
  · exact u36855
  · exact u36856
  · exact u36857
  · exact u36858
  · exact u36859

def b42775 : PairBound 9 := { available := 279, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 74 196 41 279 311 343 407 279), lower := (rows 35 74 196 41 16 32 64 128 256), losses := [] }

theorem u42775 : Upper (D 6) (R 6) [34,72,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42775 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42776 : PairBound 9 := { available := 277, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 0, region := 8, targets := 4 }], pairs := [(2,1),(3,2),(4,1)], upper := (rows 35 74 196 42 277 309 341 405 277), lower := (rows 35 74 196 42 16 32 64 128 256), losses := [] }

theorem u42776 : Upper (D 6) (R 6) [34,72,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42776 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42777 : Route 9 := (fun mask => (mask,id))

def c42777 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42777 : Upper (D 6) (R 6) [34,72,192,36] 13 := by
  apply FastRouting.sound _ _ [34,72,192,36] 13 (by decide) (choices 2) [3,5,6,257,258,260] r42777 c42777
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36860
  · exact u36861
  · exact u36862
  · exact u36863
  · exact u36864
  · exact u36865

def r42778 : Route 9 := (fun mask => (mask,id))

def c42778 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42778 : Upper (D 6) (R 6) [34,72,192,48] 13 := by
  apply FastRouting.sound _ _ [34,72,192,48] 13 (by decide) (choices 2) [3,5,6,257,258,260] r42778 c42778
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36866
  · exact u36867
  · exact u36868
  · exact u36869
  · exact u36870
  · exact u36871

def r42779 : Route 9 := (fun mask => (mask,id))

def c42779 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42779 : Upper (D 6) (R 6) [34,72,192,257] 13 := by
  apply FastRouting.sound _ _ [34,72,192,257] 13 (by decide) (choices 2) [3,5,6,33,34,36] r42779 c42779
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u36872
  · exact u36873
  · exact u36874
  · exact u36875
  · exact u36876
  · exact u36877

#print axioms u42779
end Delivery.IrregularNine14.P06

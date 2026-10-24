import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0529
import IrregularNine14P06C0530
import IrregularNine14P06C0531
import IrregularNine14P06C0532
import IrregularNine14P06C0533
import IrregularNine14P06C0534

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b41580 : PairBound 9 := { available := 423, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 50 69 76 439 423 487 423 423), lower := (rows 11 50 69 76 16 32 64 128 256), losses := [] }

theorem u41580 : Upper (D 6) (R 6) [10,48,65,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41580 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41581 : PairBound 9 := { available := 391, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 2, region := 434, targets := 64 }], pairs := [(1,6),(2,5),(4,5)], upper := (rows 11 50 69 104 407 423 455 391 391), lower := (rows 11 50 69 104 16 32 64 128 256), losses := [] }

theorem u41581 : Upper (D 6) (R 6) [10,48,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41581 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41582 : Route 9 := (fun mask => (mask,id))

def c41582 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41582 : Upper (D 6) (R 6) [10,48,65,129] 13 := by
  apply FastRouting.sound _ _ [10,48,65,129] 13 (by decide) (choices 2) [6,34,36,66,68,96,258,260,288,320] r41582 c41582
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31779
  · exact u31780
  · exact u31781
  · exact u31782
  · exact u31783
  · exact u31784
  · exact u31785
  · exact u31786
  · exact u31787
  · exact u31788

def b41583 : PairBound 9 := { available := 357, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 50 69 138 373 357 357 485 357), lower := (rows 11 50 69 138 16 32 64 128 256), losses := [] }

theorem u41583 : Upper (D 6) (R 6) [10,48,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41583 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41584 : Route 9 := (fun mask => (mask,id))

def c41584 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41584 : Upper (D 6) (R 6) [10,48,65,132] 13 := by
  apply FastRouting.sound _ _ [10,48,65,132] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,257,258,260,288,320] r41584 c41584
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31789
  · exact u31790
  · exact u31791
  · exact u31792
  · exact u31793
  · exact u31794
  · exact u31795
  · exact u31796
  · exact u31797
  · exact u31798
  · exact u31799
  · exact u31800
  · exact u31801
  · exact u31802
  · exact u31803

def r41585 : Route 9 := (fun mask => (mask,id))

def c41585 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41585 : Upper (D 6) (R 6) [10,48,65,160] 13 := by
  apply FastRouting.sound _ _ [10,48,65,160] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r41585 c41585
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31804
  · exact u31805
  · exact u31806
  · exact u31807
  · exact u31808
  · exact u31809
  · exact u31810
  · exact u31811
  · exact u31812
  · exact u31813

def r41586 : Route 9 := (fun mask => (mask,id))

def c41586 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 10 => 3 | 66 => 6 | 130 => 7 | 12 => 3 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u41586 : Upper (D 6) (R 6) [10,48,65,192] 13 := by
  apply FastRouting.sound _ _ [10,48,65,192] 13 (by decide) (choices 2) [3,5,6,33,34,36,257,258,260,288] r41586 c41586
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31814
  · exact u31815
  · exact u31816
  · exact u31817
  · exact u31818
  · exact u31819
  · exact u31820
  · exact u31821
  · exact u31822
  · exact u31823

def r41587 : Route 9 := (fun mask => (mask,id))

def c41587 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41587 : Upper (D 6) (R 6) [10,48,65,384] 13 := by
  apply FastRouting.sound _ _ [10,48,65,384] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r41587 c41587
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31824
  · exact u31825
  · exact u31826
  · exact u31827
  · exact u31828
  · exact u31829
  · exact u31830
  · exact u31831
  · exact u31832
  · exact u31833

def b41588 : PairBound 9 := { available := 485, camps := [{ cop := 2, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 50 70 13 501 485 485 485 485), lower := (rows 11 50 70 13 16 32 64 128 256), losses := [] }

theorem u41588 : Upper (D 6) (R 6) [10,48,66,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41588 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41589 : PairBound 9 := { available := 453, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 50 70 41 469 485 453 453 453), lower := (rows 11 50 70 41 16 32 64 128 256), losses := [] }

theorem u41589 : Upper (D 6) (R 6) [10,48,66,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41589 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41590 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c41590 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41590 : Upper (D 6) (R 6) [10,48,66,36] 13 := by
  apply FastRouting.sound _ _ [10,48,66,36] 13 (by decide) (choices 2) [5,65,68,129,132,192,384] r41590 c41590
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31834
  · exact u31835
  · exact u31836
  · exact u31837
  · exact u31838
  · exact u31839
  · exact u31840

def b41591 : PairBound 9 := { available := 421, camps := [{ cop := 2, region := 9, targets := 4 },{ cop := 2, region := 9, targets := 32 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 50 70 73 437 421 485 421 421), lower := (rows 11 50 70 73 16 32 64 128 256), losses := [] }

theorem u41591 : Upper (D 6) (R 6) [10,48,66,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41591 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41592 : PairBound 9 := { available := 421, camps := [{ cop := 3, region := 435, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 11 50 70 76 437 421 485 421 421), lower := (rows 11 50 70 76 16 32 64 128 256), losses := [] }

theorem u41592 : Upper (D 6) (R 6) [10,48,66,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41592 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41593 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c41593 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 68 => 6 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u41593 : Upper (D 6) (R 6) [10,48,66,96] 13 := by
  apply FastRouting.sound _ _ [10,48,66,96] 13 (by decide) (choices 2) [5,129,132,384] r41593 c41593
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u31841
  · exact u31842
  · exact u31843
  · exact u31844

def r41594 : Route 9 := (fun mask => (mask,id))

def c41594 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41594 : Upper (D 6) (R 6) [10,48,66,129] 13 := by
  apply FastRouting.sound _ _ [10,48,66,129] 13 (by decide) (choices 2) [5,33,36,65,68,96,257,260,288,320] r41594 c41594
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31845
  · exact u31846
  · exact u31847
  · exact u31848
  · exact u31849
  · exact u31850
  · exact u31851
  · exact u31852
  · exact u31853
  · exact u31854

def r41595 : Route 9 := (fun mask => (mask,id))

def c41595 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41595 : Upper (D 6) (R 6) [10,48,66,132] 13 := by
  apply FastRouting.sound _ _ [10,48,66,132] 13 (by decide) (choices 2) [5,33,36,65,68,96,257,260,288,320] r41595 c41595
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31855
  · exact u31856
  · exact u31857
  · exact u31858
  · exact u31859
  · exact u31860
  · exact u31861
  · exact u31862
  · exact u31863
  · exact u31864

def r41596 : Route 9 := (fun mask => (mask,id))

def c41596 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41596 : Upper (D 6) (R 6) [10,48,66,160] 13 := by
  apply FastRouting.sound _ _ [10,48,66,160] 13 (by decide) (choices 2) [5,65,68,257,260,320] r41596 c41596
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31865
  · exact u31866
  · exact u31867
  · exact u31868
  · exact u31869
  · exact u31870

def r41597 : Route 9 := (fun mask => (mask,id))

def c41597 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u41597 : Upper (D 6) (R 6) [10,48,66,192] 13 := by
  apply FastRouting.sound _ _ [10,48,66,192] 13 (by decide) (choices 2) [5,33,36,257,260,288] r41597 c41597
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31871
  · exact u31872
  · exact u31873
  · exact u31874
  · exact u31875
  · exact u31876

def r41598 : Route 9 := (fun mask => (mask,id))

def c41598 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41598 : Upper (D 6) (R 6) [10,48,66,384] 13 := by
  apply FastRouting.sound _ _ [10,48,66,384] 13 (by decide) (choices 2) [5,33,36,65,68,96] r41598 c41598
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31877
  · exact u31878
  · exact u31879
  · exact u31880
  · exact u31881
  · exact u31882

def b41599 : PairBound 9 := { available := 453, camps := [{ cop := 1, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 50 100 11 469 485 453 453 453), lower := (rows 11 50 100 11 16 32 64 128 256), losses := [] }

theorem u41599 : Upper (D 6) (R 6) [10,48,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41599 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41600 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c41600 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 12 => 3 | 36 => 5 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41600 : Upper (D 6) (R 6) [10,48,96,5] 13 := by
  apply FastRouting.sound _ _ [10,48,96,5] 13 (by decide) (choices 2) [3,5,6,65,66,68,129,130,132,192,384] r41600 c41600
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31883
  · exact u31884
  · exact u31885
  · exact u31886
  · exact u31887
  · exact u31888
  · exact u31889
  · exact u31890
  · exact u31891
  · exact u31892
  · exact u31893

def b41601 : PairBound 9 := { available := 453, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 3, region := 1, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 11 50 100 14 469 485 453 453 453), lower := (rows 11 50 100 14 16 32 64 128 256), losses := [] }

theorem u41601 : Upper (D 6) (R 6) [10,48,96,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41601 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41602 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c41602 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 10 => 3 | 34 => 5 | 66 => 6 | 12 => 3 | 36 => 5 | 68 => 6 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u41602 : Upper (D 6) (R 6) [10,48,96,65] 13 := by
  apply FastRouting.sound _ _ [10,48,96,65] 13 (by decide) (choices 2) [3,5,6,129,130,132,384] r41602 c41602
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31894
  · exact u31895
  · exact u31896
  · exact u31897
  · exact u31898
  · exact u31899
  · exact u31900

def b41603 : PairBound 9 := { available := 389, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 50 100 74 405 421 453 389 389), lower := (rows 11 50 100 74 16 32 64 128 256), losses := [] }

theorem u41603 : Upper (D 6) (R 6) [10,48,96,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41603 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41604 : PairBound 9 := { available := 391, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 50 100 76 407 423 455 391 391), lower := (rows 11 50 100 76 16 32 64 128 256), losses := [] }

theorem u41604 : Upper (D 6) (R 6) [10,48,96,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41604 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41605 : Route 9 := (fun mask => (mask,id))

def c41605 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41605 : Upper (D 6) (R 6) [10,48,96,129] 13 := by
  apply FastRouting.sound _ _ [10,48,96,129] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r41605 c41605
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31901
  · exact u31902
  · exact u31903
  · exact u31904
  · exact u31905
  · exact u31906
  · exact u31907
  · exact u31908
  · exact u31909
  · exact u31910

def b41606 : PairBound 9 := { available := 325, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 50 100 138 341 357 325 453 325), lower := (rows 11 50 100 138 16 32 64 128 256), losses := [] }

theorem u41606 : Upper (D 6) (R 6) [10,48,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41606 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41607 : Route 9 := (fun mask => (mask,id))

def c41607 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41607 : Upper (D 6) (R 6) [10,48,96,132] 13 := by
  apply FastRouting.sound _ _ [10,48,96,132] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r41607 c41607
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31911
  · exact u31912
  · exact u31913
  · exact u31914
  · exact u31915
  · exact u31916
  · exact u31917
  · exact u31918
  · exact u31919
  · exact u31920

def r41608 : Route 9 := (fun mask => (mask,id))

def c41608 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u41608 : Upper (D 6) (R 6) [10,48,96,192] 13 := by
  apply FastRouting.sound _ _ [10,48,96,192] 13 (by decide) (choices 2) [3,5,6,257,258,260] r41608 c41608
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31921
  · exact u31922
  · exact u31923
  · exact u31924
  · exact u31925
  · exact u31926

def r41609 : Route 9 := (fun mask => (mask,id))

def c41609 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41609 : Upper (D 6) (R 6) [10,48,96,384] 13 := by
  apply FastRouting.sound _ _ [10,48,96,384] 13 (by decide) (choices 2) [3,5,6,65,66,68] r41609 c41609
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31927
  · exact u31928
  · exact u31929
  · exact u31930
  · exact u31931
  · exact u31932

def b41610 : PairBound 9 := { available := 356, camps := [{ cop := 1, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 50 133 11 372 356 356 484 356), lower := (rows 11 50 133 11 16 32 64 128 256), losses := [] }

theorem u41610 : Upper (D 6) (R 6) [10,48,129,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41610 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41611 : PairBound 9 := { available := 358, camps := [{ cop := 2, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 11 50 133 13 374 358 358 486 358), lower := (rows 11 50 133 13 16 32 64 128 256), losses := [] }

theorem u41611 : Upper (D 6) (R 6) [10,48,129,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41611 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41612 : PairBound 9 := { available := 357, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 50 133 14 373 357 357 485 357), lower := (rows 11 50 133 14 16 32 64 128 256), losses := [] }

theorem u41612 : Upper (D 6) (R 6) [10,48,129,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41612 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41613 : PairBound 9 := { available := 326, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 50 133 41 342 358 326 454 326), lower := (rows 11 50 133 41 16 32 64 128 256), losses := [] }

theorem u41613 : Upper (D 6) (R 6) [10,48,129,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41613 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41614 : PairBound 9 := { available := 325, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 50 133 42 341 357 325 453 325), lower := (rows 11 50 133 42 16 32 64 128 256), losses := [] }

theorem u41614 : Upper (D 6) (R 6) [10,48,129,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41614 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41615 : Route 9 := (fun mask => (mask,id))

def c41615 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41615 : Upper (D 6) (R 6) [10,48,129,36] 13 := by
  apply FastRouting.sound _ _ [10,48,129,36] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r41615 c41615
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31933
  · exact u31934
  · exact u31935
  · exact u31936
  · exact u31937
  · exact u31938
  · exact u31939
  · exact u31940
  · exact u31941
  · exact u31942

def r41616 : Route 9 := (fun mask => (mask,id))

def c41616 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41616 : Upper (D 6) (R 6) [10,48,129,65] 13 := by
  apply FastRouting.sound _ _ [10,48,129,65] 13 (by decide) (choices 2) [6,34,36,66,68,96,258,260,288,320] r41616 c41616
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31943
  · exact u31944
  · exact u31945
  · exact u31946
  · exact u31947
  · exact u31948
  · exact u31949
  · exact u31950
  · exact u31951
  · exact u31952

def b41617 : PairBound 9 := { available := 357, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 50 133 74 373 357 357 485 357), lower := (rows 11 50 133 74 16 32 64 128 256), losses := [] }

theorem u41617 : Upper (D 6) (R 6) [10,48,129,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41617 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41618 : Route 9 := (fun mask => (mask,id))

def c41618 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41618 : Upper (D 6) (R 6) [10,48,129,68] 13 := by
  apply FastRouting.sound _ _ [10,48,129,68] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,257,258,260,288,320] r41618 c41618
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31953
  · exact u31954
  · exact u31955
  · exact u31956
  · exact u31957
  · exact u31958
  · exact u31959
  · exact u31960
  · exact u31961
  · exact u31962
  · exact u31963
  · exact u31964
  · exact u31965
  · exact u31966
  · exact u31967

def r41619 : Route 9 := (fun mask => (mask,id))

def c41619 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41619 : Upper (D 6) (R 6) [10,48,129,96] 13 := by
  apply FastRouting.sound _ _ [10,48,129,96] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r41619 c41619
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31968
  · exact u31969
  · exact u31970
  · exact u31971
  · exact u31972
  · exact u31973
  · exact u31974
  · exact u31975
  · exact u31976
  · exact u31977

def r41620 : Route 9 := (fun mask => (mask,id))

def c41620 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41620 : Upper (D 6) (R 6) [10,48,129,257] 13 := by
  apply FastRouting.sound _ _ [10,48,129,257] 13 (by decide) (choices 2) [6,34,36,66,68,96] r41620 c41620
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31978
  · exact u31979
  · exact u31980
  · exact u31981
  · exact u31982
  · exact u31983

def b41621 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 50 133 266 117 101 101 229 357), lower := (rows 11 50 133 266 16 32 64 128 256), losses := [] }

theorem u41621 : Upper (D 6) (R 6) [10,48,129,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41621 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41622 : Route 9 := (fun mask => (mask,id))

def c41622 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41622 : Upper (D 6) (R 6) [10,48,129,260] 13 := by
  apply FastRouting.sound _ _ [10,48,129,260] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r41622 c41622
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31984
  · exact u31985
  · exact u31986
  · exact u31987
  · exact u31988
  · exact u31989
  · exact u31990
  · exact u31991
  · exact u31992
  · exact u31993

def r41623 : Route 9 := (fun mask => (mask,id))

def c41623 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41623 : Upper (D 6) (R 6) [10,48,129,288] 13 := by
  apply FastRouting.sound _ _ [10,48,129,288] 13 (by decide) (choices 2) [3,5,6,65,66,68] r41623 c41623
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31994
  · exact u31995
  · exact u31996
  · exact u31997
  · exact u31998
  · exact u31999

def r41624 : Route 9 := (fun mask => (mask,id))

def c41624 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41624 : Upper (D 6) (R 6) [10,48,129,320] 13 := by
  apply FastRouting.sound _ _ [10,48,129,320] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r41624 c41624
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32000
  · exact u32001
  · exact u32002
  · exact u32003
  · exact u32004
  · exact u32005
  · exact u32006
  · exact u32007
  · exact u32008
  · exact u32009

def b41625 : PairBound 9 := { available := 357, camps := [{ cop := 2, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 50 134 13 373 357 357 485 357), lower := (rows 11 50 134 13 16 32 64 128 256), losses := [] }

theorem u41625 : Upper (D 6) (R 6) [10,48,130,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41625 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41626 : PairBound 9 := { available := 325, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 50 134 41 341 357 325 453 325), lower := (rows 11 50 134 41 16 32 64 128 256), losses := [] }

theorem u41626 : Upper (D 6) (R 6) [10,48,130,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41626 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41627 : Route 9 := (fun mask => (mask,id))

def c41627 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41627 : Upper (D 6) (R 6) [10,48,130,36] 13 := by
  apply FastRouting.sound _ _ [10,48,130,36] 13 (by decide) (choices 2) [5,65,68,257,260,320] r41627 c41627
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32010
  · exact u32011
  · exact u32012
  · exact u32013
  · exact u32014
  · exact u32015

def r41628 : Route 9 := (fun mask => (mask,id))

def c41628 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41628 : Upper (D 6) (R 6) [10,48,130,65] 13 := by
  apply FastRouting.sound _ _ [10,48,130,65] 13 (by decide) (choices 2) [5,33,36,65,68,96,257,260,288,320] r41628 c41628
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32016
  · exact u32017
  · exact u32018
  · exact u32019
  · exact u32020
  · exact u32021
  · exact u32022
  · exact u32023
  · exact u32024
  · exact u32025

def r41629 : Route 9 := (fun mask => (mask,id))

def c41629 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41629 : Upper (D 6) (R 6) [10,48,130,68] 13 := by
  apply FastRouting.sound _ _ [10,48,130,68] 13 (by decide) (choices 2) [5,33,36,65,68,96,257,260,288,320] r41629 c41629
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32026
  · exact u32027
  · exact u32028
  · exact u32029
  · exact u32030
  · exact u32031
  · exact u32032
  · exact u32033
  · exact u32034
  · exact u32035

def r41630 : Route 9 := (fun mask => (mask,id))

def c41630 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41630 : Upper (D 6) (R 6) [10,48,130,96] 13 := by
  apply FastRouting.sound _ _ [10,48,130,96] 13 (by decide) (choices 2) [5,65,68,257,260,320] r41630 c41630
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32036
  · exact u32037
  · exact u32038
  · exact u32039
  · exact u32040
  · exact u32041

def r41631 : Route 9 := (fun mask => (mask,id))

def c41631 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41631 : Upper (D 6) (R 6) [10,48,130,257] 13 := by
  apply FastRouting.sound _ _ [10,48,130,257] 13 (by decide) (choices 2) [5,33,36,65,68,96] r41631 c41631
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32042
  · exact u32043
  · exact u32044
  · exact u32045
  · exact u32046
  · exact u32047

def r41632 : Route 9 := (fun mask => (mask,id))

def c41632 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41632 : Upper (D 6) (R 6) [10,48,130,260] 13 := by
  apply FastRouting.sound _ _ [10,48,130,260] 13 (by decide) (choices 2) [5,33,36,65,68,96] r41632 c41632
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32048
  · exact u32049
  · exact u32050
  · exact u32051
  · exact u32052
  · exact u32053

def r41633 : Route 9 := (fun mask => (mask,id))

def c41633 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41633 : Upper (D 6) (R 6) [10,48,130,288] 13 := by
  apply FastRouting.sound _ _ [10,48,130,288] 13 (by decide) (choices 2) [5,65,68] r41633 c41633
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u32054
  · exact u32055
  · exact u32056

def r41634 : Route 9 := (fun mask => (mask,id))

def c41634 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41634 : Upper (D 6) (R 6) [10,48,130,320] 13 := by
  apply FastRouting.sound _ _ [10,48,130,320] 13 (by decide) (choices 2) [5,33,36,65,68,96] r41634 c41634
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32057
  · exact u32058
  · exact u32059
  · exact u32060
  · exact u32061
  · exact u32062

def b41635 : PairBound 9 := { available := 325, camps := [{ cop := 1, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 50 164 11 341 357 325 453 325), lower := (rows 11 50 164 11 16 32 64 128 256), losses := [] }

theorem u41635 : Upper (D 6) (R 6) [10,48,160,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41635 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41636 : Route 9 := (fun mask => (mask,id))

def c41636 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41636 : Upper (D 6) (R 6) [10,48,160,5] 13 := by
  apply FastRouting.sound _ _ [10,48,160,5] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r41636 c41636
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32063
  · exact u32064
  · exact u32065
  · exact u32066
  · exact u32067
  · exact u32068
  · exact u32069
  · exact u32070
  · exact u32071
  · exact u32072

def b41637 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 3, region := 1, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 11 50 164 14 341 357 325 453 325), lower := (rows 11 50 164 14 16 32 64 128 256), losses := [] }

theorem u41637 : Upper (D 6) (R 6) [10,48,160,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41637 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41638 : Route 9 := (fun mask => (mask,id))

def c41638 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41638 : Upper (D 6) (R 6) [10,48,160,65] 13 := by
  apply FastRouting.sound _ _ [10,48,160,65] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r41638 c41638
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32073
  · exact u32074
  · exact u32075
  · exact u32076
  · exact u32077
  · exact u32078
  · exact u32079
  · exact u32080
  · exact u32081
  · exact u32082

def b41639 : PairBound 9 := { available := 325, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 50 164 74 341 357 325 453 325), lower := (rows 11 50 164 74 16 32 64 128 256), losses := [] }

theorem u41639 : Upper (D 6) (R 6) [10,48,160,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41639 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u41639
end Delivery.IrregularNine14.P06

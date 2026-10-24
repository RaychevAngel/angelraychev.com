import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0079
import IrregularNine14P09C0080
import IrregularNine14P09C0081
import IrregularNine14P09C0082

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r7620 : Route 9 := (fun mask => (mask,id))

def c7620 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u7620 : Upper (D 9) (R 9) [34,68,160,65,264] 13 := by
  apply FastRouting.sound _ _ [34,68,160,65,264] 13 (by decide) (choices 1) [1,16,128,256] r7620 c7620
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4799
  · exact u4800
  · exact u4801
  · exact u4802

def r7621 : Route 9 := (fun mask => (mask,id))

def c7621 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7621 : Upper (D 9) (R 9) [34,68,160,65,384] 13 := by
  apply FastRouting.sound _ _ [34,68,160,65,384] 13 (by decide) (choices 1) [1,8,16,256] r7621 c7621
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4803
  · exact u4804
  · exact u4805
  · exact u4806

def r7622 : Route 9 := (fun mask => (mask,id))

def c7622 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7622 : Upper (D 9) (R 9) [34,68,160,80,129] 13 := by
  apply FastRouting.sound _ _ [34,68,160,80,129] 13 (by decide) (choices 1) [1,8,256] r7622 c7622
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4807
  · exact u4808
  · exact u4809

def b7623 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 421, targets := 64 },{ cop := 2, region := 323, targets := 128 }], pairs := [(0,6),(0,7),(2,6),(3,5),(4,5)], upper := (rows 35 70 164 88 152 289 321 385 257), lower := (rows 35 70 164 88 152 32 64 128 256), losses := [] }

theorem u7623 : Upper (D 9) (R 9) [34,68,160,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7623 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7624 : Route 9 := (fun mask => (mask,id))

def c7624 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7624 : Upper (D 9) (R 9) [34,68,160,80,257] 13 := by
  apply FastRouting.sound _ _ [34,68,160,80,257] 13 (by decide) (choices 1) [1,8,128,256] r7624 c7624
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4810
  · exact u4811
  · exact u4812
  · exact u4813

def r7625 : Route 9 := (fun mask => (mask,id))

def c7625 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7625 : Upper (D 9) (R 9) [34,68,160,80,264] 13 := by
  apply FastRouting.sound _ _ [34,68,160,80,264] 13 (by decide) (choices 1) [1,128,256] r7625 c7625
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4814
  · exact u4815
  · exact u4816

def r7626 : Route 9 := (fun mask => (mask,id))

def c7626 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7626 : Upper (D 9) (R 9) [34,68,160,80,384] 13 := by
  apply FastRouting.sound _ _ [34,68,160,80,384] 13 (by decide) (choices 1) [1,8,256] r7626 c7626
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4817
  · exact u4818
  · exact u4819

def r7627 : Route 9 := (fun mask => (mask,id))

def c7627 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | _ => 0)

theorem u7627 : Upper (D 9) (R 9) [34,68,160,129,257] 13 := by
  apply FastRouting.sound _ _ [34,68,160,129,257] 13 (by decide) (choices 1) [8,16,64,256] r7627 c7627
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4820
  · exact u4821
  · exact u4822
  · exact u4823

def r7628 : Route 9 := (fun mask => (mask,id))

def c7628 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u7628 : Upper (D 9) (R 9) [34,68,160,129,264] 13 := by
  apply FastRouting.sound _ _ [34,68,160,129,264] 13 (by decide) (choices 1) [1,16,64,256] r7628 c7628
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4824
  · exact u4825
  · exact u4826
  · exact u4827

def r7629 : Route 9 := (fun mask => (mask,id))

def c7629 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7629 : Upper (D 9) (R 9) [34,68,160,129,320] 13 := by
  apply FastRouting.sound _ _ [34,68,160,129,320] 13 (by decide) (choices 1) [1,8,16,256] r7629 c7629
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4828
  · exact u4829
  · exact u4830
  · exact u4831

def r7630 : Route 9 := (fun mask => (mask,id))

def c7630 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u7630 : Upper (D 9) (R 9) [34,68,160,144,257] 13 := by
  apply FastRouting.sound _ _ [34,68,160,144,257] 13 (by decide) (choices 1) [1,8,64,256] r7630 c7630
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4832
  · exact u4833
  · exact u4834
  · exact u4835

def r7631 : Route 9 := (fun mask => (mask,id))

def c7631 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u7631 : Upper (D 9) (R 9) [34,68,160,144,264] 13 := by
  apply FastRouting.sound _ _ [34,68,160,144,264] 13 (by decide) (choices 1) [1,64,256] r7631 c7631
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4836
  · exact u4837
  · exact u4838

def r7632 : Route 9 := (fun mask => (mask,id))

def c7632 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7632 : Upper (D 9) (R 9) [34,68,160,144,320] 13 := by
  apply FastRouting.sound _ _ [34,68,160,144,320] 13 (by decide) (choices 1) [1,8,256] r7632 c7632
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4839
  · exact u4840
  · exact u4841

def r7633 : Route 9 := (fun mask => (mask,id))

def c7633 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7633 : Upper (D 9) (R 9) [34,68,160,192,257] 13 := by
  apply FastRouting.sound _ _ [34,68,160,192,257] 13 (by decide) (choices 1) [1,8,16,256] r7633 c7633
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4842
  · exact u4843
  · exact u4844
  · exact u4845

def r7634 : Route 9 := (fun mask => (mask,id))

def c7634 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7634 : Upper (D 9) (R 9) [34,68,160,192,264] 13 := by
  apply FastRouting.sound _ _ [34,68,160,192,264] 13 (by decide) (choices 1) [1,16,256] r7634 c7634
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4846
  · exact u4847
  · exact u4848

def b7635 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 16, targets := 192 },{ cop := 4, region := 8, targets := 64 }], pairs := [(3,5),(3,6),(4,5),(4,6),(4,7)], upper := (rows 35 70 164 265 273 248 216 216 472), lower := (rows 35 70 164 265 273 32 64 128 256), losses := [] }

theorem u7635 : Upper (D 9) (R 9) [34,68,160,257,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7635 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7636 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 16, targets := 193 },{ cop := 4, region := 231, targets := 256 }], pairs := [(0,8),(1,8),(4,0),(4,6),(4,7)], upper := (rows 35 70 164 265 280 241 209 209 465), lower := (rows 35 70 164 265 280 32 64 128 256), losses := [] }

theorem u7636 : Upper (D 9) (R 9) [34,68,160,257,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7636 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7637 : Route 9 := (fun mask => (mask,id))

def c7637 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7637 : Upper (D 9) (R 9) [34,68,160,257,320] 13 := by
  apply FastRouting.sound _ _ [34,68,160,257,320] 13 (by decide) (choices 1) [1,8,16,128] r7637 c7637
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4849
  · exact u4850
  · exact u4851
  · exact u4852

def r7638 : Route 9 := (fun mask => (mask,id))

def c7638 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7638 : Upper (D 9) (R 9) [34,68,160,257,384] 13 := by
  apply FastRouting.sound _ _ [34,68,160,257,384] 13 (by decide) (choices 1) [1,8,16,64] r7638 c7638
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4853
  · exact u4854
  · exact u4855
  · exact u4856

def b7639 : PairBound 9 := { available := 193, camps := [{ cop := 8, region := 24, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7),(4,0)], upper := (rows 35 70 164 280 280 225 193 193 449), lower := (rows 35 70 164 280 280 32 64 128 256), losses := [] }

theorem u7639 : Upper (D 9) (R 9) [34,68,160,272,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7639 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7640 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 8, targets := 225 },{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(3,0),(3,5),(3,6),(3,7)], upper := (rows 35 70 164 280 336 169 201 137 393), lower := (rows 35 70 164 280 336 32 64 128 256), losses := [] }

theorem u7640 : Upper (D 9) (R 9) [34,68,160,272,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7640 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7641 : PairBound 9 := { available := 73, camps := [{ cop := 4, region := 8, targets := 225 },{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(3,0),(3,5),(3,6),(3,7)], upper := (rows 35 70 164 280 400 105 73 201 329), lower := (rows 35 70 164 280 400 32 64 128 256), losses := [] }

theorem u7641 : Upper (D 9) (R 9) [34,68,160,272,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7641 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7642 : Route 9 := (fun mask => (mask,id))

def c7642 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7642 : Upper (D 9) (R 9) [34,68,160,320,384] 13 := by
  apply FastRouting.sound _ _ [34,68,160,320,384] 13 (by decide) (choices 1) [1,8,16] r7642 c7642
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4857
  · exact u4858
  · exact u4859

def b7643 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 24, targets := 480 }], pairs := [(3,5),(3,6),(3,7),(3,8),(4,5)], upper := (rows 35 70 388 25 25 480 480 480 480), lower := (rows 35 70 388 25 25 32 64 128 256), losses := [] }

theorem u7643 : Upper (D 9) (R 9) [34,68,384,17,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7643 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7644 : PairBound 9 := { available := 456, camps := [{ cop := 0, region := 24, targets := 448 }], pairs := [(3,6),(3,7),(3,8),(4,6),(4,7)], upper := (rows 35 70 388 25 49 488 456 456 456), lower := (rows 35 70 388 25 49 32 64 128 256), losses := [] }

theorem u7644 : Upper (D 9) (R 9) [34,68,384,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7644 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7645 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 24, targets := 448 }], pairs := [(3,6),(3,7),(3,8),(4,6),(4,7)], upper := (rows 35 70 388 25 56 481 449 449 449), lower := (rows 35 70 388 25 56 32 64 128 256), losses := [] }

theorem u7645 : Upper (D 9) (R 9) [34,68,384,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7645 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7646 : PairBound 9 := { available := 424, camps := [{ cop := 4, region := 8, targets := 416 },{ cop := 3, region := 486, targets := 1 }], pairs := [(1,0),(2,0),(3,5),(3,7),(3,8)], upper := (rows 35 70 388 25 81 424 488 424 424), lower := (rows 35 70 388 25 81 32 64 128 256), losses := [] }

theorem u7646 : Upper (D 9) (R 9) [34,68,384,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7646 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7647 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c7647 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7647 : Upper (D 9) (R 9) [34,68,384,17,72] 13 := by
  apply FastRouting.sound _ _ [34,68,384,17,72] 13 (by decide) (choices 1) [1,128] r7647 c7647
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4860
  · exact u4861

def r7648 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c7648 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7648 : Upper (D 9) (R 9) [34,68,384,17,96] 13 := by
  apply FastRouting.sound _ _ [34,68,384,17,96] 13 (by decide) (choices 1) [1,8,128] r7648 c7648
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4862
  · exact u4863
  · exact u4864

def b7649 : PairBound 9 := { available := 360, camps := [{ cop := 4, region := 8, targets := 352 },{ cop := 3, region := 486, targets := 1 }], pairs := [(1,0),(2,0),(3,5),(3,6),(3,8)], upper := (rows 35 70 388 25 145 360 360 488 360), lower := (rows 35 70 388 25 145 32 64 128 256), losses := [] }

theorem u7649 : Upper (D 9) (R 9) [34,68,384,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7649 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7650 : Route 9 := (fun mask => (mask,id))

def c7650 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u7650 : Upper (D 9) (R 9) [34,68,384,17,136] 13 := by
  apply FastRouting.sound _ _ [34,68,384,17,136] 13 (by decide) (choices 1) [1,64,256] r7650 c7650
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4865
  · exact u4866
  · exact u4867

def r7651 : Route 9 := (fun mask => (mask,id))

def c7651 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u7651 : Upper (D 9) (R 9) [34,68,384,17,160] 13 := by
  apply FastRouting.sound _ _ [34,68,384,17,160] 13 (by decide) (choices 1) [1,8,64,256] r7651 c7651
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4868
  · exact u4869
  · exact u4870
  · exact u4871

def r7652 : Route 9 := (fun mask => (mask,id))

def c7652 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7652 : Upper (D 9) (R 9) [34,68,384,17,192] 13 := by
  apply FastRouting.sound _ _ [34,68,384,17,192] 13 (by decide) (choices 1) [1,8,256] r7652 c7652
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4872
  · exact u4873
  · exact u4874

def b7653 : PairBound 9 := { available := 105, camps := [{ cop := 2, region := 16, targets := 97 },{ cop := 4, region := 4, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5),(4,6)], upper := (rows 35 70 388 25 400 105 105 233 361), lower := (rows 35 70 388 25 400 32 64 128 256), losses := [] }

theorem u7653 : Upper (D 9) (R 9) [34,68,384,17,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7653 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7654 : PairBound 9 := { available := 408, camps := [{ cop := 0, region := 8, targets := 448 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(3,6),(3,7),(3,8)], upper := (rows 35 70 388 41 81 440 472 408 408), lower := (rows 35 70 388 41 81 32 64 128 256), losses := [] }

theorem u7654 : Upper (D 9) (R 9) [34,68,384,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7654 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7655 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 8, targets := 448 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(3,6),(3,7),(3,8)], upper := (rows 35 70 388 41 88 433 465 401 401), lower := (rows 35 70 388 41 88 32 64 128 256), losses := [] }

theorem u7655 : Upper (D 9) (R 9) [34,68,384,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7655 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7656 : PairBound 9 := { available := 344, camps := [{ cop := 0, region := 8, targets := 448 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(3,6),(3,7),(3,8)], upper := (rows 35 70 388 41 145 376 344 472 344), lower := (rows 35 70 388 41 145 32 64 128 256), losses := [] }

theorem u7656 : Upper (D 9) (R 9) [34,68,384,33,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7656 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7657 : PairBound 9 := { available := 337, camps := [{ cop := 0, region := 8, targets := 448 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(3,6),(3,7),(3,8)], upper := (rows 35 70 388 41 152 369 337 465 337), lower := (rows 35 70 388 41 152 32 64 128 256), losses := [] }

theorem u7657 : Upper (D 9) (R 9) [34,68,384,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7657 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7658 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 8, targets := 448 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(3,6),(3,7),(3,8)], upper := (rows 35 70 388 41 208 313 345 409 281), lower := (rows 35 70 388 41 208 32 64 128 256), losses := [] }

theorem u7658 : Upper (D 9) (R 9) [34,68,384,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7658 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7659 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c7659 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7659 : Upper (D 9) (R 9) [34,68,384,48,65] 13 := by
  apply FastRouting.sound _ _ [34,68,384,48,65] 13 (by decide) (choices 1) [1,8,128] r7659 c7659
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4875
  · exact u4876
  · exact u4877

def r7660 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c7660 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7660 : Upper (D 9) (R 9) [34,68,384,48,72] 13 := by
  apply FastRouting.sound _ _ [34,68,384,48,72] 13 (by decide) (choices 1) [1,128] r7660 c7660
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4878
  · exact u4879

def r7661 : Route 9 := (fun mask => (mask,id))

def c7661 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u7661 : Upper (D 9) (R 9) [34,68,384,48,129] 13 := by
  apply FastRouting.sound _ _ [34,68,384,48,129] 13 (by decide) (choices 1) [1,8,64,256] r7661 c7661
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4880
  · exact u4881
  · exact u4882
  · exact u4883

def r7662 : Route 9 := (fun mask => (mask,id))

def c7662 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u7662 : Upper (D 9) (R 9) [34,68,384,48,136] 13 := by
  apply FastRouting.sound _ _ [34,68,384,48,136] 13 (by decide) (choices 1) [1,64,256] r7662 c7662
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4884
  · exact u4885
  · exact u4886

def r7663 : Route 9 := (fun mask => (mask,id))

def c7663 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7663 : Upper (D 9) (R 9) [34,68,384,48,192] 13 := by
  apply FastRouting.sound _ _ [34,68,384,48,192] 13 (by decide) (choices 1) [1,8,256] r7663 c7663
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4887
  · exact u4888
  · exact u4889

def b7664 : PairBound 9 := { available := 73, camps := [{ cop := 2, region := 16, targets := 97 },{ cop := 4, region := 4, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5),(4,6)], upper := (rows 35 70 388 56 400 105 73 201 329), lower := (rows 35 70 388 56 400 32 64 128 256), losses := [] }

theorem u7664 : Upper (D 9) (R 9) [34,68,384,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7664 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7665 : Route 9 := (fun mask => (mask,id))

def c7665 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7665 : Upper (D 9) (R 9) [34,68,384,65,129] 13 := by
  apply FastRouting.sound _ _ [34,68,384,65,129] 13 (by decide) (choices 1) [8,16,256] r7665 c7665
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4890
  · exact u4891
  · exact u4892

def r7666 : Route 9 := (fun mask => (mask,id))

def c7666 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7666 : Upper (D 9) (R 9) [34,68,384,65,136] 13 := by
  apply FastRouting.sound _ _ [34,68,384,65,136] 13 (by decide) (choices 1) [1,16,256] r7666 c7666
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4893
  · exact u4894
  · exact u4895

def r7667 : Route 9 := (fun mask => (mask,id))

def c7667 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7667 : Upper (D 9) (R 9) [34,68,384,65,160] 13 := by
  apply FastRouting.sound _ _ [34,68,384,65,160] 13 (by decide) (choices 1) [1,8,16,256] r7667 c7667
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4896
  · exact u4897
  · exact u4898
  · exact u4899

def b7668 : PairBound 9 := { available := 57, camps := [{ cop := 2, region := 16, targets := 97 },{ cop := 4, region := 4, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5),(4,6)], upper := (rows 35 70 388 73 400 57 121 185 313), lower := (rows 35 70 388 73 400 32 64 128 256), losses := [] }

theorem u7668 : Upper (D 9) (R 9) [34,68,384,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7668 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7669 : Route 9 := (fun mask => (mask,id))

def c7669 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7669 : Upper (D 9) (R 9) [34,68,384,80,129] 13 := by
  apply FastRouting.sound _ _ [34,68,384,80,129] 13 (by decide) (choices 1) [1,8,256] r7669 c7669
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4900
  · exact u4901
  · exact u4902

def r7670 : Route 9 := (fun mask => (mask,id))

def c7670 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7670 : Upper (D 9) (R 9) [34,68,384,80,136] 13 := by
  apply FastRouting.sound _ _ [34,68,384,80,136] 13 (by decide) (choices 1) [1,256] r7670 c7670
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4903
  · exact u4904

def r7671 : Route 9 := (fun mask => (mask,id))

def c7671 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7671 : Upper (D 9) (R 9) [34,68,384,80,160] 13 := by
  apply FastRouting.sound _ _ [34,68,384,80,160] 13 (by decide) (choices 1) [1,8,256] r7671 c7671
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4905
  · exact u4906
  · exact u4907

def b7672 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 16, targets := 97 },{ cop := 4, region := 4, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5),(4,6)], upper := (rows 35 70 388 88 400 41 105 169 297), lower := (rows 35 70 388 88 400 32 64 128 256), losses := [] }

theorem u7672 : Upper (D 9) (R 9) [34,68,384,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7672 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7673 : Route 9 := (fun mask => (mask,id))

def c7673 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7673 : Upper (D 9) (R 9) [34,68,384,96,129] 13 := by
  apply FastRouting.sound _ _ [34,68,384,96,129] 13 (by decide) (choices 1) [1,8,16,256] r7673 c7673
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4908
  · exact u4909
  · exact u4910
  · exact u4911

def r7674 : Route 9 := (fun mask => (mask,id))

def c7674 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7674 : Upper (D 9) (R 9) [34,68,384,96,136] 13 := by
  apply FastRouting.sound _ _ [34,68,384,96,136] 13 (by decide) (choices 1) [1,16,256] r7674 c7674
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4912
  · exact u4913
  · exact u4914

def b7675 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 16, targets := 97 },{ cop := 4, region := 4, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5),(4,6)], upper := (rows 35 70 388 104 400 57 89 153 281), lower := (rows 35 70 388 104 400 32 64 128 256), losses := [] }

theorem u7675 : Upper (D 9) (R 9) [34,68,384,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7675 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m7676_16 : Upper (D 9) (R 9) [34,68,384,129,257,16] 13 :=
  permutation_upper _ _ _ [34,68,384,129,257,8] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4915

def r7676 : Route 9 := (fun mask => (mask,id))

def c7676 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7676 : Upper (D 9) (R 9) [34,68,384,129,257] 13 := by
  apply FastRouting.sound _ _ [34,68,384,129,257] 13 (by decide) (choices 1) [8,16,64] r7676 c7676
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4915
  · exact m7676_16
  · exact u4916

def r7677 : Route 9 := (fun mask => (mask,id))

def c7677 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7677 : Upper (D 9) (R 9) [34,68,384,129,264] 13 := by
  apply FastRouting.sound _ _ [34,68,384,129,264] 13 (by decide) (choices 1) [1,16,64] r7677 c7677
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4917
  · exact u4918
  · exact u4919

def r7678 : Route 9 := (fun mask => (mask,id))

def c7678 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7678 : Upper (D 9) (R 9) [34,68,384,129,288] 13 := by
  apply FastRouting.sound _ _ [34,68,384,129,288] 13 (by decide) (choices 1) [1,8,16,64] r7678 c7678
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4920
  · exact u4921
  · exact u4922
  · exact u4923

def r7679 : Route 9 := (fun mask => (mask,id))

def c7679 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7679 : Upper (D 9) (R 9) [34,68,384,129,320] 13 := by
  apply FastRouting.sound _ _ [34,68,384,129,320] 13 (by decide) (choices 1) [1,8,16] r7679 c7679
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4924
  · exact u4925
  · exact u4926

#print axioms u7679
end Delivery.IrregularNine14.P09

import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0547
import IrregularNine14P06C0548
import IrregularNine14P06C0549
import IrregularNine14P06C0550
import IrregularNine14P06C0551

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r41820 : Route 9 := (fun mask => (mask,id))

def c41820 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41820 : Upper (D 6) (R 6) [10,129,48,320] 13 := by
  apply FastRouting.sound _ _ [10,129,48,320] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r41820 c41820
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32836
  · exact u32837
  · exact u32838
  · exact u32839
  · exact u32840
  · exact u32841
  · exact u32842
  · exact u32843
  · exact u32844
  · exact u32845

def b41821 : PairBound 9 := { available := 372, camps := [{ cop := 7, region := 11, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 131 100 11 372 372 372 500 372), lower := (rows 11 131 100 11 16 32 64 128 256), losses := [] }

theorem u41821 : Upper (D 6) (R 6) [10,129,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41821 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41822 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41822 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41822 : Upper (D 6) (R 6) [10,129,96,5] 13 := by
  apply FastRouting.sound _ _ [10,129,96,5] 13 (by decide) (choices 2) [6,34,36,96,258,260,288] r41822 c41822
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32846
  · exact u32847
  · exact u32848
  · exact u32849
  · exact u32850
  · exact u32851
  · exact u32852

def b41823 : PairBound 9 := { available := 373, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 131 100 14 373 373 373 501 373), lower := (rows 11 131 100 14 16 32 64 128 256), losses := [] }

theorem u41823 : Upper (D 6) (R 6) [10,129,96,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41823 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41824 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41824 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41824 : Upper (D 6) (R 6) [10,129,96,17] 13 := by
  apply FastRouting.sound _ _ [10,129,96,17] 13 (by decide) (choices 2) [6,34,36,96,258,260,288] r41824 c41824
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32853
  · exact u32854
  · exact u32855
  · exact u32856
  · exact u32857
  · exact u32858
  · exact u32859

def b41825 : PairBound 9 := { available := 357, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 131 100 26 373 357 357 485 357), lower := (rows 11 131 100 26 16 32 64 128 256), losses := [] }

theorem u41825 : Upper (D 6) (R 6) [10,129,96,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41825 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41826 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41826 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41826 : Upper (D 6) (R 6) [10,129,96,20] 13 := by
  apply FastRouting.sound _ _ [10,129,96,20] 13 (by decide) (choices 2) [3,5,6,33,34,36,96,257,258,260,288] r41826 c41826
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32860
  · exact u32861
  · exact u32862
  · exact u32863
  · exact u32864
  · exact u32865
  · exact u32866
  · exact u32867
  · exact u32868
  · exact u32869
  · exact u32870

def r41827 : Route 9 := (fun mask => (mask,id))

def c41827 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41827 : Upper (D 6) (R 6) [10,129,96,33] 13 := by
  apply FastRouting.sound _ _ [10,129,96,33] 13 (by decide) (choices 2) [6,66,68,258,260,320] r41827 c41827
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32871
  · exact u32872
  · exact u32873
  · exact u32874
  · exact u32875
  · exact u32876

def b41828 : PairBound 9 := { available := 341, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 131 100 42 341 373 341 469 341), lower := (rows 11 131 100 42 16 32 64 128 256), losses := [] }

theorem u41828 : Upper (D 6) (R 6) [10,129,96,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41828 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41829 : PairBound 9 := { available := 343, camps := [{ cop := 2, region := 8, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 131 100 44 343 375 343 471 343), lower := (rows 11 131 100 44 16 32 64 128 256), losses := [] }

theorem u41829 : Upper (D 6) (R 6) [10,129,96,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41829 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41830 : Route 9 := (fun mask => (mask,id))

def c41830 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41830 : Upper (D 6) (R 6) [10,129,96,48] 13 := by
  apply FastRouting.sound _ _ [10,129,96,48] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r41830 c41830
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32877
  · exact u32878
  · exact u32879
  · exact u32880
  · exact u32881
  · exact u32882
  · exact u32883
  · exact u32884
  · exact u32885
  · exact u32886

def b41831 : PairBound 9 := { available := 279, camps := [{ cop := 2, region := 8, targets := 3 },{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0),(3,0),(3,1)], upper := (rows 11 131 100 104 279 311 343 407 279), lower := (rows 11 131 100 104 16 32 64 128 256), losses := [] }

theorem u41831 : Upper (D 6) (R 6) [10,129,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41831 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41832 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41832 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41832 : Upper (D 6) (R 6) [10,129,96,257] 13 := by
  apply FastRouting.sound _ _ [10,129,96,257] 13 (by decide) (choices 2) [6,34,36,96] r41832 c41832
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u32887
  · exact u32888
  · exact u32889
  · exact u32890

def b41833 : PairBound 9 := { available := 117, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 131 100 266 117 117 117 245 373), lower := (rows 11 131 100 266 16 32 64 128 256), losses := [] }

theorem u41833 : Upper (D 6) (R 6) [10,129,96,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41833 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41834 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41834 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41834 : Upper (D 6) (R 6) [10,129,96,260] 13 := by
  apply FastRouting.sound _ _ [10,129,96,260] 13 (by decide) (choices 2) [3,5,6,33,34,36,96] r41834 c41834
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32891
  · exact u32892
  · exact u32893
  · exact u32894
  · exact u32895
  · exact u32896
  · exact u32897

def r41835 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41835 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41835 : Upper (D 6) (R 6) [10,129,96,272] 13 := by
  apply FastRouting.sound _ _ [10,129,96,272] 13 (by decide) (choices 2) [3,5,6,33,34,36,96] r41835 c41835
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32898
  · exact u32899
  · exact u32900
  · exact u32901
  · exact u32902
  · exact u32903
  · exact u32904

def r41836 : Route 9 := (fun mask => (mask,id))

def c41836 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41836 : Upper (D 6) (R 6) [10,129,96,288] 13 := by
  apply FastRouting.sound _ _ [10,129,96,288] 13 (by decide) (choices 2) [3,5,6,65,66,68] r41836 c41836
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32905
  · exact u32906
  · exact u32907
  · exact u32908
  · exact u32909
  · exact u32910

def b41837 : PairBound 9 := { available := 116, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 131 261 14 116 116 116 244 372), lower := (rows 11 131 261 14 16 32 64 128 256), losses := [] }

theorem u41837 : Upper (D 6) (R 6) [10,129,257,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41837 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41838 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 131 261 26 116 100 100 228 356), lower := (rows 11 131 261 26 16 32 64 128 256), losses := [] }

theorem u41838 : Upper (D 6) (R 6) [10,129,257,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41838 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41839 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41839 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41839 : Upper (D 6) (R 6) [10,129,257,20] 13 := by
  apply FastRouting.sound _ _ [10,129,257,20] 13 (by decide) (choices 2) [6,34,36,96] r41839 c41839
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u32911
  · exact u32912
  · exact u32913
  · exact u32914

def b41840 : PairBound 9 := { available := 116, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 131 261 42 116 116 116 244 372), lower := (rows 11 131 261 42 16 32 64 128 256), losses := [] }

theorem u41840 : Upper (D 6) (R 6) [10,129,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41840 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41841 : Route 9 := (fun mask => (mask,id))

def c41841 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41841 : Upper (D 6) (R 6) [10,129,257,36] 13 := by
  apply FastRouting.sound _ _ [10,129,257,36] 13 (by decide) (choices 2) [6,34,36,66,68,96] r41841 c41841
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32915
  · exact u32916
  · exact u32917
  · exact u32918
  · exact u32919
  · exact u32920

def r41842 : Route 9 := (fun mask => (mask,id))

def c41842 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41842 : Upper (D 6) (R 6) [10,129,257,48] 13 := by
  apply FastRouting.sound _ _ [10,129,257,48] 13 (by decide) (choices 2) [6,34,36,66,68,96] r41842 c41842
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32921
  · exact u32922
  · exact u32923
  · exact u32924
  · exact u32925
  · exact u32926

def r41843 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41843 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41843 : Upper (D 6) (R 6) [10,129,257,96] 13 := by
  apply FastRouting.sound _ _ [10,129,257,96] 13 (by decide) (choices 2) [6,34,36,96] r41843 c41843
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u32927
  · exact u32928
  · exact u32929
  · exact u32930

def b41844 : PairBound 9 := { available := 116, camps := [{ cop := 2, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 131 262 13 116 116 116 244 372), lower := (rows 11 131 262 13 16 32 64 128 256), losses := [] }

theorem u41844 : Upper (D 6) (R 6) [10,129,258,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41844 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41845 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 372, targets := 1 },{ cop := 2, region := 112, targets := 2 }], pairs := [(2,0),(4,0),(4,1)], upper := (rows 11 131 262 25 116 100 100 228 356), lower := (rows 11 131 262 25 16 32 64 128 256), losses := [] }

theorem u41845 : Upper (D 6) (R 6) [10,129,258,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41845 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41846 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41846 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41846 : Upper (D 6) (R 6) [10,129,258,20] 13 := by
  apply FastRouting.sound _ _ [10,129,258,20] 13 (by decide) (choices 2) [5,33,36,96] r41846 c41846
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u32931
  · exact u32932
  · exact u32933
  · exact u32934

def b41847 : PairBound 9 := { available := 116, camps := [{ cop := 0, region := 372, targets := 1 },{ cop := 2, region := 112, targets := 2 }], pairs := [(2,0),(4,0),(4,1)], upper := (rows 11 131 262 41 116 116 116 244 372), lower := (rows 11 131 262 41 16 32 64 128 256), losses := [] }

theorem u41847 : Upper (D 6) (R 6) [10,129,258,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41847 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41848 : Route 9 := (fun mask => (mask,id))

def c41848 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41848 : Upper (D 6) (R 6) [10,129,258,36] 13 := by
  apply FastRouting.sound _ _ [10,129,258,36] 13 (by decide) (choices 2) [5,33,36,65,68,96] r41848 c41848
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32935
  · exact u32936
  · exact u32937
  · exact u32938
  · exact u32939
  · exact u32940

def r41849 : Route 9 := (fun mask => (mask,id))

def c41849 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41849 : Upper (D 6) (R 6) [10,129,258,48] 13 := by
  apply FastRouting.sound _ _ [10,129,258,48] 13 (by decide) (choices 2) [5,33,36,65,68,96] r41849 c41849
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32941
  · exact u32942
  · exact u32943
  · exact u32944
  · exact u32945
  · exact u32946

def r41850 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41850 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41850 : Upper (D 6) (R 6) [10,129,258,96] 13 := by
  apply FastRouting.sound _ _ [10,129,258,96] 13 (by decide) (choices 2) [5,33,36,96] r41850 c41850
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u32947
  · exact u32948
  · exact u32949
  · exact u32950

def b41851 : PairBound 9 := { available := 100, camps := [{ cop := 7, region := 11, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 131 276 11 116 100 100 228 356), lower := (rows 11 131 276 11 16 32 64 128 256), losses := [] }

theorem u41851 : Upper (D 6) (R 6) [10,129,272,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41851 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41852 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41852 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41852 : Upper (D 6) (R 6) [10,129,272,5] 13 := by
  apply FastRouting.sound _ _ [10,129,272,5] 13 (by decide) (choices 2) [6,34,36,96] r41852 c41852
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u32951
  · exact u32952
  · exact u32953
  · exact u32954

def b41853 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 131 276 14 117 101 101 229 357), lower := (rows 11 131 276 14 16 32 64 128 256), losses := [] }

theorem u41853 : Upper (D 6) (R 6) [10,129,272,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41853 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41854 : Route 9 := (fun mask => (mask,id))

def c41854 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41854 : Upper (D 6) (R 6) [10,129,272,33] 13 := by
  apply FastRouting.sound _ _ [10,129,272,33] 13 (by decide) (choices 2) [6,34,36,66,68,96] r41854 c41854
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32955
  · exact u32956
  · exact u32957
  · exact u32958
  · exact u32959
  · exact u32960

def b41855 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 131 276 42 117 101 101 229 357), lower := (rows 11 131 276 42 16 32 64 128 256), losses := [] }

theorem u41855 : Upper (D 6) (R 6) [10,129,272,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41855 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41856 : Route 9 := (fun mask => (mask,id))

def c41856 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41856 : Upper (D 6) (R 6) [10,129,272,36] 13 := by
  apply FastRouting.sound _ _ [10,129,272,36] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r41856 c41856
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32961
  · exact u32962
  · exact u32963
  · exact u32964
  · exact u32965
  · exact u32966
  · exact u32967
  · exact u32968
  · exact u32969
  · exact u32970

def r41857 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41857 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41857 : Upper (D 6) (R 6) [10,129,272,96] 13 := by
  apply FastRouting.sound _ _ [10,129,272,96] 13 (by decide) (choices 2) [3,5,6,33,34,36,96] r41857 c41857
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32971
  · exact u32972
  · exact u32973
  · exact u32974
  · exact u32975
  · exact u32976
  · exact u32977

def b41858 : PairBound 9 := { available := 116, camps := [{ cop := 7, region := 11, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 131 292 11 116 116 116 244 372), lower := (rows 11 131 292 11 16 32 64 128 256), losses := [] }

theorem u41858 : Upper (D 6) (R 6) [10,129,288,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41858 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41859 : Route 9 := (fun mask => (mask,id))

def c41859 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41859 : Upper (D 6) (R 6) [10,129,288,5] 13 := by
  apply FastRouting.sound _ _ [10,129,288,5] 13 (by decide) (choices 2) [6,34,36,66,68,96] r41859 c41859
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32978
  · exact u32979
  · exact u32980
  · exact u32981
  · exact u32982
  · exact u32983

def b41860 : PairBound 9 := { available := 117, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 131 292 14 117 117 117 245 373), lower := (rows 11 131 292 14 16 32 64 128 256), losses := [] }

theorem u41860 : Upper (D 6) (R 6) [10,129,288,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41860 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41861 : Route 9 := (fun mask => (mask,id))

def c41861 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41861 : Upper (D 6) (R 6) [10,129,288,17] 13 := by
  apply FastRouting.sound _ _ [10,129,288,17] 13 (by decide) (choices 2) [6,34,36,66,68,96] r41861 c41861
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32984
  · exact u32985
  · exact u32986
  · exact u32987
  · exact u32988
  · exact u32989

def b41862 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 131 292 26 117 101 101 229 357), lower := (rows 11 131 292 26 16 32 64 128 256), losses := [] }

theorem u41862 : Upper (D 6) (R 6) [10,129,288,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41862 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41863 : Route 9 := (fun mask => (mask,id))

def c41863 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41863 : Upper (D 6) (R 6) [10,129,288,20] 13 := by
  apply FastRouting.sound _ _ [10,129,288,20] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r41863 c41863
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32990
  · exact u32991
  · exact u32992
  · exact u32993
  · exact u32994
  · exact u32995
  · exact u32996
  · exact u32997
  · exact u32998
  · exact u32999

def r41864 : Route 9 := (fun mask => (mask,id))

def c41864 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41864 : Upper (D 6) (R 6) [10,129,288,33] 13 := by
  apply FastRouting.sound _ _ [10,129,288,33] 13 (by decide) (choices 2) [6,66,68] r41864 c41864
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u33000
  · exact u33001
  · exact u33002

def b41865 : PairBound 9 := { available := 85, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 131 292 42 85 117 85 213 341), lower := (rows 11 131 292 42 16 32 64 128 256), losses := [] }

theorem u41865 : Upper (D 6) (R 6) [10,129,288,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41865 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41866 : PairBound 9 := { available := 87, camps := [{ cop := 2, region := 8, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 131 292 44 87 119 87 215 343), lower := (rows 11 131 292 44 16 32 64 128 256), losses := [] }

theorem u41866 : Upper (D 6) (R 6) [10,129,288,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41866 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41867 : Route 9 := (fun mask => (mask,id))

def c41867 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41867 : Upper (D 6) (R 6) [10,129,288,48] 13 := by
  apply FastRouting.sound _ _ [10,129,288,48] 13 (by decide) (choices 2) [3,5,6,65,66,68] r41867 c41867
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33003
  · exact u33004
  · exact u33005
  · exact u33006
  · exact u33007
  · exact u33008

def r41868 : Route 9 := (fun mask => (mask,id))

def c41868 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41868 : Upper (D 6) (R 6) [10,129,288,65] 13 := by
  apply FastRouting.sound _ _ [10,129,288,65] 13 (by decide) (choices 2) [6,34,36,66,68,96] r41868 c41868
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33009
  · exact u33010
  · exact u33011
  · exact u33012
  · exact u33013
  · exact u33014

def b41869 : PairBound 9 := { available := 117, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 131 292 74 117 117 117 245 373), lower := (rows 11 131 292 74 16 32 64 128 256), losses := [] }

theorem u41869 : Upper (D 6) (R 6) [10,129,288,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41869 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41870 : Route 9 := (fun mask => (mask,id))

def c41870 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41870 : Upper (D 6) (R 6) [10,129,288,68] 13 := by
  apply FastRouting.sound _ _ [10,129,288,68] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r41870 c41870
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33015
  · exact u33016
  · exact u33017
  · exact u33018
  · exact u33019
  · exact u33020
  · exact u33021
  · exact u33022
  · exact u33023
  · exact u33024

def r41871 : Route 9 := (fun mask => (mask,id))

def c41871 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41871 : Upper (D 6) (R 6) [10,129,288,80] 13 := by
  apply FastRouting.sound _ _ [10,129,288,80] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r41871 c41871
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33025
  · exact u33026
  · exact u33027
  · exact u33028
  · exact u33029
  · exact u33030
  · exact u33031
  · exact u33032
  · exact u33033
  · exact u33034

def r41872 : Route 9 := (fun mask => (mask,id))

def c41872 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41872 : Upper (D 6) (R 6) [10,129,288,96] 13 := by
  apply FastRouting.sound _ _ [10,129,288,96] 13 (by decide) (choices 2) [3,5,6,65,66,68] r41872 c41872
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33035
  · exact u33036
  · exact u33037
  · exact u33038
  · exact u33039
  · exact u33040

def b41873 : PairBound 9 := { available := 372, camps := [{ cop := 1, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 134 37 11 372 372 372 500 372), lower := (rows 11 134 37 11 16 32 64 128 256), losses := [] }

theorem u41873 : Upper (D 6) (R 6) [10,132,33,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41873 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41874 : PairBound 9 := { available := 370, camps := [{ cop := 1, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 134 37 13 370 370 370 498 370), lower := (rows 11 134 37 13 16 32 64 128 256), losses := [] }

theorem u41874 : Upper (D 6) (R 6) [10,132,33,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41874 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41875 : PairBound 9 := { available := 369, camps := [{ cop := 1, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 134 37 14 369 369 369 497 369), lower := (rows 11 134 37 14 16 32 64 128 256), losses := [] }

theorem u41875 : Upper (D 6) (R 6) [10,132,33,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41875 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41876 : Route 9 := (fun mask => (mask,id))

def c41876 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41876 : Upper (D 6) (R 6) [10,132,33,17] 13 := by
  apply FastRouting.sound _ _ [10,132,33,17] 13 (by decide) (choices 2) [6,34,36,66,68,96,258,260,288,320] r41876 c41876
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33041
  · exact u33042
  · exact u33043
  · exact u33044
  · exact u33045
  · exact u33046
  · exact u33047
  · exact u33048
  · exact u33049
  · exact u33050

def b41877 : PairBound 9 := { available := 357, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 134 37 26 373 357 357 485 357), lower := (rows 11 134 37 26 16 32 64 128 256), losses := [] }

theorem u41877 : Upper (D 6) (R 6) [10,132,33,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41877 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41878 : Route 9 := (fun mask => (mask,id))

def c41878 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 6 => 2 | 10 => 3 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41878 : Upper (D 6) (R 6) [10,132,33,20] 13 := by
  apply FastRouting.sound _ _ [10,132,33,20] 13 (by decide) (choices 2) [3,33,34,65,66,96,257,258,288,320] r41878 c41878
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33051
  · exact u33052
  · exact u33053
  · exact u33054
  · exact u33055
  · exact u33056
  · exact u33057
  · exact u33058
  · exact u33059
  · exact u33060

def b41879 : PairBound 9 := { available := 342, camps := [{ cop := 2, region := 466, targets := 1 },{ cop := 2, region := 8, targets := 2 }], pairs := [(1,0),(3,1),(4,0)], upper := (rows 11 134 37 41 342 374 342 470 342), lower := (rows 11 134 37 41 16 32 64 128 256), losses := [] }

theorem u41879 : Upper (D 6) (R 6) [10,132,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41879 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u41879
end Delivery.IrregularNine14.P06

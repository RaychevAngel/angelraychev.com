import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0096
import IrregularNine14P05C0097
import IrregularNine14P05C0098

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b8880 : PairBound 9 := { available := 397, camps := [{ cop := 3, region := 469, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 35 84 42 413 429 461 397 397), lower := (rows 7 35 84 42 16 32 64 128 256), losses := [] }

theorem u8880 : Upper (D 5) (R 5) [6,33,80,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8880
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8881 : PairBound 9 := { available := 395, camps := [{ cop := 3, region := 3, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 35 84 44 411 427 459 395 395), lower := (rows 7 35 84 44 16 32 64 128 256), losses := [] }

theorem u8881 : Upper (D 5) (R 5) [6,33,80,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8881
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8882 : Route 9 := (fun mask => (mask,id))

def c8882 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8882 : Upper (D 5) (R 5) [6,33,80,129] 13 := by
  apply FastRouting.sound _ _ [6,33,80,129] 13 (by decide) (choices 2) [6,10,12,34,36,40,258,260,264,288] r8882 c8882
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5769
  · exact u5770
  · exact u5771
  · exact u5772
  · exact u5773
  · exact u5774
  · exact u5775
  · exact u5776
  · exact u5777
  · exact u5778

def r8883 : Route 9 := (fun mask => (mask,id))

def c8883 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8883 : Upper (D 5) (R 5) [6,33,80,130] 13 := by
  apply FastRouting.sound _ _ [6,33,80,130] 13 (by decide) (choices 2) [5,9,12,33,36,40,257,260,264,288] r8883 c8883
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5779
  · exact u5780
  · exact u5781
  · exact u5782
  · exact u5783
  · exact u5784
  · exact u5785
  · exact u5786
  · exact u5787
  · exact u5788

def r8884 : Route 9 := (fun mask => (mask,id))

def c8884 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 6 => 2 | 66 => 6 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8884 : Upper (D 5) (R 5) [6,33,80,132] 13 := by
  apply FastRouting.sound _ _ [6,33,80,132] 13 (by decide) (choices 2) [3,9,10,33,34,40,257,258,264,288] r8884 c8884
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5789
  · exact u5790
  · exact u5791
  · exact u5792
  · exact u5793
  · exact u5794
  · exact u5795
  · exact u5796
  · exact u5797
  · exact u5798

def r8885 : Route 9 := (fun mask => (mask,id))

def c8885 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8885 : Upper (D 5) (R 5) [6,33,80,160] 13 := by
  apply FastRouting.sound _ _ [6,33,80,160] 13 (by decide) (choices 2) [3,5,6,9,10,12,257,258,260,264] r8885 c8885
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5799
  · exact u5800
  · exact u5801
  · exact u5802
  · exact u5803
  · exact u5804
  · exact u5805
  · exact u5806
  · exact u5807
  · exact u5808

def r8886 : Route 9 := (fun mask => (mask,id))

def c8886 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8886 : Upper (D 5) (R 5) [6,33,80,384] 13 := by
  apply FastRouting.sound _ _ [6,33,80,384] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r8886 c8886
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5809
  · exact u5810
  · exact u5811
  · exact u5812
  · exact u5813
  · exact u5814
  · exact u5815
  · exact u5816
  · exact u5817
  · exact u5818

def b8887 : PairBound 9 := { available := 398, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 35 100 25 414 430 462 398 398), lower := (rows 7 35 100 25 16 32 64 128 256), losses := [] }

theorem u8887 : Upper (D 5) (R 5) [6,33,96,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8887
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8888 : PairBound 9 := { available := 397, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 35 100 26 413 429 461 397 397), lower := (rows 7 35 100 26 16 32 64 128 256), losses := [] }

theorem u8888 : Upper (D 5) (R 5) [6,33,96,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8888
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8889 : PairBound 9 := { available := 395, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 35 100 28 411 427 459 395 395), lower := (rows 7 35 100 28 16 32 64 128 256), losses := [] }

theorem u8889 : Upper (D 5) (R 5) [6,33,96,20] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8889
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8890 : PairBound 9 := { available := 286, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 35 100 137 286 318 350 414 286), lower := (rows 7 35 100 137 16 32 64 128 256), losses := [] }

theorem u8890 : Upper (D 5) (R 5) [6,33,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8890
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8891 : PairBound 9 := { available := 285, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 35 100 138 285 317 349 413 285), lower := (rows 7 35 100 138 16 32 64 128 256), losses := [] }

theorem u8891 : Upper (D 5) (R 5) [6,33,96,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8891
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8892 : PairBound 9 := { available := 283, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 35 100 140 283 315 347 411 283), lower := (rows 7 35 100 140 16 32 64 128 256), losses := [] }

theorem u8892 : Upper (D 5) (R 5) [6,33,96,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8892
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8893 : PairBound 9 := { available := 271, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 35 100 152 287 303 335 399 271), lower := (rows 7 35 100 152 16 32 64 128 256), losses := [] }

theorem u8893 : Upper (D 5) (R 5) [6,33,96,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8893
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8894 : PairBound 9 := { available := 31, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 35 100 392 31 63 95 159 287), lower := (rows 7 35 100 392 16 32 64 128 256), losses := [] }

theorem u8894 : Upper (D 5) (R 5) [6,33,96,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8894
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8895 : PairBound 9 := { available := 313, camps := [{ cop := 0, region := 8, targets := 1 },{ cop := 0, region := 8, targets := 32 }], pairs := [(3,0),(3,5)], upper := (rows 7 35 196 14 313 313 377 441 313), lower := (rows 7 35 196 14 16 32 64 128 256), losses := [] }

theorem u8895 : Upper (D 5) (R 5) [6,33,192,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8895
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8896 : Route 9 := (fun mask => (mask,id))

def c8896 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8896 : Upper (D 5) (R 5) [6,33,192,17] 13 := by
  apply FastRouting.sound _ _ [6,33,192,17] 13 (by decide) (choices 2) [6,10,12,34,36,40,258,260,264,288] r8896 c8896
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5819
  · exact u5820
  · exact u5821
  · exact u5822
  · exact u5823
  · exact u5824
  · exact u5825
  · exact u5826
  · exact u5827
  · exact u5828

def r8897 : Route 9 := (fun mask => (mask,id))

def c8897 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8897 : Upper (D 5) (R 5) [6,33,192,18] 13 := by
  apply FastRouting.sound _ _ [6,33,192,18] 13 (by decide) (choices 2) [5,9,12,33,36,40,257,260,264,288] r8897 c8897
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5829
  · exact u5830
  · exact u5831
  · exact u5832
  · exact u5833
  · exact u5834
  · exact u5835
  · exact u5836
  · exact u5837
  · exact u5838

def r8898 : Route 9 := (fun mask => (mask,id))

def c8898 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 6 => 2 | 66 => 6 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8898 : Upper (D 5) (R 5) [6,33,192,20] 13 := by
  apply FastRouting.sound _ _ [6,33,192,20] 13 (by decide) (choices 2) [3,9,10,33,34,40,257,258,264,288] r8898 c8898
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5839
  · exact u5840
  · exact u5841
  · exact u5842
  · exact u5843
  · exact u5844
  · exact u5845
  · exact u5846
  · exact u5847
  · exact u5848

def b8899 : PairBound 9 := { available := 286, camps := [{ cop := 1, region := 8, targets := 2 },{ cop := 1, region := 8, targets := 4 }], pairs := [(3,1),(3,2)], upper := (rows 7 35 196 41 286 318 350 414 286), lower := (rows 7 35 196 41 16 32 64 128 256), losses := [] }

theorem u8899 : Upper (D 5) (R 5) [6,33,192,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8899
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8900 : PairBound 9 := { available := 285, camps := [{ cop := 3, region := 469, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 35 196 42 285 317 349 413 285), lower := (rows 7 35 196 42 16 32 64 128 256), losses := [] }

theorem u8900 : Upper (D 5) (R 5) [6,33,192,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8900
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8901 : PairBound 9 := { available := 283, camps := [{ cop := 3, region := 3, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 35 196 44 283 315 347 411 283), lower := (rows 7 35 196 44 16 32 64 128 256), losses := [] }

theorem u8901 : Upper (D 5) (R 5) [6,33,192,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8901
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8902 : Route 9 := (fun mask => (mask,id))

def c8902 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8902 : Upper (D 5) (R 5) [6,33,192,48] 13 := by
  apply FastRouting.sound _ _ [6,33,192,48] 13 (by decide) (choices 2) [3,5,6,9,10,12,257,258,260,264] r8902 c8902
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5849
  · exact u5850
  · exact u5851
  · exact u5852
  · exact u5853
  · exact u5854
  · exact u5855
  · exact u5856
  · exact u5857
  · exact u5858

def r8903 : Route 9 := (fun mask => (mask,id))

def c8903 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8903 : Upper (D 5) (R 5) [6,33,192,257] 13 := by
  apply FastRouting.sound _ _ [6,33,192,257] 13 (by decide) (choices 2) [6,10,12,34,36,40] r8903 c8903
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5859
  · exact u5860
  · exact u5861
  · exact u5862
  · exact u5863
  · exact u5864

def r8904 : Route 9 := (fun mask => (mask,id))

def c8904 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8904 : Upper (D 5) (R 5) [6,33,192,258] 13 := by
  apply FastRouting.sound _ _ [6,33,192,258] 13 (by decide) (choices 2) [5,9,12,33,36,40] r8904 c8904
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5865
  · exact u5866
  · exact u5867
  · exact u5868
  · exact u5869
  · exact u5870

def r8905 : Route 9 := (fun mask => (mask,id))

def c8905 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8905 : Upper (D 5) (R 5) [6,33,192,260] 13 := by
  apply FastRouting.sound _ _ [6,33,192,260] 13 (by decide) (choices 2) [3,9,10,33,34,40] r8905 c8905
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5871
  · exact u5872
  · exact u5873
  · exact u5874
  · exact u5875
  · exact u5876

def r8906 : Route 9 := (fun mask => (mask,id))

def c8906 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8906 : Upper (D 5) (R 5) [6,33,192,272] 13 := by
  apply FastRouting.sound _ _ [6,33,192,272] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r8906 c8906
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5877
  · exact u5878
  · exact u5879
  · exact u5880
  · exact u5881
  · exact u5882
  · exact u5883
  · exact u5884
  · exact u5885
  · exact u5886

def r8907 : Route 9 := (fun mask => (mask,id))

def c8907 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8907 : Upper (D 5) (R 5) [6,33,192,288] 13 := by
  apply FastRouting.sound _ _ [6,33,192,288] 13 (by decide) (choices 2) [3,5,6,9,10,12] r8907 c8907
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5887
  · exact u5888
  · exact u5889
  · exact u5890
  · exact u5891
  · exact u5892

def b8908 : PairBound 9 := { available := 459, camps := [{ cop := 1, region := 473, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 7 38 44 25 475 491 459 459 459), lower := (rows 7 38 44 25 16 32 64 128 256), losses := [] }

theorem u8908 : Upper (D 5) (R 5) [6,36,40,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8908
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8909 : PairBound 9 := { available := 411, camps := [{ cop := 1, region := 473, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 7 38 44 73 411 443 475 411 411), lower := (rows 7 38 44 73 16 32 64 128 256), losses := [] }

theorem u8909 : Upper (D 5) (R 5) [6,36,40,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8909
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8910 : PairBound 9 := { available := 395, camps := [{ cop := 1, region := 473, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 7 38 44 88 411 427 459 395 395), lower := (rows 7 38 44 88 16 32 64 128 256), losses := [] }

theorem u8910 : Upper (D 5) (R 5) [6,36,40,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8910
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8911 : PairBound 9 := { available := 283, camps := [{ cop := 1, region := 473, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 7 38 44 200 283 315 347 411 283), lower := (rows 7 38 44 200 16 32 64 128 256), losses := [] }

theorem u8911 : Upper (D 5) (R 5) [6,36,40,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8911
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8912 : PairBound 9 := { available := 395, camps := [{ cop := 1, region := 457, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 7 38 52 73 411 427 459 395 395), lower := (rows 7 38 52 73 16 32 64 128 256), losses := [] }

theorem u8912 : Upper (D 5) (R 5) [6,36,48,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8912
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8913 : PairBound 9 := { available := 267, camps := [{ cop := 1, region := 457, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 7 38 52 200 283 299 331 395 267), lower := (rows 7 38 52 200 16 32 64 128 256), losses := [] }

theorem u8913 : Upper (D 5) (R 5) [6,36,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8913
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8914 : PairBound 9 := { available := 426, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 38 69 25 442 426 490 426 426), lower := (rows 7 38 69 25 16 32 64 128 256), losses := [] }

theorem u8914 : Upper (D 5) (R 5) [6,36,65,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8914
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8915 : PairBound 9 := { available := 425, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 38 69 26 441 425 489 425 425), lower := (rows 7 38 69 26 16 32 64 128 256), losses := [] }

theorem u8915 : Upper (D 5) (R 5) [6,36,65,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8915
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8916 : PairBound 9 := { available := 410, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 38 69 41 410 442 474 410 410), lower := (rows 7 38 69 41 16 32 64 128 256), losses := [] }

theorem u8916 : Upper (D 5) (R 5) [6,36,65,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8916
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8917 : PairBound 9 := { available := 395, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 38 69 56 411 427 459 395 395), lower := (rows 7 38 69 56 16 32 64 128 256), losses := [] }

theorem u8917 : Upper (D 5) (R 5) [6,36,65,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8917
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8918 : PairBound 9 := { available := 314, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 38 69 137 314 314 378 442 314), lower := (rows 7 38 69 137 16 32 64 128 256), losses := [] }

theorem u8918 : Upper (D 5) (R 5) [6,36,65,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8918
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8919 : PairBound 9 := { available := 313, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 38 69 138 313 313 377 441 313), lower := (rows 7 38 69 138 16 32 64 128 256), losses := [] }

theorem u8919 : Upper (D 5) (R 5) [6,36,65,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8919
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8920 : PairBound 9 := { available := 299, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 38 69 152 315 299 363 427 299), lower := (rows 7 38 69 152 16 32 64 128 256), losses := [] }

theorem u8920 : Upper (D 5) (R 5) [6,36,65,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8920
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8921 : PairBound 9 := { available := 283, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 38 69 168 283 315 347 411 283), lower := (rows 7 38 69 168 16 32 64 128 256), losses := [] }

theorem u8921 : Upper (D 5) (R 5) [6,36,65,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8921
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8922 : PairBound 9 := { available := 59, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 38 69 392 59 59 123 187 315), lower := (rows 7 38 69 392 16 32 64 128 256), losses := [] }

theorem u8922 : Upper (D 5) (R 5) [6,36,65,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8922
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8923 : PairBound 9 := { available := 425, camps := [{ cop := 0, region := 440, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 38 70 25 441 425 489 425 425), lower := (rows 7 38 70 25 16 32 64 128 256), losses := [] }

theorem u8923 : Upper (D 5) (R 5) [6,36,66,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8923
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8924 : PairBound 9 := { available := 409, camps := [{ cop := 0, region := 440, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 38 70 41 409 441 473 409 409), lower := (rows 7 38 70 41 16 32 64 128 256), losses := [] }

theorem u8924 : Upper (D 5) (R 5) [6,36,66,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8924
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8925 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 440, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 38 70 56 409 425 457 393 393), lower := (rows 7 38 70 56 16 32 64 128 256), losses := [] }

theorem u8925 : Upper (D 5) (R 5) [6,36,66,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8925
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8926 : PairBound 9 := { available := 313, camps := [{ cop := 0, region := 440, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 38 70 137 313 313 377 441 313), lower := (rows 7 38 70 137 16 32 64 128 256), losses := [] }

theorem u8926 : Upper (D 5) (R 5) [6,36,66,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8926
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8927 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 440, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 38 70 152 313 297 361 425 297), lower := (rows 7 38 70 152 16 32 64 128 256), losses := [] }

theorem u8927 : Upper (D 5) (R 5) [6,36,66,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8927
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8928 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 440, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 38 70 168 281 313 345 409 281), lower := (rows 7 38 70 168 16 32 64 128 256), losses := [] }

theorem u8928 : Upper (D 5) (R 5) [6,36,66,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8928
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8929 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 440, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 38 70 392 57 57 121 185 313), lower := (rows 7 38 70 392 16 32 64 128 256), losses := [] }

theorem u8929 : Upper (D 5) (R 5) [6,36,66,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8929
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8930 : PairBound 9 := { available := 427, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 38 76 25 443 427 491 427 427), lower := (rows 7 38 76 25 16 32 64 128 256), losses := [] }

theorem u8930 : Upper (D 5) (R 5) [6,36,72,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8930
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8931 : PairBound 9 := { available := 425, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 38 76 26 441 425 489 425 425), lower := (rows 7 38 76 26 16 32 64 128 256), losses := [] }

theorem u8931 : Upper (D 5) (R 5) [6,36,72,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8931
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8932 : PairBound 9 := { available := 411, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 38 76 41 411 443 475 411 411), lower := (rows 7 38 76 41 16 32 64 128 256), losses := [] }

theorem u8932 : Upper (D 5) (R 5) [6,36,72,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8932
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8933 : PairBound 9 := { available := 395, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 38 76 56 411 427 459 395 395), lower := (rows 7 38 76 56 16 32 64 128 256), losses := [] }

theorem u8933 : Upper (D 5) (R 5) [6,36,72,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8933
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8934 : PairBound 9 := { available := 315, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 38 76 137 315 315 379 443 315), lower := (rows 7 38 76 137 16 32 64 128 256), losses := [] }

theorem u8934 : Upper (D 5) (R 5) [6,36,72,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8934
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8935 : PairBound 9 := { available := 313, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 38 76 138 313 313 377 441 313), lower := (rows 7 38 76 138 16 32 64 128 256), losses := [] }

theorem u8935 : Upper (D 5) (R 5) [6,36,72,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8935
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8936 : PairBound 9 := { available := 299, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 38 76 152 315 299 363 427 299), lower := (rows 7 38 76 152 16 32 64 128 256), losses := [] }

theorem u8936 : Upper (D 5) (R 5) [6,36,72,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8936
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8937 : PairBound 9 := { available := 283, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 38 76 168 283 315 347 411 283), lower := (rows 7 38 76 168 16 32 64 128 256), losses := [] }

theorem u8937 : Upper (D 5) (R 5) [6,36,72,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8937
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8938 : PairBound 9 := { available := 59, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 38 76 392 59 59 123 187 315), lower := (rows 7 38 76 392 16 32 64 128 256), losses := [] }

theorem u8938 : Upper (D 5) (R 5) [6,36,72,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8938
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8939 : PairBound 9 := { available := 395, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 38 84 41 411 427 459 395 395), lower := (rows 7 38 84 41 16 32 64 128 256), losses := [] }

theorem u8939 : Upper (D 5) (R 5) [6,36,80,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8939
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u8939
end Delivery.IrregularNine14.P05

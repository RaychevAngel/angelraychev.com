import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0113
import IrregularNine14P05C0114
import IrregularNine14P05C0115
import IrregularNine14P05C0116
import IrregularNine14P05C0117
import IrregularNine14P05C0118

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r9180 : Route 9 := (fun mask => (mask,id))

def c9180 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9180 : Upper (D 5) (R 5) [6,72,160,288] 13 := by
  apply FastRouting.sound _ _ [6,72,160,288] 13 (by decide) (choices 2) [3,5,6,9,10,12] r9180 c9180
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6807
  · exact u6808
  · exact u6809
  · exact u6810
  · exact u6811
  · exact u6812

def r9181 : Route 9 := (fun mask => (mask,id))

def c9181 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9181 : Upper (D 5) (R 5) [6,72,384,17] 13 := by
  apply FastRouting.sound _ _ [6,72,384,17] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r9181 c9181
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6813
  · exact u6814
  · exact u6815
  · exact u6816
  · exact u6817
  · exact u6818
  · exact u6819
  · exact u6820
  · exact u6821
  · exact u6822

def r9182 : Route 9 := (fun mask => (mask,id))

def c9182 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9182 : Upper (D 5) (R 5) [6,72,384,18] 13 := by
  apply FastRouting.sound _ _ [6,72,384,18] 13 (by decide) (choices 2) [5,9,12,33,36,40] r9182 c9182
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6823
  · exact u6824
  · exact u6825
  · exact u6826
  · exact u6827
  · exact u6828

def r9183 : Route 9 := (fun mask => (mask,id))

def c9183 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9183 : Upper (D 5) (R 5) [6,72,384,20] 13 := by
  apply FastRouting.sound _ _ [6,72,384,20] 13 (by decide) (choices 2) [3,9,10,33,34,40] r9183 c9183
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6829
  · exact u6830
  · exact u6831
  · exact u6832
  · exact u6833
  · exact u6834

def r9184 : Route 9 := (fun mask => (mask,id))

def c9184 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9184 : Upper (D 5) (R 5) [6,72,384,33] 13 := by
  apply FastRouting.sound _ _ [6,72,384,33] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r9184 c9184
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6835
  · exact u6836
  · exact u6837
  · exact u6838
  · exact u6839
  · exact u6840
  · exact u6841
  · exact u6842
  · exact u6843
  · exact u6844

def r9185 : Route 9 := (fun mask => (mask,id))

def c9185 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9185 : Upper (D 5) (R 5) [6,72,384,34] 13 := by
  apply FastRouting.sound _ _ [6,72,384,34] 13 (by decide) (choices 2) [5,9,12,33,36,40] r9185 c9185
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6845
  · exact u6846
  · exact u6847
  · exact u6848
  · exact u6849
  · exact u6850

def r9186 : Route 9 := (fun mask => (mask,id))

def c9186 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9186 : Upper (D 5) (R 5) [6,72,384,36] 13 := by
  apply FastRouting.sound _ _ [6,72,384,36] 13 (by decide) (choices 2) [3,9,10,33,34,40] r9186 c9186
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6851
  · exact u6852
  · exact u6853
  · exact u6854
  · exact u6855
  · exact u6856

def r9187 : Route 9 := (fun mask => (mask,id))

def c9187 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9187 : Upper (D 5) (R 5) [6,72,384,48] 13 := by
  apply FastRouting.sound _ _ [6,72,384,48] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r9187 c9187
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6857
  · exact u6858
  · exact u6859
  · exact u6860
  · exact u6861
  · exact u6862
  · exact u6863
  · exact u6864
  · exact u6865
  · exact u6866

def b9188 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 8, targets := 1 },{ cop := 0, region := 8, targets := 32 }], pairs := [(3,0),(3,5)], upper := (rows 7 82 164 14 313 297 361 425 297), lower := (rows 7 82 164 14 16 32 64 128 256), losses := [] }

theorem u9188 : Upper (D 5) (R 5) [6,80,160,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9188
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r9189 : Route 9 := (fun mask => (mask,id))

def c9189 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9189 : Upper (D 5) (R 5) [6,80,160,33] 13 := by
  apply FastRouting.sound _ _ [6,80,160,33] 13 (by decide) (choices 2) [3,5,6,9,10,12,257,258,260,264] r9189 c9189
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6867
  · exact u6868
  · exact u6869
  · exact u6870
  · exact u6871
  · exact u6872
  · exact u6873
  · exact u6874
  · exact u6875
  · exact u6876

def r9190 : Route 9 := (fun mask => (mask,id))

def c9190 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9190 : Upper (D 5) (R 5) [6,80,160,34] 13 := by
  apply FastRouting.sound _ _ [6,80,160,34] 13 (by decide) (choices 2) [5,9,12,257,260,264] r9190 c9190
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6877
  · exact u6878
  · exact u6879
  · exact u6880
  · exact u6881
  · exact u6882

def b9191 : PairBound 9 := { available := 267, camps := [{ cop := 3, region := 339, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 82 164 44 283 299 331 395 267), lower := (rows 7 82 164 44 16 32 64 128 256), losses := [] }

theorem u9191 : Upper (D 5) (R 5) [6,80,160,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9191
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r9192 : Route 9 := (fun mask => (mask,id))

def c9192 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9192 : Upper (D 5) (R 5) [6,80,160,257] 13 := by
  apply FastRouting.sound _ _ [6,80,160,257] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r9192 c9192
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6883
  · exact u6884
  · exact u6885
  · exact u6886
  · exact u6887
  · exact u6888
  · exact u6889
  · exact u6890
  · exact u6891
  · exact u6892

def r9193 : Route 9 := (fun mask => (mask,id))

def c9193 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9193 : Upper (D 5) (R 5) [6,80,160,258] 13 := by
  apply FastRouting.sound _ _ [6,80,160,258] 13 (by decide) (choices 2) [5,9,12,33,36,40] r9193 c9193
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6893
  · exact u6894
  · exact u6895
  · exact u6896
  · exact u6897
  · exact u6898

def r9194 : Route 9 := (fun mask => (mask,id))

def c9194 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9194 : Upper (D 5) (R 5) [6,80,160,260] 13 := by
  apply FastRouting.sound _ _ [6,80,160,260] 13 (by decide) (choices 2) [3,9,10,33,34,40] r9194 c9194
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6899
  · exact u6900
  · exact u6901
  · exact u6902
  · exact u6903
  · exact u6904

def r9195 : Route 9 := (fun mask => (mask,id))

def c9195 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9195 : Upper (D 5) (R 5) [6,80,160,288] 13 := by
  apply FastRouting.sound _ _ [6,80,160,288] 13 (by decide) (choices 2) [3,5,6,9,10,12] r9195 c9195
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6905
  · exact u6906
  · exact u6907
  · exact u6908
  · exact u6909
  · exact u6910

def b9196 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 8, targets := 1 },{ cop := 0, region := 8, targets := 32 }], pairs := [(3,0),(3,5)], upper := (rows 7 82 388 14 57 41 105 169 297), lower := (rows 7 82 388 14 16 32 64 128 256), losses := [] }

theorem u9196 : Upper (D 5) (R 5) [6,80,384,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9196
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r9197 : Route 9 := (fun mask => (mask,id))

def c9197 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9197 : Upper (D 5) (R 5) [6,80,384,33] 13 := by
  apply FastRouting.sound _ _ [6,80,384,33] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r9197 c9197
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6911
  · exact u6912
  · exact u6913
  · exact u6914
  · exact u6915
  · exact u6916
  · exact u6917
  · exact u6918
  · exact u6919
  · exact u6920

def r9198 : Route 9 := (fun mask => (mask,id))

def c9198 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9198 : Upper (D 5) (R 5) [6,80,384,34] 13 := by
  apply FastRouting.sound _ _ [6,80,384,34] 13 (by decide) (choices 2) [5,9,12,33,36,40] r9198 c9198
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6921
  · exact u6922
  · exact u6923
  · exact u6924
  · exact u6925
  · exact u6926

def r9199 : Route 9 := (fun mask => (mask,id))

def c9199 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9199 : Upper (D 5) (R 5) [6,80,384,36] 13 := by
  apply FastRouting.sound _ _ [6,80,384,36] 13 (by decide) (choices 2) [3,9,10,33,34,40] r9199 c9199
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6927
  · exact u6928
  · exact u6929
  · exact u6930
  · exact u6931
  · exact u6932

def b9200 : PairBound 9 := { available := 271, camps := [{ cop := 0, region := 280, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 98 164 25 287 303 335 399 271), lower := (rows 7 98 164 25 16 32 64 128 256), losses := [] }

theorem u9200 : Upper (D 5) (R 5) [6,96,160,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9200
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9201 : PairBound 9 := { available := 269, camps := [{ cop := 0, region := 280, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 98 164 26 285 301 333 397 269), lower := (rows 7 98 164 26 16 32 64 128 256), losses := [] }

theorem u9201 : Upper (D 5) (R 5) [6,96,160,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9201
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9202 : PairBound 9 := { available := 31, camps := [{ cop := 0, region := 280, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 98 164 265 31 63 95 159 287), lower := (rows 7 98 164 265 16 32 64 128 256), losses := [] }

theorem u9202 : Upper (D 5) (R 5) [6,96,160,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9202
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9203 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 280, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 98 164 266 29 61 93 157 285), lower := (rows 7 98 164 266 16 32 64 128 256), losses := [] }

theorem u9203 : Upper (D 5) (R 5) [6,96,160,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9203
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9204 : PairBound 9 := { available := 15, camps := [{ cop := 0, region := 280, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 98 164 280 31 47 79 143 271), lower := (rows 7 98 164 280 16 32 64 128 256), losses := [] }

theorem u9204 : Upper (D 5) (R 5) [6,96,160,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9204
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9205 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 8, targets := 1 },{ cop := 0, region := 8, targets := 32 }], pairs := [(3,0),(3,5)], upper := (rows 7 98 388 14 57 57 121 185 313), lower := (rows 7 98 388 14 16 32 64 128 256), losses := [] }

theorem u9205 : Upper (D 5) (R 5) [6,96,384,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9205
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r9206 : Route 9 := (fun mask => (mask,id))

def c9206 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9206 : Upper (D 5) (R 5) [6,96,384,17] 13 := by
  apply FastRouting.sound _ _ [6,96,384,17] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r9206 c9206
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6933
  · exact u6934
  · exact u6935
  · exact u6936
  · exact u6937
  · exact u6938
  · exact u6939
  · exact u6940
  · exact u6941
  · exact u6942

def r9207 : Route 9 := (fun mask => (mask,id))

def c9207 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9207 : Upper (D 5) (R 5) [6,96,384,18] 13 := by
  apply FastRouting.sound _ _ [6,96,384,18] 13 (by decide) (choices 2) [5,9,12,33,36,40] r9207 c9207
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6943
  · exact u6944
  · exact u6945
  · exact u6946
  · exact u6947
  · exact u6948

def r9208 : Route 9 := (fun mask => (mask,id))

def c9208 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9208 : Upper (D 5) (R 5) [6,96,384,20] 13 := by
  apply FastRouting.sound _ _ [6,96,384,20] 13 (by decide) (choices 2) [3,9,10,33,34,40] r9208 c9208
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6949
  · exact u6950
  · exact u6951
  · exact u6952
  · exact u6953
  · exact u6954

def r9209 : Route 9 := (fun mask => (mask,id))

def c9209 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9209 : Upper (D 5) (R 5) [6,96,384,33] 13 := by
  apply FastRouting.sound _ _ [6,96,384,33] 13 (by decide) (choices 2) [3,5,6,9,10,12] r9209 c9209
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6955
  · exact u6956
  · exact u6957
  · exact u6958
  · exact u6959
  · exact u6960

def b9210 : PairBound 9 := { available := 29, camps := [{ cop := 3, region := 405, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 98 388 42 29 61 93 157 285), lower := (rows 7 98 388 42 16 32 64 128 256), losses := [] }

theorem u9210 : Upper (D 5) (R 5) [6,96,384,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9210
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r9211 : Route 9 := (fun mask => (mask,id))

def c9211 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9211 : Upper (D 5) (R 5) [6,96,384,36] 13 := by
  apply FastRouting.sound _ _ [6,96,384,36] 13 (by decide) (choices 2) [3,9,10] r9211 c9211
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6961
  · exact u6962
  · exact u6963

def r9212 : Route 9 := (fun mask => (mask,id))

def c9212 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9212 : Upper (D 5) (R 5) [6,96,384,48] 13 := by
  apply FastRouting.sound _ _ [6,96,384,48] 13 (by decide) (choices 2) [3,5,6,9,10,12] r9212 c9212
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6964
  · exact u6965
  · exact u6966
  · exact u6967
  · exact u6968
  · exact u6969

def b9213 : PairBound 9 := { available := 396, camps := [{ cop := 1, region := 4, targets := 2 },{ cop := 1, region := 4, targets := 8 }], pairs := [(2,1),(2,3)], upper := (rows 19 35 37 74 412 428 460 396 396), lower := (rows 19 35 37 74 16 32 64 128 256), losses := [] }

theorem u9213 : Upper (D 5) (R 5) [18,33,33,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9213
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9214 : PairBound 9 := { available := 398, camps := [{ cop := 1, region := 4, targets := 2 },{ cop := 1, region := 4, targets := 8 }], pairs := [(2,1),(2,3)], upper := (rows 19 35 37 76 414 430 462 398 398), lower := (rows 19 35 37 76 16 32 64 128 256), losses := [] }

theorem u9214 : Upper (D 5) (R 5) [18,33,33,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9214
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9215 : PairBound 9 := { available := 270, camps := [{ cop := 1, region := 4, targets := 2 },{ cop := 1, region := 4, targets := 8 }], pairs := [(2,1),(2,3)], upper := (rows 19 35 37 200 286 302 334 398 270), lower := (rows 19 35 37 200 16 32 64 128 256), losses := [] }

theorem u9215 : Upper (D 5) (R 5) [18,33,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9215
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9216 : PairBound 9 := { available := 396, camps := [{ cop := 2, region := 473, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 19 35 38 73 412 428 460 396 396), lower := (rows 19 35 38 73 16 32 64 128 256), losses := [] }

theorem u9216 : Upper (D 5) (R 5) [18,33,34,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9216
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9217 : PairBound 9 := { available := 397, camps := [{ cop := 2, region := 473, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 19 35 38 76 413 429 461 397 397), lower := (rows 19 35 38 76 16 32 64 128 256), losses := [] }

theorem u9217 : Upper (D 5) (R 5) [18,33,34,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9217
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9218 : PairBound 9 := { available := 269, camps := [{ cop := 2, region := 473, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 19 35 38 200 285 301 333 397 269), lower := (rows 19 35 38 200 16 32 64 128 256), losses := [] }

theorem u9218 : Upper (D 5) (R 5) [18,33,34,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9218
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r9219 : Route 9 := (fun mask => match mask with | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9219 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 66 => 6 | 36 => 5 | 68 => 6 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9219 : Upper (D 5) (R 5) [18,33,40,65] 13 := by
  apply FastRouting.sound _ _ [18,33,40,65] 13 (by decide) (choices 2) [6,10,12,130,132,136,384] r9219 c9219
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6970
  · exact u6971
  · exact u6972
  · exact u6973
  · exact u6974
  · exact u6975
  · exact u6976

def r9220 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9220 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9220 : Upper (D 5) (R 5) [18,33,40,66] 13 := by
  apply FastRouting.sound _ _ [18,33,40,66] 13 (by decide) (choices 2) [5,9,12,129,132,136,384] r9220 c9220
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6977
  · exact u6978
  · exact u6979
  · exact u6980
  · exact u6981
  · exact u6982
  · exact u6983

def r9221 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9221 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 34 => 5 | 66 => 6 | 36 => 5 | 68 => 6 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9221 : Upper (D 5) (R 5) [18,33,40,68] 13 := by
  apply FastRouting.sound _ _ [18,33,40,68] 13 (by decide) (choices 2) [3,5,6,9,10,12,129,130,132,136,384] r9221 c9221
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6984
  · exact u6985
  · exact u6986
  · exact u6987
  · exact u6988
  · exact u6989
  · exact u6990
  · exact u6991
  · exact u6992
  · exact u6993
  · exact u6994

def r9222 : Route 9 := (fun mask => (mask,id))

def c9222 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9222 : Upper (D 5) (R 5) [18,33,40,192] 13 := by
  apply FastRouting.sound _ _ [18,33,40,192] 13 (by decide) (choices 2) [3,5,6,9,10,12,257,258,260,264] r9222 c9222
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6995
  · exact u6996
  · exact u6997
  · exact u6998
  · exact u6999
  · exact u7000
  · exact u7001
  · exact u7002
  · exact u7003
  · exact u7004

def r9223 : Route 9 := (fun mask => (mask,id))

def c9223 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9223 : Upper (D 5) (R 5) [18,33,65,130] 13 := by
  apply FastRouting.sound _ _ [18,33,65,130] 13 (by decide) (choices 2) [12,36,40,260,264,288] r9223 c9223
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7005
  · exact u7006
  · exact u7007
  · exact u7008
  · exact u7009
  · exact u7010

def r9224 : Route 9 := (fun mask => (mask,id))

def c9224 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9224 : Upper (D 5) (R 5) [18,33,65,132] 13 := by
  apply FastRouting.sound _ _ [18,33,65,132] 13 (by decide) (choices 2) [6,10,12,34,36,40,258,260,264,288] r9224 c9224
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7011
  · exact u7012
  · exact u7013
  · exact u7014
  · exact u7015
  · exact u7016
  · exact u7017
  · exact u7018
  · exact u7019
  · exact u7020

def r9225 : Route 9 := (fun mask => (mask,id))

def c9225 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9225 : Upper (D 5) (R 5) [18,33,65,160] 13 := by
  apply FastRouting.sound _ _ [18,33,65,160] 13 (by decide) (choices 2) [6,10,12,258,260,264] r9225 c9225
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7021
  · exact u7022
  · exact u7023
  · exact u7024
  · exact u7025
  · exact u7026

def r9226 : Route 9 := (fun mask => (mask,id))

def c9226 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9226 : Upper (D 5) (R 5) [18,33,65,384] 13 := by
  apply FastRouting.sound _ _ [18,33,65,384] 13 (by decide) (choices 2) [6,10,12,34,36,40] r9226 c9226
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7027
  · exact u7028
  · exact u7029
  · exact u7030
  · exact u7031
  · exact u7032

def r9227 : Route 9 := (fun mask => (mask,id))

def c9227 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9227 : Upper (D 5) (R 5) [18,33,66,132] 13 := by
  apply FastRouting.sound _ _ [18,33,66,132] 13 (by decide) (choices 2) [5,9,12,33,36,40,257,260,264,288] r9227 c9227
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7033
  · exact u7034
  · exact u7035
  · exact u7036
  · exact u7037
  · exact u7038
  · exact u7039
  · exact u7040
  · exact u7041
  · exact u7042

def r9228 : Route 9 := (fun mask => (mask,id))

def c9228 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9228 : Upper (D 5) (R 5) [18,33,66,160] 13 := by
  apply FastRouting.sound _ _ [18,33,66,160] 13 (by decide) (choices 2) [5,9,12,257,260,264] r9228 c9228
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7043
  · exact u7044
  · exact u7045
  · exact u7046
  · exact u7047
  · exact u7048

def r9229 : Route 9 := (fun mask => (mask,id))

def c9229 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9229 : Upper (D 5) (R 5) [18,33,66,384] 13 := by
  apply FastRouting.sound _ _ [18,33,66,384] 13 (by decide) (choices 2) [5,9,12,33,36,40] r9229 c9229
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7049
  · exact u7050
  · exact u7051
  · exact u7052
  · exact u7053
  · exact u7054

theorem m9230_9 : Upper (D 5) (R 5) [18,33,72,132,9] 13 :=
  permutation_upper _ _ _ [18,33,72,132,5] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7056

theorem m9230_10 : Upper (D 5) (R 5) [18,33,72,132,10] 13 :=
  permutation_upper _ _ _ [18,33,72,132,6] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7057

theorem m9230_40 : Upper (D 5) (R 5) [18,33,72,132,40] 13 :=
  permutation_upper _ _ _ [18,33,72,132,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7061

theorem m9230_264 : Upper (D 5) (R 5) [18,33,72,132,264] 13 :=
  permutation_upper _ _ _ [18,33,72,132,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7064

def r9230 : Route 9 := (fun mask => (mask,id))

def c9230 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9230 : Upper (D 5) (R 5) [18,33,72,132] 13 := by
  apply FastRouting.sound _ _ [18,33,72,132] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40,257,258,260,264,288] r9230 c9230
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7055
  · exact u7056
  · exact u7057
  · exact m9230_9
  · exact m9230_10
  · exact u7058
  · exact u7059
  · exact u7060
  · exact u7061
  · exact m9230_40
  · exact u7062
  · exact u7063
  · exact u7064
  · exact m9230_264
  · exact u7065

def r9231 : Route 9 := (fun mask => (mask,id))

def c9231 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9231 : Upper (D 5) (R 5) [18,33,72,160] 13 := by
  apply FastRouting.sound _ _ [18,33,72,160] 13 (by decide) (choices 2) [3,5,6,9,10,12,257,258,260,264] r9231 c9231
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7066
  · exact u7067
  · exact u7068
  · exact u7069
  · exact u7070
  · exact u7071
  · exact u7072
  · exact u7073
  · exact u7074
  · exact u7075

def r9232 : Route 9 := (fun mask => (mask,id))

def c9232 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9232 : Upper (D 5) (R 5) [18,33,72,384] 13 := by
  apply FastRouting.sound _ _ [18,33,72,384] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r9232 c9232
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7076
  · exact u7077
  · exact u7078
  · exact u7079
  · exact u7080
  · exact u7081
  · exact u7082
  · exact u7083
  · exact u7084
  · exact u7085

def r9233 : Route 9 := (fun mask => (mask,id))

def c9233 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9233 : Upper (D 5) (R 5) [18,33,96,384] 13 := by
  apply FastRouting.sound _ _ [18,33,96,384] 13 (by decide) (choices 2) [3,5,6,9,10,12] r9233 c9233
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7086
  · exact u7087
  · exact u7088
  · exact u7089
  · exact u7090
  · exact u7091

def b9234 : PairBound 9 := { available := 398, camps := [{ cop := 1, region := 473, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 19 38 37 73 414 430 462 398 398), lower := (rows 19 38 37 73 16 32 64 128 256), losses := [] }

theorem u9234 : Upper (D 5) (R 5) [18,36,33,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9234
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9235 : PairBound 9 := { available := 395, camps := [{ cop := 1, region := 473, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 19 38 37 76 411 427 459 395 395), lower := (rows 19 38 37 76 16 32 64 128 256), losses := [] }

theorem u9235 : Upper (D 5) (R 5) [18,36,33,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9235
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9236 : PairBound 9 := { available := 271, camps := [{ cop := 1, region := 473, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 19 38 37 200 287 303 335 399 271), lower := (rows 19 38 37 200 16 32 64 128 256), losses := [] }

theorem u9236 : Upper (D 5) (R 5) [18,36,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9236
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9237 : PairBound 9 := { available := 397, camps := [{ cop := 5, region := 6, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 38 38 73 413 429 461 397 397), lower := (rows 19 38 38 73 16 32 64 128 256), losses := [] }

theorem u9237 : Upper (D 5) (R 5) [18,36,34,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9237
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9238 : PairBound 9 := { available := 269, camps := [{ cop := 5, region := 6, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 38 38 200 285 301 333 397 269), lower := (rows 19 38 38 200 16 32 64 128 256), losses := [] }

theorem u9238 : Upper (D 5) (R 5) [18,36,34,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9238
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9239 : PairBound 9 := { available := 399, camps := [{ cop := 1, region := 473, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 19 38 44 73 415 431 463 399 399), lower := (rows 19 38 44 73 16 32 64 128 256), losses := [] }

theorem u9239 : Upper (D 5) (R 5) [18,36,40,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9239
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u9239
end Delivery.IrregularNine14.P05

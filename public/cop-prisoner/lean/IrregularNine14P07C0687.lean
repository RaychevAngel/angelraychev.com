import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0514
import IrregularNine14P07C0515
import IrregularNine14P07C0516
import IrregularNine14P07C0517
import IrregularNine14P07C0518

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r41220 : Route 9 := (fun mask => (mask,id))

def c41220 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41220 : Upper (D 7) (R 7) [6,40,65,257] 13 := by
  apply FastRouting.sound _ _ [6,40,65,257] 13 (by decide) (choices 2) [34,66,96,130,160,192] r41220 c41220
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30852
  · exact u30853
  · exact u30854
  · exact u30855
  · exact u30856
  · exact u30857

def r41221 : Route 9 := (fun mask => (mask,id))

def c41221 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41221 : Upper (D 7) (R 7) [6,40,65,258] 13 := by
  apply FastRouting.sound _ _ [6,40,65,258] 13 (by decide) (choices 2) [33,65,96,129,160,192] r41221 c41221
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30858
  · exact u30859
  · exact u30860
  · exact u30861
  · exact u30862
  · exact u30863

def r41222 : Route 9 := (fun mask => (mask,id))

def c41222 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41222 : Upper (D 7) (R 7) [6,40,65,272] 13 := by
  apply FastRouting.sound _ _ [6,40,65,272] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r41222 c41222
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30864
  · exact u30865
  · exact u30866
  · exact u30867
  · exact u30868
  · exact u30869
  · exact u30870
  · exact u30871
  · exact u30872
  · exact u30873

def b41223 : PairBound 9 := { available := 211, camps := [{ cop := 1, region := 213, targets := 32 },{ cop := 3, region := 2, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(4,5)], upper := (rows 7 42 69 296 211 243 211 211 467), lower := (rows 7 42 69 296 16 32 64 128 256), losses := [] }

theorem u41223 : Upper (D 7) (R 7) [6,40,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41223 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41224 : Route 9 := (fun mask => (mask,id))

def c41224 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u41224 : Upper (D 7) (R 7) [6,40,65,320] 13 := by
  apply FastRouting.sound _ _ [6,40,65,320] 13 (by decide) (choices 2) [3,33,34,129,130,160] r41224 c41224
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30874
  · exact u30875
  · exact u30876
  · exact u30877
  · exact u30878
  · exact u30879

def r41225 : Route 9 := (fun mask => (mask,id))

def c41225 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41225 : Upper (D 7) (R 7) [6,40,65,384] 13 := by
  apply FastRouting.sound _ _ [6,40,65,384] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r41225 c41225
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30880
  · exact u30881
  · exact u30882
  · exact u30883
  · exact u30884
  · exact u30885
  · exact u30886
  · exact u30887
  · exact u30888
  · exact u30889

def b41226 : PairBound 9 := { available := 481, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 0, region := 500, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 7 42 84 11 497 481 481 481 481), lower := (rows 7 42 84 11 16 32 64 128 256), losses := [] }

theorem u41226 : Upper (D 7) (R 7) [6,40,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41226 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41227 : PairBound 9 := { available := 451, camps := [{ cop := 1, region := 469, targets := 32 },{ cop := 3, region := 2, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(4,5)], upper := (rows 7 42 84 41 467 483 451 451 451), lower := (rows 7 42 84 41 16 32 64 128 256), losses := [] }

theorem u41227 : Upper (D 7) (R 7) [6,40,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41227 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41228 : PairBound 9 := { available := 449, camps := [{ cop := 5, region := 10, targets := 193 }], pairs := [(1,0),(1,6),(1,7),(3,0)], upper := (rows 7 42 84 42 465 481 449 449 449), lower := (rows 7 42 84 42 16 32 64 128 256), losses := [] }

theorem u41228 : Upper (D 7) (R 7) [6,40,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41228 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41229 : Route 9 := (fun mask => (mask,id))

def c41229 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 6 => 2 | 10 => 3 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u41229 : Upper (D 7) (R 7) [6,40,80,65] 13 := by
  apply FastRouting.sound _ _ [6,40,80,65] 13 (by decide) (choices 2) [3,33,34,129,130,160,257,258,288,384] r41229 c41229
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30890
  · exact u30891
  · exact u30892
  · exact u30893
  · exact u30894
  · exact u30895
  · exact u30896
  · exact u30897
  · exact u30898
  · exact u30899

def r41230 : Route 9 := (fun mask => (mask,id))

def c41230 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u41230 : Upper (D 7) (R 7) [6,40,80,66] 13 := by
  apply FastRouting.sound _ _ [6,40,80,66] 13 (by decide) (choices 2) [33,129,160,257,288,384] r41230 c41230
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30900
  · exact u30901
  · exact u30902
  · exact u30903
  · exact u30904
  · exact u30905

def b41231 : PairBound 9 := { available := 387, camps := [{ cop := 1, region := 469, targets := 32 },{ cop := 3, region := 2, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(4,5)], upper := (rows 7 42 84 104 403 419 451 387 387), lower := (rows 7 42 84 104 16 32 64 128 256), losses := [] }

theorem u41231 : Upper (D 7) (R 7) [6,40,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41231 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41232 : Route 9 := (fun mask => (mask,id))

def c41232 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41232 : Upper (D 7) (R 7) [6,40,80,129] 13 := by
  apply FastRouting.sound _ _ [6,40,80,129] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192,257,258,288,320,384] r41232 c41232
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30906
  · exact u30907
  · exact u30908
  · exact u30909
  · exact u30910
  · exact u30911
  · exact u30912
  · exact u30913
  · exact u30914
  · exact u30915
  · exact u30916
  · exact u30917
  · exact u30918
  · exact u30919
  · exact u30920

def r41233 : Route 9 := (fun mask => (mask,id))

def c41233 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41233 : Upper (D 7) (R 7) [6,40,80,130] 13 := by
  apply FastRouting.sound _ _ [6,40,80,130] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r41233 c41233
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30921
  · exact u30922
  · exact u30923
  · exact u30924
  · exact u30925
  · exact u30926
  · exact u30927
  · exact u30928
  · exact u30929
  · exact u30930

def b41234 : PairBound 9 := { available := 451, camps := [{ cop := 1, region := 469, targets := 32 },{ cop := 3, region := 2, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(4,5)], upper := (rows 7 42 84 168 467 483 451 451 451), lower := (rows 7 42 84 168 16 32 64 128 256), losses := [] }

theorem u41234 : Upper (D 7) (R 7) [6,40,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41234 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41235 : Route 9 := (fun mask => (mask,id))

def c41235 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 6 => 2 | 10 => 3 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u41235 : Upper (D 7) (R 7) [6,40,80,192] 13 := by
  apply FastRouting.sound _ _ [6,40,80,192] 13 (by decide) (choices 2) [3,33,34,129,130,160,257,258,288,384] r41235 c41235
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30931
  · exact u30932
  · exact u30933
  · exact u30934
  · exact u30935
  · exact u30936
  · exact u30937
  · exact u30938
  · exact u30939
  · exact u30940

def r41236 : Route 9 := (fun mask => (mask,id))

def c41236 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41236 : Upper (D 7) (R 7) [6,40,80,257] 13 := by
  apply FastRouting.sound _ _ [6,40,80,257] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r41236 c41236
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30941
  · exact u30942
  · exact u30943
  · exact u30944
  · exact u30945
  · exact u30946
  · exact u30947
  · exact u30948
  · exact u30949
  · exact u30950

def r41237 : Route 9 := (fun mask => (mask,id))

def c41237 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41237 : Upper (D 7) (R 7) [6,40,80,258] 13 := by
  apply FastRouting.sound _ _ [6,40,80,258] 13 (by decide) (choices 2) [33,65,96,129,160,192] r41237 c41237
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30951
  · exact u30952
  · exact u30953
  · exact u30954
  · exact u30955
  · exact u30956

def b41238 : PairBound 9 := { available := 195, camps := [{ cop := 1, region := 213, targets := 32 },{ cop := 3, region := 2, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(4,5)], upper := (rows 7 42 84 296 211 227 195 195 451), lower := (rows 7 42 84 296 16 32 64 128 256), losses := [] }

theorem u41238 : Upper (D 7) (R 7) [6,40,80,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41238 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41239 : Route 9 := (fun mask => (mask,id))

def c41239 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u41239 : Upper (D 7) (R 7) [6,40,80,320] 13 := by
  apply FastRouting.sound _ _ [6,40,80,320] 13 (by decide) (choices 2) [3,33,34,129,130,160] r41239 c41239
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30957
  · exact u30958
  · exact u30959
  · exact u30960
  · exact u30961
  · exact u30962

def r41240 : Route 9 := (fun mask => (mask,id))

def c41240 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41240 : Upper (D 7) (R 7) [6,40,80,384] 13 := by
  apply FastRouting.sound _ _ [6,40,80,384] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r41240 c41240
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30963
  · exact u30964
  · exact u30965
  · exact u30966
  · exact u30967
  · exact u30968
  · exact u30969
  · exact u30970
  · exact u30971
  · exact u30972

def b41241 : PairBound 9 := { available := 465, camps := [{ cop := 2, region := 11, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 42 100 11 465 497 465 465 465), lower := (rows 7 42 100 11 16 32 64 128 256), losses := [] }

theorem u41241 : Upper (D 7) (R 7) [6,40,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41241 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41242 : Route 9 := (fun mask => (mask,id))

def c41242 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41242 : Upper (D 7) (R 7) [6,40,96,17] 13 := by
  apply FastRouting.sound _ _ [6,40,96,17] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r41242 c41242
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30973
  · exact u30974
  · exact u30975
  · exact u30976
  · exact u30977
  · exact u30978
  · exact u30979
  · exact u30980
  · exact u30981
  · exact u30982

def b41243 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 472, targets := 32 }], pairs := [(2,1),(3,5),(4,1),(4,5)], upper := (rows 7 42 100 26 465 481 449 449 449), lower := (rows 7 42 100 26 16 32 64 128 256), losses := [] }

theorem u41243 : Upper (D 7) (R 7) [6,40,96,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41243 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41244 : PairBound 9 := { available := 403, camps := [{ cop := 2, region := 11, targets := 128 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(1,7),(3,5),(3,7)], upper := (rows 7 42 100 73 403 435 467 403 403), lower := (rows 7 42 100 73 16 32 64 128 256), losses := [] }

theorem u41244 : Upper (D 7) (R 7) [6,40,96,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41244 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41245 : PairBound 9 := { available := 401, camps := [{ cop := 2, region := 11, targets := 128 },{ cop := 0, region := 500, targets := 2 }], pairs := [(0,7),(1,7),(2,1),(3,7)], upper := (rows 7 42 100 74 401 433 465 401 401), lower := (rows 7 42 100 74 16 32 64 128 256), losses := [] }

theorem u41245 : Upper (D 7) (R 7) [6,40,96,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41245 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41246 : Route 9 := (fun mask => (mask,id))

def c41246 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u41246 : Upper (D 7) (R 7) [6,40,96,80] 13 := by
  apply FastRouting.sound _ _ [6,40,96,80] 13 (by decide) (choices 2) [3,129,130,257,258,384] r41246 c41246
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30983
  · exact u30984
  · exact u30985
  · exact u30986
  · exact u30987
  · exact u30988

def r41247 : Route 9 := (fun mask => (mask,id))

def c41247 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41247 : Upper (D 7) (R 7) [6,40,96,129] 13 := by
  apply FastRouting.sound _ _ [6,40,96,129] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r41247 c41247
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30989
  · exact u30990
  · exact u30991
  · exact u30992
  · exact u30993
  · exact u30994
  · exact u30995
  · exact u30996
  · exact u30997
  · exact u30998

def b41248 : PairBound 9 := { available := 465, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 472, targets := 32 }], pairs := [(2,1),(3,5),(4,1),(4,5)], upper := (rows 7 42 100 138 465 497 465 465 465), lower := (rows 7 42 100 138 16 32 64 128 256), losses := [] }

theorem u41248 : Upper (D 7) (R 7) [6,40,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41248 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41249 : Route 9 := (fun mask => (mask,id))

def c41249 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41249 : Upper (D 7) (R 7) [6,40,96,144] 13 := by
  apply FastRouting.sound _ _ [6,40,96,144] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r41249 c41249
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30999
  · exact u31000
  · exact u31001
  · exact u31002
  · exact u31003
  · exact u31004
  · exact u31005
  · exact u31006
  · exact u31007
  · exact u31008

def r41250 : Route 9 := (fun mask => (mask,id))

def c41250 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u41250 : Upper (D 7) (R 7) [6,40,96,192] 13 := by
  apply FastRouting.sound _ _ [6,40,96,192] 13 (by decide) (choices 2) [3,129,130,257,258,384] r41250 c41250
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31009
  · exact u31010
  · exact u31011
  · exact u31012
  · exact u31013
  · exact u31014

def r41251 : Route 9 := (fun mask => (mask,id))

def c41251 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41251 : Upper (D 7) (R 7) [6,40,96,257] 13 := by
  apply FastRouting.sound _ _ [6,40,96,257] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41251 c41251
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31015
  · exact u31016
  · exact u31017
  · exact u31018
  · exact u31019
  · exact u31020

def b41252 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 0, region := 472, targets := 32 }], pairs := [(2,1),(3,5),(4,1),(4,5)], upper := (rows 7 42 100 266 209 241 209 209 465), lower := (rows 7 42 100 266 16 32 64 128 256), losses := [] }

theorem u41252 : Upper (D 7) (R 7) [6,40,96,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41252 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41253 : Route 9 := (fun mask => (mask,id))

def c41253 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41253 : Upper (D 7) (R 7) [6,40,96,272] 13 := by
  apply FastRouting.sound _ _ [6,40,96,272] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41253 c41253
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31021
  · exact u31022
  · exact u31023
  · exact u31024
  · exact u31025
  · exact u31026

def r41254 : Route 9 := (fun mask => (mask,id))

def c41254 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u41254 : Upper (D 7) (R 7) [6,40,96,320] 13 := by
  apply FastRouting.sound _ _ [6,40,96,320] 13 (by decide) (choices 2) [3,129,130] r41254 c41254
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u31027
  · exact u31028
  · exact u31029

def r41255 : Route 9 := (fun mask => (mask,id))

def c41255 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41255 : Upper (D 7) (R 7) [6,40,96,384] 13 := by
  apply FastRouting.sound _ _ [6,40,96,384] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41255 c41255
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31030
  · exact u31031
  · exact u31032
  · exact u31033
  · exact u31034
  · exact u31035

def b41256 : PairBound 9 := { available := 497, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 0, region := 500, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 7 42 196 11 497 497 497 497 497), lower := (rows 7 42 196 11 16 32 64 128 256), losses := [] }

theorem u41256 : Upper (D 7) (R 7) [6,40,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41256 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41257 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41257 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41257 : Upper (D 7) (R 7) [6,40,192,17] 13 := by
  apply FastRouting.sound _ _ [6,40,192,17] 13 (by decide) (choices 2) [3,33,34,65,66,96,192,257,258,288,320] r41257 c41257
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31036
  · exact u31037
  · exact u31038
  · exact u31039
  · exact u31040
  · exact u31041
  · exact u31042
  · exact u31043
  · exact u31044
  · exact u31045
  · exact u31046

def r41258 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41258 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41258 : Upper (D 7) (R 7) [6,40,192,18] 13 := by
  apply FastRouting.sound _ _ [6,40,192,18] 13 (by decide) (choices 2) [33,65,96,192,257,288,320] r41258 c41258
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31047
  · exact u31048
  · exact u31049
  · exact u31050
  · exact u31051
  · exact u31052
  · exact u31053

def b41259 : PairBound 9 := { available := 467, camps := [{ cop := 1, region := 469, targets := 32 },{ cop := 3, region := 2, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(4,5)], upper := (rows 7 42 196 41 467 499 467 467 467), lower := (rows 7 42 196 41 16 32 64 128 256), losses := [] }

theorem u41259 : Upper (D 7) (R 7) [6,40,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41259 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41260 : PairBound 9 := { available := 465, camps := [{ cop := 5, region := 10, targets := 193 }], pairs := [(1,0),(1,6),(1,7),(3,0)], upper := (rows 7 42 196 42 465 497 465 465 465), lower := (rows 7 42 196 42 16 32 64 128 256), losses := [] }

theorem u41260 : Upper (D 7) (R 7) [6,40,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41260 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41261 : PairBound 9 := { available := 451, camps := [{ cop := 1, region := 469, targets := 32 },{ cop := 3, region := 2, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(4,5)], upper := (rows 7 42 196 56 467 483 451 451 451), lower := (rows 7 42 196 56 16 32 64 128 256), losses := [] }

theorem u41261 : Upper (D 7) (R 7) [6,40,192,48] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41261 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41262 : Route 9 := (fun mask => (mask,id))

def c41262 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 6 => 2 | 10 => 3 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u41262 : Upper (D 7) (R 7) [6,40,192,65] 13 := by
  apply FastRouting.sound _ _ [6,40,192,65] 13 (by decide) (choices 2) [3,33,34,129,130,160,257,258,288,384] r41262 c41262
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31054
  · exact u31055
  · exact u31056
  · exact u31057
  · exact u31058
  · exact u31059
  · exact u31060
  · exact u31061
  · exact u31062
  · exact u31063

def r41263 : Route 9 := (fun mask => (mask,id))

def c41263 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u41263 : Upper (D 7) (R 7) [6,40,192,66] 13 := by
  apply FastRouting.sound _ _ [6,40,192,66] 13 (by decide) (choices 2) [33,129,160,257,288,384] r41263 c41263
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31064
  · exact u31065
  · exact u31066
  · exact u31067
  · exact u31068
  · exact u31069

def r41264 : Route 9 := (fun mask => (mask,id))

def c41264 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 6 => 2 | 10 => 3 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u41264 : Upper (D 7) (R 7) [6,40,192,80] 13 := by
  apply FastRouting.sound _ _ [6,40,192,80] 13 (by decide) (choices 2) [3,33,34,129,130,160,257,258,288,384] r41264 c41264
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31070
  · exact u31071
  · exact u31072
  · exact u31073
  · exact u31074
  · exact u31075
  · exact u31076
  · exact u31077
  · exact u31078
  · exact u31079

def b41265 : PairBound 9 := { available := 403, camps := [{ cop := 1, region := 469, targets := 32 },{ cop := 3, region := 2, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(4,5)], upper := (rows 7 42 196 104 403 435 467 403 403), lower := (rows 7 42 196 104 16 32 64 128 256), losses := [] }

theorem u41265 : Upper (D 7) (R 7) [6,40,192,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41265 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41266 : PairBound 9 := { available := 307, camps := [{ cop := 2, region := 8, targets := 35 },{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0),(3,0),(3,1),(3,5)], upper := (rows 7 42 196 200 307 307 371 435 307), lower := (rows 7 42 196 200 16 32 64 128 256), losses := [] }

theorem u41266 : Upper (D 7) (R 7) [6,40,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41266 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41267 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41267 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41267 : Upper (D 7) (R 7) [6,40,192,257] 13 := by
  apply FastRouting.sound _ _ [6,40,192,257] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r41267 c41267
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31080
  · exact u31081
  · exact u31082
  · exact u31083
  · exact u31084
  · exact u31085
  · exact u31086

def r41268 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41268 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41268 : Upper (D 7) (R 7) [6,40,192,258] 13 := by
  apply FastRouting.sound _ _ [6,40,192,258] 13 (by decide) (choices 2) [33,65,96,192] r41268 c41268
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u31087
  · exact u31088
  · exact u31089
  · exact u31090

def r41269 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41269 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41269 : Upper (D 7) (R 7) [6,40,192,272] 13 := by
  apply FastRouting.sound _ _ [6,40,192,272] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r41269 c41269
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31091
  · exact u31092
  · exact u31093
  · exact u31094
  · exact u31095
  · exact u31096
  · exact u31097

def b41270 : PairBound 9 := { available := 211, camps := [{ cop := 1, region := 213, targets := 32 },{ cop := 3, region := 2, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(4,5)], upper := (rows 7 42 196 296 211 243 211 211 467), lower := (rows 7 42 196 296 16 32 64 128 256), losses := [] }

theorem u41270 : Upper (D 7) (R 7) [6,40,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41270 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41271 : Route 9 := (fun mask => (mask,id))

def c41271 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u41271 : Upper (D 7) (R 7) [6,40,192,320] 13 := by
  apply FastRouting.sound _ _ [6,40,192,320] 13 (by decide) (choices 2) [3,33,34,129,130,160] r41271 c41271
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31098
  · exact u31099
  · exact u31100
  · exact u31101
  · exact u31102
  · exact u31103

def b41272 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 0, region := 500, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 7 42 261 11 240 240 240 240 496), lower := (rows 7 42 261 11 16 32 64 128 256), losses := [] }

theorem u41272 : Upper (D 7) (R 7) [6,40,257,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41272 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41273 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41273 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41273 : Upper (D 7) (R 7) [6,40,257,17] 13 := by
  apply FastRouting.sound _ _ [6,40,257,17] 13 (by decide) (choices 2) [34,66,96,192] r41273 c41273
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u31104
  · exact u31105
  · exact u31106
  · exact u31107

def r41274 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41274 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41274 : Upper (D 7) (R 7) [6,40,257,18] 13 := by
  apply FastRouting.sound _ _ [6,40,257,18] 13 (by decide) (choices 2) [33,65,96,192] r41274 c41274
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u31108
  · exact u31109
  · exact u31110
  · exact u31111

def b41275 : PairBound 9 := { available := 210, camps := [{ cop := 1, region := 469, targets := 32 },{ cop := 3, region := 2, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(4,5)], upper := (rows 7 42 261 41 210 242 210 210 466), lower := (rows 7 42 261 41 16 32 64 128 256), losses := [] }

theorem u41275 : Upper (D 7) (R 7) [6,40,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41275 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41276 : PairBound 9 := { available := 209, camps := [{ cop := 5, region := 10, targets := 193 }], pairs := [(1,0),(1,6),(1,7),(3,0)], upper := (rows 7 42 261 42 209 241 209 209 465), lower := (rows 7 42 261 42 16 32 64 128 256), losses := [] }

theorem u41276 : Upper (D 7) (R 7) [6,40,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41276 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41277 : PairBound 9 := { available := 195, camps := [{ cop := 1, region := 469, targets := 32 },{ cop := 3, region := 2, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(4,5)], upper := (rows 7 42 261 56 211 227 195 195 451), lower := (rows 7 42 261 56 16 32 64 128 256), losses := [] }

theorem u41277 : Upper (D 7) (R 7) [6,40,257,48] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41277 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41278 : Route 9 := (fun mask => (mask,id))

def c41278 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41278 : Upper (D 7) (R 7) [6,40,257,65] 13 := by
  apply FastRouting.sound _ _ [6,40,257,65] 13 (by decide) (choices 2) [34,66,96,130,160,192] r41278 c41278
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31112
  · exact u31113
  · exact u31114
  · exact u31115
  · exact u31116
  · exact u31117

def r41279 : Route 9 := (fun mask => (mask,id))

def c41279 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41279 : Upper (D 7) (R 7) [6,40,257,66] 13 := by
  apply FastRouting.sound _ _ [6,40,257,66] 13 (by decide) (choices 2) [33,65,96,129,160,192] r41279 c41279
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31118
  · exact u31119
  · exact u31120
  · exact u31121
  · exact u31122
  · exact u31123

#print axioms u41279
end Delivery.IrregularNine14.P07

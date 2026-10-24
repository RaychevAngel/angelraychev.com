import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0281
import IrregularNine14P07C0282
import IrregularNine14P07C0283
import IrregularNine14P07C0284

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r33180 : Route 9 := (fun mask => (mask,id))

def c33180 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33180 : Upper (D 7) (R 7) [12,96,33,272,129] 13 := by
  apply FastRouting.sound _ _ [12,96,33,272,129] 13 (by decide) (choices 1) [2,64,128] r33180 c33180
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16900
  · exact u16901
  · exact u16902

def r33181 : Route 9 := (fun mask => (mask,id))

def c33181 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33181 : Upper (D 7) (R 7) [12,96,33,272,130] 13 := by
  apply FastRouting.sound _ _ [12,96,33,272,130] 13 (by decide) (choices 1) [1,2,64,128] r33181 c33181
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16903
  · exact u16904
  · exact u16905
  · exact u16906

def r33182 : Route 9 := (fun mask => (mask,id))

def c33182 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33182 : Upper (D 7) (R 7) [12,96,33,272,192] 13 := by
  apply FastRouting.sound _ _ [12,96,33,272,192] 13 (by decide) (choices 1) [1,2,128] r33182 c33182
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16907
  · exact u16908
  · exact u16909

def b33183 : PairBound 9 := { available := 146, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 4, region := 456, targets := 32 },{ cop := 4, region := 164, targets := 64 }], pairs := [(1,0),(2,6),(3,0),(3,5)], upper := (rows 13 98 37 328 19 178 210 146 402), lower := (rows 13 98 37 328 19 32 64 128 256), losses := [] }

theorem u33183 : Upper (D 7) (R 7) [12,96,33,320,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33183 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33184 : Route 9 := (fun mask => (mask,id))

def c33184 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33184 : Upper (D 7) (R 7) [12,96,33,320,129] 13 := by
  apply FastRouting.sound _ _ [12,96,33,320,129] 13 (by decide) (choices 1) [2,16,128] r33184 c33184
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16910
  · exact u16911
  · exact u16912

def r33185 : Route 9 := (fun mask => (mask,id))

def c33185 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33185 : Upper (D 7) (R 7) [12,96,33,320,130] 13 := by
  apply FastRouting.sound _ _ [12,96,33,320,130] 13 (by decide) (choices 1) [1,2,16,128] r33185 c33185
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16913
  · exact u16914
  · exact u16915
  · exact u16916

def r33186 : Route 9 := (fun mask => (mask,id))

def c33186 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u33186 : Upper (D 7) (R 7) [12,96,33,384,3] 13 := by
  apply FastRouting.sound _ _ [12,96,33,384,3] 13 (by decide) (choices 1) [2,16,64,128] r33186 c33186
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16917
  · exact u16918
  · exact u16919
  · exact u16920

def r33187 : Route 9 := (fun mask => (mask,id))

def c33187 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33187 : Upper (D 7) (R 7) [12,96,33,384,65] 13 := by
  apply FastRouting.sound _ _ [12,96,33,384,65] 13 (by decide) (choices 1) [2,16,128] r33187 c33187
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16921
  · exact u16922
  · exact u16923

def b33188 : PairBound 9 := { available := 147, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 13 98 37 392 82 179 211 147 403), lower := (rows 13 98 37 392 82 32 64 128 256), losses := [] }

theorem u33188 : Upper (D 7) (R 7) [12,96,33,384,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33188 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33189 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 4, region := 102, targets := 128 }], pairs := [(1,0),(1,7),(2,7),(3,0)], upper := (rows 13 98 37 392 145 114 82 210 338), lower := (rows 13 98 37 392 145 32 64 128 256), losses := [] }

theorem u33189 : Upper (D 7) (R 7) [12,96,33,384,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33189 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33190 : Route 9 := (fun mask => (mask,id))

def c33190 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33190 : Upper (D 7) (R 7) [12,96,33,384,130] 13 := by
  apply FastRouting.sound _ _ [12,96,33,384,130] 13 (by decide) (choices 1) [1,2,16,64] r33190 c33190
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16924
  · exact u16925
  · exact u16926
  · exact u16927

def r33191 : Route 9 := (fun mask => (mask,id))

def c33191 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33191 : Upper (D 7) (R 7) [12,96,33,384,192] 13 := by
  apply FastRouting.sound _ _ [12,96,33,384,192] 13 (by decide) (choices 1) [1,2,16] r33191 c33191
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16928
  · exact u16929
  · exact u16930

def b33192 : PairBound 9 := { available := 450, camps := [{ cop := 4, region := 486, targets := 1 },{ cop := 4, region := 456, targets := 32 }], pairs := [(0,5),(1,0),(2,0),(3,5)], upper := (rows 13 98 52 137 19 482 450 450 450), lower := (rows 13 98 52 137 19 32 64 128 256), losses := [{ target := 5, region := (rows 5 2 4 28 16 0 82 146 274), good := (rows 13 450 477 137 475 0 64 128 256) }] }

theorem u33192 : Upper (D 7) (R 7) [12,96,48,129,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33192 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33193 : Route 9 := (fun mask => (mask,id))

def c33193 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u33193 : Upper (D 7) (R 7) [12,96,48,129,65] 13 := by
  apply FastRouting.sound _ _ [12,96,48,129,65] 13 (by decide) (choices 1) [2,128,256] r33193 c33193
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16931
  · exact u16932
  · exact u16933

def b33194 : PairBound 9 := { available := 387, camps := [{ cop := 1, region := 20, targets := 129 }], pairs := [(2,0),(2,7),(4,0),(4,7)], upper := (rows 13 98 52 137 82 419 451 387 387), lower := (rows 13 98 52 137 82 32 64 128 256), losses := [] }

theorem u33194 : Upper (D 7) (R 7) [12,96,48,129,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33194 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33195 : PairBound 9 := { available := 322, camps := [{ cop := 3, region := 16, targets := 98 },{ cop := 4, region := 8, targets := 2 }], pairs := [(3,1),(4,1),(4,5),(4,6)], upper := (rows 13 98 52 137 145 354 322 450 322), lower := (rows 13 98 52 137 145 32 64 128 256), losses := [] }

theorem u33195 : Upper (D 7) (R 7) [12,96,48,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33195 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33196 : Route 9 := (fun mask => (mask,id))

def c33196 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u33196 : Upper (D 7) (R 7) [12,96,48,129,130] 13 := by
  apply FastRouting.sound _ _ [12,96,48,129,130] 13 (by decide) (choices 1) [1,2,64,256] r33196 c33196
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16934
  · exact u16935
  · exact u16936
  · exact u16937

def r33197 : Route 9 := (fun mask => (mask,id))

def c33197 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u33197 : Upper (D 7) (R 7) [12,96,48,129,192] 13 := by
  apply FastRouting.sound _ _ [12,96,48,129,192] 13 (by decide) (choices 1) [1,2,256] r33197 c33197
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16938
  · exact u16939
  · exact u16940

def r33198 : Route 9 := (fun mask => (mask,id))

def c33198 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33198 : Upper (D 7) (R 7) [12,96,48,129,257] 13 := by
  apply FastRouting.sound _ _ [12,96,48,129,257] 13 (by decide) (choices 1) [2,64,128] r33198 c33198
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16941
  · exact u16942
  · exact u16943

def r33199 : Route 9 := (fun mask => (mask,id))

def c33199 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33199 : Upper (D 7) (R 7) [12,96,48,129,258] 13 := by
  apply FastRouting.sound _ _ [12,96,48,129,258] 13 (by decide) (choices 1) [1,2,64,128] r33199 c33199
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16944
  · exact u16945
  · exact u16946
  · exact u16947

def r33200 : Route 9 := (fun mask => (mask,id))

def c33200 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33200 : Upper (D 7) (R 7) [12,96,48,129,320] 13 := by
  apply FastRouting.sound _ _ [12,96,48,129,320] 13 (by decide) (choices 1) [1,2,128] r33200 c33200
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16948
  · exact u16949
  · exact u16950

def r33201 : Route 9 := (fun mask => (mask,id))

def c33201 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33201 : Upper (D 7) (R 7) [12,96,48,129,384] 13 := by
  apply FastRouting.sound _ _ [12,96,48,129,384] 13 (by decide) (choices 1) [1,2,64] r33201 c33201
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16951
  · exact u16952
  · exact u16953

def r33202 : Route 9 := (fun mask => (mask,id))

def c33202 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u33202 : Upper (D 7) (R 7) [12,96,48,130,3] 13 := by
  apply FastRouting.sound _ _ [12,96,48,130,3] 13 (by decide) (choices 1) [1,64,128,256] r33202 c33202
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16954
  · exact u16955
  · exact u16956
  · exact u16957

def r33203 : Route 9 := (fun mask => (mask,id))

def c33203 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u33203 : Upper (D 7) (R 7) [12,96,48,130,65] 13 := by
  apply FastRouting.sound _ _ [12,96,48,130,65] 13 (by decide) (choices 1) [1,2,128,256] r33203 c33203
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16958
  · exact u16959
  · exact u16960
  · exact u16961

def b33204 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 20, targets := 129 }], pairs := [(2,0),(2,7),(4,0),(4,7)], upper := (rows 13 98 52 138 82 417 449 385 385), lower := (rows 13 98 52 138 82 32 64 128 256), losses := [] }

theorem u33204 : Upper (D 7) (R 7) [12,96,48,130,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33204 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33205 : Route 9 := (fun mask => (mask,id))

def c33205 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u33205 : Upper (D 7) (R 7) [12,96,48,130,129] 13 := by
  apply FastRouting.sound _ _ [12,96,48,130,129] 13 (by decide) (choices 1) [1,2,64,256] r33205 c33205
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16962
  · exact u16963
  · exact u16964
  · exact u16965

def b33206 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 16, targets := 97 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,5),(4,6)], upper := (rows 13 98 52 138 146 353 321 449 321), lower := (rows 13 98 52 138 146 32 64 128 256), losses := [] }

theorem u33206 : Upper (D 7) (R 7) [12,96,48,130,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33206 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33207 : Route 9 := (fun mask => (mask,id))

def c33207 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u33207 : Upper (D 7) (R 7) [12,96,48,130,192] 13 := by
  apply FastRouting.sound _ _ [12,96,48,130,192] 13 (by decide) (choices 1) [1,2,256] r33207 c33207
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16966
  · exact u16967
  · exact u16968

def r33208 : Route 9 := (fun mask => (mask,id))

def c33208 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33208 : Upper (D 7) (R 7) [12,96,48,130,257] 13 := by
  apply FastRouting.sound _ _ [12,96,48,130,257] 13 (by decide) (choices 1) [1,2,64,128] r33208 c33208
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16969
  · exact u16970
  · exact u16971
  · exact u16972

def r33209 : Route 9 := (fun mask => (mask,id))

def c33209 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33209 : Upper (D 7) (R 7) [12,96,48,130,258] 13 := by
  apply FastRouting.sound _ _ [12,96,48,130,258] 13 (by decide) (choices 1) [1,64,128] r33209 c33209
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16973
  · exact u16974
  · exact u16975

def r33210 : Route 9 := (fun mask => (mask,id))

def c33210 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33210 : Upper (D 7) (R 7) [12,96,48,130,320] 13 := by
  apply FastRouting.sound _ _ [12,96,48,130,320] 13 (by decide) (choices 1) [1,2,128] r33210 c33210
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16976
  · exact u16977
  · exact u16978

def r33211 : Route 9 := (fun mask => (mask,id))

def c33211 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33211 : Upper (D 7) (R 7) [12,96,48,130,384] 13 := by
  apply FastRouting.sound _ _ [12,96,48,130,384] 13 (by decide) (choices 1) [1,2,64] r33211 c33211
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16979
  · exact u16980
  · exact u16981

def r33212 : Route 9 := (fun mask => (mask,id))

def c33212 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u33212 : Upper (D 7) (R 7) [12,96,48,192,3] 13 := by
  apply FastRouting.sound _ _ [12,96,48,192,3] 13 (by decide) (choices 1) [1,2,128,256] r33212 c33212
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16982
  · exact u16983
  · exact u16984
  · exact u16985

def r33213 : Route 9 := (fun mask => (mask,id))

def c33213 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u33213 : Upper (D 7) (R 7) [12,96,48,192,129] 13 := by
  apply FastRouting.sound _ _ [12,96,48,192,129] 13 (by decide) (choices 1) [1,2,256] r33213 c33213
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16986
  · exact u16987
  · exact u16988

def r33214 : Route 9 := (fun mask => (mask,id))

def c33214 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u33214 : Upper (D 7) (R 7) [12,96,48,192,130] 13 := by
  apply FastRouting.sound _ _ [12,96,48,192,130] 13 (by decide) (choices 1) [1,2,256] r33214 c33214
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16989
  · exact u16990
  · exact u16991

def r33215 : Route 9 := (fun mask => (mask,id))

def c33215 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33215 : Upper (D 7) (R 7) [12,96,48,192,257] 13 := by
  apply FastRouting.sound _ _ [12,96,48,192,257] 13 (by decide) (choices 1) [1,2,128] r33215 c33215
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16992
  · exact u16993
  · exact u16994

def r33216 : Route 9 := (fun mask => (mask,id))

def c33216 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33216 : Upper (D 7) (R 7) [12,96,48,192,258] 13 := by
  apply FastRouting.sound _ _ [12,96,48,192,258] 13 (by decide) (choices 1) [1,2,128] r33216 c33216
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16995
  · exact u16996
  · exact u16997

def r33217 : Route 9 := (fun mask => (mask,id))

def c33217 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33217 : Upper (D 7) (R 7) [12,96,48,192,384] 13 := by
  apply FastRouting.sound _ _ [12,96,48,192,384] 13 (by decide) (choices 1) [1,2] r33217 c33217
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16998
  · exact u16999

def b33218 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 4, region := 456, targets := 32 }], pairs := [(0,5),(1,0),(2,0),(3,5)], upper := (rows 13 98 52 265 19 226 194 194 450), lower := (rows 13 98 52 265 19 32 64 128 256), losses := [{ target := 5, region := (rows 5 2 4 28 16 0 82 146 274), good := (rows 13 450 477 265 475 0 64 128 256) }] }

theorem u33218 : Upper (D 7) (R 7) [12,96,48,257,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33218 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33219 : Route 9 := (fun mask => (mask,id))

def c33219 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33219 : Upper (D 7) (R 7) [12,96,48,257,65] 13 := by
  apply FastRouting.sound _ _ [12,96,48,257,65] 13 (by decide) (choices 1) [2,128] r33219 c33219
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u17000
  · exact u17001

def b33220 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 20, targets := 129 }], pairs := [(2,0),(2,7),(4,0),(4,7)], upper := (rows 13 98 52 265 82 163 195 131 387), lower := (rows 13 98 52 265 82 32 64 128 256), losses := [] }

theorem u33220 : Upper (D 7) (R 7) [12,96,48,257,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33220 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33221 : Route 9 := (fun mask => (mask,id))

def c33221 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33221 : Upper (D 7) (R 7) [12,96,48,257,129] 13 := by
  apply FastRouting.sound _ _ [12,96,48,257,129] 13 (by decide) (choices 1) [2,64,128] r33221 c33221
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17002
  · exact u17003
  · exact u17004

def r33222 : Route 9 := (fun mask => (mask,id))

def c33222 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33222 : Upper (D 7) (R 7) [12,96,48,257,130] 13 := by
  apply FastRouting.sound _ _ [12,96,48,257,130] 13 (by decide) (choices 1) [1,2,64,128] r33222 c33222
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17005
  · exact u17006
  · exact u17007
  · exact u17008

def r33223 : Route 9 := (fun mask => (mask,id))

def c33223 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33223 : Upper (D 7) (R 7) [12,96,48,257,192] 13 := by
  apply FastRouting.sound _ _ [12,96,48,257,192] 13 (by decide) (choices 1) [1,2,128] r33223 c33223
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17009
  · exact u17010
  · exact u17011

def r33224 : Route 9 := (fun mask => (mask,id))

def c33224 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33224 : Upper (D 7) (R 7) [12,96,48,258,3] 13 := by
  apply FastRouting.sound _ _ [12,96,48,258,3] 13 (by decide) (choices 1) [1,64,128] r33224 c33224
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17012
  · exact u17013
  · exact u17014

def r33225 : Route 9 := (fun mask => (mask,id))

def c33225 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33225 : Upper (D 7) (R 7) [12,96,48,258,65] 13 := by
  apply FastRouting.sound _ _ [12,96,48,258,65] 13 (by decide) (choices 1) [1,2,128] r33225 c33225
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17015
  · exact u17016
  · exact u17017

def b33226 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 20, targets := 129 }], pairs := [(2,0),(2,7),(4,0),(4,7)], upper := (rows 13 98 52 266 82 161 193 129 385), lower := (rows 13 98 52 266 82 32 64 128 256), losses := [] }

theorem u33226 : Upper (D 7) (R 7) [12,96,48,258,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33226 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33227 : Route 9 := (fun mask => (mask,id))

def c33227 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33227 : Upper (D 7) (R 7) [12,96,48,258,129] 13 := by
  apply FastRouting.sound _ _ [12,96,48,258,129] 13 (by decide) (choices 1) [1,2,64,128] r33227 c33227
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17018
  · exact u17019
  · exact u17020
  · exact u17021

def r33228 : Route 9 := (fun mask => (mask,id))

def c33228 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33228 : Upper (D 7) (R 7) [12,96,48,258,130] 13 := by
  apply FastRouting.sound _ _ [12,96,48,258,130] 13 (by decide) (choices 1) [1,64,128] r33228 c33228
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17022
  · exact u17023
  · exact u17024

def r33229 : Route 9 := (fun mask => (mask,id))

def c33229 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33229 : Upper (D 7) (R 7) [12,96,48,258,192] 13 := by
  apply FastRouting.sound _ _ [12,96,48,258,192] 13 (by decide) (choices 1) [1,2,128] r33229 c33229
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17025
  · exact u17026
  · exact u17027

def r33230 : Route 9 := (fun mask => (mask,id))

def c33230 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33230 : Upper (D 7) (R 7) [12,96,48,320,3] 13 := by
  apply FastRouting.sound _ _ [12,96,48,320,3] 13 (by decide) (choices 1) [1,2,128] r33230 c33230
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17028
  · exact u17029
  · exact u17030

def r33231 : Route 9 := (fun mask => (mask,id))

def c33231 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33231 : Upper (D 7) (R 7) [12,96,48,320,129] 13 := by
  apply FastRouting.sound _ _ [12,96,48,320,129] 13 (by decide) (choices 1) [1,2,128] r33231 c33231
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17031
  · exact u17032
  · exact u17033

def r33232 : Route 9 := (fun mask => (mask,id))

def c33232 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33232 : Upper (D 7) (R 7) [12,96,48,320,130] 13 := by
  apply FastRouting.sound _ _ [12,96,48,320,130] 13 (by decide) (choices 1) [1,2,128] r33232 c33232
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17034
  · exact u17035
  · exact u17036

def r33233 : Route 9 := (fun mask => (mask,id))

def c33233 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33233 : Upper (D 7) (R 7) [12,96,48,384,3] 13 := by
  apply FastRouting.sound _ _ [12,96,48,384,3] 13 (by decide) (choices 1) [1,2,64,128] r33233 c33233
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17037
  · exact u17038
  · exact u17039
  · exact u17040

def r33234 : Route 9 := (fun mask => (mask,id))

def c33234 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33234 : Upper (D 7) (R 7) [12,96,48,384,65] 13 := by
  apply FastRouting.sound _ _ [12,96,48,384,65] 13 (by decide) (choices 1) [1,2,128] r33234 c33234
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17041
  · exact u17042
  · exact u17043

def b33235 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 20, targets := 129 }], pairs := [(2,0),(2,7),(4,0),(4,7)], upper := (rows 13 98 52 392 82 163 195 131 387), lower := (rows 13 98 52 392 82 32 64 128 256), losses := [] }

theorem u33235 : Upper (D 7) (R 7) [12,96,48,384,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33235 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33236 : Route 9 := (fun mask => (mask,id))

def c33236 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33236 : Upper (D 7) (R 7) [12,96,48,384,129] 13 := by
  apply FastRouting.sound _ _ [12,96,48,384,129] 13 (by decide) (choices 1) [1,2,64] r33236 c33236
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17044
  · exact u17045
  · exact u17046

def r33237 : Route 9 := (fun mask => (mask,id))

def c33237 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33237 : Upper (D 7) (R 7) [12,96,48,384,130] 13 := by
  apply FastRouting.sound _ _ [12,96,48,384,130] 13 (by decide) (choices 1) [1,2,64] r33237 c33237
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17047
  · exact u17048
  · exact u17049

def r33238 : Route 9 := (fun mask => (mask,id))

def c33238 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33238 : Upper (D 7) (R 7) [12,96,48,384,192] 13 := by
  apply FastRouting.sound _ _ [12,96,48,384,192] 13 (by decide) (choices 1) [1,2] r33238 c33238
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u17050
  · exact u17051

def b33239 : PairBound 9 := { available := 210, camps := [{ cop := 4, region := 461, targets := 32 },{ cop := 0, region := 242, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(3,5)], upper := (rows 13 98 133 265 50 242 210 210 466), lower := (rows 13 98 133 265 50 32 64 128 256), losses := [] }

theorem u33239 : Upper (D 7) (R 7) [12,96,129,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33239 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u33239
end Delivery.IrregularNine14.P07

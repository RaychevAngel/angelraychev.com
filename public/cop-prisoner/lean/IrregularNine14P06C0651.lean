import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0421
import IrregularNine14P06C0422

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r39060 : Route 9 := (fun mask => (mask,id))

def c39060 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39060 : Upper (D 6) (R 6) [34,384,66,17,72] 13 := by
  apply FastRouting.sound _ _ [34,384,66,17,72] 13 (by decide) (choices 1) [1,4] r39060 c39060
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25263
  · exact u25264

def r39061 : Route 9 := (fun mask => (mask,id))

def c39061 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39061 : Upper (D 6) (R 6) [34,384,66,17,96] 13 := by
  apply FastRouting.sound _ _ [34,384,66,17,96] 13 (by decide) (choices 1) [1,4,8] r39061 c39061
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25265
  · exact u25266
  · exact u25267

def b39062 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 386 70 41 81 60 92 156 284), lower := (rows 35 386 70 41 81 32 64 128 256), losses := [] }

theorem u39062 : Upper (D 6) (R 6) [34,384,66,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39062 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39063 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 386 70 41 88 53 85 149 277), lower := (rows 35 386 70 41 88 32 64 128 256), losses := [] }

theorem u39063 : Upper (D 6) (R 6) [34,384,66,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39063 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39064 : Route 9 := (fun mask => (mask,id))

def c39064 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39064 : Upper (D 6) (R 6) [34,384,66,36,65] 13 := by
  apply FastRouting.sound _ _ [34,384,66,36,65] 13 (by decide) (choices 1) [1,4,8,16] r39064 c39064
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25268
  · exact u25269
  · exact u25270
  · exact u25271

def r39065 : Route 9 := (fun mask => (mask,id))

def c39065 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39065 : Upper (D 6) (R 6) [34,384,66,36,72] 13 := by
  apply FastRouting.sound _ _ [34,384,66,36,72] 13 (by decide) (choices 1) [1,4,16] r39065 c39065
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25272
  · exact u25273
  · exact u25274

def b39066 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(1,5),(2,5)], upper := (rows 35 386 70 56 88 37 69 133 261), lower := (rows 35 386 70 56 88 32 64 128 256), losses := [] }

theorem u39066 : Upper (D 6) (R 6) [34,384,66,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39066 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39067 : PairBound 9 := { available := 116, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 386 76 13 19 116 116 244 372), lower := (rows 35 386 76 13 19 32 64 128 256), losses := [] }

theorem u39067 : Upper (D 6) (R 6) [34,384,72,5,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39067 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39068 : PairBound 9 := { available := 114, camps := [{ cop := 3, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 35 386 76 13 21 114 114 242 370), lower := (rows 35 386 76 13 21 32 64 128 256), losses := [] }

theorem u39068 : Upper (D 6) (R 6) [34,384,72,5,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39068 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39069 : Route 9 := (fun mask => (mask,id))

def c39069 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39069 : Upper (D 6) (R 6) [34,384,72,5,6] 13 := by
  apply FastRouting.sound _ _ [34,384,72,5,6] 13 (by decide) (choices 1) [1,16,64] r39069 c39069
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25275
  · exact u25276
  · exact u25277

def b39070 : PairBound 9 := { available := 86, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 386 76 13 49 118 86 214 342), lower := (rows 35 386 76 13 49 32 64 128 256), losses := [] }

theorem u39070 : Upper (D 6) (R 6) [34,384,72,5,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39070 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39071 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 386 76 13 50 117 85 213 341), lower := (rows 35 386 76 13 50 32 64 128 256), losses := [] }

theorem u39071 : Upper (D 6) (R 6) [34,384,72,5,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39071 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39072 : Route 9 := (fun mask => (mask,id))

def c39072 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39072 : Upper (D 6) (R 6) [34,384,72,5,36] 13 := by
  apply FastRouting.sound _ _ [34,384,72,5,36] 13 (by decide) (choices 1) [1,2,16,64] r39072 c39072
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25278
  · exact u25279
  · exact u25280
  · exact u25281

def b39073 : PairBound 9 := { available := 54, camps := [{ cop := 4, region := 12, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 35 386 76 13 81 54 118 182 310), lower := (rows 35 386 76 13 81 32 64 128 256), losses := [] }

theorem u39073 : Upper (D 6) (R 6) [34,384,72,5,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39073 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39074 : Route 9 := (fun mask => (mask,id))

def c39074 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39074 : Upper (D 6) (R 6) [34,384,72,5,66] 13 := by
  apply FastRouting.sound _ _ [34,384,72,5,66] 13 (by decide) (choices 1) [1,4,16] r39074 c39074
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25282
  · exact u25283
  · exact u25284

def b39075 : PairBound 9 := { available := 51, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 386 76 13 84 51 115 179 307), lower := (rows 35 386 76 13 84 32 64 128 256), losses := [] }

theorem u39075 : Upper (D 6) (R 6) [34,384,72,5,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39075 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39076 : Route 9 := (fun mask => (mask,id))

def c39076 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39076 : Upper (D 6) (R 6) [34,384,72,5,96] 13 := by
  apply FastRouting.sound _ _ [34,384,72,5,96] 13 (by decide) (choices 1) [1,2,4,16] r39076 c39076
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25285
  · exact u25286
  · exact u25287
  · exact u25288

def r39077 : Route 9 := (fun mask => (mask,id))

def c39077 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39077 : Upper (D 6) (R 6) [34,384,72,6,5] 13 := by
  apply FastRouting.sound _ _ [34,384,72,6,5] 13 (by decide) (choices 1) [1,16,64] r39077 c39077
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25289
  · exact u25290
  · exact u25291

def b39078 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 386 76 14 49 117 85 213 341), lower := (rows 35 386 76 14 49 32 64 128 256), losses := [] }

theorem u39078 : Upper (D 6) (R 6) [34,384,72,6,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39078 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39079 : Route 9 := (fun mask => (mask,id))

def c39079 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39079 : Upper (D 6) (R 6) [34,384,72,6,36] 13 := by
  apply FastRouting.sound _ _ [34,384,72,6,36] 13 (by decide) (choices 1) [1,16,64] r39079 c39079
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25292
  · exact u25293
  · exact u25294

def r39080 : Route 9 := (fun mask => (mask,id))

def c39080 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39080 : Upper (D 6) (R 6) [34,384,72,6,65] 13 := by
  apply FastRouting.sound _ _ [34,384,72,6,65] 13 (by decide) (choices 1) [1,4,16] r39080 c39080
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25295
  · exact u25296
  · exact u25297

def b39081 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 386 76 14 84 49 113 177 305), lower := (rows 35 386 76 14 84 32 64 128 256), losses := [] }

theorem u39081 : Upper (D 6) (R 6) [34,384,72,6,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39081 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39082 : Route 9 := (fun mask => (mask,id))

def c39082 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39082 : Upper (D 6) (R 6) [34,384,72,6,96] 13 := by
  apply FastRouting.sound _ _ [34,384,72,6,96] 13 (by decide) (choices 1) [1,4,16] r39082 c39082
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25298
  · exact u25299
  · exact u25300

def b39083 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 24, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 386 76 25 19 100 100 228 356), lower := (rows 35 386 76 25 19 32 64 128 256), losses := [] }

theorem u39083 : Upper (D 6) (R 6) [34,384,72,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39083 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39084 : PairBound 9 := { available := 102, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 386 76 25 21 102 102 230 358), lower := (rows 35 386 76 25 21 32 64 128 256), losses := [] }

theorem u39084 : Upper (D 6) (R 6) [34,384,72,17,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39084 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39085 : Route 9 := (fun mask => (mask,id))

def c39085 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39085 : Upper (D 6) (R 6) [34,384,72,17,6] 13 := by
  apply FastRouting.sound _ _ [34,384,72,17,6] 13 (by decide) (choices 1) [1,4,64] r39085 c39085
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25301
  · exact u25302
  · exact u25303

def b39086 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 24, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 386 76 25 49 102 70 198 326), lower := (rows 35 386 76 25 49 32 64 128 256), losses := [] }

theorem u39086 : Upper (D 6) (R 6) [34,384,72,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39086 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39087 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 386 76 25 50 101 69 197 325), lower := (rows 35 386 76 25 50 32 64 128 256), losses := [] }

theorem u39087 : Upper (D 6) (R 6) [34,384,72,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39087 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39088 : Route 9 := (fun mask => (mask,id))

def c39088 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39088 : Upper (D 6) (R 6) [34,384,72,17,36] 13 := by
  apply FastRouting.sound _ _ [34,384,72,17,36] 13 (by decide) (choices 1) [1,2,4,64] r39088 c39088
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25304
  · exact u25305
  · exact u25306
  · exact u25307

def b39089 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 12, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 35 386 76 25 81 38 102 166 294), lower := (rows 35 386 76 25 81 32 64 128 256), losses := [] }

theorem u39089 : Upper (D 6) (R 6) [34,384,72,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39089 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39090 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 3, region := 100, targets := 2 }], pairs := [(0,6),(1,6),(2,1)], upper := (rows 35 386 76 25 82 37 101 165 293), lower := (rows 35 386 76 25 82 32 64 128 256), losses := [] }

theorem u39090 : Upper (D 6) (R 6) [34,384,72,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39090 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39091 : PairBound 9 := { available := 39, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 386 76 25 84 39 103 167 295), lower := (rows 35 386 76 25 84 32 64 128 256), losses := [] }

theorem u39091 : Upper (D 6) (R 6) [34,384,72,17,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39091 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39092 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 3, region := 454, targets := 32 }], pairs := [(0,6),(1,5),(1,6)], upper := (rows 35 386 76 25 112 39 71 135 263), lower := (rows 35 386 76 25 112 32 64 128 256), losses := [] }

theorem u39092 : Upper (D 6) (R 6) [34,384,72,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39092 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39093 : Route 9 := (fun mask => (mask,id))

def c39093 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39093 : Upper (D 6) (R 6) [34,384,72,18,5] 13 := by
  apply FastRouting.sound _ _ [34,384,72,18,5] 13 (by decide) (choices 1) [1,4,64] r39093 c39093
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25308
  · exact u25309
  · exact u25310

def b39094 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 386 76 26 49 101 69 197 325), lower := (rows 35 386 76 26 49 32 64 128 256), losses := [] }

theorem u39094 : Upper (D 6) (R 6) [34,384,72,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39094 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39095 : Route 9 := (fun mask => (mask,id))

def c39095 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39095 : Upper (D 6) (R 6) [34,384,72,18,36] 13 := by
  apply FastRouting.sound _ _ [34,384,72,18,36] 13 (by decide) (choices 1) [1,4,64] r39095 c39095
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25311
  · exact u25312
  · exact u25313

def r39096 : Route 9 := (fun mask => (mask,id))

def c39096 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39096 : Upper (D 6) (R 6) [34,384,72,18,65] 13 := by
  apply FastRouting.sound _ _ [34,384,72,18,65] 13 (by decide) (choices 1) [1,4] r39096 c39096
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25314
  · exact u25315

def b39097 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 386 76 26 84 37 101 165 293), lower := (rows 35 386 76 26 84 32 64 128 256), losses := [] }

theorem u39097 : Upper (D 6) (R 6) [34,384,72,18,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39097 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39098 : Route 9 := (fun mask => (mask,id))

def c39098 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39098 : Upper (D 6) (R 6) [34,384,72,18,96] 13 := by
  apply FastRouting.sound _ _ [34,384,72,18,96] 13 (by decide) (choices 1) [1,4] r39098 c39098
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25316
  · exact u25317

def b39099 : PairBound 9 := { available := 101, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 386 76 28 19 101 101 229 357), lower := (rows 35 386 76 28 19 32 64 128 256), losses := [] }

theorem u39099 : Upper (D 6) (R 6) [34,384,72,20,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39099 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39100 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 386 76 28 21 99 99 227 355), lower := (rows 35 386 76 28 21 32 64 128 256), losses := [] }

theorem u39100 : Upper (D 6) (R 6) [34,384,72,20,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39100 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39101 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 386 76 28 22 97 97 225 353), lower := (rows 35 386 76 28 22 32 64 128 256), losses := [] }

theorem u39101 : Upper (D 6) (R 6) [34,384,72,20,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39101 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39102 : PairBound 9 := { available := 71, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 386 76 28 49 103 71 199 327), lower := (rows 35 386 76 28 49 32 64 128 256), losses := [] }

theorem u39102 : Upper (D 6) (R 6) [34,384,72,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39102 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39103 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 386 76 28 50 101 69 197 325), lower := (rows 35 386 76 28 50 32 64 128 256), losses := [] }

theorem u39103 : Upper (D 6) (R 6) [34,384,72,20,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39103 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39104 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 386 76 28 52 99 67 195 323), lower := (rows 35 386 76 28 52 32 64 128 256), losses := [] }

theorem u39104 : Upper (D 6) (R 6) [34,384,72,20,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39104 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39105 : PairBound 9 := { available := 39, camps := [{ cop := 4, region := 12, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 35 386 76 28 81 39 103 167 295), lower := (rows 35 386 76 28 81 32 64 128 256), losses := [] }

theorem u39105 : Upper (D 6) (R 6) [34,384,72,20,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39105 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39106 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 12, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 35 386 76 28 82 37 101 165 293), lower := (rows 35 386 76 28 82 32 64 128 256), losses := [] }

theorem u39106 : Upper (D 6) (R 6) [34,384,72,20,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39106 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39107 : PairBound 9 := { available := 35, camps := [{ cop := 6, region := 28, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 35 386 76 28 84 35 99 163 291), lower := (rows 35 386 76 28 84 32 64 128 256), losses := [] }

theorem u39107 : Upper (D 6) (R 6) [34,384,72,20,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39107 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39108 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 12, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 35 386 76 28 112 39 71 135 263), lower := (rows 35 386 76 28 112 32 64 128 256), losses := [] }

theorem u39108 : Upper (D 6) (R 6) [34,384,72,20,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39108 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39109 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 386 76 44 19 117 85 213 341), lower := (rows 35 386 76 44 19 32 64 128 256), losses := [] }

theorem u39109 : Upper (D 6) (R 6) [34,384,72,36,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39109 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39110 : PairBound 9 := { available := 83, camps := [{ cop := 4, region := 483, targets := 4 },{ cop := 4, region := 450, targets := 32 }], pairs := [(0,2),(1,2),(1,5)], upper := (rows 35 386 76 44 21 115 83 211 339), lower := (rows 35 386 76 44 21 32 64 128 256), losses := [] }

theorem u39110 : Upper (D 6) (R 6) [34,384,72,36,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39110 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39111 : Route 9 := (fun mask => (mask,id))

def c39111 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39111 : Upper (D 6) (R 6) [34,384,72,36,6] 13 := by
  apply FastRouting.sound _ _ [34,384,72,36,6] 13 (by decide) (choices 1) [1,16,64] r39111 c39111
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25318
  · exact u25319
  · exact u25320

def r39112 : Route 9 := (fun mask => (mask,id))

def c39112 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39112 : Upper (D 6) (R 6) [34,384,72,36,65] 13 := by
  apply FastRouting.sound _ _ [34,384,72,36,65] 13 (by decide) (choices 1) [1,2,4,16] r39112 c39112
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25321
  · exact u25322
  · exact u25323
  · exact u25324

def r39113 : Route 9 := (fun mask => (mask,id))

def c39113 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39113 : Upper (D 6) (R 6) [34,384,72,36,66] 13 := by
  apply FastRouting.sound _ _ [34,384,72,36,66] 13 (by decide) (choices 1) [1,4,16] r39113 c39113
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25325
  · exact u25326
  · exact u25327

def b39114 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 386 76 44 84 51 83 147 275), lower := (rows 35 386 76 44 84 32 64 128 256), losses := [] }

theorem u39114 : Upper (D 6) (R 6) [34,384,72,36,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39114 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39115 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 386 76 56 19 101 69 197 325), lower := (rows 35 386 76 56 19 32 64 128 256), losses := [] }

theorem u39115 : Upper (D 6) (R 6) [34,384,72,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39115 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39116 : Route 9 := (fun mask => (mask,id))

def c39116 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39116 : Upper (D 6) (R 6) [34,384,72,48,5] 13 := by
  apply FastRouting.sound _ _ [34,384,72,48,5] 13 (by decide) (choices 1) [1,2,4,64] r39116 c39116
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25328
  · exact u25329
  · exact u25330
  · exact u25331

def r39117 : Route 9 := (fun mask => (mask,id))

def c39117 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39117 : Upper (D 6) (R 6) [34,384,72,48,6] 13 := by
  apply FastRouting.sound _ _ [34,384,72,48,6] 13 (by decide) (choices 1) [1,4,64] r39117 c39117
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25332
  · exact u25333
  · exact u25334

def r39118 : Route 9 := (fun mask => (mask,id))

def c39118 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39118 : Upper (D 6) (R 6) [34,384,72,48,65] 13 := by
  apply FastRouting.sound _ _ [34,384,72,48,65] 13 (by decide) (choices 1) [1,2,4] r39118 c39118
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25335
  · exact u25336
  · exact u25337

def r39119 : Route 9 := (fun mask => (mask,id))

def c39119 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39119 : Upper (D 6) (R 6) [34,384,72,48,66] 13 := by
  apply FastRouting.sound _ _ [34,384,72,48,66] 13 (by decide) (choices 1) [1,4] r39119 c39119
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25338
  · exact u25339

#print axioms u39119
end Delivery.IrregularNine14.P06

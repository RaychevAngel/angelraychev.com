import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0075
import IrregularNine14P06C0076

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b17160 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 344, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 162 37 280 84 34 69 197 325), lower := (rows 11 162 37 280 84 34 64 128 256), losses := [] }

theorem u17160 : Upper (D 6) (R 6) [10,160,33,272,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17160 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17161 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 194, targets := 4 }], pairs := [(1,2),(2,1),(2,6)], upper := (rows 11 162 37 280 84 36 67 195 323), lower := (rows 11 162 37 280 84 36 64 128 256), losses := [] }

theorem u17161 : Upper (D 6) (R 6) [10,160,33,272,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17161 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17162 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 130, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 162 37 280 84 96 71 135 263), lower := (rows 11 162 37 280 84 96 64 128 256), losses := [{ target := 6, region := (rows 17 6 4 24 16 32 0 148 276), good := (rows 11 162 423 409 415 32 0 128 256) }] }

theorem u17162 : Upper (D 6) (R 6) [10,160,33,272,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17162 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17163 : PairBound 9 := { available := 84, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 162 37 328 22 33 84 212 340), lower := (rows 11 162 37 328 22 33 64 128 256), losses := [] }

theorem u17163 : Upper (D 6) (R 6) [10,160,33,320,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17163 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17164 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 329, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 162 37 328 22 36 81 209 337), lower := (rows 11 162 37 328 22 36 64 128 256), losses := [] }

theorem u17164 : Upper (D 6) (R 6) [10,160,33,320,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17164 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17165 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 52, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 11 162 37 328 22 48 69 197 325), lower := (rows 11 162 37 328 22 48 64 128 256), losses := [] }

theorem u17165 : Upper (D 6) (R 6) [10,160,33,320,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17165 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17166 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 146, targets := 64 },{ cop := 4, region := 329, targets := 32 }], pairs := [(0,5),(1,6),(4,6)], upper := (rows 11 162 37 328 22 96 85 149 277), lower := (rows 11 162 37 328 22 96 64 128 256), losses := [] }

theorem u17166 : Upper (D 6) (R 6) [10,160,33,320,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17166 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17167 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 344, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 162 37 328 81 34 84 148 276), lower := (rows 11 162 37 328 81 34 64 128 256), losses := [] }

theorem u17167 : Upper (D 6) (R 6) [10,160,33,320,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17167 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17168 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 4, region := 166, targets := 64 }], pairs := [(1,6),(2,1),(2,6)], upper := (rows 11 162 37 328 81 36 86 150 278), lower := (rows 11 162 37 328 81 36 64 128 256), losses := [] }

theorem u17168 : Upper (D 6) (R 6) [10,160,33,320,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17168 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17169 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 458, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 11 162 37 328 81 48 70 134 262), lower := (rows 11 162 37 328 81 48 64 128 256), losses := [] }

theorem u17169 : Upper (D 6) (R 6) [10,160,33,320,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17169 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17170 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 162 37 328 82 33 84 148 276), lower := (rows 11 162 37 328 82 33 64 128 256), losses := [] }

theorem u17170 : Upper (D 6) (R 6) [10,160,33,320,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17170 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17171 : Route 9 := (fun mask => (mask,id))

def c17171 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17171 : Upper (D 6) (R 6) [10,160,33,320,66,4] 13 := by
  apply FastRouting.sound _ _ [10,160,33,320,66,4] 13 (by decide) (choices 1) [1,4,16] r17171 c17171
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4539
  · exact u4540
  · exact u4541

def b17172 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 328, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 11 162 37 328 82 48 69 133 261), lower := (rows 11 162 37 328 82 48 64 128 256), losses := [] }

theorem u17172 : Upper (D 6) (R 6) [10,160,33,320,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17172 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17173 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 162 37 328 84 33 86 150 278), lower := (rows 11 162 37 328 84 33 64 128 256), losses := [] }

theorem u17173 : Upper (D 6) (R 6) [10,160,33,320,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17173 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17174 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 344, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 162 37 328 84 34 85 149 277), lower := (rows 11 162 37 328 84 34 64 128 256), losses := [] }

theorem u17174 : Upper (D 6) (R 6) [10,160,33,320,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17174 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17175 : Route 9 := (fun mask => (mask,id))

def c17175 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17175 : Upper (D 6) (R 6) [10,160,33,320,68,4] 13 := by
  apply FastRouting.sound _ _ [10,160,33,320,68,4] 13 (by decide) (choices 1) [1,2,16] r17175 c17175
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4542
  · exact u4543
  · exact u4544

def r17176 : Route 9 := (fun mask => (mask,id))

def c17176 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17176 : Upper (D 6) (R 6) [10,160,33,320,68,16] 13 := by
  apply FastRouting.sound _ _ [10,160,33,320,68,16] 13 (by decide) (choices 1) [1,2,4] r17176 c17176
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4545
  · exact u4546
  · exact u4547

def b17177 : PairBound 9 := { available := 324, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 52 13 81 34 324 452 324), lower := (rows 11 162 52 13 81 34 64 128 256), losses := [] }

theorem u17177 : Upper (D 6) (R 6) [10,160,48,5,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17177 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17178 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 44, targets := 66 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 11 162 52 13 81 36 322 450 322), lower := (rows 11 162 52 13 81 36 64 128 256), losses := [] }

theorem u17178 : Upper (D 6) (R 6) [10,160,48,5,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17178 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17179 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 162 52 13 81 96 326 390 262), lower := (rows 11 162 52 13 81 96 64 128 256), losses := [] }

theorem u17179 : Upper (D 6) (R 6) [10,160,48,5,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17179 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17180 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 422, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 162 52 13 81 288 70 198 326), lower := (rows 11 162 52 13 81 288 64 128 256), losses := [] }

theorem u17180 : Upper (D 6) (R 6) [10,160,48,5,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17180 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17181 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 45, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 162 52 13 82 33 324 452 324), lower := (rows 11 162 52 13 82 33 64 128 256), losses := [] }

theorem u17181 : Upper (D 6) (R 6) [10,160,48,5,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17181 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17182 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 45, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 162 52 13 82 36 321 449 321), lower := (rows 11 162 52 13 82 36 64 128 256), losses := [] }

theorem u17182 : Upper (D 6) (R 6) [10,160,48,5,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17182 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17183 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 162 52 13 82 96 325 389 261), lower := (rows 11 162 52 13 82 96 64 128 256), losses := [] }

theorem u17183 : Upper (D 6) (R 6) [10,160,48,5,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17183 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17184 : Route 9 := (fun mask => (mask,id))

def c17184 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17184 : Upper (D 6) (R 6) [10,160,48,5,66,256] 13 := by
  apply FastRouting.sound _ _ [10,160,48,5,66,256] 13 (by decide) (choices 1) [1,4] r17184 c17184
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4548
  · exact u4549

def b17185 : PairBound 9 := { available := 68, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 52 13 273 34 68 196 324), lower := (rows 11 162 52 13 273 34 64 128 256), losses := [] }

theorem u17185 : Upper (D 6) (R 6) [10,160,48,5,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17185 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17186 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 44, targets := 66 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 11 162 52 13 273 36 66 194 322), lower := (rows 11 162 52 13 273 36 64 128 256), losses := [] }

theorem u17186 : Upper (D 6) (R 6) [10,160,48,5,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17186 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17187 : Route 9 := (fun mask => (mask,id))

def c17187 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17187 : Upper (D 6) (R 6) [10,160,48,5,257,64] 13 := by
  apply FastRouting.sound _ _ [10,160,48,5,257,64] 13 (by decide) (choices 1) [2,4] r17187 c17187
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4550
  · exact u4551

def b17188 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 45, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 162 52 13 274 33 68 196 324), lower := (rows 11 162 52 13 274 33 64 128 256), losses := [] }

theorem u17188 : Upper (D 6) (R 6) [10,160,48,5,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17188 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17189 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 45, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 162 52 13 274 36 65 193 321), lower := (rows 11 162 52 13 274 36 64 128 256), losses := [] }

theorem u17189 : Upper (D 6) (R 6) [10,160,48,5,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17189 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17190 : Route 9 := (fun mask => (mask,id))

def c17190 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17190 : Upper (D 6) (R 6) [10,160,48,5,258,64] 13 := by
  apply FastRouting.sound _ _ [10,160,48,5,258,64] 13 (by decide) (choices 1) [1,4] r17190 c17190
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4552
  · exact u4553

def b17191 : PairBound 9 := { available := 70, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 52 13 336 33 70 198 326), lower := (rows 11 162 52 13 336 33 64 128 256), losses := [] }

theorem u17191 : Upper (D 6) (R 6) [10,160,48,5,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17191 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17192 : PairBound 9 := { available := 69, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 52 13 336 34 69 197 325), lower := (rows 11 162 52 13 336 34 64 128 256), losses := [] }

theorem u17192 : Upper (D 6) (R 6) [10,160,48,5,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17192 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17193 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 162 52 13 336 36 67 195 323), lower := (rows 11 162 52 13 336 36 64 128 256), losses := [] }

theorem u17193 : Upper (D 6) (R 6) [10,160,48,5,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17193 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17194 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 139, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 162 52 13 336 96 71 135 263), lower := (rows 11 162 52 13 336 96 64 128 256), losses := [] }

theorem u17194 : Upper (D 6) (R 6) [10,160,48,5,320,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17194 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17195 : PairBound 9 := { available := 324, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 52 73 21 34 324 452 324), lower := (rows 11 162 52 73 21 34 64 128 256), losses := [] }

theorem u17195 : Upper (D 6) (R 6) [10,160,48,65,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17195 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17196 : PairBound 9 := { available := 322, camps := [{ cop := 0, region := 52, targets := 66 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 11 162 52 73 21 36 322 450 322), lower := (rows 11 162 52 73 21 36 64 128 256), losses := [] }

theorem u17196 : Upper (D 6) (R 6) [10,160,48,65,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17196 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17197 : PairBound 9 := { available := 262, camps := [{ cop := 3, region := 52, targets := 2 },{ cop := 4, region := 482, targets := 1 }], pairs := [(1,0),(2,1),(4,1)], upper := (rows 11 162 52 73 21 96 326 390 262), lower := (rows 11 162 52 73 21 96 64 128 256), losses := [] }

theorem u17197 : Upper (D 6) (R 6) [10,160,48,65,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17197 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17198 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 486, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 162 52 73 21 288 70 198 326), lower := (rows 11 162 52 73 21 288 64 128 256), losses := [] }

theorem u17198 : Upper (D 6) (R 6) [10,160,48,65,5,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17198 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17199 : PairBound 9 := { available := 262, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 52 73 84 33 326 390 262), lower := (rows 11 162 52 73 84 33 64 128 256), losses := [] }

theorem u17199 : Upper (D 6) (R 6) [10,160,48,65,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17199 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17200 : PairBound 9 := { available := 261, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 52 73 84 34 325 389 261), lower := (rows 11 162 52 73 84 34 64 128 256), losses := [] }

theorem u17200 : Upper (D 6) (R 6) [10,160,48,65,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17200 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17201 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 329, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 162 52 73 84 36 323 387 259), lower := (rows 11 162 52 73 84 36 64 128 256), losses := [] }

theorem u17201 : Upper (D 6) (R 6) [10,160,48,65,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17201 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17202 : Route 9 := (fun mask => (mask,id))

def c17202 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17202 : Upper (D 6) (R 6) [10,160,48,65,68,256] 13 := by
  apply FastRouting.sound _ _ [10,160,48,65,68,256] 13 (by decide) (choices 1) [1,2,4] r17202 c17202
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4554
  · exact u4555
  · exact u4556

def b17203 : PairBound 9 := { available := 68, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 52 73 273 34 68 196 324), lower := (rows 11 162 52 73 273 34 64 128 256), losses := [] }

theorem u17203 : Upper (D 6) (R 6) [10,160,48,65,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17203 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17204 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 4, region := 36, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 11 162 52 73 273 36 70 198 326), lower := (rows 11 162 52 73 273 36 64 128 256), losses := [] }

theorem u17204 : Upper (D 6) (R 6) [10,160,48,65,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17204 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17205 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 2, region := 130, targets := 64 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 162 52 73 273 96 70 134 262), lower := (rows 11 162 52 73 273 96 64 128 256), losses := [] }

theorem u17205 : Upper (D 6) (R 6) [10,160,48,65,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17205 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17206 : PairBound 9 := { available := 68, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 52 73 274 33 68 196 324), lower := (rows 11 162 52 73 274 33 64 128 256), losses := [] }

theorem u17206 : Upper (D 6) (R 6) [10,160,48,65,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17206 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17207 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 162 52 73 274 36 69 197 325), lower := (rows 11 162 52 73 274 36 64 128 256), losses := [] }

theorem u17207 : Upper (D 6) (R 6) [10,160,48,65,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17207 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17208 : Route 9 := (fun mask => (mask,id))

def c17208 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17208 : Upper (D 6) (R 6) [10,160,48,65,258,64] 13 := by
  apply FastRouting.sound _ _ [10,160,48,65,258,64] 13 (by decide) (choices 1) [1,4] r17208 c17208
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4557
  · exact u4558

def b17209 : PairBound 9 := { available := 70, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 52 73 276 33 70 198 326), lower := (rows 11 162 52 73 276 33 64 128 256), losses := [] }

theorem u17209 : Upper (D 6) (R 6) [10,160,48,65,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17209 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17210 : PairBound 9 := { available := 69, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 52 73 276 34 69 197 325), lower := (rows 11 162 52 73 276 34 64 128 256), losses := [] }

theorem u17210 : Upper (D 6) (R 6) [10,160,48,65,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17210 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17211 : PairBound 9 := { available := 67, camps := [{ cop := 8, region := 52, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 162 52 73 276 36 67 195 323), lower := (rows 11 162 52 73 276 36 64 128 256), losses := [] }

theorem u17211 : Upper (D 6) (R 6) [10,160,48,65,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17211 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17212 : Route 9 := (fun mask => (mask,id))

def c17212 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17212 : Upper (D 6) (R 6) [10,160,48,65,260,64] 13 := by
  apply FastRouting.sound _ _ [10,160,48,65,260,64] 13 (by decide) (choices 1) [1,2,4] r17212 c17212
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4559
  · exact u4560
  · exact u4561

def b17213 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 52 73 336 33 70 134 262), lower := (rows 11 162 52 73 336 33 64 128 256), losses := [] }

theorem u17213 : Upper (D 6) (R 6) [10,160,48,65,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17213 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17214 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 52 73 336 34 69 133 261), lower := (rows 11 162 52 73 336 34 64 128 256), losses := [] }

theorem u17214 : Upper (D 6) (R 6) [10,160,48,65,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17214 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17215 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 162 52 73 336 36 71 135 263), lower := (rows 11 162 52 73 336 36 64 128 256), losses := [] }

theorem u17215 : Upper (D 6) (R 6) [10,160,48,65,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17215 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17216 : Route 9 := (fun mask => (mask,id))

def c17216 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u17216 : Upper (D 6) (R 6) [10,160,48,68,66,1] 13 := by
  apply FastRouting.sound _ _ [10,160,48,68,66,1] 13 (by decide) (choices 1) [1,4,256] r17216 c17216
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4562
  · exact u4563
  · exact u4564

def b17217 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 162 52 76 82 36 321 385 257), lower := (rows 11 162 52 76 82 36 64 128 256), losses := [] }

theorem u17217 : Upper (D 6) (R 6) [10,160,48,68,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17217 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17218 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 419, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 162 52 76 82 288 69 133 261), lower := (rows 11 162 52 76 82 288 64 128 256), losses := [] }

theorem u17218 : Upper (D 6) (R 6) [10,160,48,68,66,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17218 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17219 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 202, targets := 1 },{ cop := 4, region := 36, targets := 2 }], pairs := [(1,0),(2,1),(3,0)], upper := (rows 11 162 52 76 273 33 70 198 326), lower := (rows 11 162 52 76 273 33 64 128 256), losses := [] }

theorem u17219 : Upper (D 6) (R 6) [10,160,48,68,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17219 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u17219
end Delivery.IrregularNine14.P06

import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0143
import IrregularNine14P07C0144

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b25200 : PairBound 9 := { available := 138, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 4, region := 234, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,0)], upper := (rows 37 194 69 56 273 34 202 138 394), lower := (rows 37 194 69 56 273 34 64 128 256), losses := [] }

theorem u25200 : Upper (D 7) (R 7) [36,192,65,48,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25200 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25201 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 37 194 69 56 273 40 194 130 386), lower := (rows 37 194 69 56 273 40 64 128 256), losses := [] }

theorem u25201 : Upper (D 7) (R 7) [36,192,65,48,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25201 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25202 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 37, targets := 2 },{ cop := 4, region := 234, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(3,0)], upper := (rows 37 194 69 56 273 160 74 138 266), lower := (rows 37 194 69 56 273 160 64 128 256), losses := [] }

theorem u25202 : Upper (D 7) (R 7) [36,192,65,48,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25202 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25203 : PairBound 9 := { available := 138, camps := [{ cop := 3, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 37 194 69 56 274 33 202 138 394), lower := (rows 37 194 69 56 274 33 64 128 256), losses := [] }

theorem u25203 : Upper (D 7) (R 7) [36,192,65,48,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25203 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25204 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 40, targets := 193 },{ cop := 1, region := 37, targets := 128 }], pairs := [(0,7),(3,0),(3,6),(3,7)], upper := (rows 37 194 69 56 274 34 201 137 393), lower := (rows 37 194 69 56 274 34 64 128 256), losses := [] }

theorem u25204 : Upper (D 7) (R 7) [36,192,65,48,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25204 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25205 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 37 194 69 56 274 40 195 131 387), lower := (rows 37 194 69 56 274 40 64 128 256), losses := [] }

theorem u25205 : Upper (D 7) (R 7) [36,192,65,48,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25205 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25206 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 37, targets := 2 }], pairs := [(0,1),(2,1),(3,0),(3,1)], upper := (rows 37 194 69 56 274 160 75 139 267), lower := (rows 37 194 69 56 274 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 162 64 128 256), good := (rows 36 226 68 56 314 160 64 160 256) },{ target := 1, region := (rows 19 0 6 24 16 162 64 128 256), good := (rows 37 229 69 57 317 160 64 160 256) }] }

theorem u25206 : Upper (D 7) (R 7) [36,192,65,48,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25206 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25207 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 37 194 69 56 280 33 194 130 386), lower := (rows 37 194 69 56 280 33 64 128 256), losses := [] }

theorem u25207 : Upper (D 7) (R 7) [36,192,65,48,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25207 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25208 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 198, targets := 32 },{ cop := 1, region := 37, targets := 128 }], pairs := [(0,7),(1,5),(2,5),(2,7)], upper := (rows 37 194 69 56 280 34 195 131 387), lower := (rows 37 194 69 56 280 34 64 128 256), losses := [] }

theorem u25208 : Upper (D 7) (R 7) [36,192,65,48,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25208 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25209 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 198, targets := 32 },{ cop := 1, region := 37, targets := 2 }], pairs := [(0,1),(1,5),(2,1),(2,5)], upper := (rows 37 194 69 56 280 160 67 131 259), lower := (rows 37 194 69 56 280 160 64 128 256), losses := [] }

theorem u25209 : Upper (D 7) (R 7) [36,192,65,48,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25209 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25210 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 37 194 69 56 400 33 74 138 266), lower := (rows 37 194 69 56 400 33 64 128 256), losses := [] }

theorem u25210 : Upper (D 7) (R 7) [36,192,65,48,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25210 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25211 : Route 9 := (fun mask => (mask,id))

def c25211 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25211 : Upper (D 7) (R 7) [36,192,65,48,384,2] 13 := by
  apply FastRouting.sound _ _ [36,192,65,48,384,2] 13 (by decide) (choices 1) [1,2,8] r25211 c25211
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8618
  · exact u8619
  · exact u8620

def b25212 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 37 194 69 56 400 40 67 131 259), lower := (rows 37 194 69 56 400 40 64 128 256), losses := [] }

theorem u25212 : Upper (D 7) (R 7) [36,192,65,48,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25212 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25213 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 3, region := 370, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,0)], upper := (rows 37 194 69 137 274 34 120 184 312), lower := (rows 37 194 69 137 274 34 64 128 256), losses := [] }

theorem u25213 : Upper (D 7) (R 7) [36,192,65,129,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25213 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25214 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 45, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 37 194 69 137 274 40 114 178 306), lower := (rows 37 194 69 137 274 40 64 128 256), losses := [] }

theorem u25214 : Upper (D 7) (R 7) [36,192,65,129,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25214 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25215 : Route 9 := (fun mask => (mask,id))

def c25215 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25215 : Upper (D 7) (R 7) [36,192,65,129,258,16] 13 := by
  apply FastRouting.sound _ _ [36,192,65,129,258,16] 13 (by decide) (choices 1) [2,8,32] r25215 c25215
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8621
  · exact u8622
  · exact u8623

def b25216 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 3, region := 370, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,0)], upper := (rows 37 194 69 137 280 34 114 178 306), lower := (rows 37 194 69 137 280 34 64 128 256), losses := [] }

theorem u25216 : Upper (D 7) (R 7) [36,192,65,129,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25216 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25217 : Route 9 := (fun mask => (mask,id))

def c25217 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25217 : Upper (D 7) (R 7) [36,192,65,129,264,16] 13 := by
  apply FastRouting.sound _ _ [36,192,65,129,264,16] 13 (by decide) (choices 1) [2,32] r25217 c25217
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8624
  · exact u8625

def b25218 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 3, region := 370, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,0)], upper := (rows 37 194 69 137 304 34 90 154 282), lower := (rows 37 194 69 137 304 34 64 128 256), losses := [] }

theorem u25218 : Upper (D 7) (R 7) [36,192,65,129,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25218 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25219 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 45, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 37 194 69 137 304 40 82 146 274), lower := (rows 37 194 69 137 304 40 64 128 256), losses := [] }

theorem u25219 : Upper (D 7) (R 7) [36,192,65,129,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25219 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25220 : PairBound 9 := { available := 10, camps := [{ cop := 8, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 37 194 69 137 304 48 74 138 266), lower := (rows 37 194 69 137 304 48 64 128 256), losses := [] }

theorem u25220 : Upper (D 7) (R 7) [36,192,65,129,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25220 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25221 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 4, region := 234, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,0)], upper := (rows 37 194 69 152 273 34 106 170 298), lower := (rows 37 194 69 152 273 34 64 128 256), losses := [] }

theorem u25221 : Upper (D 7) (R 7) [36,192,65,144,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25221 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25222 : Route 9 := (fun mask => (mask,id))

def c25222 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25222 : Upper (D 7) (R 7) [36,192,65,144,257,8] 13 := by
  apply FastRouting.sound _ _ [36,192,65,144,257,8] 13 (by decide) (choices 1) [2,32] r25222 c25222
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8626
  · exact u8627

def b25223 : PairBound 9 := { available := 42, camps := [{ cop := 6, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 194 69 152 274 33 106 170 298), lower := (rows 37 194 69 152 274 33 64 128 256), losses := [] }

theorem u25223 : Upper (D 7) (R 7) [36,192,65,144,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25223 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25224 : Route 9 := (fun mask => (mask,id))

def c25224 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25224 : Upper (D 7) (R 7) [36,192,65,144,258,2] 13 := by
  apply FastRouting.sound _ _ [36,192,65,144,258,2] 13 (by decide) (choices 1) [1,8,32] r25224 c25224
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8628
  · exact u8629
  · exact u8630

def r25225 : Route 9 := (fun mask => (mask,id))

def c25225 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25225 : Upper (D 7) (R 7) [36,192,65,144,258,8] 13 := by
  apply FastRouting.sound _ _ [36,192,65,144,258,8] 13 (by decide) (choices 1) [1,2,32] r25225 c25225
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8631
  · exact u8632
  · exact u8633

def b25226 : PairBound 9 := { available := 34, camps := [{ cop := 6, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 194 69 152 280 33 98 162 290), lower := (rows 37 194 69 152 280 33 64 128 256), losses := [] }

theorem u25226 : Upper (D 7) (R 7) [36,192,65,144,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25226 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25227 : Route 9 := (fun mask => (mask,id))

def c25227 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25227 : Upper (D 7) (R 7) [36,192,65,144,264,2] 13 := by
  apply FastRouting.sound _ _ [36,192,65,144,264,2] 13 (by decide) (choices 1) [1,2,32] r25227 c25227
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8634
  · exact u8635
  · exact u8636

def b25228 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 202, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 37 194 69 152 304 33 74 138 266), lower := (rows 37 194 69 152 304 33 64 128 256), losses := [] }

theorem u25228 : Upper (D 7) (R 7) [36,192,65,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25228 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25229 : Route 9 := (fun mask => (mask,id))

def c25229 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25229 : Upper (D 7) (R 7) [36,192,65,144,288,2] 13 := by
  apply FastRouting.sound _ _ [36,192,65,144,288,2] 13 (by decide) (choices 1) [1,2,8] r25229 c25229
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8637
  · exact u8638
  · exact u8639

def r25230 : Route 9 := (fun mask => (mask,id))

def c25230 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25230 : Upper (D 7) (R 7) [36,192,65,144,288,8] 13 := by
  apply FastRouting.sound _ _ [36,192,65,144,288,8] 13 (by decide) (choices 1) [1,2] r25230 c25230
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8640
  · exact u8641

def b25231 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 40, targets := 65 },{ cop := 1, region := 37, targets := 128 }], pairs := [(0,7),(2,7),(3,0),(3,6)], upper := (rows 37 194 69 168 273 34 90 154 282), lower := (rows 37 194 69 168 273 34 64 128 256), losses := [] }

theorem u25231 : Upper (D 7) (R 7) [36,192,65,160,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25231 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25232 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 37 194 69 168 273 40 82 146 274), lower := (rows 37 194 69 168 273 40 64 128 256), losses := [] }

theorem u25232 : Upper (D 7) (R 7) [36,192,65,160,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25232 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25233 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 202, targets := 1 },{ cop := 3, region := 66, targets := 32 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 37 194 69 168 273 48 74 138 266), lower := (rows 37 194 69 168 273 48 64 128 256), losses := [] }

theorem u25233 : Upper (D 7) (R 7) [36,192,65,160,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25233 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25234 : PairBound 9 := { available := 26, camps := [{ cop := 3, region := 338, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 37 194 69 168 274 33 90 154 282), lower := (rows 37 194 69 168 274 33 64 128 256), losses := [] }

theorem u25234 : Upper (D 7) (R 7) [36,192,65,160,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25234 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25235 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 40, targets := 65 },{ cop := 1, region := 37, targets := 128 }], pairs := [(0,7),(2,7),(3,0),(3,6)], upper := (rows 37 194 69 168 274 34 89 153 281), lower := (rows 37 194 69 168 274 34 64 128 256), losses := [] }

theorem u25235 : Upper (D 7) (R 7) [36,192,65,160,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25235 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25236 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 37 194 69 168 274 40 83 147 275), lower := (rows 37 194 69 168 274 40 64 128 256), losses := [] }

theorem u25236 : Upper (D 7) (R 7) [36,192,65,160,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25236 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25237 : Route 9 := (fun mask => (mask,id))

def c25237 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25237 : Upper (D 7) (R 7) [36,192,65,160,258,16] 13 := by
  apply FastRouting.sound _ _ [36,192,65,160,258,16] 13 (by decide) (choices 1) [1,2,8] r25237 c25237
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8642
  · exact u8643
  · exact u8644

def b25238 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 338, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 37 194 69 168 280 33 82 146 274), lower := (rows 37 194 69 168 280 33 64 128 256), losses := [] }

theorem u25238 : Upper (D 7) (R 7) [36,192,65,160,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25238 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25239 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 40, targets := 65 },{ cop := 1, region := 37, targets := 128 }], pairs := [(0,7),(2,7),(3,0),(3,6)], upper := (rows 37 194 69 168 280 34 83 147 275), lower := (rows 37 194 69 168 280 34 64 128 256), losses := [] }

theorem u25239 : Upper (D 7) (R 7) [36,192,65,160,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25239 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25240 : Route 9 := (fun mask => (mask,id))

def c25240 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25240 : Upper (D 7) (R 7) [36,192,65,160,264,16] 13 := by
  apply FastRouting.sound _ _ [36,192,65,160,264,16] 13 (by decide) (choices 1) [1,2] r25240 c25240
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8645
  · exact u8646

def b25241 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 194 76 11 50 33 464 400 400), lower := (rows 37 194 76 11 50 33 64 128 256), losses := [] }

theorem u25241 : Upper (D 7) (R 7) [36,192,72,3,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25241 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25242 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 76 11 50 48 449 385 385), lower := (rows 37 194 76 11 50 48 64 128 256), losses := [] }

theorem u25242 : Upper (D 7) (R 7) [36,192,72,3,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25242 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25243 : PairBound 9 := { available := 273, camps := [{ cop := 4, region := 333, targets := 128 },{ cop := 1, region := 48, targets := 1 }], pairs := [(0,7),(2,7),(3,7),(4,0)], upper := (rows 37 194 76 11 50 160 337 401 273), lower := (rows 37 194 76 11 50 160 64 128 256), losses := [] }

theorem u25243 : Upper (D 7) (R 7) [36,192,72,3,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25243 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25244 : Route 9 := (fun mask => (mask,id))

def c25244 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u25244 : Upper (D 7) (R 7) [36,192,72,3,34,256] 13 := by
  apply FastRouting.sound _ _ [36,192,72,3,34,256] 13 (by decide) (choices 1) [1,16,128] r25244 c25244
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8647
  · exact u8648
  · exact u8649

def b25245 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 0, region := 400, targets := 2 }], pairs := [(0,7),(2,7),(3,7),(4,1)], upper := (rows 37 194 76 11 145 34 368 432 304), lower := (rows 37 194 76 11 145 34 64 128 256), losses := [] }

theorem u25245 : Upper (D 7) (R 7) [36,192,72,3,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25245 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25246 : PairBound 9 := { available := 290, camps := [{ cop := 0, region := 450, targets := 1 },{ cop := 3, region := 432, targets := 64 }], pairs := [(1,0),(2,0),(4,6)], upper := (rows 37 194 76 11 145 48 354 418 290), lower := (rows 37 194 76 11 145 48 64 128 256), losses := [{ target := 0, region := (rows 0 59 12 8 16 48 113 177 305), good := (rows 486 194 78 462 498 498 64 128 256) }] }

theorem u25246 : Upper (D 7) (R 7) [36,192,72,3,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25246 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25247 : PairBound 9 := { available := 50, camps := [{ cop := 3, region := 432, targets := 64 },{ cop := 4, region := 354, targets := 1 }], pairs := [(0,6),(1,0),(4,6)], upper := (rows 37 194 76 11 145 288 114 178 306), lower := (rows 37 194 76 11 145 288 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 8 28 300 0 136 264), good := (rows 53 130 445 443 145 288 0 128 288) }] }

theorem u25247 : Upper (D 7) (R 7) [36,192,72,3,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25247 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25248 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 0, region := 466, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 37 194 76 11 176 33 338 402 274), lower := (rows 37 194 76 11 176 33 64 128 256), losses := [] }

theorem u25248 : Upper (D 7) (R 7) [36,192,72,3,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25248 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25249 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 1, region := 48, targets := 1 }], pairs := [(0,7),(2,7),(3,7),(4,0)], upper := (rows 37 194 76 11 176 34 337 401 273), lower := (rows 37 194 76 11 176 34 64 128 256), losses := [] }

theorem u25249 : Upper (D 7) (R 7) [36,192,72,3,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25249 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25250 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 194 76 11 176 48 323 387 259), lower := (rows 37 194 76 11 176 48 64 128 256), losses := [] }

theorem u25250 : Upper (D 7) (R 7) [36,192,72,3,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25250 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25251 : Route 9 := (fun mask => (mask,id))

def c25251 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25251 : Upper (D 7) (R 7) [36,192,72,3,160,256] 13 := by
  apply FastRouting.sound _ _ [36,192,72,3,160,256] 13 (by decide) (choices 1) [1,2,16] r25251 c25251
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8650
  · exact u8651
  · exact u8652

def b25252 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 0, region := 400, targets := 2 }], pairs := [(0,7),(2,7),(3,7),(4,1)], upper := (rows 37 194 76 11 273 34 240 176 432), lower := (rows 37 194 76 11 273 34 64 128 256), losses := [] }

theorem u25252 : Upper (D 7) (R 7) [36,192,72,3,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25252 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25253 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 194, targets := 1 },{ cop := 3, region := 432, targets := 64 }], pairs := [(1,0),(2,0),(4,6)], upper := (rows 37 194 76 11 273 48 226 162 418), lower := (rows 37 194 76 11 273 48 64 128 256), losses := [{ target := 0, region := (rows 0 59 12 8 16 48 113 177 305), good := (rows 486 194 78 462 498 498 64 128 256) }] }

theorem u25253 : Upper (D 7) (R 7) [36,192,72,3,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25253 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25254 : Route 9 := (fun mask => (mask,id))

def c25254 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25254 : Upper (D 7) (R 7) [36,192,72,3,257,128] 13 := by
  apply FastRouting.sound _ _ [36,192,72,3,257,128] 13 (by decide) (choices 1) [2,16,32] r25254 c25254
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8653
  · exact u8654
  · exact u8655

def b25255 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 0, region := 466, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 37 194 76 11 274 33 240 176 432), lower := (rows 37 194 76 11 274 33 64 128 256), losses := [] }

theorem u25255 : Upper (D 7) (R 7) [36,192,72,3,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25255 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25256 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 432, targets := 64 }], pairs := [(0,6),(2,1),(4,6)], upper := (rows 37 194 76 11 274 48 225 161 417), lower := (rows 37 194 76 11 274 48 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 16 48 65 129 257), good := (rows 485 192 76 461 304 48 64 128 256) },{ target := 6, region := (rows 5 2 4 8 24 60 0 141 269), good := (rows 421 130 445 443 306 48 0 128 256) }] }

theorem u25256 : Upper (D 7) (R 7) [36,192,72,3,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25256 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25257 : Route 9 := (fun mask => (mask,id))

def c25257 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25257 : Upper (D 7) (R 7) [36,192,72,3,258,128] 13 := by
  apply FastRouting.sound _ _ [36,192,72,3,258,128] 13 (by decide) (choices 1) [1,16,32] r25257 c25257
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8656
  · exact u8657
  · exact u8658

def b25258 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 0, region := 466, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 37 194 76 11 304 33 210 146 402), lower := (rows 37 194 76 11 304 33 64 128 256), losses := [] }

theorem u25258 : Upper (D 7) (R 7) [36,192,72,3,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25258 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25259 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 0, region := 400, targets := 2 }], pairs := [(0,7),(2,7),(3,7),(4,1)], upper := (rows 37 194 76 11 304 34 209 145 401), lower := (rows 37 194 76 11 304 34 64 128 256), losses := [] }

theorem u25259 : Upper (D 7) (R 7) [36,192,72,3,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25259 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u25259
end Delivery.IrregularNine14.P07

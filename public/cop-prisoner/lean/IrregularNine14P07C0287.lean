import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0069

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b17220 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 148 392 49 96 67 131 259), lower := (rows 13 98 148 392 49 96 64 128 256), losses := [] }

theorem u17220 : Upper (D 7) (R 7) [12,96,144,384,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17220 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17221 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 13 98 164 200 273 33 82 146 274), lower := (rows 13 98 164 200 273 33 64 128 256), losses := [] }

theorem u17221 : Upper (D 7) (R 7) [12,96,160,192,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17221 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17222 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 370, targets := 128 },{ cop := 3, region := 38, targets := 1 }], pairs := [(1,0),(1,7),(2,0),(4,7)], upper := (rows 13 98 164 200 273 34 83 147 275), lower := (rows 13 98 164 200 273 34 64 128 256), losses := [] }

theorem u17222 : Upper (D 7) (R 7) [12,96,160,192,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17222 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m17223_1 : Upper (D 7) (R 7) [12,96,160,192,257,16,1] 13 :=
  permutation_upper _ _ _ [12,96,160,192,257,1,16] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4155

theorem m17223_2 : Upper (D 7) (R 7) [12,96,160,192,257,16,2] 13 :=
  permutation_upper _ _ _ [12,96,160,192,257,2,16] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4156

def r17223 : Route 9 := (fun mask => (mask,id))

def c17223 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17223 : Upper (D 7) (R 7) [12,96,160,192,257,16] 13 := by
  apply FastRouting.sound _ _ [12,96,160,192,257,16] 13 (by decide) (choices 1) [1,2] r17223 c17223
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m17223_1
  · exact m17223_2

def b17224 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 13 98 164 200 274 33 83 147 275), lower := (rows 13 98 164 200 274 33 64 128 256), losses := [] }

theorem u17224 : Upper (D 7) (R 7) [12,96,160,192,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17224 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17225 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 370, targets := 128 },{ cop := 3, region := 38, targets := 1 }], pairs := [(1,0),(1,7),(2,0),(4,7)], upper := (rows 13 98 164 200 274 34 81 145 273), lower := (rows 13 98 164 200 274 34 64 128 256), losses := [] }

theorem u17225 : Upper (D 7) (R 7) [12,96,160,192,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17225 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m17226_1 : Upper (D 7) (R 7) [12,96,160,192,258,16,1] 13 :=
  permutation_upper _ _ _ [12,96,160,192,258,1,16] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4157

theorem m17226_2 : Upper (D 7) (R 7) [12,96,160,192,258,16,2] 13 :=
  permutation_upper _ _ _ [12,96,160,192,258,2,16] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4158

def r17226 : Route 9 := (fun mask => (mask,id))

def c17226 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17226 : Upper (D 7) (R 7) [12,96,160,192,258,16] 13 := by
  apply FastRouting.sound _ _ [12,96,160,192,258,16] 13 (by decide) (choices 1) [1,2] r17226 c17226
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m17226_1
  · exact m17226_2

def b17227 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 4, region := 456, targets := 34 }], pairs := [(1,0),(2,0),(3,1),(3,5)], upper := (rows 13 98 164 265 19 34 208 208 464), lower := (rows 13 98 164 265 19 34 64 128 256), losses := [] }

theorem u17227 : Upper (D 7) (R 7) [12,96,160,257,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17227 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17228 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 4, region := 456, targets := 32 }], pairs := [(1,0),(2,0),(3,5)], upper := (rows 13 98 164 265 19 48 194 194 450), lower := (rows 13 98 164 265 19 48 64 128 256), losses := [] }

theorem u17228 : Upper (D 7) (R 7) [12,96,160,257,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17228 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17229 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 164 265 19 96 210 146 402), lower := (rows 13 98 164 265 19 96 64 128 256), losses := [] }

theorem u17229 : Upper (D 7) (R 7) [12,96,160,257,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17229 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17230 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 13 98 164 265 19 160 82 210 338), lower := (rows 13 98 164 265 19 160 64 128 256), losses := [] }

theorem u17230 : Upper (D 7) (R 7) [12,96,160,257,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17230 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17231 : Route 9 := (fun mask => (mask,id))

def c17231 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17231 : Upper (D 7) (R 7) [12,96,160,257,65,2] 13 := by
  apply FastRouting.sound _ _ [12,96,160,257,65,2] 13 (by decide) (choices 1) [2,16,128] r17231 c17231
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4159
  · exact u4160
  · exact u4161

def b17232 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 13 98 164 265 81 48 194 130 386), lower := (rows 13 98 164 265 81 48 64 128 256), losses := [] }

theorem u17232 : Upper (D 7) (R 7) [12,96,160,257,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17232 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17233 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 13 98 164 265 81 160 82 146 274), lower := (rows 13 98 164 265 81 160 64 128 256), losses := [] }

theorem u17233 : Upper (D 7) (R 7) [12,96,160,257,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17233 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17234 : PairBound 9 := { available := 82, camps := [{ cop := 5, region := 214, targets := 1 },{ cop := 1, region := 144, targets := 32 }], pairs := [(1,0),(2,0),(4,0),(4,5)], upper := (rows 13 98 164 265 146 33 82 210 338), lower := (rows 13 98 164 265 146 33 64 128 256), losses := [] }

theorem u17234 : Upper (D 7) (R 7) [12,96,160,257,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17234 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17235 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 36, targets := 65 },{ cop := 6, region := 34, targets := 129 }], pairs := [(1,0),(1,7),(2,0),(2,6)], upper := (rows 13 98 164 265 146 34 81 209 337), lower := (rows 13 98 164 265 146 34 64 128 256), losses := [] }

theorem u17235 : Upper (D 7) (R 7) [12,96,160,257,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17235 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17236 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 331, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 13 98 164 265 146 48 67 195 323), lower := (rows 13 98 164 265 146 48 64 128 256), losses := [] }

theorem u17236 : Upper (D 7) (R 7) [12,96,160,257,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17236 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17237 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 164 265 146 96 83 147 275), lower := (rows 13 98 164 265 146 96 64 128 256), losses := [] }

theorem u17237 : Upper (D 7) (R 7) [12,96,160,257,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17237 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17238 : PairBound 9 := { available := 18, camps := [{ cop := 5, region := 214, targets := 1 },{ cop := 1, region := 144, targets := 32 }], pairs := [(1,0),(2,0),(4,0),(4,5)], upper := (rows 13 98 164 265 208 33 82 146 274), lower := (rows 13 98 164 265 208 33 64 128 256), losses := [] }

theorem u17238 : Upper (D 7) (R 7) [12,96,160,257,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17238 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17239 : Route 9 := (fun mask => (mask,id))

def c17239 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17239 : Upper (D 7) (R 7) [12,96,160,257,192,2] 13 := by
  apply FastRouting.sound _ _ [12,96,160,257,192,2] 13 (by decide) (choices 1) [1,2,16] r17239 c17239
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4162
  · exact u4163
  · exact u4164

def b17240 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 13 98 164 265 208 48 67 131 259), lower := (rows 13 98 164 265 208 48 64 128 256), losses := [] }

theorem u17240 : Upper (D 7) (R 7) [12,96,160,257,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17240 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17241 : Route 9 := (fun mask => (mask,id))

def c17241 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17241 : Upper (D 7) (R 7) [12,96,160,258,3,1] 13 := by
  apply FastRouting.sound _ _ [12,96,160,258,3,1] 13 (by decide) (choices 1) [16,128] r17241 c17241
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4165
  · exact u4166

def r17242 : Route 9 := (fun mask => (mask,id))

def c17242 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17242 : Upper (D 7) (R 7) [12,96,160,258,3,16] 13 := by
  apply FastRouting.sound _ _ [12,96,160,258,3,16] 13 (by decide) (choices 1) [1,128] r17242 c17242
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4167
  · exact u4168

def b17243 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 164 266 19 96 209 145 401), lower := (rows 13 98 164 266 19 96 64 128 256), losses := [] }

theorem u17243 : Upper (D 7) (R 7) [12,96,160,258,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17243 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17244 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 13 98 164 266 19 160 81 209 337), lower := (rows 13 98 164 266 19 160 64 128 256), losses := [] }

theorem u17244 : Upper (D 7) (R 7) [12,96,160,258,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17244 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17245 : Route 9 := (fun mask => (mask,id))

def c17245 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17245 : Upper (D 7) (R 7) [12,96,160,258,65,1] 13 := by
  apply FastRouting.sound _ _ [12,96,160,258,65,1] 13 (by decide) (choices 1) [2,16,128] r17245 c17245
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4169
  · exact u4170
  · exact u4171

def b17246 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 208, targets := 34 },{ cop := 4, region := 34, targets := 129 }], pairs := [(1,0),(1,7),(4,1),(4,5)], upper := (rows 13 98 164 266 81 34 209 145 401), lower := (rows 13 98 164 266 81 34 64 128 256), losses := [] }

theorem u17246 : Upper (D 7) (R 7) [12,96,160,258,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17246 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17247 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 13 98 164 266 81 48 195 131 387), lower := (rows 13 98 164 266 81 48 64 128 256), losses := [] }

theorem u17247 : Upper (D 7) (R 7) [12,96,160,258,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17247 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17248 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 13 98 164 266 81 160 83 147 275), lower := (rows 13 98 164 266 81 160 64 128 256), losses := [] }

theorem u17248 : Upper (D 7) (R 7) [12,96,160,258,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17248 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17249 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 36, targets := 66 },{ cop := 4, region := 362, targets := 128 }], pairs := [(1,7),(2,1),(2,6),(3,7)], upper := (rows 13 98 164 266 145 33 82 210 338), lower := (rows 13 98 164 266 145 33 64 128 256), losses := [] }

theorem u17249 : Upper (D 7) (R 7) [12,96,160,258,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17249 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17250 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 208, targets := 34 },{ cop := 4, region := 362, targets := 128 }], pairs := [(1,7),(3,7),(4,1),(4,5)], upper := (rows 13 98 164 266 145 34 81 209 337), lower := (rows 13 98 164 266 145 34 64 128 256), losses := [] }

theorem u17250 : Upper (D 7) (R 7) [12,96,160,258,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17250 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17251 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 331, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 13 98 164 266 145 48 67 195 323), lower := (rows 13 98 164 266 145 48 64 128 256), losses := [] }

theorem u17251 : Upper (D 7) (R 7) [12,96,160,258,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17251 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17252 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 164 266 145 96 83 147 275), lower := (rows 13 98 164 266 145 96 64 128 256), losses := [] }

theorem u17252 : Upper (D 7) (R 7) [12,96,160,258,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17252 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17253 : Route 9 := (fun mask => (mask,id))

def c17253 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17253 : Upper (D 7) (R 7) [12,96,160,258,130,1] 13 := by
  apply FastRouting.sound _ _ [12,96,160,258,130,1] 13 (by decide) (choices 1) [1,16] r17253 c17253
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4172
  · exact u4173

def b17254 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 331, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 13 98 164 266 146 48 65 193 321), lower := (rows 13 98 164 266 146 48 64 128 256), losses := [] }

theorem u17254 : Upper (D 7) (R 7) [12,96,160,258,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17254 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17255 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 164 266 146 96 81 145 273), lower := (rows 13 98 164 266 146 96 64 128 256), losses := [] }

theorem u17255 : Upper (D 7) (R 7) [12,96,160,258,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17255 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17256 : Route 9 := (fun mask => (mask,id))

def c17256 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17256 : Upper (D 7) (R 7) [12,96,160,258,192,1] 13 := by
  apply FastRouting.sound _ _ [12,96,160,258,192,1] 13 (by decide) (choices 1) [1,2,16] r17256 c17256
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4174
  · exact u4175
  · exact u4176

def b17257 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 208, targets := 34 },{ cop := 4, region := 38, targets := 1 }], pairs := [(1,0),(2,0),(4,1),(4,5)], upper := (rows 13 98 164 266 208 34 81 145 273), lower := (rows 13 98 164 266 208 34 64 128 256), losses := [] }

theorem u17257 : Upper (D 7) (R 7) [12,96,160,258,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17257 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17258 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 13 98 164 266 208 48 67 131 259), lower := (rows 13 98 164 266 208 48 64 128 256), losses := [] }

theorem u17258 : Upper (D 7) (R 7) [12,96,160,258,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17258 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17259 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 456, targets := 33 },{ cop := 5, region := 198, targets := 1 }], pairs := [(1,0),(2,0),(3,0),(3,5)], upper := (rows 13 98 164 280 19 33 194 194 450), lower := (rows 13 98 164 280 19 33 64 128 256), losses := [] }

theorem u17259 : Upper (D 7) (R 7) [12,96,160,272,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17259 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17260 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 456, targets := 34 },{ cop := 6, region := 34, targets := 129 }], pairs := [(1,0),(1,7),(3,1),(3,5)], upper := (rows 13 98 164 280 19 34 193 193 449), lower := (rows 13 98 164 280 19 34 64 128 256), losses := [] }

theorem u17260 : Upper (D 7) (R 7) [12,96,160,272,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17260 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17261 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 164 280 19 96 195 131 387), lower := (rows 13 98 164 280 19 96 64 128 256), losses := [] }

theorem u17261 : Upper (D 7) (R 7) [12,96,160,272,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17261 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17262 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 13 98 164 280 19 160 67 195 323), lower := (rows 13 98 164 280 19 160 64 128 256), losses := [] }

theorem u17262 : Upper (D 7) (R 7) [12,96,160,272,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17262 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17263 : PairBound 9 := { available := 130, camps := [{ cop := 5, region := 198, targets := 1 },{ cop := 1, region := 132, targets := 64 },{ cop := 4, region := 34, targets := 128 }], pairs := [(1,0),(1,7),(2,0),(2,6)], upper := (rows 13 98 164 280 81 33 194 130 386), lower := (rows 13 98 164 280 81 33 64 128 256), losses := [] }

theorem u17263 : Upper (D 7) (R 7) [12,96,160,272,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17263 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17264 : Route 9 := (fun mask => (mask,id))

def c17264 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17264 : Upper (D 7) (R 7) [12,96,160,272,65,2] 13 := by
  apply FastRouting.sound _ _ [12,96,160,272,65,2] 13 (by decide) (choices 1) [1,2,128] r17264 c17264
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4177
  · exact u4178
  · exact u4179

def b17265 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 13 98 164 280 81 160 67 131 259), lower := (rows 13 98 164 280 81 160 64 128 256), losses := [] }

theorem u17265 : Upper (D 7) (R 7) [12,96,160,272,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17265 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17266 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 36, targets := 66 },{ cop := 4, region := 362, targets := 128 }], pairs := [(1,7),(2,1),(2,6),(3,7)], upper := (rows 13 98 164 280 145 33 66 194 322), lower := (rows 13 98 164 280 145 33 64 128 256), losses := [] }

theorem u17266 : Upper (D 7) (R 7) [12,96,160,272,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17266 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17267 : Route 9 := (fun mask => (mask,id))

def c17267 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17267 : Upper (D 7) (R 7) [12,96,160,272,129,2] 13 := by
  apply FastRouting.sound _ _ [12,96,160,272,129,2] 13 (by decide) (choices 1) [1,2] r17267 c17267
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4180
  · exact u4181

def b17268 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 164 280 145 96 67 131 259), lower := (rows 13 98 164 280 145 96 64 128 256), losses := [] }

theorem u17268 : Upper (D 7) (R 7) [12,96,160,272,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17268 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17269 : Route 9 := (fun mask => (mask,id))

def c17269 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17269 : Upper (D 7) (R 7) [12,96,160,272,130,1] 13 := by
  apply FastRouting.sound _ _ [12,96,160,272,130,1] 13 (by decide) (choices 1) [1,2] r17269 c17269
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4182
  · exact u4183

def b17270 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 36, targets := 65 },{ cop := 6, region := 34, targets := 129 }], pairs := [(1,0),(1,7),(2,0),(2,6)], upper := (rows 13 98 164 280 146 34 65 193 321), lower := (rows 13 98 164 280 146 34 64 128 256), losses := [] }

theorem u17270 : Upper (D 7) (R 7) [12,96,160,272,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17270 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17271 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 164 280 146 96 67 131 259), lower := (rows 13 98 164 280 146 96 64 128 256), losses := [] }

theorem u17271 : Upper (D 7) (R 7) [12,96,160,272,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17271 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17272 : Route 9 := (fun mask => (mask,id))

def c17272 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17272 : Upper (D 7) (R 7) [12,96,160,272,192,1] 13 := by
  apply FastRouting.sound _ _ [12,96,160,272,192,1] 13 (by decide) (choices 1) [1,2] r17272 c17272
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4184
  · exact u4185

def r17273 : Route 9 := (fun mask => (mask,id))

def c17273 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17273 : Upper (D 7) (R 7) [12,96,160,272,192,2] 13 := by
  apply FastRouting.sound _ _ [12,96,160,272,192,2] 13 (by decide) (choices 1) [1,2] r17273 c17273
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4186
  · exact u4187

def r17274 : Route 9 := (fun mask => (mask,id))

def c17274 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17274 : Upper (D 7) (R 7) [12,96,160,320,3,1] 13 := by
  apply FastRouting.sound _ _ [12,96,160,320,3,1] 13 (by decide) (choices 1) [2,16,128] r17274 c17274
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4188
  · exact u4189
  · exact u4190

def b17275 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 34, targets := 129 },{ cop := 4, region := 456, targets := 34 }], pairs := [(1,0),(1,7),(3,1),(3,5)], upper := (rows 13 98 164 328 19 34 209 145 401), lower := (rows 13 98 164 328 19 34 64 128 256), losses := [] }

theorem u17275 : Upper (D 7) (R 7) [12,96,160,320,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17275 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17276 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 456, targets := 32 },{ cop := 4, region := 164, targets := 64 }], pairs := [(0,5),(2,6),(3,5)], upper := (rows 13 98 164 328 19 48 195 131 387), lower := (rows 13 98 164 328 19 48 64 128 256), losses := [{ target := 5, region := (rows 5 2 4 56 16 0 80 144 272), good := (rows 13 74 141 328 475 472 64 128 256) }] }

theorem u17276 : Upper (D 7) (R 7) [12,96,160,320,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17276 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17277 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 13 98 164 328 19 160 83 147 275), lower := (rows 13 98 164 328 19 160 64 128 256), losses := [] }

theorem u17277 : Upper (D 7) (R 7) [12,96,160,320,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17277 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17278 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 36, targets := 66 },{ cop := 4, region := 362, targets := 128 }], pairs := [(1,7),(2,1),(2,6),(3,7)], upper := (rows 13 98 164 328 145 33 82 146 274), lower := (rows 13 98 164 328 145 33 64 128 256), losses := [] }

theorem u17278 : Upper (D 7) (R 7) [12,96,160,320,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17278 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17279 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 34, targets := 129 },{ cop := 4, region := 362, targets := 128 }], pairs := [(1,0),(1,7),(2,0),(3,7)], upper := (rows 13 98 164 328 145 34 83 147 275), lower := (rows 13 98 164 328 145 34 64 128 256), losses := [{ target := 0, region := (rows 0 74 20 8 16 107 64 128 256), good := (rows 46 98 164 362 180 34 98 128 256) }] }

theorem u17279 : Upper (D 7) (R 7) [12,96,160,320,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17279 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u17279
end Delivery.IrregularNine14.P07

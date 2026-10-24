import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0088

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b18180 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 386 38 104 84 48 69 133 261), lower := (rows 11 386 38 104 84 48 64 128 256), losses := [] }

theorem u18180 : Upper (D 6) (R 6) [10,384,34,96,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18180 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18181 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 422, targets := 1 }], pairs := [(1,0),(2,0),(4,1)], upper := (rows 11 386 52 13 81 34 100 228 356), lower := (rows 11 386 52 13 81 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 24 32 68 132 260), good := (rows 25 384 500 477 81 32 64 128 256) }] }

theorem u18181 : Upper (D 6) (R 6) [10,384,48,5,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18181 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18182 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 44, targets := 66 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 11 386 52 13 81 36 98 226 354), lower := (rows 11 386 52 13 81 36 64 128 256), losses := [] }

theorem u18182 : Upper (D 6) (R 6) [10,384,48,5,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18182 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18183 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 386 52 13 81 96 102 166 294), lower := (rows 11 386 52 13 81 96 64 128 256), losses := [] }

theorem u18183 : Upper (D 6) (R 6) [10,384,48,5,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18183 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18184 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 45, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 386 52 13 82 33 100 228 356), lower := (rows 11 386 52 13 82 33 64 128 256), losses := [] }

theorem u18184 : Upper (D 6) (R 6) [10,384,48,5,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18184 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18185 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 45, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 386 52 13 82 36 97 225 353), lower := (rows 11 386 52 13 82 36 64 128 256), losses := [] }

theorem u18185 : Upper (D 6) (R 6) [10,384,48,5,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18185 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18186 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 386 52 13 82 96 101 165 293), lower := (rows 11 386 52 13 82 96 64 128 256), losses := [] }

theorem u18186 : Upper (D 6) (R 6) [10,384,48,5,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18186 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18187 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 386 52 13 84 33 98 226 354), lower := (rows 11 386 52 13 84 33 64 128 256), losses := [] }

theorem u18187 : Upper (D 6) (R 6) [10,384,48,5,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18187 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18188 : Route 9 := (fun mask => (mask,id))

def c18188 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18188 : Upper (D 6) (R 6) [10,384,48,5,68,2] 13 := by
  apply FastRouting.sound _ _ [10,384,48,5,68,2] 13 (by decide) (choices 1) [1,32] r18188 c18188
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5289
  · exact u5290

def b18189 : PairBound 9 := { available := 35, camps := [{ cop := 5, region := 20, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 386 52 13 84 96 99 163 291), lower := (rows 11 386 52 13 84 96 64 128 256), losses := [] }

theorem u18189 : Upper (D 6) (R 6) [10,384,48,5,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18189 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18190 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 386 52 41 82 33 68 196 324), lower := (rows 11 386 52 41 82 33 64 128 256), losses := [] }

theorem u18190 : Upper (D 6) (R 6) [10,384,48,33,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18190 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18191 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 45, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 386 52 41 82 36 69 197 325), lower := (rows 11 386 52 41 82 36 64 128 256), losses := [] }

theorem u18191 : Upper (D 6) (R 6) [10,384,48,33,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18191 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18192 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 386 52 41 82 96 69 133 261), lower := (rows 11 386 52 41 82 96 64 128 256), losses := [] }

theorem u18192 : Upper (D 6) (R 6) [10,384,48,33,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18192 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18193 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 386 52 41 84 33 70 198 326), lower := (rows 11 386 52 41 84 33 64 128 256), losses := [] }

theorem u18193 : Upper (D 6) (R 6) [10,384,48,33,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18193 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18194 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 386 52 41 84 34 69 197 325), lower := (rows 11 386 52 41 84 34 64 128 256), losses := [] }

theorem u18194 : Upper (D 6) (R 6) [10,384,48,33,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18194 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18195 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 451, targets := 36 }], pairs := [(0,2),(0,5),(1,2)], upper := (rows 11 386 52 41 84 36 67 195 323), lower := (rows 11 386 52 41 84 36 64 128 256), losses := [] }

theorem u18195 : Upper (D 6) (R 6) [10,384,48,33,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18195 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18196 : PairBound 9 := { available := 7, camps := [{ cop := 5, region := 20, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 386 52 41 84 96 71 135 263), lower := (rows 11 386 52 41 84 96 64 128 256), losses := [] }

theorem u18196 : Upper (D 6) (R 6) [10,384,48,33,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18196 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18197 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 52, targets := 64 },{ cop := 4, region := 482, targets := 1 }], pairs := [(1,0),(2,6),(4,6)], upper := (rows 11 386 52 73 21 34 100 228 356), lower := (rows 11 386 52 73 21 34 64 128 256), losses := [] }

theorem u18197 : Upper (D 6) (R 6) [10,384,48,65,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18197 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18198 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 52, targets := 66 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 11 386 52 73 21 36 98 226 354), lower := (rows 11 386 52 73 21 36 64 128 256), losses := [] }

theorem u18198 : Upper (D 6) (R 6) [10,384,48,65,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18198 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18199 : PairBound 9 := { available := 38, camps := [{ cop := 3, region := 52, targets := 2 },{ cop := 4, region := 482, targets := 1 }], pairs := [(1,0),(2,1),(4,1)], upper := (rows 11 386 52 73 21 96 102 166 294), lower := (rows 11 386 52 73 21 96 64 128 256), losses := [] }

theorem u18199 : Upper (D 6) (R 6) [10,384,48,65,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18199 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18200 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 386 52 73 22 33 100 228 356), lower := (rows 11 386 52 73 22 33 64 128 256), losses := [] }

theorem u18200 : Upper (D 6) (R 6) [10,384,48,65,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18200 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18201 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 52, targets := 65 }], pairs := [(2,0),(2,6),(4,0)], upper := (rows 11 386 52 73 22 36 97 225 353), lower := (rows 11 386 52 73 22 36 64 128 256), losses := [] }

theorem u18201 : Upper (D 6) (R 6) [10,384,48,65,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18201 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18202 : Route 9 := (fun mask => (mask,id))

def c18202 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18202 : Upper (D 6) (R 6) [10,384,48,65,6,64] 13 := by
  apply FastRouting.sound _ _ [10,384,48,65,6,64] 13 (by decide) (choices 1) [1,4,32] r18202 c18202
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5291
  · exact u5292
  · exact u5293

def b18203 : PairBound 9 := { available := 38, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 386 52 73 84 33 102 166 294), lower := (rows 11 386 52 73 84 33 64 128 256), losses := [] }

theorem u18203 : Upper (D 6) (R 6) [10,384,48,65,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18203 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18204 : Route 9 := (fun mask => (mask,id))

def c18204 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18204 : Upper (D 6) (R 6) [10,384,48,65,68,2] 13 := by
  apply FastRouting.sound _ _ [10,384,48,65,68,2] 13 (by decide) (choices 1) [1,4,32] r18204 c18204
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5294
  · exact u5295
  · exact u5296

def b18205 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 52, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 386 52 73 84 36 99 163 291), lower := (rows 11 386 52 73 84 36 64 128 256), losses := [] }

theorem u18205 : Upper (D 6) (R 6) [10,384,48,65,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18205 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18206 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 52, targets := 66 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 11 386 52 76 21 33 98 226 354), lower := (rows 11 386 52 76 21 33 64 128 256), losses := [] }

theorem u18206 : Upper (D 6) (R 6) [10,384,48,68,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18206 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18207 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 52, targets := 64 },{ cop := 3, region := 419, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 386 52 76 21 34 97 225 353), lower := (rows 11 386 52 76 21 34 64 128 256), losses := [] }

theorem u18207 : Upper (D 6) (R 6) [10,384,48,68,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18207 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18208 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 419, targets := 4 }], pairs := [(0,2),(1,2),(2,1)], upper := (rows 11 386 52 76 21 96 99 163 291), lower := (rows 11 386 52 76 21 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 8 17 104 64 128 256), good := (rows 61 384 52 108 21 96 96 128 256) }] }

theorem u18208 : Upper (D 6) (R 6) [10,384,48,68,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18208 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18209 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 52, targets := 64 },{ cop := 3, region := 419, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 386 52 76 22 33 97 225 353), lower := (rows 11 386 52 76 22 33 64 128 256), losses := [] }

theorem u18209 : Upper (D 6) (R 6) [10,384,48,68,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18209 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18210 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 419, targets := 4 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 11 386 52 76 22 96 97 161 289), lower := (rows 11 386 52 76 22 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 5 8 17 104 64 128 256), good := (rows 62 386 52 108 22 96 96 128 256) }] }

theorem u18210 : Upper (D 6) (R 6) [10,384,48,68,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18210 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18211 : Route 9 := (fun mask => (mask,id))

def c18211 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18211 : Upper (D 6) (R 6) [10,384,48,68,66,1] 13 := by
  apply FastRouting.sound _ _ [10,384,48,68,66,1] 13 (by decide) (choices 1) [1,4,32] r18211 c18211
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5297
  · exact u5298
  · exact u5299

def b18212 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 386 52 76 82 36 97 161 289), lower := (rows 11 386 52 76 82 36 64 128 256), losses := [] }

theorem u18212 : Upper (D 6) (R 6) [10,384,48,68,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18212 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18213 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 52, targets := 66 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 11 386 52 104 21 33 70 198 326), lower := (rows 11 386 52 104 21 33 64 128 256), losses := [] }

theorem u18213 : Upper (D 6) (R 6) [10,384,48,96,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18213 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18214 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 52, targets := 64 },{ cop := 4, region := 450, targets := 32 }], pairs := [(1,5),(2,6),(4,6)], upper := (rows 11 386 52 104 21 34 69 197 325), lower := (rows 11 386 52 104 21 34 64 128 256), losses := [] }

theorem u18214 : Upper (D 6) (R 6) [10,384,48,96,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18214 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18215 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 52, targets := 66 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 11 386 52 104 21 36 67 195 323), lower := (rows 11 386 52 104 21 36 64 128 256), losses := [] }

theorem u18215 : Upper (D 6) (R 6) [10,384,48,96,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18215 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18216 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 386 52 104 21 96 71 135 263), lower := (rows 11 386 52 104 21 96 64 128 256), losses := [] }

theorem u18216 : Upper (D 6) (R 6) [10,384,48,96,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18216 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18217 : Route 9 := (fun mask => (mask,id))

def c18217 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18217 : Upper (D 6) (R 6) [10,384,48,96,6,1] 13 := by
  apply FastRouting.sound _ _ [10,384,48,96,6,1] 13 (by decide) (choices 1) [1,4] r18217 c18217
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5300
  · exact u5301

def b18218 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 52, targets := 65 }], pairs := [(2,0),(2,6),(4,0)], upper := (rows 11 386 52 104 22 36 65 193 321), lower := (rows 11 386 52 104 22 36 64 128 256), losses := [] }

theorem u18218 : Upper (D 6) (R 6) [10,384,48,96,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18218 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18219 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 386 52 104 22 96 69 133 261), lower := (rows 11 386 52 104 22 96 64 128 256), losses := [] }

theorem u18219 : Upper (D 6) (R 6) [10,384,48,96,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18219 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18220 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 458, targets := 1 },{ cop := 4, region := 36, targets := 2 }], pairs := [(1,0),(2,1),(3,0)], upper := (rows 11 386 52 104 81 33 70 134 262), lower := (rows 11 386 52 104 81 33 64 128 256), losses := [] }

theorem u18220 : Upper (D 6) (R 6) [10,384,48,96,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18220 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18221 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(2,0),(2,6)], upper := (rows 11 386 52 104 81 34 69 133 261), lower := (rows 11 386 52 104 81 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 35 64 128 256), good := (rows 42 418 60 104 124 34 64 128 256) }] }

theorem u18221 : Upper (D 6) (R 6) [10,384,48,96,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18221 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18222 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 386 52 104 81 36 71 135 263), lower := (rows 11 386 52 104 81 36 64 128 256), losses := [] }

theorem u18222 : Upper (D 6) (R 6) [10,384,48,96,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18222 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18223 : Route 9 := (fun mask => (mask,id))

def c18223 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18223 : Upper (D 6) (R 6) [10,384,48,96,66,1] 13 := by
  apply FastRouting.sound _ _ [10,384,48,96,66,1] 13 (by decide) (choices 1) [1,4] r18223 c18223
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5302
  · exact u5303

def b18224 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 386 52 104 82 36 69 133 261), lower := (rows 11 386 52 104 82 36 64 128 256), losses := [] }

theorem u18224 : Upper (D 6) (R 6) [10,384,48,96,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18224 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18225 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 48, targets := 68 },{ cop := 4, region := 454, targets := 1 }], pairs := [(1,0),(4,2),(4,6)], upper := (rows 11 386 100 13 49 34 84 212 340), lower := (rows 11 386 100 13 49 34 64 128 256), losses := [] }

theorem u18225 : Upper (D 6) (R 6) [10,384,96,5,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18225 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18226 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 48, targets := 66 },{ cop := 4, region := 450, targets := 1 }], pairs := [(1,0),(4,1),(4,6)], upper := (rows 11 386 100 13 49 36 82 210 338), lower := (rows 11 386 100 13 49 36 64 128 256), losses := [] }

theorem u18226 : Upper (D 6) (R 6) [10,384,96,5,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18226 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18227 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 48, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 386 100 13 49 48 70 198 326), lower := (rows 11 386 100 13 49 48 64 128 256), losses := [] }

theorem u18227 : Upper (D 6) (R 6) [10,384,96,5,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18227 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18228 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 386 100 13 49 96 86 150 278), lower := (rows 11 386 100 13 49 96 64 128 256), losses := [] }

theorem u18228 : Upper (D 6) (R 6) [10,384,96,5,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18228 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18229 : PairBound 9 := { available := 84, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 386 100 13 50 33 84 212 340), lower := (rows 11 386 100 13 50 33 64 128 256), losses := [] }

theorem u18229 : Upper (D 6) (R 6) [10,384,96,5,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18229 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18230 : PairBound 9 := { available := 81, camps := [{ cop := 6, region := 36, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 386 100 13 50 36 81 209 337), lower := (rows 11 386 100 13 50 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 68 8 17 108 64 128 256), good := (rows 58 386 100 60 50 36 100 128 256) }] }

theorem u18230 : Upper (D 6) (R 6) [10,384,96,5,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18230 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18231 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 48, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 11 386 100 13 50 48 69 197 325), lower := (rows 11 386 100 13 50 48 64 128 256), losses := [] }

theorem u18231 : Upper (D 6) (R 6) [10,384,96,5,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18231 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18232 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 386 100 13 50 96 85 149 277), lower := (rows 11 386 100 13 50 96 64 128 256), losses := [] }

theorem u18232 : Upper (D 6) (R 6) [10,384,96,5,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18232 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18233 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 48, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 11 386 100 28 49 33 70 198 326), lower := (rows 11 386 100 28 49 33 64 128 256), losses := [] }

theorem u18233 : Upper (D 6) (R 6) [10,384,96,20,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18233 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18234 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 48, targets := 68 },{ cop := 3, region := 451, targets := 32 }], pairs := [(0,5),(4,2),(4,6)], upper := (rows 11 386 100 28 49 34 69 197 325), lower := (rows 11 386 100 28 49 34 64 128 256), losses := [] }

theorem u18234 : Upper (D 6) (R 6) [10,384,96,20,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18234 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18235 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 451, targets := 36 }], pairs := [(0,2),(0,5),(1,2)], upper := (rows 11 386 100 28 49 36 67 195 323), lower := (rows 11 386 100 28 49 36 64 128 256), losses := [] }

theorem u18235 : Upper (D 6) (R 6) [10,384,96,20,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18235 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18236 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 386 100 28 49 96 71 135 263), lower := (rows 11 386 100 28 49 96 64 128 256), losses := [] }

theorem u18236 : Upper (D 6) (R 6) [10,384,96,20,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18236 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18237 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 386 100 41 22 33 84 212 340), lower := (rows 11 386 100 41 22 33 64 128 256), losses := [] }

theorem u18237 : Upper (D 6) (R 6) [10,384,96,33,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18237 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18238 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 41, targets := 64 },{ cop := 6, region := 36, targets := 1 }], pairs := [(0,6),(2,0),(3,6)], upper := (rows 11 386 100 41 22 36 81 209 337), lower := (rows 11 386 100 41 22 36 64 128 256), losses := [] }

theorem u18238 : Upper (D 6) (R 6) [10,384,96,33,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18238 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18239 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 11 386 100 41 22 48 69 197 325), lower := (rows 11 386 100 41 22 48 64 128 256), losses := [] }

theorem u18239 : Upper (D 6) (R 6) [10,384,96,33,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18239 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u18239
end Delivery.IrregularNine14.P06

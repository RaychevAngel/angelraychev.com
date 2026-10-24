import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0051

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b14160 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 460, targets := 1 },{ cop := 4, region := 34, targets := 4 }], pairs := [(1,2),(2,0),(3,0)], upper := (rows 11 50 70 392 21 33 100 228 356), lower := (rows 11 50 70 392 21 33 64 128 256), losses := [] }

theorem u14160 : Upper (D 6) (R 6) [10,48,66,384,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14160 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14161 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 457, targets := 4 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 11 50 70 392 21 36 97 225 353), lower := (rows 11 50 70 392 21 36 64 128 256), losses := [] }

theorem u14161 : Upper (D 6) (R 6) [10,48,66,384,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14161 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14162 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 488, targets := 2 }], pairs := [(1,0),(1,2),(3,1)], upper := (rows 11 50 70 392 21 96 101 165 293), lower := (rows 11 50 70 392 21 96 64 128 256), losses := [{ target := 0, region := (rows 0 18 4 8 16 100 64 128 256), good := (rows 10 50 102 392 54 96 96 128 256) },{ target := 2, region := (rows 1 18 0 8 16 100 64 128 256), good := (rows 11 50 98 392 51 96 96 128 256) }] }

theorem u14162 : Upper (D 6) (R 6) [10,48,66,384,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14162 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14163 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 460, targets := 1 },{ cop := 2, region := 425, targets := 64 }], pairs := [(0,6),(2,0),(3,0)], upper := (rows 11 50 70 392 81 33 100 164 292), lower := (rows 11 50 70 392 81 33 64 128 256), losses := [] }

theorem u14163 : Upper (D 6) (R 6) [10,48,66,384,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14163 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14164 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 425, targets := 64 },{ cop := 4, region := 38, targets := 1 }], pairs := [(0,6),(1,0),(3,6)], upper := (rows 11 50 70 392 81 36 101 165 293), lower := (rows 11 50 70 392 81 36 64 128 256), losses := [] }

theorem u14164 : Upper (D 6) (R 6) [10,48,66,384,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14164 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14165 : PairBound 9 := { available := 388, camps := [{ cop := 3, region := 464, targets := 34 },{ cop := 4, region := 34, targets := 1 }], pairs := [(1,0),(4,1),(4,5)], upper := (rows 11 50 100 13 81 34 452 388 388), lower := (rows 11 50 100 13 81 34 64 128 256), losses := [] }

theorem u14165 : Upper (D 6) (R 6) [10,48,96,5,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14165 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14166 : PairBound 9 := { available := 386, camps := [{ cop := 0, region := 464, targets := 36 },{ cop := 4, region := 38, targets := 1 }], pairs := [(1,0),(4,2),(4,5)], upper := (rows 11 50 100 13 81 36 450 386 386), lower := (rows 11 50 100 13 81 36 64 128 256), losses := [] }

theorem u14166 : Upper (D 6) (R 6) [10,48,96,5,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14166 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14167 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 422, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 50 100 13 81 160 326 390 262), lower := (rows 11 50 100 13 81 160 64 128 256), losses := [] }

theorem u14167 : Upper (D 6) (R 6) [10,48,96,5,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14167 [(5,7)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14168 : PairBound 9 := { available := 324, camps := [{ cop := 3, region := 464, targets := 34 },{ cop := 4, region := 34, targets := 1 }], pairs := [(1,0),(4,1),(4,5)], upper := (rows 11 50 100 13 145 34 324 452 324), lower := (rows 11 50 100 13 145 34 64 128 256), losses := [] }

theorem u14168 : Upper (D 6) (R 6) [10,48,96,5,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14168 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14169 : PairBound 9 := { available := 322, camps := [{ cop := 0, region := 464, targets := 36 },{ cop := 4, region := 358, targets := 1 }], pairs := [(1,0),(4,2),(4,5)], upper := (rows 11 50 100 13 145 36 322 450 322), lower := (rows 11 50 100 13 145 36 64 128 256), losses := [] }

theorem u14169 : Upper (D 6) (R 6) [10,48,96,5,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14169 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14170 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 50 100 13 145 96 326 390 262), lower := (rows 11 50 100 13 145 96 64 128 256), losses := [] }

theorem u14170 : Upper (D 6) (R 6) [10,48,96,5,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14170 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14171 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 358, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 50 100 13 145 288 70 198 326), lower := (rows 11 50 100 13 145 288 64 128 256), losses := [] }

theorem u14171 : Upper (D 6) (R 6) [10,48,96,5,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14171 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14172 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 50 100 13 148 33 322 450 322), lower := (rows 11 50 100 13 148 33 64 128 256), losses := [] }

theorem u14172 : Upper (D 6) (R 6) [10,48,96,5,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14172 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14173 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 50 100 13 148 34 321 449 321), lower := (rows 11 50 100 13 148 34 64 128 256), losses := [] }

theorem u14173 : Upper (D 6) (R 6) [10,48,96,5,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14173 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14174 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 50 100 13 148 96 323 387 259), lower := (rows 11 50 100 13 148 96 64 128 256), losses := [] }

theorem u14174 : Upper (D 6) (R 6) [10,48,96,5,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14174 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14175 : Route 9 := (fun mask => (mask,id))

def c14175 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14175 : Upper (D 6) (R 6) [10,48,96,5,132,256] 13 := by
  apply FastRouting.sound _ _ [10,48,96,5,132,256] 13 (by decide) (choices 1) [1,2] r14175 c14175
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3090
  · exact u3091

def b14176 : PairBound 9 := { available := 262, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 50 100 13 208 33 326 390 262), lower := (rows 11 50 100 13 208 33 64 128 256), losses := [] }

theorem u14176 : Upper (D 6) (R 6) [10,48,96,5,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14176 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14177 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 464, targets := 34 },{ cop := 4, region := 34, targets := 1 }], pairs := [(1,0),(4,1),(4,5)], upper := (rows 11 50 100 13 208 34 325 389 261), lower := (rows 11 50 100 13 208 34 64 128 256), losses := [] }

theorem u14177 : Upper (D 6) (R 6) [10,48,96,5,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14177 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14178 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 464, targets := 36 },{ cop := 4, region := 38, targets := 1 }], pairs := [(1,0),(4,2),(4,5)], upper := (rows 11 50 100 13 208 36 323 387 259), lower := (rows 11 50 100 13 208 36 64 128 256), losses := [] }

theorem u14178 : Upper (D 6) (R 6) [10,48,96,5,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14178 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14179 : Route 9 := (fun mask => (mask,id))

def c14179 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14179 : Upper (D 6) (R 6) [10,48,96,5,192,256] 13 := by
  apply FastRouting.sound _ _ [10,48,96,5,192,256] 13 (by decide) (choices 1) [1,2,4] r14179 c14179
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3092
  · exact u3093
  · exact u3094

def b14180 : PairBound 9 := { available := 70, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 50 100 13 400 33 70 198 326), lower := (rows 11 50 100 13 400 33 64 128 256), losses := [] }

theorem u14180 : Upper (D 6) (R 6) [10,48,96,5,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14180 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14181 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 50 100 13 400 34 69 197 325), lower := (rows 11 50 100 13 400 34 64 128 256), losses := [] }

theorem u14181 : Upper (D 6) (R 6) [10,48,96,5,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14181 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14182 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 464, targets := 36 },{ cop := 6, region := 36, targets := 1 }], pairs := [(2,0),(4,2),(4,5)], upper := (rows 11 50 100 13 400 36 67 195 323), lower := (rows 11 50 100 13 400 36 64 128 256), losses := [] }

theorem u14182 : Upper (D 6) (R 6) [10,48,96,5,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14182 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14183 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 50 100 13 400 96 71 135 263), lower := (rows 11 50 100 13 400 96 64 128 256), losses := [] }

theorem u14183 : Upper (D 6) (R 6) [10,48,96,5,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14183 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14184 : PairBound 9 := { available := 260, camps := [{ cop := 4, region := 358, targets := 1 },{ cop := 4, region := 34, targets := 4 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 11 50 100 73 145 34 324 388 260), lower := (rows 11 50 100 73 145 34 64 128 256), losses := [] }

theorem u14184 : Upper (D 6) (R 6) [10,48,96,65,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14184 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14185 : PairBound 9 := { available := 262, camps := [{ cop := 3, region := 36, targets := 3 },{ cop := 4, region := 358, targets := 1 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 11 50 100 73 145 36 326 390 262), lower := (rows 11 50 100 73 145 36 64 128 256), losses := [] }

theorem u14185 : Upper (D 6) (R 6) [10,48,96,65,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14185 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14186 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 358, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 50 100 73 145 288 70 134 262), lower := (rows 11 50 100 73 145 288 64 128 256), losses := [] }

theorem u14186 : Upper (D 6) (R 6) [10,48,96,65,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14186 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14187 : PairBound 9 := { available := 260, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 50 100 73 146 33 324 388 260), lower := (rows 11 50 100 73 146 33 64 128 256), losses := [] }

theorem u14187 : Upper (D 6) (R 6) [10,48,96,65,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14187 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14188 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 364, targets := 2 },{ cop := 3, region := 36, targets := 1 }], pairs := [(2,0),(2,1),(3,1)], upper := (rows 11 50 100 73 146 36 325 389 261), lower := (rows 11 50 100 73 146 36 64 128 256), losses := [] }

theorem u14188 : Upper (D 6) (R 6) [10,48,96,65,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14188 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14189 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 364, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 11 50 100 73 146 288 69 133 261), lower := (rows 11 50 100 73 146 288 64 128 256), losses := [] }

theorem u14189 : Upper (D 6) (R 6) [10,48,96,65,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14189 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14190 : PairBound 9 := { available := 262, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 50 100 73 148 33 326 390 262), lower := (rows 11 50 100 73 148 33 64 128 256), losses := [] }

theorem u14190 : Upper (D 6) (R 6) [10,48,96,65,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14190 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14191 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 50 100 73 148 34 325 389 261), lower := (rows 11 50 100 73 148 34 64 128 256), losses := [] }

theorem u14191 : Upper (D 6) (R 6) [10,48,96,65,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14191 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14192 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 329, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 50 100 73 148 36 323 387 259), lower := (rows 11 50 100 73 148 36 64 128 256), losses := [] }

theorem u14192 : Upper (D 6) (R 6) [10,48,96,65,132,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14192 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14193 : Route 9 := (fun mask => (mask,id))

def c14193 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14193 : Upper (D 6) (R 6) [10,48,96,65,132,256] 13 := by
  apply FastRouting.sound _ _ [10,48,96,65,132,256] 13 (by decide) (choices 1) [1,2,4] r14193 c14193
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3095
  · exact u3096
  · exact u3097

def b14194 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 50 100 73 400 33 70 134 262), lower := (rows 11 50 100 73 400 33 64 128 256), losses := [] }

theorem u14194 : Upper (D 6) (R 6) [10,48,96,65,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14194 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14195 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 50 100 73 400 34 69 133 261), lower := (rows 11 50 100 73 400 34 64 128 256), losses := [] }

theorem u14195 : Upper (D 6) (R 6) [10,48,96,65,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14195 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14196 : Route 9 := (fun mask => (mask,id))

def c14196 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14196 : Upper (D 6) (R 6) [10,48,96,65,384,4] 13 := by
  apply FastRouting.sound _ _ [10,48,96,65,384,4] 13 (by decide) (choices 1) [1,2,4] r14196 c14196
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3098
  · exact u3099
  · exact u3100

def b14197 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 358, targets := 1 },{ cop := 4, region := 456, targets := 2 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 11 50 100 137 21 34 324 452 324), lower := (rows 11 50 100 137 21 34 64 128 256), losses := [] }

theorem u14197 : Upper (D 6) (R 6) [10,48,96,129,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14197 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14198 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 457, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 50 100 137 21 36 322 450 322), lower := (rows 11 50 100 137 21 36 64 128 256), losses := [] }

theorem u14198 : Upper (D 6) (R 6) [10,48,96,129,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14198 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14199 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 50 100 137 21 96 326 390 262), lower := (rows 11 50 100 137 21 96 64 128 256), losses := [] }

theorem u14199 : Upper (D 6) (R 6) [10,48,96,129,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14199 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14200 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 358, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 50 100 137 21 288 70 198 326), lower := (rows 11 50 100 137 21 288 64 128 256), losses := [] }

theorem u14200 : Upper (D 6) (R 6) [10,48,96,129,5,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14200 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14201 : PairBound 9 := { available := 260, camps := [{ cop := 4, region := 38, targets := 1 },{ cop := 4, region := 34, targets := 4 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 11 50 100 137 81 34 324 388 260), lower := (rows 11 50 100 137 81 34 64 128 256), losses := [] }

theorem u14201 : Upper (D 6) (R 6) [10,48,96,129,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14201 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14202 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 38, targets := 1 },{ cop := 4, region := 36, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 11 50 100 137 81 36 326 390 262), lower := (rows 11 50 100 137 81 36 64 128 256), losses := [] }

theorem u14202 : Upper (D 6) (R 6) [10,48,96,129,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14202 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14203 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 294, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 50 100 137 81 288 70 134 262), lower := (rows 11 50 100 137 81 288 64 128 256), losses := [] }

theorem u14203 : Upper (D 6) (R 6) [10,48,96,129,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14203 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14204 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 102, targets := 1 },{ cop := 4, region := 34, targets := 4 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 11 50 100 137 273 34 68 196 324), lower := (rows 11 50 100 137 273 34 64 128 256), losses := [] }

theorem u14204 : Upper (D 6) (R 6) [10,48,96,129,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14204 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14205 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 102, targets := 1 },{ cop := 6, region := 36, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 11 50 100 137 273 36 70 198 326), lower := (rows 11 50 100 137 273 36 64 128 256), losses := [] }

theorem u14205 : Upper (D 6) (R 6) [10,48,96,129,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14205 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14206 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 50 100 137 273 96 70 134 262), lower := (rows 11 50 100 137 273 96 64 128 256), losses := [] }

theorem u14206 : Upper (D 6) (R 6) [10,48,96,129,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14206 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14207 : PairBound 9 := { available := 68, camps := [{ cop := 5, region := 342, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 50 100 137 274 33 68 196 324), lower := (rows 11 50 100 137 274 33 64 128 256), losses := [] }

theorem u14207 : Upper (D 6) (R 6) [10,48,96,129,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14207 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14208 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 6, region := 36, targets := 1 }], pairs := [(2,0),(2,1),(3,1)], upper := (rows 11 50 100 137 274 36 69 197 325), lower := (rows 11 50 100 137 274 36 64 128 256), losses := [] }

theorem u14208 : Upper (D 6) (R 6) [10,48,96,129,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14208 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14209 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 50 100 137 274 96 69 133 261), lower := (rows 11 50 100 137 274 96 64 128 256), losses := [] }

theorem u14209 : Upper (D 6) (R 6) [10,48,96,129,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14209 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14210 : PairBound 9 := { available := 70, camps := [{ cop := 5, region := 342, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 50 100 137 276 33 70 198 326), lower := (rows 11 50 100 137 276 33 64 128 256), losses := [] }

theorem u14210 : Upper (D 6) (R 6) [10,48,96,129,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14210 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14211 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 50 100 137 276 34 69 197 325), lower := (rows 11 50 100 137 276 34 64 128 256), losses := [] }

theorem u14211 : Upper (D 6) (R 6) [10,48,96,129,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14211 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14212 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 201, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 50 100 137 276 36 67 195 323), lower := (rows 11 50 100 137 276 36 64 128 256), losses := [] }

theorem u14212 : Upper (D 6) (R 6) [10,48,96,129,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14212 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14213 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 50 100 137 276 96 71 135 263), lower := (rows 11 50 100 137 276 96 64 128 256), losses := [] }

theorem u14213 : Upper (D 6) (R 6) [10,48,96,129,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14213 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14214 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 342, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 50 100 137 336 33 70 134 262), lower := (rows 11 50 100 137 336 33 64 128 256), losses := [] }

theorem u14214 : Upper (D 6) (R 6) [10,48,96,129,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14214 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14215 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 38, targets := 1 },{ cop := 4, region := 34, targets := 4 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 11 50 100 137 336 34 69 133 261), lower := (rows 11 50 100 137 336 34 64 128 256), losses := [] }

theorem u14215 : Upper (D 6) (R 6) [10,48,96,129,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14215 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14216 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 38, targets := 1 },{ cop := 4, region := 36, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 11 50 100 137 336 36 71 135 263), lower := (rows 11 50 100 137 336 36 64 128 256), losses := [] }

theorem u14216 : Upper (D 6) (R 6) [10,48,96,129,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14216 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14217 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 460, targets := 1 },{ cop := 4, region := 34, targets := 4 }], pairs := [(1,2),(2,0),(3,0)], upper := (rows 11 50 100 140 81 33 326 390 262), lower := (rows 11 50 100 140 81 33 64 128 256), losses := [] }

theorem u14217 : Upper (D 6) (R 6) [10,48,96,132,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14217 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14218 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 38, targets := 1 },{ cop := 4, region := 34, targets := 4 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 11 50 100 140 81 34 325 389 261), lower := (rows 11 50 100 140 81 34 64 128 256), losses := [] }

theorem u14218 : Upper (D 6) (R 6) [10,48,96,132,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14218 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14219 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 336, targets := 36 },{ cop := 4, region := 38, targets := 1 }], pairs := [(1,0),(4,2),(4,5)], upper := (rows 11 50 100 140 81 36 323 387 259), lower := (rows 11 50 100 140 81 36 64 128 256), losses := [] }

theorem u14219 : Upper (D 6) (R 6) [10,48,96,132,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14219 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u14219
end Delivery.IrregularNine14.P06

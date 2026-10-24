import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0285
import IrregularNine14P06C0286
import IrregularNine14P06C0287

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r33840 : Route 9 := (fun mask => (mask,id))

def c33840 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33840 : Upper (D 6) (R 6) [10,160,33,272,65] 13 := by
  apply FastRouting.sound _ _ [10,160,33,272,65] 13 (by decide) (choices 1) [2,4,64] r33840 c33840
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17153
  · exact u17154
  · exact u17155

def r33841 : Route 9 := (fun mask => (mask,id))

def c33841 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33841 : Upper (D 6) (R 6) [10,160,33,272,66] 13 := by
  apply FastRouting.sound _ _ [10,160,33,272,66] 13 (by decide) (choices 1) [1,4,64] r33841 c33841
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17156
  · exact u17157
  · exact u17158

def r33842 : Route 9 := (fun mask => (mask,id))

def c33842 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33842 : Upper (D 6) (R 6) [10,160,33,272,68] 13 := by
  apply FastRouting.sound _ _ [10,160,33,272,68] 13 (by decide) (choices 1) [1,2,4,64] r33842 c33842
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17159
  · exact u17160
  · exact u17161
  · exact u17162

def b33843 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 162 37 328 19 116 84 212 340), lower := (rows 11 162 37 328 19 32 64 128 256), losses := [] }

theorem u33843 : Upper (D 6) (R 6) [10,160,33,320,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33843 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33844 : PairBound 9 := { available := 86, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 162 37 328 21 118 86 214 342), lower := (rows 11 162 37 328 21 32 64 128 256), losses := [] }

theorem u33844 : Upper (D 6) (R 6) [10,160,33,320,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33844 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33845 : Route 9 := (fun mask => (mask,id))

def c33845 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33845 : Upper (D 6) (R 6) [10,160,33,320,6] 13 := by
  apply FastRouting.sound _ _ [10,160,33,320,6] 13 (by decide) (choices 1) [1,4,16,64] r33845 c33845
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17163
  · exact u17164
  · exact u17165
  · exact u17166

def r33846 : Route 9 := (fun mask => (mask,id))

def c33846 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33846 : Upper (D 6) (R 6) [10,160,33,320,65] 13 := by
  apply FastRouting.sound _ _ [10,160,33,320,65] 13 (by decide) (choices 1) [2,4,16] r33846 c33846
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17167
  · exact u17168
  · exact u17169

def r33847 : Route 9 := (fun mask => (mask,id))

def c33847 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33847 : Upper (D 6) (R 6) [10,160,33,320,66] 13 := by
  apply FastRouting.sound _ _ [10,160,33,320,66] 13 (by decide) (choices 1) [1,4,16] r33847 c33847
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17170
  · exact u17171
  · exact u17172

def r33848 : Route 9 := (fun mask => (mask,id))

def c33848 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33848 : Upper (D 6) (R 6) [10,160,33,320,68] 13 := by
  apply FastRouting.sound _ _ [10,160,33,320,68] 13 (by decide) (choices 1) [1,2,4,16] r33848 c33848
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17173
  · exact u17174
  · exact u17175
  · exact u17176

def b33849 : PairBound 9 := { available := 324, camps := [{ cop := 1, region := 29, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 162 52 13 19 356 324 452 324), lower := (rows 11 162 52 13 19 32 64 128 256), losses := [] }

theorem u33849 : Upper (D 6) (R 6) [10,160,48,5,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33849 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33850 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 29, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 162 52 13 21 354 322 450 322), lower := (rows 11 162 52 13 21 32 64 128 256), losses := [] }

theorem u33850 : Upper (D 6) (R 6) [10,160,48,5,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33850 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33851 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 29, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 162 52 13 22 353 321 449 321), lower := (rows 11 162 52 13 22 32 64 128 256), losses := [] }

theorem u33851 : Upper (D 6) (R 6) [10,160,48,5,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33851 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33852 : Route 9 := (fun mask => (mask,id))

def c33852 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u33852 : Upper (D 6) (R 6) [10,160,48,5,65] 13 := by
  apply FastRouting.sound _ _ [10,160,48,5,65] 13 (by decide) (choices 1) [2,4,64,256] r33852 c33852
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17177
  · exact u17178
  · exact u17179
  · exact u17180

def r33853 : Route 9 := (fun mask => (mask,id))

def c33853 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u33853 : Upper (D 6) (R 6) [10,160,48,5,66] 13 := by
  apply FastRouting.sound _ _ [10,160,48,5,66] 13 (by decide) (choices 1) [1,4,64,256] r33853 c33853
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17181
  · exact u17182
  · exact u17183
  · exact u17184

def b33854 : PairBound 9 := { available := 323, camps := [{ cop := 3, region := 483, targets := 4 }], pairs := [(0,2),(1,2),(4,5)], upper := (rows 11 162 52 13 84 355 323 451 323), lower := (rows 11 162 52 13 84 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 4 8 24 0 65 129 257), good := (rows 475 130 20 477 84 0 64 128 256) }] }

theorem u33854 : Upper (D 6) (R 6) [10,160,48,5,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33854 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33855 : Route 9 := (fun mask => (mask,id))

def c33855 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33855 : Upper (D 6) (R 6) [10,160,48,5,257] 13 := by
  apply FastRouting.sound _ _ [10,160,48,5,257] 13 (by decide) (choices 1) [2,4,64] r33855 c33855
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17185
  · exact u17186
  · exact u17187

def r33856 : Route 9 := (fun mask => (mask,id))

def c33856 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33856 : Upper (D 6) (R 6) [10,160,48,5,258] 13 := by
  apply FastRouting.sound _ _ [10,160,48,5,258] 13 (by decide) (choices 1) [1,4,64] r33856 c33856
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17188
  · exact u17189
  · exact u17190

def b33857 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 227, targets := 4 }], pairs := [(0,2),(1,2),(4,5)], upper := (rows 11 162 52 13 276 99 67 195 323), lower := (rows 11 162 52 13 276 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 4 8 24 0 65 129 257), good := (rows 475 130 20 477 276 0 64 128 256) }] }

theorem u33857 : Upper (D 6) (R 6) [10,160,48,5,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33857 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33858 : Route 9 := (fun mask => (mask,id))

def c33858 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33858 : Upper (D 6) (R 6) [10,160,48,5,320] 13 := by
  apply FastRouting.sound _ _ [10,160,48,5,320] 13 (by decide) (choices 1) [1,2,4,64] r33858 c33858
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17191
  · exact u17192
  · exact u17193
  · exact u17194

def b33859 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 162 52 73 19 356 324 452 324), lower := (rows 11 162 52 73 19 32 64 128 256), losses := [] }

theorem u33859 : Upper (D 6) (R 6) [10,160,48,65,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33859 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33860 : Route 9 := (fun mask => (mask,id))

def c33860 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u33860 : Upper (D 6) (R 6) [10,160,48,65,5] 13 := by
  apply FastRouting.sound _ _ [10,160,48,65,5] 13 (by decide) (choices 1) [2,4,64,256] r33860 c33860
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17195
  · exact u17196
  · exact u17197
  · exact u17198

def b33861 : PairBound 9 := { available := 325, camps := [{ cop := 1, region := 20, targets := 65 }], pairs := [(2,0),(2,6),(4,0)], upper := (rows 11 162 52 73 22 357 325 453 325), lower := (rows 11 162 52 73 22 32 64 128 256), losses := [] }

theorem u33861 : Upper (D 6) (R 6) [10,160,48,65,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33861 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33862 : PairBound 9 := { available := 262, camps := [{ cop := 3, region := 16, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 11 162 52 73 81 294 326 390 262), lower := (rows 11 162 52 73 81 32 64 128 256), losses := [] }

theorem u33862 : Upper (D 6) (R 6) [10,160,48,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33862 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33863 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 9, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 162 52 73 82 293 325 389 261), lower := (rows 11 162 52 73 82 32 64 128 256), losses := [] }

theorem u33863 : Upper (D 6) (R 6) [10,160,48,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33863 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33864 : Route 9 := (fun mask => (mask,id))

def c33864 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u33864 : Upper (D 6) (R 6) [10,160,48,65,68] 13 := by
  apply FastRouting.sound _ _ [10,160,48,65,68] 13 (by decide) (choices 1) [1,2,4,256] r33864 c33864
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17199
  · exact u17200
  · exact u17201
  · exact u17202

def r33865 : Route 9 := (fun mask => (mask,id))

def c33865 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33865 : Upper (D 6) (R 6) [10,160,48,65,257] 13 := by
  apply FastRouting.sound _ _ [10,160,48,65,257] 13 (by decide) (choices 1) [2,4,64] r33865 c33865
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17203
  · exact u17204
  · exact u17205

def r33866 : Route 9 := (fun mask => (mask,id))

def c33866 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33866 : Upper (D 6) (R 6) [10,160,48,65,258] 13 := by
  apply FastRouting.sound _ _ [10,160,48,65,258] 13 (by decide) (choices 1) [1,4,64] r33866 c33866
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17206
  · exact u17207
  · exact u17208

def r33867 : Route 9 := (fun mask => (mask,id))

def c33867 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33867 : Upper (D 6) (R 6) [10,160,48,65,260] 13 := by
  apply FastRouting.sound _ _ [10,160,48,65,260] 13 (by decide) (choices 1) [1,2,4,64] r33867 c33867
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17209
  · exact u17210
  · exact u17211
  · exact u17212

def r33868 : Route 9 := (fun mask => (mask,id))

def c33868 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33868 : Upper (D 6) (R 6) [10,160,48,65,320] 13 := by
  apply FastRouting.sound _ _ [10,160,48,65,320] 13 (by decide) (choices 1) [1,2,4] r33868 c33868
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17213
  · exact u17214
  · exact u17215

def b33869 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 162 52 76 19 357 325 453 325), lower := (rows 11 162 52 76 19 32 64 128 256), losses := [] }

theorem u33869 : Upper (D 6) (R 6) [10,160,48,68,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33869 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33870 : PairBound 9 := { available := 323, camps := [{ cop := 3, region := 419, targets := 4 }], pairs := [(0,2),(1,2),(3,5)], upper := (rows 11 162 52 76 21 355 323 451 323), lower := (rows 11 162 52 76 21 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 4 24 16 0 65 129 257), good := (rows 459 130 28 76 477 0 64 128 256) }] }

theorem u33870 : Upper (D 6) (R 6) [10,160,48,68,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33870 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33871 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 20, targets := 65 }], pairs := [(2,0),(2,6),(4,0)], upper := (rows 11 162 52 76 22 353 321 449 321), lower := (rows 11 162 52 76 22 32 64 128 256), losses := [] }

theorem u33871 : Upper (D 6) (R 6) [10,160,48,68,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33871 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33872 : PairBound 9 := { available := 263, camps := [{ cop := 3, region := 419, targets := 64 },{ cop := 4, region := 422, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 162 52 76 81 295 327 391 263), lower := (rows 11 162 52 76 81 32 64 128 256), losses := [] }

theorem u33872 : Upper (D 6) (R 6) [10,160,48,68,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33872 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33873 : Route 9 := (fun mask => (mask,id))

def c33873 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u33873 : Upper (D 6) (R 6) [10,160,48,68,66] 13 := by
  apply FastRouting.sound _ _ [10,160,48,68,66] 13 (by decide) (choices 1) [1,4,256] r33873 c33873
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17216
  · exact u17217
  · exact u17218

def b33874 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 162 52 76 84 291 323 387 259), lower := (rows 11 162 52 76 84 32 64 128 256), losses := [] }

theorem u33874 : Upper (D 6) (R 6) [10,160,48,68,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33874 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33875 : Route 9 := (fun mask => (mask,id))

def c33875 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33875 : Upper (D 6) (R 6) [10,160,48,68,257] 13 := by
  apply FastRouting.sound _ _ [10,160,48,68,257] 13 (by decide) (choices 1) [1,2,4,64] r33875 c33875
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17219
  · exact u17220
  · exact u17221
  · exact u17222

def r33876 : Route 9 := (fun mask => (mask,id))

def c33876 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33876 : Upper (D 6) (R 6) [10,160,48,68,258] 13 := by
  apply FastRouting.sound _ _ [10,160,48,68,258] 13 (by decide) (choices 1) [1,4,64] r33876 c33876
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17223
  · exact u17224
  · exact u17225

def r33877 : Route 9 := (fun mask => (mask,id))

def c33877 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33877 : Upper (D 6) (R 6) [10,160,48,68,260] 13 := by
  apply FastRouting.sound _ _ [10,160,48,68,260] 13 (by decide) (choices 1) [1,2,64] r33877 c33877
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17226
  · exact u17227
  · exact u17228

def r33878 : Route 9 := (fun mask => (mask,id))

def c33878 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33878 : Upper (D 6) (R 6) [10,160,48,68,320] 13 := by
  apply FastRouting.sound _ _ [10,160,48,68,320] 13 (by decide) (choices 1) [1,2,4] r33878 c33878
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17229
  · exact u17230
  · exact u17231

def b33879 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 162 52 265 19 100 68 196 324), lower := (rows 11 162 52 265 19 32 64 128 256), losses := [] }

theorem u33879 : Upper (D 6) (R 6) [10,160,48,257,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33879 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33880 : Route 9 := (fun mask => (mask,id))

def c33880 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33880 : Upper (D 6) (R 6) [10,160,48,257,5] 13 := by
  apply FastRouting.sound _ _ [10,160,48,257,5] 13 (by decide) (choices 1) [2,4,64] r33880 c33880
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17232
  · exact u17233
  · exact u17234

def b33881 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 20, targets := 65 }], pairs := [(2,0),(2,6),(4,0)], upper := (rows 11 162 52 265 22 101 69 197 325), lower := (rows 11 162 52 265 22 32 64 128 256), losses := [] }

theorem u33881 : Upper (D 6) (R 6) [10,160,48,257,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33881 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33882 : Route 9 := (fun mask => (mask,id))

def c33882 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33882 : Upper (D 6) (R 6) [10,160,48,257,65] 13 := by
  apply FastRouting.sound _ _ [10,160,48,257,65] 13 (by decide) (choices 1) [2,4,64] r33882 c33882
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17235
  · exact u17236
  · exact u17237

def r33883 : Route 9 := (fun mask => (mask,id))

def c33883 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33883 : Upper (D 6) (R 6) [10,160,48,257,66] 13 := by
  apply FastRouting.sound _ _ [10,160,48,257,66] 13 (by decide) (choices 1) [1,4,64] r33883 c33883
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17238
  · exact u17239
  · exact u17240

def r33884 : Route 9 := (fun mask => (mask,id))

def c33884 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33884 : Upper (D 6) (R 6) [10,160,48,257,68] 13 := by
  apply FastRouting.sound _ _ [10,160,48,257,68] 13 (by decide) (choices 1) [1,2,4,64] r33884 c33884
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17241
  · exact u17242
  · exact u17243
  · exact u17244

def b33885 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 162 52 268 19 101 69 197 325), lower := (rows 11 162 52 268 19 32 64 128 256), losses := [] }

theorem u33885 : Upper (D 6) (R 6) [10,160,48,260,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33885 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33886 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 227, targets := 4 }], pairs := [(0,2),(1,2),(3,5)], upper := (rows 11 162 52 268 21 99 67 195 323), lower := (rows 11 162 52 268 21 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 4 24 16 0 65 129 257), good := (rows 459 130 28 268 477 0 64 128 256) }] }

theorem u33886 : Upper (D 6) (R 6) [10,160,48,260,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33886 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33887 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 20, targets := 65 }], pairs := [(2,0),(2,6),(4,0)], upper := (rows 11 162 52 268 22 97 65 193 321), lower := (rows 11 162 52 268 22 32 64 128 256), losses := [] }

theorem u33887 : Upper (D 6) (R 6) [10,160,48,260,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33887 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33888 : Route 9 := (fun mask => (mask,id))

def c33888 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33888 : Upper (D 6) (R 6) [10,160,48,260,65] 13 := by
  apply FastRouting.sound _ _ [10,160,48,260,65] 13 (by decide) (choices 1) [1,2,4,64] r33888 c33888
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17245
  · exact u17246
  · exact u17247
  · exact u17248

def r33889 : Route 9 := (fun mask => (mask,id))

def c33889 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33889 : Upper (D 6) (R 6) [10,160,48,260,66] 13 := by
  apply FastRouting.sound _ _ [10,160,48,260,66] 13 (by decide) (choices 1) [1,4,64] r33889 c33889
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17249
  · exact u17250
  · exact u17251

def r33890 : Route 9 := (fun mask => (mask,id))

def c33890 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33890 : Upper (D 6) (R 6) [10,160,48,260,68] 13 := by
  apply FastRouting.sound _ _ [10,160,48,260,68] 13 (by decide) (choices 1) [1,2,64] r33890 c33890
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17252
  · exact u17253
  · exact u17254

def b33891 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 162 52 328 19 101 69 197 325), lower := (rows 11 162 52 328 19 32 64 128 256), losses := [] }

theorem u33891 : Upper (D 6) (R 6) [10,160,48,320,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33891 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33892 : Route 9 := (fun mask => (mask,id))

def c33892 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33892 : Upper (D 6) (R 6) [10,160,48,320,5] 13 := by
  apply FastRouting.sound _ _ [10,160,48,320,5] 13 (by decide) (choices 1) [1,2,4,64] r33892 c33892
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17255
  · exact u17256
  · exact u17257
  · exact u17258

def b33893 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 20, targets := 65 }], pairs := [(2,0),(2,6),(4,0)], upper := (rows 11 162 52 328 22 101 69 197 325), lower := (rows 11 162 52 328 22 32 64 128 256), losses := [] }

theorem u33893 : Upper (D 6) (R 6) [10,160,48,320,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33893 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33894 : Route 9 := (fun mask => (mask,id))

def c33894 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33894 : Upper (D 6) (R 6) [10,160,48,320,65] 13 := by
  apply FastRouting.sound _ _ [10,160,48,320,65] 13 (by decide) (choices 1) [1,2,4] r33894 c33894
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17259
  · exact u17260
  · exact u17261

def r33895 : Route 9 := (fun mask => (mask,id))

def c33895 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33895 : Upper (D 6) (R 6) [10,160,48,320,66] 13 := by
  apply FastRouting.sound _ _ [10,160,48,320,66] 13 (by decide) (choices 1) [1,4] r33895 c33895
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u17262
  · exact u17263

def r33896 : Route 9 := (fun mask => (mask,id))

def c33896 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33896 : Upper (D 6) (R 6) [10,160,48,320,68] 13 := by
  apply FastRouting.sound _ _ [10,160,48,320,68] 13 (by decide) (choices 1) [1,2,4] r33896 c33896
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17264
  · exact u17265
  · exact u17266

def b33897 : PairBound 9 := { available := 356, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 162 69 25 22 356 356 484 356), lower := (rows 11 162 69 25 22 32 64 128 256), losses := [] }

theorem u33897 : Upper (D 6) (R 6) [10,160,65,17,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33897 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33898 : PairBound 9 := { available := 324, camps := [{ cop := 1, region := 25, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 162 69 25 50 356 324 452 324), lower := (rows 11 162 69 25 50 32 64 128 256), losses := [] }

theorem u33898 : Upper (D 6) (R 6) [10,160,65,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33898 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33899 : PairBound 9 := { available := 326, camps := [{ cop := 2, region := 434, targets := 1 },{ cop := 0, region := 324, targets := 32 }], pairs := [(1,0),(2,5),(4,0)], upper := (rows 11 162 69 25 52 358 326 454 326), lower := (rows 11 162 69 25 52 32 64 128 256), losses := [] }

theorem u33899 : Upper (D 6) (R 6) [10,160,65,17,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33899 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u33899
end Delivery.IrregularNine14.P06

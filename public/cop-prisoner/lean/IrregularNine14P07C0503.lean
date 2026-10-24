import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0198
import IrregularNine14P07C0199

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b30180 : PairBound 9 := { available := 480, camps := [{ cop := 4, region := 10, targets := 224 }], pairs := [(1,5),(1,6),(1,7),(3,5)], upper := (rows 7 26 100 11 145 480 480 480 480), lower := (rows 7 26 100 11 145 32 64 128 256), losses := [] }

theorem u30180 : Upper (D 7) (R 7) [6,24,96,3,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30180 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30181 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 8, targets := 192 }], pairs := [(2,1),(3,6),(3,7),(4,1)], upper := (rows 7 26 100 11 176 481 449 449 449), lower := (rows 7 26 100 11 176 32 64 128 256), losses := [] }

theorem u30181 : Upper (D 7) (R 7) [6,24,96,3,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30181 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30182 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 10, targets := 224 }], pairs := [(1,5),(1,6),(1,7),(3,5)], upper := (rows 7 26 100 11 273 224 224 224 480), lower := (rows 7 26 100 11 273 32 64 128 256), losses := [] }

theorem u30182 : Upper (D 7) (R 7) [6,24,96,3,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30182 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30183 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 8, targets := 192 }], pairs := [(2,1),(3,6),(3,7),(4,1)], upper := (rows 7 26 100 11 304 225 193 193 449), lower := (rows 7 26 100 11 304 32 64 128 256), losses := [] }

theorem u30183 : Upper (D 7) (R 7) [6,24,96,3,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30183 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30184 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 0, region := 228, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 7 26 100 11 400 225 225 225 481), lower := (rows 7 26 100 11 400 32 64 128 256), losses := [] }

theorem u30184 : Upper (D 7) (R 7) [6,24,96,3,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30184 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30185 : PairBound 9 := { available := 386, camps := [{ cop := 2, region := 27, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 26 100 41 81 418 450 386 386), lower := (rows 7 26 100 41 81 32 64 128 256), losses := [] }

theorem u30185 : Upper (D 7) (R 7) [6,24,96,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30185 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30186 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 27, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 26 100 41 82 417 449 385 385), lower := (rows 7 26 100 41 82 32 64 128 256), losses := [] }

theorem u30186 : Upper (D 7) (R 7) [6,24,96,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30186 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30187 : Route 9 := (fun mask => (mask,id))

def c30187 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u30187 : Upper (D 7) (R 7) [6,24,96,33,129] 13 := by
  apply FastRouting.sound _ _ [6,24,96,33,129] 13 (by decide) (choices 1) [2,64,128,256] r30187 c30187
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11886
  · exact u11887
  · exact u11888
  · exact u11889

def b30188 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(2,1),(3,1),(4,5)], upper := (rows 7 26 100 41 146 481 449 449 449), lower := (rows 7 26 100 41 146 32 64 128 256), losses := [] }

theorem u30188 : Upper (D 7) (R 7) [6,24,96,33,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30188 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30189 : Route 9 := (fun mask => (mask,id))

def c30189 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u30189 : Upper (D 7) (R 7) [6,24,96,33,192] 13 := by
  apply FastRouting.sound _ _ [6,24,96,33,192] 13 (by decide) (choices 1) [1,2,128,256] r30189 c30189
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11890
  · exact u11891
  · exact u11892
  · exact u11893

def r30190 : Route 9 := (fun mask => (mask,id))

def c30190 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30190 : Upper (D 7) (R 7) [6,24,96,33,257] 13 := by
  apply FastRouting.sound _ _ [6,24,96,33,257] 13 (by decide) (choices 1) [2,64,128] r30190 c30190
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11894
  · exact u11895
  · exact u11896

def b30191 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(2,1),(3,1),(4,5)], upper := (rows 7 26 100 41 274 225 193 193 449), lower := (rows 7 26 100 41 274 32 64 128 256), losses := [] }

theorem u30191 : Upper (D 7) (R 7) [6,24,96,33,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30191 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30192 : Route 9 := (fun mask => (mask,id))

def c30192 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30192 : Upper (D 7) (R 7) [6,24,96,33,320] 13 := by
  apply FastRouting.sound _ _ [6,24,96,33,320] 13 (by decide) (choices 1) [1,2,128] r30192 c30192
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11897
  · exact u11898
  · exact u11899

def r30193 : Route 9 := (fun mask => (mask,id))

def c30193 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30193 : Upper (D 7) (R 7) [6,24,96,33,384] 13 := by
  apply FastRouting.sound _ _ [6,24,96,33,384] 13 (by decide) (choices 1) [1,2,64,128] r30193 c30193
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11900
  · exact u11901
  · exact u11902
  · exact u11903

def r30194 : Route 9 := (fun mask => (mask,id))

def c30194 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u30194 : Upper (D 7) (R 7) [6,24,96,34,129] 13 := by
  apply FastRouting.sound _ _ [6,24,96,34,129] 13 (by decide) (choices 1) [1,64,128,256] r30194 c30194
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11904
  · exact u11905
  · exact u11906
  · exact u11907

def b30195 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 464, targets := 32 },{ cop := 0, region := 424, targets := 64 }], pairs := [(2,1),(3,6),(4,1),(4,5)], upper := (rows 7 26 100 42 208 417 449 385 385), lower := (rows 7 26 100 42 208 32 64 128 256), losses := [] }

theorem u30195 : Upper (D 7) (R 7) [6,24,96,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30195 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30196 : Route 9 := (fun mask => (mask,id))

def c30196 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30196 : Upper (D 7) (R 7) [6,24,96,34,257] 13 := by
  apply FastRouting.sound _ _ [6,24,96,34,257] 13 (by decide) (choices 1) [1,64,128] r30196 c30196
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11908
  · exact u11909
  · exact u11910

def b30197 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 464, targets := 32 },{ cop := 0, region := 168, targets := 64 }], pairs := [(2,1),(3,6),(4,1),(4,5)], upper := (rows 7 26 100 42 336 161 193 129 385), lower := (rows 7 26 100 42 336 32 64 128 256), losses := [] }

theorem u30197 : Upper (D 7) (R 7) [6,24,96,34,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30197 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30198 : Route 9 := (fun mask => (mask,id))

def c30198 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30198 : Upper (D 7) (R 7) [6,24,96,34,384] 13 := by
  apply FastRouting.sound _ _ [6,24,96,34,384] 13 (by decide) (choices 1) [1,64,128] r30198 c30198
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11911
  · exact u11912
  · exact u11913

def b30199 : PairBound 9 := { available := 387, camps := [{ cop := 2, region := 8, targets := 131 },{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0),(3,0),(3,1),(3,7)], upper := (rows 7 26 100 104 145 419 451 387 387), lower := (rows 7 26 100 104 145 32 64 128 256), losses := [] }

theorem u30199 : Upper (D 7) (R 7) [6,24,96,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30199 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30200 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 8, targets := 131 },{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0),(3,0),(3,1),(3,7)], upper := (rows 7 26 100 104 146 417 449 385 385), lower := (rows 7 26 100 104 146 32 64 128 256), losses := [] }

theorem u30200 : Upper (D 7) (R 7) [6,24,96,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30200 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30201 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 8, targets := 131 },{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0),(3,0),(3,1),(3,7)], upper := (rows 7 26 100 104 273 163 195 131 387), lower := (rows 7 26 100 104 273 32 64 128 256), losses := [] }

theorem u30201 : Upper (D 7) (R 7) [6,24,96,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30201 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30202 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 8, targets := 131 },{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0),(3,0),(3,1),(3,7)], upper := (rows 7 26 100 104 274 161 193 129 385), lower := (rows 7 26 100 104 274 32 64 128 256), losses := [] }

theorem u30202 : Upper (D 7) (R 7) [6,24,96,96,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30202 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30203 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 8, targets := 131 },{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0),(3,0),(3,1),(3,7)], upper := (rows 7 26 100 104 400 163 195 131 387), lower := (rows 7 26 100 104 400 32 64 128 256), losses := [] }

theorem u30203 : Upper (D 7) (R 7) [6,24,96,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30203 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30204 : PairBound 9 := { available := 354, camps := [{ cop := 3, region := 18, targets := 96 }], pairs := [(1,5),(1,6),(4,5),(4,6)], upper := (rows 7 26 100 137 145 354 354 482 354), lower := (rows 7 26 100 137 145 32 64 128 256), losses := [] }

theorem u30204 : Upper (D 7) (R 7) [6,24,96,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30204 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30205 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 18, targets := 97 }], pairs := [(1,0),(1,5),(1,6),(4,0)], upper := (rows 7 26 100 137 146 353 353 481 353), lower := (rows 7 26 100 137 146 32 64 128 256), losses := [] }

theorem u30205 : Upper (D 7) (R 7) [6,24,96,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30205 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30206 : Route 9 := (fun mask => (mask,id))

def c30206 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u30206 : Upper (D 7) (R 7) [6,24,96,129,160] 13 := by
  apply FastRouting.sound _ _ [6,24,96,129,160] 13 (by decide) (choices 1) [1,2,64,256] r30206 c30206
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11914
  · exact u11915
  · exact u11916
  · exact u11917

def r30207 : Route 9 := (fun mask => (mask,id))

def c30207 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30207 : Upper (D 7) (R 7) [6,24,96,129,257] 13 := by
  apply FastRouting.sound _ _ [6,24,96,129,257] 13 (by decide) (choices 1) [2,64,128] r30207 c30207
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11918
  · exact u11919
  · exact u11920

def r30208 : Route 9 := (fun mask => (mask,id))

def c30208 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30208 : Upper (D 7) (R 7) [6,24,96,129,258] 13 := by
  apply FastRouting.sound _ _ [6,24,96,129,258] 13 (by decide) (choices 1) [1,64,128] r30208 c30208
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11921
  · exact u11922
  · exact u11923

def r30209 : Route 9 := (fun mask => (mask,id))

def c30209 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30209 : Upper (D 7) (R 7) [6,24,96,129,288] 13 := by
  apply FastRouting.sound _ _ [6,24,96,129,288] 13 (by decide) (choices 1) [1,2,64,128] r30209 c30209
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11924
  · exact u11925
  · exact u11926
  · exact u11927

def r30210 : Route 9 := (fun mask => (mask,id))

def c30210 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30210 : Upper (D 7) (R 7) [6,24,96,129,384] 13 := by
  apply FastRouting.sound _ _ [6,24,96,129,384] 13 (by decide) (choices 1) [1,2,64] r30210 c30210
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11928
  · exact u11929
  · exact u11930

def b30211 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 10, targets := 97 }], pairs := [(1,0),(1,5),(1,6),(3,0)], upper := (rows 7 26 100 138 176 353 321 449 321), lower := (rows 7 26 100 138 176 32 64 128 256), losses := [] }

theorem u30211 : Upper (D 7) (R 7) [6,24,96,130,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30211 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30212 : Route 9 := (fun mask => (mask,id))

def c30212 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30212 : Upper (D 7) (R 7) [6,24,96,130,257] 13 := by
  apply FastRouting.sound _ _ [6,24,96,130,257] 13 (by decide) (choices 1) [1,64,128] r30212 c30212
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11931
  · exact u11932
  · exact u11933

def r30213 : Route 9 := (fun mask => (mask,id))

def c30213 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30213 : Upper (D 7) (R 7) [6,24,96,130,288] 13 := by
  apply FastRouting.sound _ _ [6,24,96,130,288] 13 (by decide) (choices 1) [1,64,128] r30213 c30213
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11934
  · exact u11935
  · exact u11936

def b30214 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 10, targets := 97 }], pairs := [(1,0),(1,5),(1,6),(3,0)], upper := (rows 7 26 100 138 400 97 97 225 353), lower := (rows 7 26 100 138 400 32 64 128 256), losses := [] }

theorem u30214 : Upper (D 7) (R 7) [6,24,96,130,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30214 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30215 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 357, targets := 128 },{ cop := 0, region := 464, targets := 32 },{ cop := 0, region := 424, targets := 64 }], pairs := [(0,7),(2,7),(3,6),(4,5)], upper := (rows 7 26 100 168 208 291 323 387 259), lower := (rows 7 26 100 168 208 32 64 128 256), losses := [] }

theorem u30215 : Upper (D 7) (R 7) [6,24,96,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30215 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30216 : Route 9 := (fun mask => (mask,id))

def c30216 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30216 : Upper (D 7) (R 7) [6,24,96,160,257] 13 := by
  apply FastRouting.sound _ _ [6,24,96,160,257] 13 (by decide) (choices 1) [1,2,64,128] r30216 c30216
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11937
  · exact u11938
  · exact u11939
  · exact u11940

def r30217 : Route 9 := (fun mask => (mask,id))

def c30217 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30217 : Upper (D 7) (R 7) [6,24,96,160,258] 13 := by
  apply FastRouting.sound _ _ [6,24,96,160,258] 13 (by decide) (choices 1) [1,64,128] r30217 c30217
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11941
  · exact u11942
  · exact u11943

def r30218 : Route 9 := (fun mask => (mask,id))

def c30218 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30218 : Upper (D 7) (R 7) [6,24,96,160,320] 13 := by
  apply FastRouting.sound _ _ [6,24,96,160,320] 13 (by decide) (choices 1) [1,2,128] r30218 c30218
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11944
  · exact u11945
  · exact u11946

def r30219 : Route 9 := (fun mask => (mask,id))

def c30219 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30219 : Upper (D 7) (R 7) [6,24,96,160,384] 13 := by
  apply FastRouting.sound _ _ [6,24,96,160,384] 13 (by decide) (choices 1) [1,2,64] r30219 c30219
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11947
  · exact u11948
  · exact u11949

def b30220 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 0, region := 484, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 7 26 261 11 112 224 224 224 480), lower := (rows 7 26 261 11 112 32 64 128 256), losses := [] }

theorem u30220 : Upper (D 7) (R 7) [6,24,257,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30220 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30221 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 18, targets := 192 }], pairs := [(1,6),(1,7),(4,6),(4,7)], upper := (rows 7 26 261 41 50 224 192 192 448), lower := (rows 7 26 261 41 50 32 64 128 256), losses := [] }

theorem u30221 : Upper (D 7) (R 7) [6,24,257,33,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30221 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30222 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 3, region := 210, targets := 1 }], pairs := [(1,0),(2,1),(3,1),(4,0)], upper := (rows 7 26 261 41 82 224 224 224 480), lower := (rows 7 26 261 41 82 32 64 128 256), losses := [] }

theorem u30222 : Upper (D 7) (R 7) [6,24,257,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30222 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30223 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 453, targets := 32 },{ cop := 3, region := 210, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(4,0)], upper := (rows 7 26 261 41 112 226 194 194 450), lower := (rows 7 26 261 41 112 32 64 128 256), losses := [] }

theorem u30223 : Upper (D 7) (R 7) [6,24,257,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30223 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30224 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c30224 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30224 : Upper (D 7) (R 7) [6,24,257,33,192] 13 := by
  apply FastRouting.sound _ _ [6,24,257,33,192] 13 (by decide) (choices 1) [2,64] r30224 c30224
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11950
  · exact u11951

def b30225 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 10, targets := 193 }], pairs := [(1,0),(1,6),(1,7),(3,0)], upper := (rows 7 26 261 42 112 225 193 193 449), lower := (rows 7 26 261 42 112 32 64 128 256), losses := [] }

theorem u30225 : Upper (D 7) (R 7) [6,24,257,34,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30225 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30226 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c30226 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30226 : Upper (D 7) (R 7) [6,24,257,34,192] 13 := by
  apply FastRouting.sound _ _ [6,24,257,34,192] 13 (by decide) (choices 1) [1,64] r30226 c30226
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11952
  · exact u11953

def b30227 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 18, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 7 26 261 104 112 163 195 131 387), lower := (rows 7 26 261 104 112 32 64 128 256), losses := [] }

theorem u30227 : Upper (D 7) (R 7) [6,24,257,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30227 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m30228_128 : Upper (D 7) (R 7) [6,24,257,96,160,128] 13 :=
  permutation_upper _ _ _ [6,24,257,96,160,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11956

def r30228 : Route 9 := (fun mask => (mask,id))

def c30228 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30228 : Upper (D 7) (R 7) [6,24,257,96,160] 13 := by
  apply FastRouting.sound _ _ [6,24,257,96,160] 13 (by decide) (choices 1) [1,2,64,128] r30228 c30228
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11954
  · exact u11955
  · exact u11956
  · exact m30228_128

def b30229 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 27, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 26 292 11 49 224 192 192 448), lower := (rows 7 26 292 11 49 32 64 128 256), losses := [] }

theorem u30229 : Upper (D 7) (R 7) [6,24,288,3,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30229 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30230 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 10, targets := 224 }], pairs := [(1,5),(1,6),(1,7),(3,5)], upper := (rows 7 26 292 11 81 224 224 224 480), lower := (rows 7 26 292 11 81 32 64 128 256), losses := [] }

theorem u30230 : Upper (D 7) (R 7) [6,24,288,3,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30230 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30231 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 8, targets := 192 }], pairs := [(2,1),(3,6),(3,7),(4,1)], upper := (rows 7 26 292 11 112 225 193 193 449), lower := (rows 7 26 292 11 112 32 64 128 256), losses := [] }

theorem u30231 : Upper (D 7) (R 7) [6,24,288,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30231 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30232 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 0, region := 484, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 7 26 292 11 208 225 225 225 481), lower := (rows 7 26 292 11 208 32 64 128 256), losses := [] }

theorem u30232 : Upper (D 7) (R 7) [6,24,288,3,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30232 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30233 : Route 9 := (fun mask => (mask,id))

def c30233 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30233 : Upper (D 7) (R 7) [6,24,288,33,65] 13 := by
  apply FastRouting.sound _ _ [6,24,288,33,65] 13 (by decide) (choices 1) [2,64,128] r30233 c30233
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11957
  · exact u11958
  · exact u11959

def b30234 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 3, region := 210, targets := 32 }], pairs := [(1,5),(2,1),(3,1),(4,5)], upper := (rows 7 26 292 41 82 225 193 193 449), lower := (rows 7 26 292 41 82 32 64 128 256), losses := [] }

theorem u30234 : Upper (D 7) (R 7) [6,24,288,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30234 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30235 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c30235 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30235 : Upper (D 7) (R 7) [6,24,288,33,192] 13 := by
  apply FastRouting.sound _ _ [6,24,288,33,192] 13 (by decide) (choices 1) [1,2,64] r30235 c30235
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11960
  · exact u11961
  · exact u11962

def r30236 : Route 9 := (fun mask => (mask,id))

def c30236 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30236 : Upper (D 7) (R 7) [6,24,288,34,65] 13 := by
  apply FastRouting.sound _ _ [6,24,288,34,65] 13 (by decide) (choices 1) [1,64,128] r30236 c30236
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11963
  · exact u11964
  · exact u11965

def r30237 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c30237 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30237 : Upper (D 7) (R 7) [6,24,288,34,192] 13 := by
  apply FastRouting.sound _ _ [6,24,288,34,192] 13 (by decide) (choices 1) [1,64] r30237 c30237
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11966
  · exact u11967

def b30238 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 18, targets := 160 }], pairs := [(1,5),(1,7),(4,5),(4,7)], upper := (rows 7 26 292 73 81 162 226 162 418), lower := (rows 7 26 292 73 81 32 64 128 256), losses := [] }

theorem u30238 : Upper (D 7) (R 7) [6,24,288,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30238 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30239 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 18, targets := 161 }], pairs := [(1,0),(1,5),(1,7),(4,0)], upper := (rows 7 26 292 73 82 161 225 161 417), lower := (rows 7 26 292 73 82 32 64 128 256), losses := [] }

theorem u30239 : Upper (D 7) (R 7) [6,24,288,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30239 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u30239
end Delivery.IrregularNine14.P07

import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0014
import IrregularNine14P06C0015

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b9180 : PairBound 9 := { available := 52, camps := [], pairs := [(2,0),(2,6),(3,0)], upper := (rows 7 11 164 328 81 34 116 180 308), lower := (rows 7 11 164 328 81 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 35 80 144 272), good := (rows 38 42 164 328 508 34 64 128 256) },{ target := 6, region := (rows 1 2 20 8 16 35 0 144 272), good := (rows 39 43 164 264 437 34 0 128 256) }] }

theorem u9180 : Upper (D 6) (R 6) [6,9,160,320,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9180 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9181 : PairBound 9 := { available := 50, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 11 164 328 81 36 114 178 306), lower := (rows 7 11 164 328 81 36 64 128 256), losses := [] }

theorem u9181 : Upper (D 6) (R 6) [6,9,160,320,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9181 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9182 : Route 9 := (fun mask => (mask,id))

def c9182 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9182 : Upper (D 6) (R 6) [6,9,160,320,65,16] 13 := by
  apply FastRouting.sound _ _ [6,9,160,320,65,16] 13 (by decide) (choices 1) [2,4,32] r9182 c9182
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u899
  · exact u900
  · exact u901

def b9183 : PairBound 9 := { available := 52, camps := [{ cop := 4, region := 165, targets := 64 }], pairs := [(0,6),(2,1),(2,6)], upper := (rows 7 11 164 328 82 33 116 180 308), lower := (rows 7 11 164 328 82 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 24 16 35 80 144 272), good := (rows 37 41 164 328 508 33 64 128 256) }] }

theorem u9183 : Upper (D 6) (R 6) [6,9,160,320,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9183 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9184 : PairBound 9 := { available := 49, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 11 164 328 82 36 113 177 305), lower := (rows 7 11 164 328 82 36 64 128 256), losses := [] }

theorem u9184 : Upper (D 6) (R 6) [6,9,160,320,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9184 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9185 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 165, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 11 164 328 82 48 101 165 293), lower := (rows 7 11 164 328 82 48 64 128 256), losses := [] }

theorem u9185 : Upper (D 6) (R 6) [6,9,160,320,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9185 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9186 : Route 9 := (fun mask => (mask,id))

def c9186 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9186 : Upper (D 6) (R 6) [6,9,160,320,68,1] 13 := by
  apply FastRouting.sound _ _ [6,9,160,320,68,1] 13 (by decide) (choices 1) [2,16,32] r9186 c9186
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u902
  · exact u903
  · exact u904

def r9187 : Route 9 := (fun mask => (mask,id))

def c9187 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9187 : Upper (D 6) (R 6) [6,9,160,320,68,2] 13 := by
  apply FastRouting.sound _ _ [6,9,160,320,68,2] 13 (by decide) (choices 1) [1,16,32] r9187 c9187
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u905
  · exact u906
  · exact u907

def r9188 : Route 9 := (fun mask => (mask,id))

def c9188 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9188 : Upper (D 6) (R 6) [6,9,160,320,68,16] 13 := by
  apply FastRouting.sound _ _ [6,9,160,320,68,16] 13 (by decide) (choices 1) [1,2,32] r9188 c9188
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u908
  · exact u909
  · exact u910

def r9189 : Route 9 := (fun mask => (mask,id))

def c9189 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9189 : Upper (D 6) (R 6) [6,9,160,320,96,1] 13 := by
  apply FastRouting.sound _ _ [6,9,160,320,96,1] 13 (by decide) (choices 1) [2,4,16] r9189 c9189
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u911
  · exact u912
  · exact u913

def r9190 : Route 9 := (fun mask => (mask,id))

def c9190 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9190 : Upper (D 6) (R 6) [6,9,160,320,96,2] 13 := by
  apply FastRouting.sound _ _ [6,9,160,320,96,2] 13 (by decide) (choices 1) [1,4,16] r9190 c9190
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u914
  · exact u915
  · exact u916

def b9191 : PairBound 9 := { available := 19, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 11 164 328 112 36 83 147 275), lower := (rows 7 11 164 328 112 36 64 128 256), losses := [] }

theorem u9191 : Upper (D 6) (R 6) [6,9,160,320,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9191 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9192 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 331, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 11 164 328 112 48 71 135 263), lower := (rows 7 11 164 328 112 48 64 128 256), losses := [] }

theorem u9192 : Upper (D 6) (R 6) [6,9,160,320,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9192 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9193 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 468, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 11 388 26 112 33 100 228 356), lower := (rows 7 11 388 26 112 33 64 128 256), losses := [] }

theorem u9193 : Upper (D 6) (R 6) [6,9,384,18,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9193 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m9194_1 : Upper (D 6) (R 6) [6,9,384,18,96,4,1] 13 :=
  permutation_upper _ _ _ [6,9,384,18,96,1,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u917

def r9194 : Route 9 := (fun mask => (mask,id))

def c9194 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9194 : Upper (D 6) (R 6) [6,9,384,18,96,4] 13 := by
  apply FastRouting.sound _ _ [6,9,384,18,96,4] 13 (by decide) (choices 1) [1,32] r9194 c9194
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m9194_1
  · exact u918

def b9195 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 11 388 26 112 96 101 165 293), lower := (rows 7 11 388 26 112 96 64 128 256), losses := [] }

theorem u9195 : Upper (D 6) (R 6) [6,9,384,18,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9195 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9196 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 42, targets := 68 }], pairs := [(1,2),(1,6),(3,2)], upper := (rows 7 11 388 42 84 33 112 240 368), lower := (rows 7 11 388 42 84 33 64 128 256), losses := [] }

theorem u9196 : Upper (D 6) (R 6) [6,9,384,34,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9196 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9197 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 11 388 42 84 48 97 225 353), lower := (rows 7 11 388 42 84 48 64 128 256), losses := [] }

theorem u9197 : Upper (D 6) (R 6) [6,9,384,34,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9197 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9198 : Route 9 := (fun mask => (mask,id))

def c9198 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9198 : Upper (D 6) (R 6) [6,9,384,34,68,64] 13 := by
  apply FastRouting.sound _ _ [6,9,384,34,68,64] 13 (by decide) (choices 1) [1,16,32] r9198 c9198
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u919
  · exact u920
  · exact u921

def b9199 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 42, targets := 68 }], pairs := [(1,2),(1,6),(3,2)], upper := (rows 7 11 388 42 112 33 84 212 340), lower := (rows 7 11 388 42 112 33 64 128 256), losses := [] }

theorem u9199 : Upper (D 6) (R 6) [6,9,384,34,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9199 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9200 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 11 388 42 112 36 81 209 337), lower := (rows 7 11 388 42 112 36 64 128 256), losses := [] }

theorem u9200 : Upper (D 6) (R 6) [6,9,384,34,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9200 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9201 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 455, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 11 388 42 112 48 69 197 325), lower := (rows 7 11 388 42 112 48 64 128 256), losses := [] }

theorem u9201 : Upper (D 6) (R 6) [6,9,384,34,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9201 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9202 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 11 388 42 112 96 85 149 277), lower := (rows 7 11 388 42 112 96 64 128 256), losses := [] }

theorem u9202 : Upper (D 6) (R 6) [6,9,384,34,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9202 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9203 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 42, targets := 68 }], pairs := [(1,2),(1,6),(3,2)], upper := (rows 7 11 388 56 81 34 100 228 356), lower := (rows 7 11 388 56 81 34 64 128 256), losses := [] }

theorem u9203 : Upper (D 6) (R 6) [6,9,384,48,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9203 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9204 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 484, targets := 1 }], pairs := [(2,0),(3,0),(3,1)], upper := (rows 7 11 388 56 81 36 98 226 354), lower := (rows 7 11 388 56 81 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 23 24 16 63 67 131 259), good := (rows 486 494 420 60 508 36 64 128 256) },{ target := 1, region := (rows 1 0 4 24 16 37 64 128 256), good := (rows 37 41 420 56 121 36 64 128 256) }] }

theorem u9204 : Upper (D 6) (R 6) [6,9,384,48,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9204 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9205 : PairBound 9 := { available := 38, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 11 388 56 81 96 102 166 294), lower := (rows 7 11 388 56 81 96 64 128 256), losses := [] }

theorem u9205 : Upper (D 6) (R 6) [6,9,384,48,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9205 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9206 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 452, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 11 388 56 82 33 100 228 356), lower := (rows 7 11 388 56 82 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 46 8 18 32 104 168 296), good := (rows 22 478 388 508 86 484 64 128 256) }] }

theorem u9206 : Upper (D 6) (R 6) [6,9,384,48,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9206 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9207 : Route 9 := (fun mask => (mask,id))

def c9207 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9207 : Upper (D 6) (R 6) [6,9,384,48,66,4] 13 := by
  apply FastRouting.sound _ _ [6,9,384,48,66,4] 13 (by decide) (choices 1) [1,32] r9207 c9207
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u922
  · exact u923

def b9208 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 11 388 56 82 96 101 165 293), lower := (rows 7 11 388 56 82 96 64 128 256), losses := [] }

theorem u9208 : Upper (D 6) (R 6) [6,9,384,48,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9208 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9209 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 11 388 56 84 33 98 226 354), lower := (rows 7 11 388 56 84 33 64 128 256), losses := [] }

theorem u9209 : Upper (D 6) (R 6) [6,9,384,48,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9209 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9210 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 11 388 56 84 34 97 225 353), lower := (rows 7 11 388 56 84 34 64 128 256), losses := [] }

theorem u9210 : Upper (D 6) (R 6) [6,9,384,48,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9210 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9211 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 11 388 56 84 96 99 163 291), lower := (rows 7 11 388 56 84 96 64 128 256), losses := [] }

theorem u9211 : Upper (D 6) (R 6) [6,9,384,48,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9211 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9212 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 460, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 11 388 104 49 34 84 212 340), lower := (rows 7 11 388 104 49 34 64 128 256), losses := [] }

theorem u9212 : Upper (D 6) (R 6) [6,9,384,96,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9212 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9213 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 48, targets := 66 },{ cop := 4, region := 74, targets := 4 }], pairs := [(1,2),(4,1),(4,6)], upper := (rows 7 11 388 104 49 36 82 210 338), lower := (rows 7 11 388 104 49 36 64 128 256), losses := [] }

theorem u9213 : Upper (D 6) (R 6) [6,9,384,96,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9213 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9214 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 48, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 7 11 388 104 49 48 70 198 326), lower := (rows 7 11 388 104 49 48 64 128 256), losses := [] }

theorem u9214 : Upper (D 6) (R 6) [6,9,384,96,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9214 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9215 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 11 388 104 49 96 86 150 278), lower := (rows 7 11 388 104 49 96 64 128 256), losses := [] }

theorem u9215 : Upper (D 6) (R 6) [6,9,384,96,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9215 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9216 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 460, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 11 388 104 50 33 84 212 340), lower := (rows 7 11 388 104 50 33 64 128 256), losses := [] }

theorem u9216 : Upper (D 6) (R 6) [6,9,384,96,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9216 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9217 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 453, targets := 32 },{ cop := 0, region := 48, targets := 1 }], pairs := [(0,5),(2,5),(4,0)], upper := (rows 7 11 388 104 50 36 81 209 337), lower := (rows 7 11 388 104 50 36 64 128 256), losses := [] }

theorem u9217 : Upper (D 6) (R 6) [6,9,384,96,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9217 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9218 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 48, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 11 388 104 50 48 69 197 325), lower := (rows 7 11 388 104 50 48 64 128 256), losses := [] }

theorem u9218 : Upper (D 6) (R 6) [6,9,384,96,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9218 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9219 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 11 388 104 50 96 85 149 277), lower := (rows 7 11 388 104 50 96 64 128 256), losses := [] }

theorem u9219 : Upper (D 6) (R 6) [6,9,384,96,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9219 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9220 : Route 9 := (fun mask => (mask,id))

def c9220 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9220 : Upper (D 6) (R 6) [6,9,384,96,36,1] 13 := by
  apply FastRouting.sound _ _ [6,9,384,96,36,1] 13 (by decide) (choices 1) [2,16] r9220 c9220
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u924
  · exact u925

def b9221 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 48, targets := 1 },{ cop := 0, region := 48, targets := 64 }], pairs := [(2,1),(4,0),(4,6)], upper := (rows 7 11 388 104 52 34 81 209 337), lower := (rows 7 11 388 104 52 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 39 40 56 32 66 130 258), good := (rows 453 477 388 124 60 508 64 128 256) }] }

theorem u9221 : Upper (D 6) (R 6) [6,9,384,96,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9221 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9222 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 11 388 104 52 48 67 195 323), lower := (rows 7 11 388 104 52 48 64 128 256), losses := [] }

theorem u9222 : Upper (D 6) (R 6) [6,9,384,96,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9222 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9223 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 11 388 104 52 96 83 147 275), lower := (rows 7 11 388 104 52 96 64 128 256), losses := [] }

theorem u9223 : Upper (D 6) (R 6) [6,9,384,96,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9223 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9224 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 37, targets := 64 },{ cop := 2, region := 72, targets := 2 }], pairs := [(0,6),(2,6),(3,1)], upper := (rows 7 26 37 73 400 34 100 228 356), lower := (rows 7 26 37 73 400 34 64 128 256), losses := [] }

theorem u9224 : Upper (D 6) (R 6) [6,24,33,65,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9224 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9225 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 474, targets := 4 }], pairs := [(1,2),(3,2),(4,2)], upper := (rows 7 26 37 73 400 36 98 226 354), lower := (rows 7 26 37 73 400 36 64 128 256), losses := [] }

theorem u9225 : Upper (D 6) (R 6) [6,24,33,65,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9225 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9226 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 496, targets := 1 },{ cop := 3, region := 36, targets := 2 }], pairs := [(1,0),(2,1),(4,0)], upper := (rows 7 26 37 73 400 96 102 166 294), lower := (rows 7 26 37 73 400 96 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 29 109 65 129 257), good := (rows 502 58 500 506 400 96 96 128 256) }] }

theorem u9226 : Upper (D 6) (R 6) [6,24,33,65,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9226 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9227 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 7 26 37 74 400 33 100 228 356), lower := (rows 7 26 37 74 400 33 64 128 256), losses := [] }

theorem u9227 : Upper (D 6) (R 6) [6,24,33,66,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9227 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9228 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 474, targets := 4 }], pairs := [(1,2),(3,2),(4,2)], upper := (rows 7 26 37 74 400 36 97 225 353), lower := (rows 7 26 37 74 400 36 64 128 256), losses := [] }

theorem u9228 : Upper (D 6) (R 6) [6,24,33,66,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9228 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9229 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 2, region := 400, targets := 64 }], pairs := [(2,1),(4,1),(4,6)], upper := (rows 7 26 37 74 400 96 101 165 293), lower := (rows 7 26 37 74 400 96 64 128 256), losses := [] }

theorem u9229 : Upper (D 6) (R 6) [6,24,33,66,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9229 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9230 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 7 26 37 76 400 33 98 226 354), lower := (rows 7 26 37 76 400 33 64 128 256), losses := [] }

theorem u9230 : Upper (D 6) (R 6) [6,24,33,68,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9230 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9231 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 37, targets := 64 },{ cop := 2, region := 72, targets := 2 }], pairs := [(0,6),(2,6),(3,1)], upper := (rows 7 26 37 76 400 34 97 225 353), lower := (rows 7 26 37 76 400 34 64 128 256), losses := [] }

theorem u9231 : Upper (D 6) (R 6) [6,24,33,68,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9231 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9232 : Route 9 := (fun mask => (mask,id))

def c9232 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9232 : Upper (D 6) (R 6) [6,24,33,68,384,64] 13 := by
  apply FastRouting.sound _ _ [6,24,33,68,384,64] 13 (by decide) (choices 1) [1,2,32] r9232 c9232
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u926
  · exact u927
  · exact u928

def b9233 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 7 26 37 104 400 33 70 198 326), lower := (rows 7 26 37 104 400 33 64 128 256), losses := [] }

theorem u9233 : Upper (D 6) (R 6) [6,24,33,96,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9233 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9234 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 464, targets := 34 },{ cop := 1, region := 37, targets := 64 }], pairs := [(0,6),(4,1),(4,5)], upper := (rows 7 26 37 104 400 34 69 197 325), lower := (rows 7 26 37 104 400 34 64 128 256), losses := [] }

theorem u9234 : Upper (D 6) (R 6) [6,24,33,96,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9234 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9235 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 474, targets := 4 }], pairs := [(1,2),(3,2),(4,2)], upper := (rows 7 26 37 104 400 36 67 195 323), lower := (rows 7 26 37 104 400 36 64 128 256), losses := [] }

theorem u9235 : Upper (D 6) (R 6) [6,24,33,96,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9235 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9236 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 26 37 104 400 96 71 135 263), lower := (rows 7 26 37 104 400 96 64 128 256), losses := [] }

theorem u9236 : Upper (D 6) (R 6) [6,24,33,96,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9236 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9237 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 37, targets := 64 },{ cop := 2, region := 200, targets := 2 }], pairs := [(0,6),(2,6),(3,1)], upper := (rows 7 26 37 137 336 34 100 228 356), lower := (rows 7 26 37 137 336 34 64 128 256), losses := [] }

theorem u9237 : Upper (D 6) (R 6) [6,24,33,129,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9237 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9238 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 474, targets := 4 }], pairs := [(1,2),(3,2),(4,2)], upper := (rows 7 26 37 137 336 36 98 226 354), lower := (rows 7 26 37 137 336 36 64 128 256), losses := [] }

theorem u9238 : Upper (D 6) (R 6) [6,24,33,129,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9238 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9239 : Route 9 := (fun mask => (mask,id))

def c9239 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9239 : Upper (D 6) (R 6) [6,24,33,129,320,64] 13 := by
  apply FastRouting.sound _ _ [6,24,33,129,320,64] 13 (by decide) (choices 1) [2,4,32] r9239 c9239
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u929
  · exact u930
  · exact u931

#print axioms u9239
end Delivery.IrregularNine14.P06

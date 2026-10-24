import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0124

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b24180 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 276, targets := 64 },{ cop := 0, region := 260, targets := 32 }], pairs := [(2,5),(2,6),(4,6)], upper := (rows 35 138 261 88 52 96 71 135 263), lower := (rows 35 138 261 88 52 96 64 128 256), losses := [] }

theorem u24180 : Upper (D 6) (R 6) [34,136,257,80,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24180 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24181 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 138 261 104 22 33 84 212 340), lower := (rows 35 138 261 104 22 33 64 128 256), losses := [] }

theorem u24181 : Upper (D 6) (R 6) [34,136,257,96,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24181 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24182 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,5),(4,5)], upper := (rows 35 138 261 104 22 36 81 209 337), lower := (rows 35 138 261 104 22 36 64 128 256), losses := [] }

theorem u24182 : Upper (D 6) (R 6) [34,136,257,96,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24182 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24183 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 138 261 104 22 48 69 197 325), lower := (rows 35 138 261 104 22 48 64 128 256), losses := [] }

theorem u24183 : Upper (D 6) (R 6) [34,136,257,96,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24183 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24184 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 138 261 104 22 96 85 149 277), lower := (rows 35 138 261 104 22 96 64 128 256), losses := [] }

theorem u24184 : Upper (D 6) (R 6) [34,136,257,96,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24184 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24185 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 261 104 81 34 84 148 276), lower := (rows 35 138 261 104 81 34 64 128 256), losses := [] }

theorem u24185 : Upper (D 6) (R 6) [34,136,257,96,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24185 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24186 : Route 9 := (fun mask => (mask,id))

def c24186 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24186 : Upper (D 6) (R 6) [34,136,257,96,65,4] 13 := by
  apply FastRouting.sound _ _ [34,136,257,96,65,4] 13 (by decide) (choices 1) [2,4,16] r24186 c24186
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7463
  · exact u7464
  · exact u7465

def b24187 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 138 261 104 81 48 70 134 262), lower := (rows 35 138 261 104 81 48 64 128 256), losses := [] }

theorem u24187 : Upper (D 6) (R 6) [34,136,257,96,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24187 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24188 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 138 261 104 84 33 86 150 278), lower := (rows 35 138 261 104 84 33 64 128 256), losses := [] }

theorem u24188 : Upper (D 6) (R 6) [34,136,257,96,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24188 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24189 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 261 104 84 34 85 149 277), lower := (rows 35 138 261 104 84 34 64 128 256), losses := [] }

theorem u24189 : Upper (D 6) (R 6) [34,136,257,96,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24189 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24190 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 4, region := 40, targets := 1 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 35 138 261 104 84 36 83 147 275), lower := (rows 35 138 261 104 84 36 64 128 256), losses := [] }

theorem u24190 : Upper (D 6) (R 6) [34,136,257,96,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24190 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24191 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 138 261 104 84 48 71 135 263), lower := (rows 35 138 261 104 84 48 64 128 256), losses := [] }

theorem u24191 : Upper (D 6) (R 6) [34,136,257,96,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24191 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24192 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 35 138 262 13 52 33 80 208 336), lower := (rows 35 138 262 13 52 33 64 128 256), losses := [] }

theorem u24192 : Upper (D 6) (R 6) [34,136,258,5,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24192 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24193 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 138 262 13 52 48 65 193 321), lower := (rows 35 138 262 13 52 48 64 128 256), losses := [] }

theorem u24193 : Upper (D 6) (R 6) [34,136,258,5,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24193 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24194 : Route 9 := (fun mask => (mask,id))

def c24194 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24194 : Upper (D 6) (R 6) [34,136,258,5,36,64] 13 := by
  apply FastRouting.sound _ _ [34,136,258,5,36,64] 13 (by decide) (choices 1) [1,16] r24194 c24194
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7466
  · exact u7467

def b24195 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 80, targets := 6 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(4,1),(4,2)], upper := (rows 35 138 262 13 81 36 112 240 368), lower := (rows 35 138 262 13 81 36 64 128 256), losses := [] }

theorem u24195 : Upper (D 6) (R 6) [34,136,258,5,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24195 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24196 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 324, targets := 1 },{ cop := 3, region := 112, targets := 2 }], pairs := [(2,0),(4,1)], upper := (rows 35 138 262 13 81 48 100 228 356), lower := (rows 35 138 262 13 81 48 64 128 256), losses := [] }

theorem u24196 : Upper (D 6) (R 6) [34,136,258,5,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24196 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24197 : Route 9 := (fun mask => (mask,id))

def c24197 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24197 : Upper (D 6) (R 6) [34,136,258,5,65,64] 13 := by
  apply FastRouting.sound _ _ [34,136,258,5,65,64] 13 (by decide) (choices 1) [4,16,32] r24197 c24197
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7468
  · exact u7469
  · exact u7470

def b24198 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 340, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 138 262 13 84 33 112 240 368), lower := (rows 35 138 262 13 84 33 64 128 256), losses := [] }

theorem u24198 : Upper (D 6) (R 6) [34,136,258,5,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24198 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24199 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 112, targets := 2 }], pairs := [(1,2),(4,1)], upper := (rows 35 138 262 13 84 48 97 225 353), lower := (rows 35 138 262 13 84 48 64 128 256), losses := [{ target := 2, region := (rows 1 10 0 8 16 48 65 129 257), good := (rows 483 138 258 459 112 48 64 128 256) }] }

theorem u24199 : Upper (D 6) (R 6) [34,136,258,5,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24199 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24200 : Route 9 := (fun mask => (mask,id))

def c24200 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24200 : Upper (D 6) (R 6) [34,136,258,5,68,64] 13 := by
  apply FastRouting.sound _ _ [34,136,258,5,68,64] 13 (by decide) (choices 1) [1,16,32] r24200 c24200
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7471
  · exact u7472
  · exact u7473

def b24201 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 340, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 138 262 13 112 33 84 212 340), lower := (rows 35 138 262 13 112 33 64 128 256), losses := [] }

theorem u24201 : Upper (D 6) (R 6) [34,136,258,5,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24201 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24202 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 80, targets := 6 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(4,1),(4,2)], upper := (rows 35 138 262 13 112 36 81 209 337), lower := (rows 35 138 262 13 112 36 64 128 256), losses := [] }

theorem u24202 : Upper (D 6) (R 6) [34,136,258,5,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24202 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24203 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 138 262 13 112 48 69 197 325), lower := (rows 35 138 262 13 112 48 64 128 256), losses := [] }

theorem u24203 : Upper (D 6) (R 6) [34,136,258,5,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24203 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24204 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 138 262 13 112 96 85 149 277), lower := (rows 35 138 262 13 112 96 64 128 256), losses := [] }

theorem u24204 : Upper (D 6) (R 6) [34,136,258,5,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24204 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24205 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 138 262 25 52 33 68 196 324), lower := (rows 35 138 262 25 52 33 64 128 256), losses := [] }

theorem u24205 : Upper (D 6) (R 6) [34,136,258,17,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24205 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24206 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 35 138 262 25 52 36 65 193 321), lower := (rows 35 138 262 25 52 36 64 128 256), losses := [] }

theorem u24206 : Upper (D 6) (R 6) [34,136,258,17,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24206 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24207 : Route 9 := (fun mask => (mask,id))

def c24207 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24207 : Upper (D 6) (R 6) [34,136,258,17,36,64] 13 := by
  apply FastRouting.sound _ _ [34,136,258,17,36,64] 13 (by decide) (choices 1) [1,4] r24207 c24207
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7474
  · exact u7475

def b24208 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 340, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 138 262 25 84 33 100 228 356), lower := (rows 35 138 262 25 84 33 64 128 256), losses := [] }

theorem u24208 : Upper (D 6) (R 6) [34,136,258,17,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24208 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24209 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(1,2),(3,6)], upper := (rows 35 138 262 25 84 36 97 225 353), lower := (rows 35 138 262 25 84 36 64 128 256), losses := [{ target := 2, region := (rows 1 10 0 8 16 32 65 129 257), good := (rows 483 138 258 475 80 32 64 128 256) },{ target := 6, region := (rows 5 2 4 24 16 52 0 128 256), good := (rows 35 138 295 57 61 37 0 128 256) }] }

theorem u24209 : Upper (D 6) (R 6) [34,136,258,17,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24209 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24210 : Route 9 := (fun mask => (mask,id))

def c24210 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24210 : Upper (D 6) (R 6) [34,136,258,17,68,64] 13 := by
  apply FastRouting.sound _ _ [34,136,258,17,68,64] 13 (by decide) (choices 1) [1,4,32] r24210 c24210
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7476
  · exact u7477
  · exact u7478

def b24211 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 138 262 25 112 33 68 196 324), lower := (rows 35 138 262 25 112 33 64 128 256), losses := [] }

theorem u24211 : Upper (D 6) (R 6) [34,136,258,17,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24211 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24212 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 454, targets := 32 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(1,5),(2,5)], upper := (rows 35 138 262 25 112 36 69 197 325), lower := (rows 35 138 262 25 112 36 64 128 256), losses := [] }

theorem u24212 : Upper (D 6) (R 6) [34,136,258,17,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24212 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24213 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 138 262 25 112 96 69 133 261), lower := (rows 35 138 262 25 112 96 64 128 256), losses := [] }

theorem u24213 : Upper (D 6) (R 6) [34,136,258,17,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24213 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24214 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 0, region := 324, targets := 1 }], pairs := [(0,2),(0,6),(2,0)], upper := (rows 35 138 262 28 81 33 100 228 356), lower := (rows 35 138 262 28 81 33 64 128 256), losses := [] }

theorem u24214 : Upper (D 6) (R 6) [34,136,258,20,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24214 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24215 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 80, targets := 6 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(4,1),(4,2)], upper := (rows 35 138 262 28 81 36 97 225 353), lower := (rows 35 138 262 28 81 36 64 128 256), losses := [] }

theorem u24215 : Upper (D 6) (R 6) [34,136,258,20,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24215 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24216 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 260, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 35 138 262 28 81 96 101 165 293), lower := (rows 35 138 262 28 81 96 64 128 256), losses := [{ target := 6, region := (rows 1 18 21 24 16 32 0 129 257), good := (rows 423 138 262 30 415 32 0 128 256) }] }

theorem u24216 : Upper (D 6) (R 6) [34,136,258,20,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24216 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24217 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 0, region := 324, targets := 32 }], pairs := [(0,2),(0,6),(2,5)], upper := (rows 35 138 262 28 112 33 69 197 325), lower := (rows 35 138 262 28 112 33 64 128 256), losses := [] }

theorem u24217 : Upper (D 6) (R 6) [34,136,258,20,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24217 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24218 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 80, targets := 6 },{ cop := 0, region := 324, targets := 32 }], pairs := [(2,5),(4,1),(4,2)], upper := (rows 35 138 262 28 112 36 65 193 321), lower := (rows 35 138 262 28 112 36 64 128 256), losses := [] }

theorem u24218 : Upper (D 6) (R 6) [34,136,258,20,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24218 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24219 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 138 262 28 112 96 69 133 261), lower := (rows 35 138 262 28 112 96 64 128 256), losses := [] }

theorem u24219 : Upper (D 6) (R 6) [34,136,258,20,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24219 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24220 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 138 262 44 81 33 84 212 340), lower := (rows 35 138 262 44 81 33 64 128 256), losses := [] }

theorem u24220 : Upper (D 6) (R 6) [34,136,258,36,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24220 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24221 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 211, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 138 262 44 81 36 81 209 337), lower := (rows 35 138 262 44 81 36 64 128 256), losses := [] }

theorem u24221 : Upper (D 6) (R 6) [34,136,258,36,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24221 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24222 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 35 138 262 44 81 48 69 197 325), lower := (rows 35 138 262 44 81 48 64 128 256), losses := [] }

theorem u24222 : Upper (D 6) (R 6) [34,136,258,36,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24222 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24223 : Route 9 := (fun mask => (mask,id))

def c24223 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24223 : Upper (D 6) (R 6) [34,136,258,36,65,64] 13 := by
  apply FastRouting.sound _ _ [34,136,258,36,65,64] 13 (by decide) (choices 1) [1,4,16] r24223 c24223
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7479
  · exact u7480
  · exact u7481

def b24224 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 138 262 44 84 33 81 209 337), lower := (rows 35 138 262 44 84 33 64 128 256), losses := [] }

theorem u24224 : Upper (D 6) (R 6) [34,136,258,36,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24224 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24225 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 138 262 44 84 48 65 193 321), lower := (rows 35 138 262 44 84 48 64 128 256), losses := [] }

theorem u24225 : Upper (D 6) (R 6) [34,136,258,36,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24225 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24226 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 4, region := 40, targets := 1 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 35 138 262 44 84 96 81 145 273), lower := (rows 35 138 262 44 84 96 64 128 256), losses := [] }

theorem u24226 : Upper (D 6) (R 6) [34,136,258,36,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24226 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24227 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 138 262 56 84 33 69 197 325), lower := (rows 35 138 262 56 84 33 64 128 256), losses := [] }

theorem u24227 : Upper (D 6) (R 6) [34,136,258,48,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24227 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24228 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 138 262 56 84 36 65 193 321), lower := (rows 35 138 262 56 84 36 64 128 256), losses := [] }

theorem u24228 : Upper (D 6) (R 6) [34,136,258,48,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24228 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24229 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 138 262 56 84 96 69 133 261), lower := (rows 35 138 262 56 84 96 64 128 256), losses := [] }

theorem u24229 : Upper (D 6) (R 6) [34,136,258,48,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24229 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24230 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 49, targets := 64 },{ cop := 4, region := 104, targets := 2 }], pairs := [(0,6),(3,1),(4,6)], upper := (rows 35 138 262 73 21 36 112 240 368), lower := (rows 35 138 262 73 21 36 64 128 256), losses := [] }

theorem u24230 : Upper (D 6) (R 6) [34,136,258,65,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24230 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24231 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 49, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 138 262 73 21 48 100 228 356), lower := (rows 35 138 262 73 21 48 64 128 256), losses := [] }

theorem u24231 : Upper (D 6) (R 6) [34,136,258,65,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24231 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24232 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 276, targets := 64 },{ cop := 4, region := 104, targets := 2 }], pairs := [(2,6),(3,1),(4,6)], upper := (rows 35 138 262 73 21 96 116 180 308), lower := (rows 35 138 262 73 21 96 64 128 256), losses := [] }

theorem u24232 : Upper (D 6) (R 6) [34,136,258,65,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24232 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24233 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 340, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 138 262 73 52 33 84 212 340), lower := (rows 35 138 262 73 52 33 64 128 256), losses := [] }

theorem u24233 : Upper (D 6) (R 6) [34,136,258,65,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24233 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24234 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 203, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 138 262 73 52 36 81 209 337), lower := (rows 35 138 262 73 52 36 64 128 256), losses := [] }

theorem u24234 : Upper (D 6) (R 6) [34,136,258,65,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24234 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24235 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 138 262 73 52 48 69 197 325), lower := (rows 35 138 262 73 52 48 64 128 256), losses := [] }

theorem u24235 : Upper (D 6) (R 6) [34,136,258,65,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24235 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24236 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 276, targets := 64 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 35 138 262 73 52 96 85 149 277), lower := (rows 35 138 262 73 52 96 64 128 256), losses := [{ target := 2, region := (rows 3 2 0 8 16 104 64 128 256), good := (rows 35 171 259 105 48 96 96 128 256) }] }

theorem u24236 : Upper (D 6) (R 6) [34,136,258,65,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24236 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24237 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 340, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 138 262 73 84 33 116 180 308), lower := (rows 35 138 262 73 84 33 64 128 256), losses := [] }

theorem u24237 : Upper (D 6) (R 6) [34,136,258,65,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24237 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24238 : Route 9 := (fun mask => (mask,id))

def c24238 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24238 : Upper (D 6) (R 6) [34,136,258,65,68,4] 13 := by
  apply FastRouting.sound _ _ [34,136,258,65,68,4] 13 (by decide) (choices 1) [1,16,32] r24238 c24238
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7482
  · exact u7483
  · exact u7484

def b24239 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 260, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 35 138 262 73 84 48 101 165 293), lower := (rows 35 138 262 73 84 48 64 128 256), losses := [{ target := 6, region := (rows 1 10 13 8 16 48 0 129 257), good := (rows 423 142 262 399 52 48 0 128 256) }] }

theorem u24239 : Upper (D 6) (R 6) [34,136,258,65,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24239 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u24239
end Delivery.IrregularNine14.P06

import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0132

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b24180 : PairBound 9 := { available := 138, camps := [{ cop := 2, region := 33, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 134 88 273 33 202 138 394), lower := (rows 37 98 134 88 273 33 64 128 256), losses := [{ target := 7, region := (rows 5 10 4 8 16 53 64 0 256), good := (rows 37 98 39 122 305 33 64 0 256) }] }

theorem u24180 : Upper (D 7) (R 7) [36,96,130,80,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24180 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24181 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 98 134 88 273 34 201 137 393), lower := (rows 37 98 134 88 273 34 64 128 256), losses := [] }

theorem u24181 : Upper (D 7) (R 7) [36,96,130,80,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24181 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24182 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 37 98 134 88 273 40 195 131 387), lower := (rows 37 98 134 88 273 40 64 128 256), losses := [] }

theorem u24182 : Upper (D 7) (R 7) [36,96,130,80,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24182 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24183 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 98 134 88 273 160 75 139 267), lower := (rows 37 98 134 88 273 160 64 128 256), losses := [] }

theorem u24183 : Upper (D 7) (R 7) [36,96,130,80,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24183 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24184 : Route 9 := (fun mask => (mask,id))

def c24184 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24184 : Upper (D 7) (R 7) [36,96,130,80,258,1] 13 := by
  apply FastRouting.sound _ _ [36,96,130,80,258,1] 13 (by decide) (choices 1) [1,8,128] r24184 c24184
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7926
  · exact u7927
  · exact u7928

def b24185 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 37 98 134 88 274 40 193 129 385), lower := (rows 37 98 134 88 274 40 64 128 256), losses := [] }

theorem u24185 : Upper (D 7) (R 7) [36,96,130,80,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24185 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24186 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 98 134 88 274 160 73 137 265), lower := (rows 37 98 134 88 274 160 64 128 256), losses := [] }

theorem u24186 : Upper (D 7) (R 7) [36,96,130,80,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24186 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24187 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 133, targets := 64 },{ cop := 2, region := 33, targets := 130 }], pairs := [(0,1),(0,6),(0,7),(2,6)], upper := (rows 37 98 134 88 280 33 195 131 387), lower := (rows 37 98 134 88 280 33 64 128 256), losses := [] }

theorem u24187 : Upper (D 7) (R 7) [36,96,130,80,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24187 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24188 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 98 134 88 280 34 193 129 385), lower := (rows 37 98 134 88 280 34 64 128 256), losses := [] }

theorem u24188 : Upper (D 7) (R 7) [36,96,130,80,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24188 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24189 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 1, region := 133, targets := 64 }], pairs := [(0,6),(1,7),(3,7),(4,7)], upper := (rows 37 98 134 88 280 160 67 131 259), lower := (rows 37 98 134 88 280 160 64 128 256), losses := [] }

theorem u24189 : Upper (D 7) (R 7) [36,96,130,80,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24189 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24190 : Route 9 := (fun mask => (mask,id))

def c24190 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24190 : Upper (D 7) (R 7) [36,96,130,80,384,1] 13 := by
  apply FastRouting.sound _ _ [36,96,130,80,384,1] 13 (by decide) (choices 1) [1,2,8] r24190 c24190
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7929
  · exact u7930
  · exact u7931

def b24191 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 98 134 88 400 34 73 137 265), lower := (rows 37 98 134 88 400 34 64 128 256), losses := [] }

theorem u24191 : Upper (D 7) (R 7) [36,96,130,80,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24191 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24192 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 37 98 134 88 400 40 67 131 259), lower := (rows 37 98 134 88 400 40 64 128 256), losses := [] }

theorem u24192 : Upper (D 7) (R 7) [36,96,130,80,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24192 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24193 : PairBound 9 := { available := 88, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 98 134 137 273 34 88 216 344), lower := (rows 37 98 134 137 273 34 64 128 256), losses := [] }

theorem u24193 : Upper (D 7) (R 7) [36,96,130,129,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24193 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24194 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 37 98 134 137 273 40 82 210 338), lower := (rows 37 98 134 137 273 40 64 128 256), losses := [] }

theorem u24194 : Upper (D 7) (R 7) [36,96,130,129,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24194 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24195 : Route 9 := (fun mask => (mask,id))

def c24195 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24195 : Upper (D 7) (R 7) [36,96,130,129,257,16] 13 := by
  apply FastRouting.sound _ _ [36,96,130,129,257,16] 13 (by decide) (choices 1) [2,8] r24195 c24195
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7932
  · exact u7933

def b24196 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 134 137 273 96 90 154 282), lower := (rows 37 98 134 137 273 96 64 128 256), losses := [] }

theorem u24196 : Upper (D 7) (R 7) [36,96,130,129,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24196 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24197 : PairBound 9 := { available := 88, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1),(3,6)], upper := (rows 37 98 134 137 274 33 88 216 344), lower := (rows 37 98 134 137 274 33 64 128 256), losses := [] }

theorem u24197 : Upper (D 7) (R 7) [36,96,130,129,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24197 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24198 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 37 98 134 137 274 40 81 209 337), lower := (rows 37 98 134 137 274 40 64 128 256), losses := [] }

theorem u24198 : Upper (D 7) (R 7) [36,96,130,129,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24198 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24199 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 200, targets := 34 },{ cop := 3, region := 370, targets := 128 }], pairs := [(1,7),(3,1),(3,5)], upper := (rows 37 98 134 137 274 48 73 201 329), lower := (rows 37 98 134 137 274 48 64 128 256), losses := [] }

theorem u24199 : Upper (D 7) (R 7) [36,96,130,129,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24199 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24200 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 134 137 274 96 89 153 281), lower := (rows 37 98 134 137 274 96 64 128 256), losses := [] }

theorem u24200 : Upper (D 7) (R 7) [36,96,130,129,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24200 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24201 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1),(3,6)], upper := (rows 37 98 134 137 280 33 82 210 338), lower := (rows 37 98 134 137 280 33 64 128 256), losses := [] }

theorem u24201 : Upper (D 7) (R 7) [36,96,130,129,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24201 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24202 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 98 134 137 280 34 81 209 337), lower := (rows 37 98 134 137 280 34 64 128 256), losses := [] }

theorem u24202 : Upper (D 7) (R 7) [36,96,130,129,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24202 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24203 : Route 9 := (fun mask => (mask,id))

def c24203 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24203 : Upper (D 7) (R 7) [36,96,130,129,264,16] 13 := by
  apply FastRouting.sound _ _ [36,96,130,129,264,16] 13 (by decide) (choices 1) [1,2] r24203 c24203
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7934
  · exact u7935

def b24204 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 134 137 280 96 83 147 275), lower := (rows 37 98 134 137 280 96 64 128 256), losses := [] }

theorem u24204 : Upper (D 7) (R 7) [36,96,130,129,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24204 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24205 : PairBound 9 := { available := 26, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1),(3,6)], upper := (rows 37 98 134 137 336 33 90 154 282), lower := (rows 37 98 134 137 336 33 64 128 256), losses := [] }

theorem u24205 : Upper (D 7) (R 7) [36,96,130,129,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24205 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24206 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 98 134 137 336 34 89 153 281), lower := (rows 37 98 134 137 336 34 64 128 256), losses := [] }

theorem u24206 : Upper (D 7) (R 7) [36,96,130,129,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24206 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24207 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 37 98 134 137 336 40 83 147 275), lower := (rows 37 98 134 137 336 40 64 128 256), losses := [] }

theorem u24207 : Upper (D 7) (R 7) [36,96,130,129,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24207 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24208 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 141, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 98 134 137 336 48 75 139 267), lower := (rows 37 98 134 137 336 48 64 128 256), losses := [] }

theorem u24208 : Upper (D 7) (R 7) [36,96,130,129,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24208 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24209 : PairBound 9 := { available := 74, camps := [{ cop := 2, region := 33, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 134 152 273 33 74 202 330), lower := (rows 37 98 134 152 273 33 64 128 256), losses := [{ target := 7, region := (rows 5 10 4 8 16 53 72 0 264), good := (rows 37 98 39 378 305 33 64 0 256) }] }

theorem u24209 : Upper (D 7) (R 7) [36,96,130,144,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24209 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24210 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 98 134 152 273 34 73 201 329), lower := (rows 37 98 134 152 273 34 64 128 256), losses := [] }

theorem u24210 : Upper (D 7) (R 7) [36,96,130,144,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24210 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24211 : Route 9 := (fun mask => (mask,id))

def c24211 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24211 : Upper (D 7) (R 7) [36,96,130,144,257,8] 13 := by
  apply FastRouting.sound _ _ [36,96,130,144,257,8] 13 (by decide) (choices 1) [1,2] r24211 c24211
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7936
  · exact u7937

def b24212 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 134 152 273 96 75 139 267), lower := (rows 37 98 134 152 273 96 64 128 256), losses := [] }

theorem u24212 : Upper (D 7) (R 7) [36,96,130,144,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24212 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24213 : Route 9 := (fun mask => (mask,id))

def c24213 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24213 : Upper (D 7) (R 7) [36,96,130,144,258,1] 13 := by
  apply FastRouting.sound _ _ [36,96,130,144,258,1] 13 (by decide) (choices 1) [1,8] r24213 c24213
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7938
  · exact u7939

def r24214 : Route 9 := (fun mask => (mask,id))

def c24214 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24214 : Upper (D 7) (R 7) [36,96,130,144,258,8] 13 := by
  apply FastRouting.sound _ _ [36,96,130,144,258,8] 13 (by decide) (choices 1) [1] r24214 c24214
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u7940

def b24215 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 134 152 274 96 73 137 265), lower := (rows 37 98 134 152 274 96 64 128 256), losses := [] }

theorem u24215 : Upper (D 7) (R 7) [36,96,130,144,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24215 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24216 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 33, targets := 66 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 134 152 280 33 67 195 323), lower := (rows 37 98 134 152 280 33 64 128 256), losses := [] }

theorem u24216 : Upper (D 7) (R 7) [36,96,130,144,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24216 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24217 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 98 134 152 280 34 65 193 321), lower := (rows 37 98 134 152 280 34 64 128 256), losses := [] }

theorem u24217 : Upper (D 7) (R 7) [36,96,130,144,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24217 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24218 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 134 152 280 96 67 131 259), lower := (rows 37 98 134 152 280 96 64 128 256), losses := [] }

theorem u24218 : Upper (D 7) (R 7) [36,96,130,144,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24218 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24219 : Route 9 := (fun mask => (mask,id))

def c24219 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24219 : Upper (D 7) (R 7) [36,96,130,144,320,1] 13 := by
  apply FastRouting.sound _ _ [36,96,130,144,320,1] 13 (by decide) (choices 1) [1,2,8] r24219 c24219
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7941
  · exact u7942
  · exact u7943

def b24220 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 98 134 152 336 34 73 137 265), lower := (rows 37 98 134 152 336 34 64 128 256), losses := [] }

theorem u24220 : Upper (D 7) (R 7) [36,96,130,144,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24220 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24221 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 338, targets := 128 },{ cop := 1, region := 133, targets := 64 }], pairs := [(0,6),(1,7),(4,7)], upper := (rows 37 98 134 152 336 40 67 131 259), lower := (rows 37 98 134 152 336 40 64 128 256), losses := [] }

theorem u24221 : Upper (D 7) (R 7) [36,96,130,144,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24221 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24222 : Route 9 := (fun mask => (mask,id))

def c24222 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24222 : Upper (D 7) (R 7) [36,96,130,192,257,1] 13 := by
  apply FastRouting.sound _ _ [36,96,130,192,257,1] 13 (by decide) (choices 1) [2,8,16] r24222 c24222
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7944
  · exact u7945
  · exact u7946

def b24223 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 98 134 200 273 34 89 153 281), lower := (rows 37 98 134 200 273 34 64 128 256), losses := [] }

theorem u24223 : Upper (D 7) (R 7) [36,96,130,192,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24223 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24224 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 37 98 134 200 273 40 83 147 275), lower := (rows 37 98 134 200 273 40 64 128 256), losses := [] }

theorem u24224 : Upper (D 7) (R 7) [36,96,130,192,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24224 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24225 : Route 9 := (fun mask => (mask,id))

def c24225 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24225 : Upper (D 7) (R 7) [36,96,130,192,257,16] 13 := by
  apply FastRouting.sound _ _ [36,96,130,192,257,16] 13 (by decide) (choices 1) [1,2,8] r24225 c24225
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7947
  · exact u7948
  · exact u7949

def r24226 : Route 9 := (fun mask => (mask,id))

def c24226 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24226 : Upper (D 7) (R 7) [36,96,130,192,258,1] 13 := by
  apply FastRouting.sound _ _ [36,96,130,192,258,1] 13 (by decide) (choices 1) [1,8,16] r24226 c24226
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7950
  · exact u7951
  · exact u7952

def b24227 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 37 98 134 200 274 40 81 145 273), lower := (rows 37 98 134 200 274 40 64 128 256), losses := [] }

theorem u24227 : Upper (D 7) (R 7) [36,96,130,192,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24227 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24228 : Route 9 := (fun mask => (mask,id))

def c24228 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24228 : Upper (D 7) (R 7) [36,96,130,192,258,16] 13 := by
  apply FastRouting.sound _ _ [36,96,130,192,258,16] 13 (by decide) (choices 1) [1,8] r24228 c24228
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7953
  · exact u7954

def r24229 : Route 9 := (fun mask => (mask,id))

def c24229 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24229 : Upper (D 7) (R 7) [36,96,130,192,264,1] 13 := by
  apply FastRouting.sound _ _ [36,96,130,192,264,1] 13 (by decide) (choices 1) [1,2,16] r24229 c24229
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7955
  · exact u7956
  · exact u7957

def b24230 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 98 134 200 280 34 81 145 273), lower := (rows 37 98 134 200 280 34 64 128 256), losses := [] }

theorem u24230 : Upper (D 7) (R 7) [36,96,130,192,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24230 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24231 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 133, targets := 64 },{ cop := 0, region := 66, targets := 128 }], pairs := [(0,6),(1,7),(2,6)], upper := (rows 37 98 134 200 280 48 67 131 259), lower := (rows 37 98 134 200 280 48 64 128 256), losses := [] }

theorem u24231 : Upper (D 7) (R 7) [36,96,130,192,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24231 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24232 : PairBound 9 := { available := 400, camps := [{ cop := 3, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 37 98 140 11 81 34 464 400 400), lower := (rows 37 98 140 11 81 34 64 128 256), losses := [] }

theorem u24232 : Upper (D 7) (R 7) [36,96,136,3,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24232 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24233 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 98 140 11 81 48 450 386 386), lower := (rows 37 98 140 11 81 48 64 128 256), losses := [] }

theorem u24233 : Upper (D 7) (R 7) [36,96,136,3,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24233 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24234 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 98 140 11 81 160 338 402 274), lower := (rows 37 98 140 11 81 160 64 128 256), losses := [] }

theorem u24234 : Upper (D 7) (R 7) [36,96,136,3,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24234 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24235 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 212, targets := 32 },{ cop := 4, region := 418, targets := 1 }], pairs := [(1,0),(2,5),(4,5)], upper := (rows 37 98 140 11 81 288 210 146 402), lower := (rows 37 98 140 11 81 288 64 128 256), losses := [] }

theorem u24235 : Upper (D 7) (R 7) [36,96,136,3,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24235 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24236 : PairBound 9 := { available := 336, camps := [{ cop := 3, region := 468, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 37 98 140 11 146 33 336 464 336), lower := (rows 37 98 140 11 146 33 64 128 256), losses := [] }

theorem u24236 : Upper (D 7) (R 7) [36,96,136,3,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24236 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24237 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 45, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 98 140 11 146 48 321 449 321), lower := (rows 37 98 140 11 146 48 64 128 256), losses := [] }

theorem u24237 : Upper (D 7) (R 7) [36,96,136,3,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24237 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24238 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 140 11 146 96 337 401 273), lower := (rows 37 98 140 11 146 96 64 128 256), losses := [] }

theorem u24238 : Upper (D 7) (R 7) [36,96,136,3,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24238 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24239 : Route 9 := (fun mask => (mask,id))

def c24239 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24239 : Upper (D 7) (R 7) [36,96,136,3,130,256] 13 := by
  apply FastRouting.sound _ _ [36,96,136,3,130,256] 13 (by decide) (choices 1) [1,16] r24239 c24239
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7958
  · exact u7959

#print axioms u24239
end Delivery.IrregularNine14.P07

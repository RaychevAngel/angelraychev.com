import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0038

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b14160 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 196, targets := 34 },{ cop := 0, region := 464, targets := 32 }], pairs := [(2,1),(2,5),(4,5)], upper := (rows 7 98 140 41 274 48 193 193 449), lower := (rows 7 98 140 41 274 48 64 128 256), losses := [] }

theorem u14160 : Upper (D 7) (R 7) [6,96,136,33,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14160 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14161 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 140 41 274 96 209 145 401), lower := (rows 7 98 140 41 274 96 64 128 256), losses := [] }

theorem u14161 : Upper (D 7) (R 7) [6,96,136,33,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14161 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14162 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 338, targets := 128 },{ cop := 0, region := 336, targets := 32 }], pairs := [(1,7),(3,1),(4,5),(4,7)], upper := (rows 7 98 140 41 274 160 81 209 337), lower := (rows 7 98 140 41 274 160 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 16 164 64 128 256), good := (rows 45 96 172 41 272 160 64 160 256) }] }

theorem u14162 : Upper (D 7) (R 7) [6,96,136,33,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14162 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14163 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 40, targets := 194 },{ cop := 3, region := 466, targets := 1 }], pairs := [(1,0),(3,1),(3,6),(3,7)], upper := (rows 7 98 140 41 336 33 210 146 402), lower := (rows 7 98 140 41 336 33 64 128 256), losses := [] }

theorem u14163 : Upper (D 7) (R 7) [6,96,136,33,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14163 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14164 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 7 98 140 41 336 34 209 145 401), lower := (rows 7 98 140 41 336 34 64 128 256), losses := [] }

theorem u14164 : Upper (D 7) (R 7) [6,96,136,33,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14164 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14165 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 141, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 140 41 336 48 195 131 387), lower := (rows 7 98 140 41 336 48 64 128 256), losses := [] }

theorem u14165 : Upper (D 7) (R 7) [6,96,136,33,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14165 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14166 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 338, targets := 128 },{ cop := 0, region := 336, targets := 32 }], pairs := [(1,7),(3,1),(4,5),(4,7)], upper := (rows 7 98 140 41 336 160 83 147 275), lower := (rows 7 98 140 41 336 160 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 16 164 64 128 256), good := (rows 45 96 172 41 336 160 64 160 256) }] }

theorem u14166 : Upper (D 7) (R 7) [6,96,136,33,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14166 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14167 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 40, targets := 194 },{ cop := 3, region := 466, targets := 1 }], pairs := [(1,0),(3,1),(3,6),(3,7)], upper := (rows 7 98 140 41 400 33 82 210 338), lower := (rows 7 98 140 41 400 33 64 128 256), losses := [] }

theorem u14167 : Upper (D 7) (R 7) [6,96,136,33,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14167 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14168 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 7 98 140 41 400 34 81 209 337), lower := (rows 7 98 140 41 400 34 64 128 256), losses := [] }

theorem u14168 : Upper (D 7) (R 7) [6,96,136,33,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14168 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14169 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 464, targets := 32 },{ cop := 3, region := 66, targets := 128 }], pairs := [(1,7),(2,5),(4,5)], upper := (rows 7 98 140 41 400 48 67 195 323), lower := (rows 7 98 140 41 400 48 64 128 256), losses := [{ target := 5, region := (rows 1 2 12 8 25 0 65 129 257), good := (rows 471 66 156 477 400 16 64 128 256) }] }

theorem u14169 : Upper (D 7) (R 7) [6,96,136,33,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14169 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14170 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 140 41 400 96 83 147 275), lower := (rows 7 98 140 41 400 96 64 128 256), losses := [] }

theorem u14170 : Upper (D 7) (R 7) [6,96,136,33,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14170 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14171 : PairBound 9 := { available := 386, camps := [{ cop := 3, region := 454, targets := 1 },{ cop := 4, region := 40, targets := 66 }], pairs := [(1,0),(2,0),(3,1),(3,6)], upper := (rows 7 98 140 56 81 33 450 386 386), lower := (rows 7 98 140 56 81 33 64 128 256), losses := [] }

theorem u14171 : Upper (D 7) (R 7) [6,96,136,48,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14171 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14172 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 42, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 7 98 140 56 81 34 449 385 385), lower := (rows 7 98 140 56 81 34 64 128 256), losses := [] }

theorem u14172 : Upper (D 7) (R 7) [6,96,136,48,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14172 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14173 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 336, targets := 32 },{ cop := 0, region := 336, targets := 128 }], pairs := [(2,6),(3,6),(4,5),(4,7)], upper := (rows 7 98 140 56 81 160 323 387 259), lower := (rows 7 98 140 56 81 160 64 128 256), losses := [{ target := 6, region := (rows 1 2 20 24 16 181 0 129 257), good := (rows 423 34 172 60 445 160 0 160 256) }] }

theorem u14173 : Upper (D 7) (R 7) [6,96,136,48,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14173 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14174 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(2,6),(3,6),(4,5)], upper := (rows 7 98 140 56 81 288 195 131 387), lower := (rows 7 98 140 56 81 288 64 128 256), losses := [{ target := 6, region := (rows 1 2 20 24 16 305 0 129 257), good := (rows 423 34 140 60 445 288 0 128 288) }] }

theorem u14174 : Upper (D 7) (R 7) [6,96,136,48,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14174 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14175 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 45, targets := 64 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,6),(0,7),(2,6),(3,6)], upper := (rows 7 98 140 56 146 33 321 449 321), lower := (rows 7 98 140 56 146 33 64 128 256), losses := [] }

theorem u14175 : Upper (D 7) (R 7) [6,96,136,48,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14175 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14176 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 140 56 146 96 321 385 257), lower := (rows 7 98 140 56 146 96 64 128 256), losses := [] }

theorem u14176 : Upper (D 7) (R 7) [6,96,136,48,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14176 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14177 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 0, region := 208, targets := 32 }], pairs := [(0,7),(1,7),(4,5)], upper := (rows 7 98 140 56 146 288 65 193 321), lower := (rows 7 98 140 56 146 288 64 128 256), losses := [] }

theorem u14177 : Upper (D 7) (R 7) [6,96,136,48,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14177 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14178 : Route 9 := (fun mask => (mask,id))

def c14178 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u14178 : Upper (D 7) (R 7) [6,96,136,48,192,1] 13 := by
  apply FastRouting.sound _ _ [6,96,136,48,192,1] 13 (by decide) (choices 1) [1,2,256] r14178 c14178
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2290
  · exact u2291
  · exact u2292

def b14179 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 46, targets := 1 },{ cop := 0, region := 464, targets := 2 }], pairs := [(1,0),(2,0),(3,0),(4,1)], upper := (rows 7 98 140 56 208 34 321 385 257), lower := (rows 7 98 140 56 208 34 64 128 256), losses := [] }

theorem u14179 : Upper (D 7) (R 7) [6,96,136,48,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14179 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14180 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 0, region := 208, targets := 32 }], pairs := [(0,7),(1,7),(4,5)], upper := (rows 7 98 140 56 208 288 67 131 259), lower := (rows 7 98 140 56 208 288 64 128 256), losses := [] }

theorem u14180 : Upper (D 7) (R 7) [6,96,136,48,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14180 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14181 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 40, targets := 194 },{ cop := 3, region := 194, targets := 1 }], pairs := [(1,0),(3,1),(3,6),(3,7)], upper := (rows 7 98 140 56 273 33 194 194 450), lower := (rows 7 98 140 56 273 33 64 128 256), losses := [] }

theorem u14181 : Upper (D 7) (R 7) [6,96,136,48,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14181 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14182 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 464, targets := 34 },{ cop := 6, region := 34, targets := 129 }], pairs := [(1,0),(1,7),(4,1),(4,5)], upper := (rows 7 98 140 56 273 34 193 193 449), lower := (rows 7 98 140 56 273 34 64 128 256), losses := [] }

theorem u14182 : Upper (D 7) (R 7) [6,96,136,48,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14182 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14183 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 140 56 273 96 195 131 387), lower := (rows 7 98 140 56 273 96 64 128 256), losses := [] }

theorem u14183 : Upper (D 7) (R 7) [6,96,136,48,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14183 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14184 : Route 9 := (fun mask => (mask,id))

def c14184 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14184 : Upper (D 7) (R 7) [6,96,136,48,257,128] 13 := by
  apply FastRouting.sound _ _ [6,96,136,48,257,128] 13 (by decide) (choices 1) [1,2] r14184 c14184
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2293
  · exact u2294

def r14185 : Route 9 := (fun mask => (mask,id))

def c14185 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14185 : Upper (D 7) (R 7) [6,96,136,48,258,1] 13 := by
  apply FastRouting.sound _ _ [6,96,136,48,258,1] 13 (by decide) (choices 1) [1,128] r14185 c14185
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2295
  · exact u2296

def b14186 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 140 56 274 96 193 129 385), lower := (rows 7 98 140 56 274 96 64 128 256), losses := [] }

theorem u14186 : Upper (D 7) (R 7) [6,96,136,48,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14186 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14187 : Route 9 := (fun mask => (mask,id))

def c14187 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14187 : Upper (D 7) (R 7) [6,96,136,48,258,128] 13 := by
  apply FastRouting.sound _ _ [6,96,136,48,258,128] 13 (by decide) (choices 1) [1] r14187 c14187
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u2297

def r14188 : Route 9 := (fun mask => (mask,id))

def c14188 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14188 : Upper (D 7) (R 7) [6,96,136,48,320,1] 13 := by
  apply FastRouting.sound _ _ [6,96,136,48,320,1] 13 (by decide) (choices 1) [1,2,128] r14188 c14188
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2298
  · exact u2299
  · exact u2300

def b14189 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 42, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 7 98 140 56 336 34 193 129 385), lower := (rows 7 98 140 56 336 34 64 128 256), losses := [] }

theorem u14189 : Upper (D 7) (R 7) [6,96,136,48,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14189 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14190 : Route 9 := (fun mask => (mask,id))

def c14190 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14190 : Upper (D 7) (R 7) [6,96,136,48,320,128] 13 := by
  apply FastRouting.sound _ _ [6,96,136,48,320,128] 13 (by decide) (choices 1) [1,2] r14190 c14190
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2301
  · exact u2302

def r14191 : Route 9 := (fun mask => (mask,id))

def c14191 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14191 : Upper (D 7) (R 7) [6,96,136,48,384,1] 13 := by
  apply FastRouting.sound _ _ [6,96,136,48,384,1] 13 (by decide) (choices 1) [1,2] r14191 c14191
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2303
  · exact u2304

def b14192 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 464, targets := 34 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(1,7),(4,1),(4,5)], upper := (rows 7 98 140 56 400 34 65 193 321), lower := (rows 7 98 140 56 400 34 64 128 256), losses := [] }

theorem u14192 : Upper (D 7) (R 7) [6,96,136,48,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14192 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14193 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 140 56 400 96 67 131 259), lower := (rows 7 98 140 56 400 96 64 128 256), losses := [] }

theorem u14193 : Upper (D 7) (R 7) [6,96,136,48,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14193 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14194 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,5)], upper := (rows 7 98 140 265 49 34 208 208 464), lower := (rows 7 98 140 265 49 34 64 128 256), losses := [] }

theorem u14194 : Upper (D 7) (R 7) [6,96,136,257,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14194 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14195 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 48, targets := 194 }], pairs := [(4,1),(4,6),(4,7)], upper := (rows 7 98 140 265 49 48 194 194 450), lower := (rows 7 98 140 265 49 48 64 128 256), losses := [] }

theorem u14195 : Upper (D 7) (R 7) [6,96,136,257,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14195 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14196 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 140 265 49 96 210 146 402), lower := (rows 7 98 140 265 49 96 64 128 256), losses := [] }

theorem u14196 : Upper (D 7) (R 7) [6,96,136,257,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14196 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14197 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 330, targets := 128 },{ cop := 4, region := 66, targets := 1 }], pairs := [(1,0),(1,7),(3,7),(4,1)], upper := (rows 7 98 140 265 49 160 82 210 338), lower := (rows 7 98 140 265 49 160 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 164 64 128 256), good := (rows 53 96 172 281 49 160 64 160 256) }] }

theorem u14197 : Upper (D 7) (R 7) [6,96,136,257,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14197 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14198 : Route 9 := (fun mask => (mask,id))

def c14198 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14198 : Upper (D 7) (R 7) [6,96,136,257,129,2] 13 := by
  apply FastRouting.sound _ _ [6,96,136,257,129,2] 13 (by decide) (choices 1) [16,32] r14198 c14198
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2305
  · exact u2306

def b14199 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 362, targets := 128 },{ cop := 4, region := 98, targets := 1 }], pairs := [(1,0),(1,7),(3,7)], upper := (rows 7 98 140 265 145 48 98 226 354), lower := (rows 7 98 140 265 145 48 64 128 256), losses := [] }

theorem u14199 : Upper (D 7) (R 7) [6,96,136,257,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14199 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14200 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 140 265 145 96 114 178 306), lower := (rows 7 98 140 265 145 96 64 128 256), losses := [] }

theorem u14200 : Upper (D 7) (R 7) [6,96,136,257,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14200 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14201 : Route 9 := (fun mask => (mask,id))

def c14201 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14201 : Upper (D 7) (R 7) [6,96,136,257,130,1] 13 := by
  apply FastRouting.sound _ _ [6,96,136,257,130,1] 13 (by decide) (choices 1) [16,32] r14201 c14201
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2307
  · exact u2308

theorem m14202_1 : Upper (D 7) (R 7) [6,96,136,257,130,16,1] 13 :=
  permutation_upper _ _ _ [6,96,136,257,130,1,16] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2307

def r14202 : Route 9 := (fun mask => (mask,id))

def c14202 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14202 : Upper (D 7) (R 7) [6,96,136,257,130,16] 13 := by
  apply FastRouting.sound _ _ [6,96,136,257,130,16] 13 (by decide) (choices 1) [1,32] r14202 c14202
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m14202_1
  · exact u2309

def b14203 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 140 265 146 96 113 177 305), lower := (rows 7 98 140 265 146 96 64 128 256), losses := [] }

theorem u14203 : Upper (D 7) (R 7) [6,96,136,257,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14203 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14204 : PairBound 9 := { available := 82, camps := [{ cop := 5, region := 210, targets := 1 },{ cop := 4, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(2,0),(4,0)], upper := (rows 7 98 140 265 176 33 82 210 338), lower := (rows 7 98 140 265 176 33 64 128 256), losses := [{ target := 0, region := (rows 0 50 12 8 50 32 115 179 307), good := (rows 470 498 140 460 498 498 64 128 256) }] }

theorem u14204 : Upper (D 7) (R 7) [6,96,136,257,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14204 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14205 : Route 9 := (fun mask => (mask,id))

def c14205 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14205 : Upper (D 7) (R 7) [6,96,136,257,160,2] 13 := by
  apply FastRouting.sound _ _ [6,96,136,257,160,2] 13 (by decide) (choices 1) [1,16] r14205 c14205
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2310
  · exact u2311

def b14206 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 397, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 98 140 265 176 48 67 195 323), lower := (rows 7 98 140 265 176 48 64 128 256), losses := [] }

theorem u14206 : Upper (D 7) (R 7) [6,96,136,257,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14206 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14207 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 140 265 176 96 83 147 275), lower := (rows 7 98 140 265 176 96 64 128 256), losses := [] }

theorem u14207 : Upper (D 7) (R 7) [6,96,136,257,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14207 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14208 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 462, targets := 1 },{ cop := 0, region := 48, targets := 64 }], pairs := [(1,0),(2,0),(3,0),(4,6)], upper := (rows 7 98 140 266 49 33 208 208 464), lower := (rows 7 98 140 266 49 33 64 128 256), losses := [] }

theorem u14208 : Upper (D 7) (R 7) [6,96,136,258,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14208 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14209 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 397, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 98 140 266 49 48 193 193 449), lower := (rows 7 98 140 266 49 48 64 128 256), losses := [] }

theorem u14209 : Upper (D 7) (R 7) [6,96,136,258,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14209 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14210 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 140 266 49 96 209 145 401), lower := (rows 7 98 140 266 49 96 64 128 256), losses := [] }

theorem u14210 : Upper (D 7) (R 7) [6,96,136,258,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14210 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14211 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 330, targets := 128 },{ cop := 0, region := 240, targets := 2 }], pairs := [(1,7),(3,7),(4,1),(4,6)], upper := (rows 7 98 140 266 49 160 81 209 337), lower := (rows 7 98 140 266 49 160 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 8 17 164 0 128 256), good := (rows 55 34 172 266 49 160 0 160 256) }] }

theorem u14211 : Upper (D 7) (R 7) [6,96,136,258,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14211 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14212 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 362, targets := 128 },{ cop := 0, region := 240, targets := 2 }], pairs := [(1,7),(2,1),(3,7),(4,1)], upper := (rows 7 98 140 266 145 33 112 240 368), lower := (rows 7 98 140 266 145 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 49 49 115 179 307), good := (rows 501 496 140 460 497 497 64 128 256) }] }

theorem u14212 : Upper (D 7) (R 7) [6,96,136,258,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14212 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14213 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 362, targets := 128 },{ cop := 0, region := 240, targets := 2 }], pairs := [(1,7),(3,7),(4,1)], upper := (rows 7 98 140 266 145 48 97 225 353), lower := (rows 7 98 140 266 145 48 64 128 256), losses := [] }

theorem u14213 : Upper (D 7) (R 7) [6,96,136,258,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14213 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14214 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 140 266 145 96 113 177 305), lower := (rows 7 98 140 266 145 96 64 128 256), losses := [] }

theorem u14214 : Upper (D 7) (R 7) [6,96,136,258,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14214 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14215 : Route 9 := (fun mask => (mask,id))

def c14215 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14215 : Upper (D 7) (R 7) [6,96,136,258,160,1] 13 := by
  apply FastRouting.sound _ _ [6,96,136,258,160,1] 13 (by decide) (choices 1) [1,16] r14215 c14215
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2312
  · exact u2313

def b14216 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 397, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 98 140 266 176 48 65 193 321), lower := (rows 7 98 140 266 176 48 64 128 256), losses := [] }

theorem u14216 : Upper (D 7) (R 7) [6,96,136,258,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14216 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14217 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 140 266 176 96 81 145 273), lower := (rows 7 98 140 266 176 96 64 128 256), losses := [] }

theorem u14217 : Upper (D 7) (R 7) [6,96,136,258,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14217 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14218 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 48, targets := 194 },{ cop := 4, region := 194, targets := 1 }], pairs := [(1,0),(4,1),(4,6),(4,7)], upper := (rows 7 98 140 280 49 33 194 194 450), lower := (rows 7 98 140 280 49 33 64 128 256), losses := [] }

theorem u14218 : Upper (D 7) (R 7) [6,96,136,272,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14218 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14219 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,5)], upper := (rows 7 98 140 280 49 34 193 193 449), lower := (rows 7 98 140 280 49 34 64 128 256), losses := [] }

theorem u14219 : Upper (D 7) (R 7) [6,96,136,272,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14219 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u14219
end Delivery.IrregularNine14.P07

import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P10C0014
import IrregularNine14P10C0015

namespace Delivery.IrregularNine14.P10
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2160 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 70 140 328 273 176 240 176 432), lower := (rows 35 70 140 328 273 32 64 128 256), losses := [] }

theorem u2160 : Upper (D 10) (R 10) [34,68,136,320,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2160 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2161 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 70 140 328 304 177 241 177 433), lower := (rows 35 70 140 328 304 32 64 128 256), losses := [] }

theorem u2161 : Upper (D 10) (R 10) [34,68,136,320,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2161 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2162 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 70 140 328 400 49 113 177 305), lower := (rows 35 70 140 328 400 32 64 128 256), losses := [] }

theorem u2162 : Upper (D 10) (R 10) [34,68,136,320,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2162 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2163 : PairBound 9 := { available := 305, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 70 140 392 112 305 369 433 305), lower := (rows 35 70 140 392 112 32 64 128 256), losses := [] }

theorem u2163 : Upper (D 10) (R 10) [34,68,136,384,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2163 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2164 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 70 140 392 273 112 112 240 368), lower := (rows 35 70 140 392 273 32 64 128 256), losses := [] }

theorem u2164 : Upper (D 10) (R 10) [34,68,136,384,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2164 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2165 : PairBound 9 := { available := 113, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 70 140 392 304 113 113 241 369), lower := (rows 35 70 140 392 304 32 64 128 256), losses := [] }

theorem u2165 : Upper (D 10) (R 10) [34,68,136,384,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2165 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2166 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 70 140 392 336 49 113 177 305), lower := (rows 35 70 140 392 336 32 64 128 256), losses := [] }

theorem u2166 : Upper (D 10) (R 10) [34,68,136,384,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2166 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2167 : Route 9 := (fun mask => (mask,id))

def c2167 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u2167 : Upper (D 10) (R 10) [34,68,160,48,192] 13 := by
  apply FastRouting.sound _ _ [34,68,160,48,192] 13 (by decide) (choices 1) [1,8,256] r2167 c2167
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u847
  · exact u848
  · exact u849

def r2168 : Route 9 := (fun mask => (mask,id))

def c2168 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u2168 : Upper (D 10) (R 10) [34,68,160,48,320] 13 := by
  apply FastRouting.sound _ _ [34,68,160,48,320] 13 (by decide) (choices 1) [1,8,128,256] r2168 c2168
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u850
  · exact u851
  · exact u852
  · exact u853

def r2169 : Route 9 := (fun mask => (mask,id))

def c2169 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u2169 : Upper (D 10) (R 10) [34,68,160,48,384] 13 := by
  apply FastRouting.sound _ _ [34,68,160,48,384] 13 (by decide) (choices 1) [1,8,64,256] r2169 c2169
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u854
  · exact u855
  · exact u856
  · exact u857

def b2170 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 35 70 164 73 152 304 368 432 304), lower := (rows 35 70 164 73 152 32 64 128 256), losses := [] }

theorem u2170 : Upper (D 10) (R 10) [34,68,160,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2170 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2171 : PairBound 9 := { available := 432, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 35 70 164 73 280 432 496 432 432), lower := (rows 35 70 164 73 280 32 64 128 256), losses := [] }

theorem u2171 : Upper (D 10) (R 10) [34,68,160,65,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2171 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2172 : PairBound 9 := { available := 408, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 35 70 164 73 304 440 472 408 408), lower := (rows 35 70 164 73 304 32 64 128 256), losses := [] }

theorem u2172 : Upper (D 10) (R 10) [34,68,160,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2172 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2173 : PairBound 9 := { available := 312, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 35 70 164 73 400 312 376 440 312), lower := (rows 35 70 164 73 400 32 64 128 256), losses := [] }

theorem u2173 : Upper (D 10) (R 10) [34,68,160,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2173 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2174 : PairBound 9 := { available := 296, camps := [{ cop := 3, region := 420, targets := 64 },{ cop := 4, region := 360, targets := 128 }], pairs := [(2,6),(3,7)], upper := (rows 35 70 164 88 145 296 360 424 296), lower := (rows 35 70 164 88 145 32 64 128 256), losses := [] }

theorem u2174 : Upper (D 10) (R 10) [34,68,160,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2174 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2175 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 70 164 88 152 289 353 417 289), lower := (rows 35 70 164 88 152 32 64 128 256), losses := [] }

theorem u2175 : Upper (D 10) (R 10) [34,68,160,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2175 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2176 : PairBound 9 := { available := 265, camps := [{ cop := 2, region := 16, targets := 320 }], pairs := [(4,6),(4,8)], upper := (rows 35 70 164 88 176 297 329 393 265), lower := (rows 35 70 164 88 176 32 64 128 256), losses := [] }

theorem u2176 : Upper (D 10) (R 10) [34,68,160,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2176 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2177 : Route 9 := (fun mask => (mask,id))

def c2177 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u2177 : Upper (D 10) (R 10) [34,68,160,80,257] 13 := by
  apply FastRouting.sound _ _ [34,68,160,80,257] 13 (by decide) (choices 1) [8,128,256] r2177 c2177
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u858
  · exact u859
  · exact u860

def b2178 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 70 164 88 280 417 481 417 417), lower := (rows 35 70 164 88 280 32 64 128 256), losses := [] }

theorem u2178 : Upper (D 10) (R 10) [34,68,160,80,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2178 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2179 : Route 9 := (fun mask => (mask,id))

def c2179 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u2179 : Upper (D 10) (R 10) [34,68,160,80,288] 13 := by
  apply FastRouting.sound _ _ [34,68,160,80,288] 13 (by decide) (choices 1) [1,8,128,256] r2179 c2179
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u861
  · exact u862
  · exact u863
  · exact u864

def r2180 : Route 9 := (fun mask => (mask,id))

def c2180 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u2180 : Upper (D 10) (R 10) [34,68,160,80,384] 13 := by
  apply FastRouting.sound _ _ [34,68,160,80,384] 13 (by decide) (choices 1) [1,8,256] r2180 c2180
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u865
  · exact u866
  · exact u867

def r2181 : Route 9 := (fun mask => (mask,id))

def c2181 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u2181 : Upper (D 10) (R 10) [34,68,160,96,129] 13 := by
  apply FastRouting.sound _ _ [34,68,160,96,129] 13 (by decide) (choices 1) [8,16,256] r2181 c2181
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u868
  · exact u869
  · exact u870

def r2182 : Route 9 := (fun mask => (mask,id))

def c2182 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u2182 : Upper (D 10) (R 10) [34,68,160,96,136] 13 := by
  apply FastRouting.sound _ _ [34,68,160,96,136] 13 (by decide) (choices 1) [1,16,256] r2182 c2182
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u871
  · exact u872
  · exact u873

def r2183 : Route 9 := (fun mask => (mask,id))

def c2183 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0)

theorem u2183 : Upper (D 10) (R 10) [34,68,160,96,257] 13 := by
  apply FastRouting.sound _ _ [34,68,160,96,257] 13 (by decide) (choices 1) [8,16,128,256] r2183 c2183
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u874
  · exact u875
  · exact u876
  · exact u877

def r2184 : Route 9 := (fun mask => (mask,id))

def c2184 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u2184 : Upper (D 10) (R 10) [34,68,160,96,264] 13 := by
  apply FastRouting.sound _ _ [34,68,160,96,264] 13 (by decide) (choices 1) [1,16,128,256] r2184 c2184
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u878
  · exact u879
  · exact u880
  · exact u881

def r2185 : Route 9 := (fun mask => (mask,id))

def c2185 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u2185 : Upper (D 10) (R 10) [34,68,160,96,384] 13 := by
  apply FastRouting.sound _ _ [34,68,160,96,384] 13 (by decide) (choices 1) [1,8,16,256] r2185 c2185
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u882
  · exact u883
  · exact u884
  · exact u885

def r2186 : Route 9 := (fun mask => (mask,id))

def c2186 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u2186 : Upper (D 10) (R 10) [34,68,160,129,264] 13 := by
  apply FastRouting.sound _ _ [34,68,160,129,264] 13 (by decide) (choices 1) [16,64,256] r2186 c2186
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u886
  · exact u887
  · exact u888

def r2187 : Route 9 := (fun mask => (mask,id))

def c2187 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | _ => 0)

theorem u2187 : Upper (D 10) (R 10) [34,68,160,129,288] 13 := by
  apply FastRouting.sound _ _ [34,68,160,129,288] 13 (by decide) (choices 1) [8,16,64,256] r2187 c2187
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u889
  · exact u890
  · exact u891
  · exact u892

def r2188 : Route 9 := (fun mask => (mask,id))

def c2188 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u2188 : Upper (D 10) (R 10) [34,68,160,129,320] 13 := by
  apply FastRouting.sound _ _ [34,68,160,129,320] 13 (by decide) (choices 1) [8,16,256] r2188 c2188
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u893
  · exact u894
  · exact u895

def r2189 : Route 9 := (fun mask => (mask,id))

def c2189 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u2189 : Upper (D 10) (R 10) [34,68,160,144,257] 13 := by
  apply FastRouting.sound _ _ [34,68,160,144,257] 13 (by decide) (choices 1) [8,64,256] r2189 c2189
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u896
  · exact u897
  · exact u898

def b2190 : PairBound 9 := { available := 353, camps := [{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 70 164 152 280 353 353 481 353), lower := (rows 35 70 164 152 280 32 64 128 256), losses := [] }

theorem u2190 : Upper (D 10) (R 10) [34,68,160,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2190 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2191 : Route 9 := (fun mask => (mask,id))

def c2191 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u2191 : Upper (D 10) (R 10) [34,68,160,144,288] 13 := by
  apply FastRouting.sound _ _ [34,68,160,144,288] 13 (by decide) (choices 1) [1,8,64,256] r2191 c2191
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u899
  · exact u900
  · exact u901
  · exact u902

def r2192 : Route 9 := (fun mask => (mask,id))

def c2192 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u2192 : Upper (D 10) (R 10) [34,68,160,144,320] 13 := by
  apply FastRouting.sound _ _ [34,68,160,144,320] 13 (by decide) (choices 1) [1,8,256] r2192 c2192
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u903
  · exact u904
  · exact u905

def b2193 : PairBound 9 := { available := 344, camps := [{ cop := 2, region := 8, targets := 320 }], pairs := [(3,6),(3,8)], upper := (rows 35 70 164 168 273 376 344 472 344), lower := (rows 35 70 164 168 273 32 64 128 256), losses := [] }

theorem u2193 : Upper (D 10) (R 10) [34,68,160,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2193 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2194 : PairBound 9 := { available := 337, camps := [{ cop := 2, region := 8, targets := 320 }], pairs := [(3,6),(3,8)], upper := (rows 35 70 164 168 280 369 337 465 337), lower := (rows 35 70 164 168 280 32 64 128 256), losses := [] }

theorem u2194 : Upper (D 10) (R 10) [34,68,160,160,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2194 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2195 : PairBound 9 := { available := 281, camps := [{ cop := 2, region := 8, targets := 320 }], pairs := [(3,6),(3,8)], upper := (rows 35 70 164 168 336 313 345 409 281), lower := (rows 35 70 164 168 336 32 64 128 256), losses := [] }

theorem u2195 : Upper (D 10) (R 10) [34,68,160,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2195 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2196 : Route 9 := (fun mask => (mask,id))

def c2196 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u2196 : Upper (D 10) (R 10) [34,68,160,192,257] 13 := by
  apply FastRouting.sound _ _ [34,68,160,192,257] 13 (by decide) (choices 1) [8,16,256] r2196 c2196
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u906
  · exact u907
  · exact u908

def r2197 : Route 9 := (fun mask => (mask,id))

def c2197 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u2197 : Upper (D 10) (R 10) [34,68,160,192,264] 13 := by
  apply FastRouting.sound _ _ [34,68,160,192,264] 13 (by decide) (choices 1) [1,16,256] r2197 c2197
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u909
  · exact u910
  · exact u911

def r2198 : Route 9 := (fun mask => (mask,id))

def c2198 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u2198 : Upper (D 10) (R 10) [34,68,160,192,288] 13 := by
  apply FastRouting.sound _ _ [34,68,160,192,288] 13 (by decide) (choices 1) [1,8,16,256] r2198 c2198
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u912
  · exact u913
  · exact u914
  · exact u915

def b2199 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 16, targets := 96 }], pairs := [(4,5),(4,6)], upper := (rows 35 70 164 265 280 240 240 240 496), lower := (rows 35 70 164 265 280 32 64 128 256), losses := [] }

theorem u2199 : Upper (D 10) (R 10) [34,68,160,257,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2199 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2200 : Route 9 := (fun mask => (mask,id))

def c2200 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u2200 : Upper (D 10) (R 10) [34,68,160,257,288] 13 := by
  apply FastRouting.sound _ _ [34,68,160,257,288] 13 (by decide) (choices 1) [8,16,64,128] r2200 c2200
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u916
  · exact u917
  · exact u918
  · exact u919

def r2201 : Route 9 := (fun mask => (mask,id))

def c2201 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2201 : Upper (D 10) (R 10) [34,68,160,257,320] 13 := by
  apply FastRouting.sound _ _ [34,68,160,257,320] 13 (by decide) (choices 1) [8,16,128] r2201 c2201
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u920
  · exact u921
  · exact u922

def r2202 : Route 9 := (fun mask => (mask,id))

def c2202 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2202 : Upper (D 10) (R 10) [34,68,160,257,384] 13 := by
  apply FastRouting.sound _ _ [34,68,160,257,384] 13 (by decide) (choices 1) [8,16,64] r2202 c2202
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u923
  · exact u924
  · exact u925

def b2203 : PairBound 9 := { available := 225, camps := [{ cop := 8, region := 24, targets := 96 }], pairs := [(3,5),(3,6)], upper := (rows 35 70 164 280 280 225 225 225 481), lower := (rows 35 70 164 280 280 32 64 128 256), losses := [] }

theorem u2203 : Upper (D 10) (R 10) [34,68,160,272,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2203 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2204 : PairBound 9 := { available := 201, camps := [{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 35 70 164 280 304 233 201 201 457), lower := (rows 35 70 164 280 304 32 64 128 256), losses := [] }

theorem u2204 : Upper (D 10) (R 10) [34,68,160,272,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2204 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2205 : PairBound 9 := { available := 169, camps := [{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 35 70 164 280 336 169 233 169 425), lower := (rows 35 70 164 280 336 32 64 128 256), losses := [] }

theorem u2205 : Upper (D 10) (R 10) [34,68,160,272,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2205 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2206 : PairBound 9 := { available := 105, camps := [{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 35 70 164 280 400 105 105 233 361), lower := (rows 35 70 164 280 400 32 64 128 256), losses := [] }

theorem u2206 : Upper (D 10) (R 10) [34,68,160,272,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2206 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2207 : Route 9 := (fun mask => (mask,id))

def c2207 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2207 : Upper (D 10) (R 10) [34,68,160,288,320] 13 := by
  apply FastRouting.sound _ _ [34,68,160,288,320] 13 (by decide) (choices 1) [1,8,16,128] r2207 c2207
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u926
  · exact u927
  · exact u928
  · exact u929

def r2208 : Route 9 := (fun mask => (mask,id))

def c2208 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2208 : Upper (D 10) (R 10) [34,68,160,288,384] 13 := by
  apply FastRouting.sound _ _ [34,68,160,288,384] 13 (by decide) (choices 1) [1,8,16,64] r2208 c2208
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u930
  · exact u931
  · exact u932
  · exact u933

def r2209 : Route 9 := (fun mask => (mask,id))

def c2209 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2209 : Upper (D 10) (R 10) [34,68,160,320,384] 13 := by
  apply FastRouting.sound _ _ [34,68,160,320,384] 13 (by decide) (choices 1) [1,8,16] r2209 c2209
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u934
  · exact u935
  · exact u936

def b2210 : PairBound 9 := { available := 297, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 70 196 56 400 297 361 425 297), lower := (rows 35 70 196 56 400 32 64 128 256), losses := [] }

theorem u2210 : Upper (D 10) (R 10) [34,68,192,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2210 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2211 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 70 196 137 280 304 368 432 304), lower := (rows 35 70 196 137 280 32 64 128 256), losses := [] }

theorem u2211 : Upper (D 10) (R 10) [34,68,192,129,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2211 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2212 : PairBound 9 := { available := 312, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 70 196 137 304 312 376 440 312), lower := (rows 35 70 196 137 304 32 64 128 256), losses := [] }

theorem u2212 : Upper (D 10) (R 10) [34,68,192,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2212 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2213 : PairBound 9 := { available := 296, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 70 196 152 273 296 360 424 296), lower := (rows 35 70 196 152 273 32 64 128 256), losses := [] }

theorem u2213 : Upper (D 10) (R 10) [34,68,192,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2213 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2214 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 70 196 152 280 289 353 417 289), lower := (rows 35 70 196 152 280 32 64 128 256), losses := [] }

theorem u2214 : Upper (D 10) (R 10) [34,68,192,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2214 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2215 : PairBound 9 := { available := 297, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 70 196 152 304 297 361 425 297), lower := (rows 35 70 196 152 304 32 64 128 256), losses := [] }

theorem u2215 : Upper (D 10) (R 10) [34,68,192,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2215 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2216 : PairBound 9 := { available := 312, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 70 196 168 273 312 376 440 312), lower := (rows 35 70 196 168 273 32 64 128 256), losses := [] }

theorem u2216 : Upper (D 10) (R 10) [34,68,192,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2216 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2217 : PairBound 9 := { available := 305, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 70 196 168 280 305 369 433 305), lower := (rows 35 70 196 168 280 32 64 128 256), losses := [] }

theorem u2217 : Upper (D 10) (R 10) [34,68,192,160,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2217 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2218 : PairBound 9 := { available := 281, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 70 196 168 304 313 345 409 281), lower := (rows 35 70 196 168 304 32 64 128 256), losses := [] }

theorem u2218 : Upper (D 10) (R 10) [34,68,192,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2218 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2219 : PairBound 9 := { available := 184, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 70 196 265 304 184 248 184 440), lower := (rows 35 70 196 265 304 32 64 128 256), losses := [] }

theorem u2219 : Upper (D 10) (R 10) [34,68,192,257,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2219 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

#print axioms u2219
end Delivery.IrregularNine14.P10

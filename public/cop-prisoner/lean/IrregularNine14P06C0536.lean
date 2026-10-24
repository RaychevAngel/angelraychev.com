import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0242
import IrregularNine14P06C0243

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b32160 : PairBound 9 := { available := 39, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 50 196 265 84 39 103 167 295), lower := (rows 11 50 196 265 84 32 64 128 256), losses := [] }

theorem u32160 : Upper (D 6) (R 6) [10,48,192,257,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32160 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32161 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 196 265 112 39 71 135 263), lower := (rows 11 50 196 265 112 32 64 128 256), losses := [] }

theorem u32161 : Upper (D 6) (R 6) [10,48,192,257,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32161 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32162 : PairBound 9 := { available := 101, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 50 196 268 19 101 101 229 357), lower := (rows 11 50 196 268 19 32 64 128 256), losses := [] }

theorem u32162 : Upper (D 6) (R 6) [10,48,192,260,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32162 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32163 : Route 9 := (fun mask => (mask,id))

def c32163 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32163 : Upper (D 6) (R 6) [10,48,192,260,5] 13 := by
  apply FastRouting.sound _ _ [10,48,192,260,5] 13 (by decide) (choices 1) [1,2,64] r32163 c32163
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14539
  · exact u14540
  · exact u14541

def r32164 : Route 9 := (fun mask => (mask,id))

def c32164 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32164 : Upper (D 6) (R 6) [10,48,192,260,6] 13 := by
  apply FastRouting.sound _ _ [10,48,192,260,6] 13 (by decide) (choices 1) [1,64] r32164 c32164
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u14542
  · exact u14543

def b32165 : PairBound 9 := { available := 71, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 196 268 49 103 71 199 327), lower := (rows 11 50 196 268 49 32 64 128 256), losses := [] }

theorem u32165 : Upper (D 6) (R 6) [10,48,192,260,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32165 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32166 : PairBound 9 := { available := 69, camps := [{ cop := 5, region := 18, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 50 196 268 50 101 69 197 325), lower := (rows 11 50 196 268 50 32 64 128 256), losses := [] }

theorem u32166 : Upper (D 6) (R 6) [10,48,192,260,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32166 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32167 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 196 268 52 99 67 195 323), lower := (rows 11 50 196 268 52 32 64 128 256), losses := [] }

theorem u32167 : Upper (D 6) (R 6) [10,48,192,260,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32167 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32168 : Route 9 := (fun mask => (mask,id))

def c32168 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32168 : Upper (D 6) (R 6) [10,48,192,260,65] 13 := by
  apply FastRouting.sound _ _ [10,48,192,260,65] 13 (by decide) (choices 1) [1,2,4] r32168 c32168
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14544
  · exact u14545
  · exact u14546

def r32169 : Route 9 := (fun mask => (mask,id))

def c32169 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32169 : Upper (D 6) (R 6) [10,48,192,260,66] 13 := by
  apply FastRouting.sound _ _ [10,48,192,260,66] 13 (by decide) (choices 1) [1,4] r32169 c32169
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u14547
  · exact u14548

def b32170 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 50 196 268 84 35 99 163 291), lower := (rows 11 50 196 268 84 32 64 128 256), losses := [] }

theorem u32170 : Upper (D 6) (R 6) [10,48,192,260,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32170 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32171 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 196 268 112 39 71 135 263), lower := (rows 11 50 196 268 112 32 64 128 256), losses := [] }

theorem u32171 : Upper (D 6) (R 6) [10,48,192,260,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32171 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32172 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 19, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 50 196 296 19 101 69 197 325), lower := (rows 11 50 196 296 19 32 64 128 256), losses := [] }

theorem u32172 : Upper (D 6) (R 6) [10,48,192,288,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32172 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32173 : Route 9 := (fun mask => (mask,id))

def c32173 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32173 : Upper (D 6) (R 6) [10,48,192,288,5] 13 := by
  apply FastRouting.sound _ _ [10,48,192,288,5] 13 (by decide) (choices 1) [1,2,4,64] r32173 c32173
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14549
  · exact u14550
  · exact u14551
  · exact u14552

def b32174 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 0, region := 196, targets := 32 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 11 50 196 296 22 101 69 197 325), lower := (rows 11 50 196 296 22 32 64 128 256), losses := [] }

theorem u32174 : Upper (D 6) (R 6) [10,48,192,288,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32174 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32175 : Route 9 := (fun mask => (mask,id))

def c32175 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32175 : Upper (D 6) (R 6) [10,48,192,288,65] 13 := by
  apply FastRouting.sound _ _ [10,48,192,288,65] 13 (by decide) (choices 1) [1,2,4] r32175 c32175
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14553
  · exact u14554
  · exact u14555

def b32176 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 0, region := 196, targets := 32 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 11 50 196 296 82 37 69 133 261), lower := (rows 11 50 196 296 82 32 64 128 256), losses := [] }

theorem u32176 : Upper (D 6) (R 6) [10,48,192,288,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32176 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32177 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 50 196 296 84 39 71 135 263), lower := (rows 11 50 196 296 84 32 64 128 256), losses := [] }

theorem u32177 : Upper (D 6) (R 6) [10,48,192,288,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32177 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32178 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 50 196 328 19 37 101 165 293), lower := (rows 11 50 196 328 19 32 64 128 256), losses := [] }

theorem u32178 : Upper (D 6) (R 6) [10,48,192,320,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32178 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32179 : Route 9 := (fun mask => (mask,id))

def c32179 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32179 : Upper (D 6) (R 6) [10,48,192,320,5] 13 := by
  apply FastRouting.sound _ _ [10,48,192,320,5] 13 (by decide) (choices 1) [1,2,4] r32179 c32179
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14556
  · exact u14557
  · exact u14558

def r32180 : Route 9 := (fun mask => (mask,id))

def c32180 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32180 : Upper (D 6) (R 6) [10,48,192,320,6] 13 := by
  apply FastRouting.sound _ _ [10,48,192,320,6] 13 (by decide) (choices 1) [1,4] r32180 c32180
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u14559
  · exact u14560

def b32181 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 196 328 49 39 71 135 263), lower := (rows 11 50 196 328 49 32 64 128 256), losses := [] }

theorem u32181 : Upper (D 6) (R 6) [10,48,192,320,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32181 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32182 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 18, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 50 196 328 50 37 69 133 261), lower := (rows 11 50 196 328 50 32 64 128 256), losses := [] }

theorem u32182 : Upper (D 6) (R 6) [10,48,192,320,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32182 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32183 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 196 328 52 39 71 135 263), lower := (rows 11 50 196 328 52 32 64 128 256), losses := [] }

theorem u32183 : Upper (D 6) (R 6) [10,48,192,320,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32183 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32184 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 50 388 13 19 100 100 228 356), lower := (rows 11 50 388 13 19 32 64 128 256), losses := [] }

theorem u32184 : Upper (D 6) (R 6) [10,48,384,5,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32184 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32185 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 50 388 13 21 98 98 226 354), lower := (rows 11 50 388 13 21 32 64 128 256), losses := [] }

theorem u32185 : Upper (D 6) (R 6) [10,48,384,5,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32185 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32186 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 50 388 13 22 97 97 225 353), lower := (rows 11 50 388 13 22 32 64 128 256), losses := [] }

theorem u32186 : Upper (D 6) (R 6) [10,48,384,5,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32186 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32187 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 388 13 49 102 70 198 326), lower := (rows 11 50 388 13 49 32 64 128 256), losses := [] }

theorem u32187 : Upper (D 6) (R 6) [10,48,384,5,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32187 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32188 : PairBound 9 := { available := 69, camps := [{ cop := 5, region := 18, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 50 388 13 50 101 69 197 325), lower := (rows 11 50 388 13 50 32 64 128 256), losses := [] }

theorem u32188 : Upper (D 6) (R 6) [10,48,384,5,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32188 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32189 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 388 13 52 99 67 195 323), lower := (rows 11 50 388 13 52 32 64 128 256), losses := [] }

theorem u32189 : Upper (D 6) (R 6) [10,48,384,5,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32189 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32190 : Route 9 := (fun mask => (mask,id))

def c32190 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32190 : Upper (D 6) (R 6) [10,48,384,5,65] 13 := by
  apply FastRouting.sound _ _ [10,48,384,5,65] 13 (by decide) (choices 1) [2,4,64] r32190 c32190
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14561
  · exact u14562
  · exact u14563

def r32191 : Route 9 := (fun mask => (mask,id))

def c32191 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32191 : Upper (D 6) (R 6) [10,48,384,5,66] 13 := by
  apply FastRouting.sound _ _ [10,48,384,5,66] 13 (by decide) (choices 1) [1,4,64] r32191 c32191
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14564
  · exact u14565
  · exact u14566

def r32192 : Route 9 := (fun mask => (mask,id))

def c32192 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32192 : Upper (D 6) (R 6) [10,48,384,5,68] 13 := by
  apply FastRouting.sound _ _ [10,48,384,5,68] 13 (by decide) (choices 1) [1,2,64] r32192 c32192
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14567
  · exact u14568
  · exact u14569

def b32193 : PairBound 9 := { available := 71, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 388 13 112 103 71 199 327), lower := (rows 11 50 388 13 112 32 64 128 256), losses := [] }

theorem u32193 : Upper (D 6) (R 6) [10,48,384,5,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32193 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32194 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 19, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 50 388 44 19 101 69 197 325), lower := (rows 11 50 388 44 19 32 64 128 256), losses := [] }

theorem u32194 : Upper (D 6) (R 6) [10,48,384,36,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32194 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32195 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 19, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 11 50 388 44 21 99 67 195 323), lower := (rows 11 50 388 44 21 32 64 128 256), losses := [] }

theorem u32195 : Upper (D 6) (R 6) [10,48,384,36,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32195 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32196 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 19, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 11 50 388 44 22 97 65 193 321), lower := (rows 11 50 388 44 22 32 64 128 256), losses := [] }

theorem u32196 : Upper (D 6) (R 6) [10,48,384,36,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32196 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32197 : Route 9 := (fun mask => (mask,id))

def c32197 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32197 : Upper (D 6) (R 6) [10,48,384,36,65] 13 := by
  apply FastRouting.sound _ _ [10,48,384,36,65] 13 (by decide) (choices 1) [1,2,4,64] r32197 c32197
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14570
  · exact u14571
  · exact u14572
  · exact u14573

def b32198 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 0, region := 452, targets := 32 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 11 50 388 44 82 101 69 197 325), lower := (rows 11 50 388 44 82 32 64 128 256), losses := [] }

theorem u32198 : Upper (D 6) (R 6) [10,48,384,36,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32198 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32199 : Route 9 := (fun mask => (mask,id))

def c32199 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32199 : Upper (D 6) (R 6) [10,48,384,36,68] 13 := by
  apply FastRouting.sound _ _ [10,48,384,36,68] 13 (by decide) (choices 1) [1,2,64] r32199 c32199
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14574
  · exact u14575
  · exact u14576

def b32200 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 50 388 73 19 100 100 228 356), lower := (rows 11 50 388 73 19 32 64 128 256), losses := [] }

theorem u32200 : Upper (D 6) (R 6) [10,48,384,65,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32200 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32201 : Route 9 := (fun mask => (mask,id))

def c32201 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32201 : Upper (D 6) (R 6) [10,48,384,65,5] 13 := by
  apply FastRouting.sound _ _ [10,48,384,65,5] 13 (by decide) (choices 1) [2,4,64] r32201 c32201
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14577
  · exact u14578
  · exact u14579

def r32202 : Route 9 := (fun mask => (mask,id))

def c32202 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32202 : Upper (D 6) (R 6) [10,48,384,65,6] 13 := by
  apply FastRouting.sound _ _ [10,48,384,65,6] 13 (by decide) (choices 1) [1,4,64] r32202 c32202
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14580
  · exact u14581
  · exact u14582

def b32203 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 388 73 49 102 70 198 326), lower := (rows 11 50 388 73 49 32 64 128 256), losses := [] }

theorem u32203 : Upper (D 6) (R 6) [10,48,384,65,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32203 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32204 : PairBound 9 := { available := 69, camps := [{ cop := 5, region := 18, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 50 388 73 50 101 69 197 325), lower := (rows 11 50 388 73 50 32 64 128 256), losses := [] }

theorem u32204 : Upper (D 6) (R 6) [10,48,384,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32204 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32205 : PairBound 9 := { available := 71, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 388 73 52 103 71 199 327), lower := (rows 11 50 388 73 52 32 64 128 256), losses := [] }

theorem u32205 : Upper (D 6) (R 6) [10,48,384,65,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32205 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32206 : PairBound 9 := { available := 38, camps := [{ cop := 3, region := 16, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 11 50 388 73 81 38 102 166 294), lower := (rows 11 50 388 73 81 32 64 128 256), losses := [] }

theorem u32206 : Upper (D 6) (R 6) [10,48,384,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32206 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32207 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 9, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 50 388 73 82 37 101 165 293), lower := (rows 11 50 388 73 82 32 64 128 256), losses := [] }

theorem u32207 : Upper (D 6) (R 6) [10,48,384,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32207 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32208 : Route 9 := (fun mask => (mask,id))

def c32208 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32208 : Upper (D 6) (R 6) [10,48,384,65,68] 13 := by
  apply FastRouting.sound _ _ [10,48,384,65,68] 13 (by decide) (choices 1) [1,2,4] r32208 c32208
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14583
  · exact u14584
  · exact u14585

def b32209 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 388 73 112 39 71 135 263), lower := (rows 11 50 388 73 112 32 64 128 256), losses := [] }

theorem u32209 : Upper (D 6) (R 6) [10,48,384,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32209 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32210 : PairBound 9 := { available := 101, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 50 388 76 19 101 101 229 357), lower := (rows 11 50 388 76 19 32 64 128 256), losses := [] }

theorem u32210 : Upper (D 6) (R 6) [10,48,384,68,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32210 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32211 : Route 9 := (fun mask => (mask,id))

def c32211 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32211 : Upper (D 6) (R 6) [10,48,384,68,5] 13 := by
  apply FastRouting.sound _ _ [10,48,384,68,5] 13 (by decide) (choices 1) [1,2,64] r32211 c32211
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14586
  · exact u14587
  · exact u14588

def r32212 : Route 9 := (fun mask => (mask,id))

def c32212 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32212 : Upper (D 6) (R 6) [10,48,384,68,6] 13 := by
  apply FastRouting.sound _ _ [10,48,384,68,6] 13 (by decide) (choices 1) [1,64] r32212 c32212
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u14589
  · exact u14590

def b32213 : PairBound 9 := { available := 71, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 388 76 49 103 71 199 327), lower := (rows 11 50 388 76 49 32 64 128 256), losses := [] }

theorem u32213 : Upper (D 6) (R 6) [10,48,384,68,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32213 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32214 : PairBound 9 := { available := 69, camps := [{ cop := 5, region := 18, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 50 388 76 50 101 69 197 325), lower := (rows 11 50 388 76 50 32 64 128 256), losses := [] }

theorem u32214 : Upper (D 6) (R 6) [10,48,384,68,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32214 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32215 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 388 76 52 99 67 195 323), lower := (rows 11 50 388 76 52 32 64 128 256), losses := [] }

theorem u32215 : Upper (D 6) (R 6) [10,48,384,68,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32215 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32216 : Route 9 := (fun mask => (mask,id))

def c32216 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32216 : Upper (D 6) (R 6) [10,48,384,68,65] 13 := by
  apply FastRouting.sound _ _ [10,48,384,68,65] 13 (by decide) (choices 1) [1,2,4] r32216 c32216
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14591
  · exact u14592
  · exact u14593

def b32217 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 0, region := 420, targets := 64 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 11 50 388 76 82 37 101 165 293), lower := (rows 11 50 388 76 82 32 64 128 256), losses := [] }

theorem u32217 : Upper (D 6) (R 6) [10,48,384,68,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32217 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32218 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 50 388 76 84 35 99 163 291), lower := (rows 11 50 388 76 84 32 64 128 256), losses := [] }

theorem u32218 : Upper (D 6) (R 6) [10,48,384,68,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32218 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32219 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 388 76 112 39 71 135 263), lower := (rows 11 50 388 76 112 32 64 128 256), losses := [] }

theorem u32219 : Upper (D 6) (R 6) [10,48,384,68,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32219 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u32219
end Delivery.IrregularNine14.P06

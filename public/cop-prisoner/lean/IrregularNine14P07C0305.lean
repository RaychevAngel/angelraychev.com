import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0081
import IrregularNine14P07C0082

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b18300 : PairBound 9 := { available := 322, camps := [{ cop := 3, region := 52, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 44 137 148 48 322 450 322), lower := (rows 35 67 44 137 148 48 64 128 256), losses := [] }

theorem u18300 : Upper (D 7) (R 7) [34,65,40,129,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18300 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18301 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 67 44 137 148 96 338 402 274), lower := (rows 35 67 44 137 148 96 64 128 256), losses := [] }

theorem u18301 : Upper (D 7) (R 7) [34,65,40,129,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18301 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18302 : Route 9 := (fun mask => (mask,id))

def c18302 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18302 : Upper (D 7) (R 7) [34,65,40,129,132,256] 13 := by
  apply FastRouting.sound _ _ [34,65,40,129,132,256] 13 (by decide) (choices 1) [2,16] r18302 c18302
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4919
  · exact u4920

def b18303 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 44 137 208 34 340 404 276), lower := (rows 35 67 44 137 208 34 64 128 256), losses := [] }

theorem u18303 : Upper (D 7) (R 7) [34,65,40,129,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18303 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18304 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 44 137 208 36 338 402 274), lower := (rows 35 67 44 137 208 36 64 128 256), losses := [] }

theorem u18304 : Upper (D 7) (R 7) [34,65,40,129,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18304 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18305 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 396, targets := 64 },{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7),(2,6),(3,6)], upper := (rows 35 67 44 137 208 48 326 390 262), lower := (rows 35 67 44 137 208 48 64 128 256), losses := [] }

theorem u18305 : Upper (D 7) (R 7) [34,65,40,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18305 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18306 : Route 9 := (fun mask => (mask,id))

def c18306 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18306 : Upper (D 7) (R 7) [34,65,40,129,192,256] 13 := by
  apply FastRouting.sound _ _ [34,65,40,129,192,256] 13 (by decide) (choices 1) [2,4,16] r18306 c18306
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4921
  · exact u4922
  · exact u4923

def b18307 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 44 137 274 36 208 208 464), lower := (rows 35 67 44 137 274 36 64 128 256), losses := [] }

theorem u18307 : Upper (D 7) (R 7) [34,65,40,129,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18307 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18308 : PairBound 9 := { available := 196, camps := [{ cop := 0, region := 204, targets := 2 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1)], upper := (rows 35 67 44 137 274 48 196 196 452), lower := (rows 35 67 44 137 274 48 64 128 256), losses := [] }

theorem u18308 : Upper (D 7) (R 7) [34,65,40,129,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18308 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18309 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 5, region := 3, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 67 44 137 274 96 212 148 404), lower := (rows 35 67 44 137 274 96 64 128 256), losses := [] }

theorem u18309 : Upper (D 7) (R 7) [34,65,40,129,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18309 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18310 : PairBound 9 := { available := 84, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 35 67 44 137 274 160 84 212 340), lower := (rows 35 67 44 137 274 160 64 128 256), losses := [] }

theorem u18310 : Upper (D 7) (R 7) [34,65,40,129,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18310 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18311 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 44 137 276 34 208 208 464), lower := (rows 35 67 44 137 276 34 64 128 256), losses := [] }

theorem u18311 : Upper (D 7) (R 7) [34,65,40,129,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18311 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18312 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5),(2,0),(3,5)], upper := (rows 35 67 44 137 276 48 194 194 450), lower := (rows 35 67 44 137 276 48 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 24 60 67 131 259), good := (rows 482 450 60 508 308 48 64 128 256) }] }

theorem u18312 : Upper (D 7) (R 7) [34,65,40,129,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18312 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18313 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 5, region := 3, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 67 44 137 276 96 210 146 402), lower := (rows 35 67 44 137 276 96 64 128 256), losses := [] }

theorem u18313 : Upper (D 7) (R 7) [34,65,40,129,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18313 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18314 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 35 67 44 137 276 160 82 210 338), lower := (rows 35 67 44 137 276 160 64 128 256), losses := [] }

theorem u18314 : Upper (D 7) (R 7) [34,65,40,129,260,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18314 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18315 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 44 137 336 34 212 148 404), lower := (rows 35 67 44 137 336 34 64 128 256), losses := [] }

theorem u18315 : Upper (D 7) (R 7) [34,65,40,129,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18315 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18316 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 44 137 336 36 210 146 402), lower := (rows 35 67 44 137 336 36 64 128 256), losses := [] }

theorem u18316 : Upper (D 7) (R 7) [34,65,40,129,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18316 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18317 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 140, targets := 64 },{ cop := 4, region := 35, targets := 128 }], pairs := [(0,7),(2,6),(3,6)], upper := (rows 35 67 44 137 336 48 198 134 390), lower := (rows 35 67 44 137 336 48 64 128 256), losses := [] }

theorem u18317 : Upper (D 7) (R 7) [34,65,40,129,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18317 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18318 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 35 67 44 137 336 160 86 150 278), lower := (rows 35 67 44 137 336 160 64 128 256), losses := [] }

theorem u18318 : Upper (D 7) (R 7) [34,65,40,129,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18318 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18319 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 44 137 400 34 84 212 340), lower := (rows 35 67 44 137 400 34 64 128 256), losses := [] }

theorem u18319 : Upper (D 7) (R 7) [34,65,40,129,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18319 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18320 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 44 137 400 36 82 210 338), lower := (rows 35 67 44 137 400 36 64 128 256), losses := [] }

theorem u18320 : Upper (D 7) (R 7) [34,65,40,129,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18320 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18321 : Route 9 := (fun mask => (mask,id))

def c18321 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18321 : Upper (D 7) (R 7) [34,65,40,129,384,16] 13 := by
  apply FastRouting.sound _ _ [34,65,40,129,384,16] 13 (by decide) (choices 1) [2,4] r18321 c18321
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4924
  · exact u4925

def b18322 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 5, region := 3, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 67 44 137 400 96 86 150 278), lower := (rows 35 67 44 137 400 96 64 128 256), losses := [] }

theorem u18322 : Upper (D 7) (R 7) [34,65,40,129,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18322 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18323 : PairBound 9 := { available := 336, camps := [{ cop := 0, region := 474, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 35 67 44 138 145 36 336 464 336), lower := (rows 35 67 44 138 145 36 64 128 256), losses := [] }

theorem u18323 : Upper (D 7) (R 7) [34,65,40,130,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18323 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18324 : PairBound 9 := { available := 324, camps := [{ cop := 3, region := 53, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 67 44 138 145 48 324 452 324), lower := (rows 35 67 44 138 145 48 64 128 256), losses := [] }

theorem u18324 : Upper (D 7) (R 7) [34,65,40,130,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18324 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18325 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 5, region := 3, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 67 44 138 145 96 340 404 276), lower := (rows 35 67 44 138 145 96 64 128 256), losses := [] }

theorem u18325 : Upper (D 7) (R 7) [34,65,40,130,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18325 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18326 : Route 9 := (fun mask => (mask,id))

def c18326 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18326 : Upper (D 7) (R 7) [34,65,40,130,129,256] 13 := by
  apply FastRouting.sound _ _ [34,65,40,130,129,256] 13 (by decide) (choices 1) [4,16] r18326 c18326
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4926
  · exact u4927

def b18327 : PairBound 9 := { available := 336, camps := [{ cop := 0, region := 476, targets := 1 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(2,0),(3,0),(4,0)], upper := (rows 35 67 44 138 148 33 336 464 336), lower := (rows 35 67 44 138 148 33 64 128 256), losses := [] }

theorem u18327 : Upper (D 7) (R 7) [34,65,40,130,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18327 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18328 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 52, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 67 44 138 148 48 321 449 321), lower := (rows 35 67 44 138 148 48 64 128 256), losses := [] }

theorem u18328 : Upper (D 7) (R 7) [34,65,40,130,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18328 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18329 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 67 44 138 148 96 337 401 273), lower := (rows 35 67 44 138 148 96 64 128 256), losses := [] }

theorem u18329 : Upper (D 7) (R 7) [34,65,40,130,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18329 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18330 : Route 9 := (fun mask => (mask,id))

def c18330 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18330 : Upper (D 7) (R 7) [34,65,40,130,132,256] 13 := by
  apply FastRouting.sound _ _ [34,65,40,130,132,256] 13 (by decide) (choices 1) [1,16] r18330 c18330
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4928
  · exact u4929

def b18331 : PairBound 9 := { available := 276, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 67 44 138 208 33 340 404 276), lower := (rows 35 67 44 138 208 33 64 128 256), losses := [] }

theorem u18331 : Upper (D 7) (R 7) [34,65,40,130,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18331 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18332 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 35 67 44 138 208 36 337 401 273), lower := (rows 35 67 44 138 208 36 64 128 256), losses := [] }

theorem u18332 : Upper (D 7) (R 7) [34,65,40,130,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18332 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18333 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 396, targets := 64 },{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7),(2,6),(3,6)], upper := (rows 35 67 44 138 208 48 325 389 261), lower := (rows 35 67 44 138 208 48 64 128 256), losses := [] }

theorem u18333 : Upper (D 7) (R 7) [34,65,40,130,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18333 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18334 : Route 9 := (fun mask => (mask,id))

def c18334 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18334 : Upper (D 7) (R 7) [34,65,40,130,192,256] 13 := by
  apply FastRouting.sound _ _ [34,65,40,130,192,256] 13 (by decide) (choices 1) [1,4,16] r18334 c18334
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4930
  · exact u4931
  · exact u4932

def b18335 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 35 67 44 138 273 36 208 208 464), lower := (rows 35 67 44 138 273 36 64 128 256), losses := [] }

theorem u18335 : Upper (D 7) (R 7) [34,65,40,130,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18335 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18336 : Route 9 := (fun mask => (mask,id))

def c18336 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u18336 : Upper (D 7) (R 7) [34,65,40,130,257,16] 13 := by
  apply FastRouting.sound _ _ [34,65,40,130,257,16] 13 (by decide) (choices 1) [4,128] r18336 c18336
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4933
  · exact u4934

def b18337 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 5, region := 3, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 67 44 138 273 96 212 148 404), lower := (rows 35 67 44 138 273 96 64 128 256), losses := [] }

theorem u18337 : Upper (D 7) (R 7) [34,65,40,130,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18337 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18338 : PairBound 9 := { available := 84, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 35 67 44 138 273 160 84 212 340), lower := (rows 35 67 44 138 273 160 64 128 256), losses := [] }

theorem u18338 : Upper (D 7) (R 7) [34,65,40,130,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18338 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18339 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 67 44 138 276 33 208 208 464), lower := (rows 35 67 44 138 276 33 64 128 256), losses := [] }

theorem u18339 : Upper (D 7) (R 7) [34,65,40,130,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18339 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18340 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5),(2,1),(3,5)], upper := (rows 35 67 44 138 276 48 193 193 449), lower := (rows 35 67 44 138 276 48 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 24 60 67 131 259), good := (rows 481 449 60 508 308 48 64 128 256) }] }

theorem u18340 : Upper (D 7) (R 7) [34,65,40,130,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18340 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18341 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 5, region := 3, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 67 44 138 276 96 209 145 401), lower := (rows 35 67 44 138 276 96 64 128 256), losses := [] }

theorem u18341 : Upper (D 7) (R 7) [34,65,40,130,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18341 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18342 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 35 67 44 138 276 160 81 209 337), lower := (rows 35 67 44 138 276 160 64 128 256), losses := [] }

theorem u18342 : Upper (D 7) (R 7) [34,65,40,130,260,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18342 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18343 : PairBound 9 := { available := 148, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 67 44 138 336 33 212 148 404), lower := (rows 35 67 44 138 336 33 64 128 256), losses := [] }

theorem u18343 : Upper (D 7) (R 7) [34,65,40,130,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18343 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18344 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 35 67 44 138 336 36 209 145 401), lower := (rows 35 67 44 138 336 36 64 128 256), losses := [] }

theorem u18344 : Upper (D 7) (R 7) [34,65,40,130,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18344 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18345 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 140, targets := 64 },{ cop := 4, region := 35, targets := 128 }], pairs := [(0,7),(2,6),(3,6)], upper := (rows 35 67 44 138 336 48 197 133 389), lower := (rows 35 67 44 138 336 48 64 128 256), losses := [] }

theorem u18345 : Upper (D 7) (R 7) [34,65,40,130,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18345 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18346 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 35 67 44 138 336 160 85 149 277), lower := (rows 35 67 44 138 336 160 64 128 256), losses := [] }

theorem u18346 : Upper (D 7) (R 7) [34,65,40,130,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18346 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18347 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 67 44 138 400 33 84 212 340), lower := (rows 35 67 44 138 400 33 64 128 256), losses := [] }

theorem u18347 : Upper (D 7) (R 7) [34,65,40,130,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18347 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18348 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 35 67 44 138 400 36 81 209 337), lower := (rows 35 67 44 138 400 36 64 128 256), losses := [] }

theorem u18348 : Upper (D 7) (R 7) [34,65,40,130,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18348 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18349 : Route 9 := (fun mask => (mask,id))

def c18349 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18349 : Upper (D 7) (R 7) [34,65,40,130,384,16] 13 := by
  apply FastRouting.sound _ _ [34,65,40,130,384,16] 13 (by decide) (choices 1) [1,4] r18349 c18349
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4935
  · exact u4936

def b18350 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 5, region := 3, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 67 44 138 400 96 85 149 277), lower := (rows 35 67 44 138 400 96 64 128 256), losses := [] }

theorem u18350 : Upper (D 7) (R 7) [34,65,40,130,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18350 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18351 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5),(2,1),(3,1),(4,1)], upper := (rows 35 67 44 140 273 34 208 208 464), lower := (rows 35 67 44 140 273 34 64 128 256), losses := [] }

theorem u18351 : Upper (D 7) (R 7) [34,65,40,132,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18351 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18352 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 204, targets := 1 },{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5),(2,0),(3,0)], upper := (rows 35 67 44 140 273 48 194 194 450), lower := (rows 35 67 44 140 273 48 64 128 256), losses := [] }

theorem u18352 : Upper (D 7) (R 7) [34,65,40,132,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18352 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18353 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5),(2,6),(3,6),(4,6)], upper := (rows 35 67 44 140 273 96 210 146 402), lower := (rows 35 67 44 140 273 96 64 128 256), losses := [] }

theorem u18353 : Upper (D 7) (R 7) [34,65,40,132,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18353 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18354 : PairBound 9 := { available := 82, camps := [{ cop := 5, region := 12, targets := 67 }], pairs := [(2,0),(2,1),(2,6),(3,0)], upper := (rows 35 67 44 140 273 160 82 210 338), lower := (rows 35 67 44 140 273 160 64 128 256), losses := [] }

theorem u18354 : Upper (D 7) (R 7) [34,65,40,132,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18354 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18355 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 476, targets := 1 },{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5),(2,0),(3,0),(4,0)], upper := (rows 35 67 44 140 274 33 208 208 464), lower := (rows 35 67 44 140 274 33 64 128 256), losses := [] }

theorem u18355 : Upper (D 7) (R 7) [34,65,40,132,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18355 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18356 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 204, targets := 2 },{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5),(2,1),(3,1)], upper := (rows 35 67 44 140 274 48 193 193 449), lower := (rows 35 67 44 140 274 48 64 128 256), losses := [] }

theorem u18356 : Upper (D 7) (R 7) [34,65,40,132,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18356 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18357 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5),(2,6),(3,6),(4,6)], upper := (rows 35 67 44 140 274 96 209 145 401), lower := (rows 35 67 44 140 274 96 64 128 256), losses := [] }

theorem u18357 : Upper (D 7) (R 7) [34,65,40,132,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18357 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18358 : PairBound 9 := { available := 81, camps := [{ cop := 5, region := 12, targets := 67 }], pairs := [(2,0),(2,1),(2,6),(3,0)], upper := (rows 35 67 44 140 274 160 81 209 337), lower := (rows 35 67 44 140 274 160 64 128 256), losses := [] }

theorem u18358 : Upper (D 7) (R 7) [34,65,40,132,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18358 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18359 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 476, targets := 1 },{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5),(2,0),(3,0),(4,0)], upper := (rows 35 67 44 140 336 33 210 146 402), lower := (rows 35 67 44 140 336 33 64 128 256), losses := [] }

theorem u18359 : Upper (D 7) (R 7) [34,65,40,132,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18359 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u18359
end Delivery.IrregularNine14.P07

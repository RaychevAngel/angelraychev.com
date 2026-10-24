import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0365
import IrregularNine14P07C0366

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b36360 : PairBound 9 := { available := 133, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 181, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 35 322 28 74 176 165 197 133 389), lower := (rows 35 322 28 74 176 32 64 128 256), losses := [] }

theorem u36360 : Upper (D 7) (R 7) [34,320,24,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36360 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36361 : Route 9 := (fun mask => (mask,id))

def c36361 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36361 : Upper (D 7) (R 7) [34,320,24,68,129] 13 := by
  apply FastRouting.sound _ _ [34,320,24,68,129] 13 (by decide) (choices 1) [1,2,128] r36361 c36361
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21913
  · exact u21914
  · exact u21915

def r36362 : Route 9 := (fun mask => (mask,id))

def c36362 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36362 : Upper (D 7) (R 7) [34,320,24,68,130] 13 := by
  apply FastRouting.sound _ _ [34,320,24,68,130] 13 (by decide) (choices 1) [1,128] r36362 c36362
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u21916
  · exact u21917

def r36363 : Route 9 := (fun mask => (mask,id))

def c36363 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36363 : Upper (D 7) (R 7) [34,320,24,68,160] 13 := by
  apply FastRouting.sound _ _ [34,320,24,68,160] 13 (by decide) (choices 1) [1,2,128] r36363 c36363
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21918
  · exact u21919
  · exact u21920

def r36364 : Route 9 := (fun mask => (mask,id))

def c36364 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36364 : Upper (D 7) (R 7) [34,320,24,96,129] 13 := by
  apply FastRouting.sound _ _ [34,320,24,96,129] 13 (by decide) (choices 1) [1,2,4,128] r36364 c36364
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21921
  · exact u21922
  · exact u21923
  · exact u21924

def r36365 : Route 9 := (fun mask => (mask,id))

def c36365 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36365 : Upper (D 7) (R 7) [34,320,24,96,130] 13 := by
  apply FastRouting.sound _ _ [34,320,24,96,130] 13 (by decide) (choices 1) [1,4,128] r36365 c36365
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21925
  · exact u21926
  · exact u21927

def r36366 : Route 9 := (fun mask => (mask,id))

def c36366 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36366 : Upper (D 7) (R 7) [34,320,24,96,132] 13 := by
  apply FastRouting.sound _ _ [34,320,24,96,132] 13 (by decide) (choices 1) [1,2,128] r36366 c36366
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21928
  · exact u21929
  · exact u21930

def b36367 : PairBound 9 := { available := 102, camps := [{ cop := 3, region := 20, targets := 98 }], pairs := [(2,1),(2,5),(2,6),(4,1)], upper := (rows 35 322 28 137 145 102 102 230 358), lower := (rows 35 322 28 137 145 32 64 128 256), losses := [] }

theorem u36367 : Upper (D 7) (R 7) [34,320,24,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36367 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36368 : Route 9 := (fun mask => (mask,id))

def c36368 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36368 : Upper (D 7) (R 7) [34,320,24,129,130] 13 := by
  apply FastRouting.sound _ _ [34,320,24,129,130] 13 (by decide) (choices 1) [1,4,64] r36368 c36368
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21931
  · exact u21932
  · exact u21933

def b36369 : PairBound 9 := { available := 99, camps := [{ cop := 3, region := 20, targets := 99 }], pairs := [(2,0),(2,1),(2,5),(2,6)], upper := (rows 35 322 28 137 148 99 99 227 355), lower := (rows 35 322 28 137 148 32 64 128 256), losses := [] }

theorem u36369 : Upper (D 7) (R 7) [34,320,24,129,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36369 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36370 : Route 9 := (fun mask => (mask,id))

def c36370 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36370 : Upper (D 7) (R 7) [34,320,24,129,160] 13 := by
  apply FastRouting.sound _ _ [34,320,24,129,160] 13 (by decide) (choices 1) [1,2,4,64] r36370 c36370
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21934
  · exact u21935
  · exact u21936
  · exact u21937

def r36371 : Route 9 := (fun mask => (mask,id))

def c36371 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36371 : Upper (D 7) (R 7) [34,320,24,129,192] 13 := by
  apply FastRouting.sound _ _ [34,320,24,129,192] 13 (by decide) (choices 1) [1,2,4] r36371 c36371
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21938
  · exact u21939
  · exact u21940

def b36372 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 20, targets := 99 }], pairs := [(2,0),(2,1),(2,5),(2,6)], upper := (rows 35 322 28 138 148 97 97 225 353), lower := (rows 35 322 28 138 148 32 64 128 256), losses := [] }

theorem u36372 : Upper (D 7) (R 7) [34,320,24,130,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36372 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36373 : Route 9 := (fun mask => (mask,id))

def c36373 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36373 : Upper (D 7) (R 7) [34,320,24,130,160] 13 := by
  apply FastRouting.sound _ _ [34,320,24,130,160] 13 (by decide) (choices 1) [1,4,64] r36373 c36373
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21941
  · exact u21942
  · exact u21943

def r36374 : Route 9 := (fun mask => (mask,id))

def c36374 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36374 : Upper (D 7) (R 7) [34,320,24,130,192] 13 := by
  apply FastRouting.sound _ _ [34,320,24,130,192] 13 (by decide) (choices 1) [1,4] r36374 c36374
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u21944
  · exact u21945

def b36375 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 12, targets := 99 }], pairs := [(2,0),(2,1),(2,5),(2,6)], upper := (rows 35 322 28 140 176 99 67 195 323), lower := (rows 35 322 28 140 176 32 64 128 256), losses := [] }

theorem u36375 : Upper (D 7) (R 7) [34,320,24,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36375 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36376 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 12, targets := 99 }], pairs := [(2,0),(2,1),(2,5),(2,6)], upper := (rows 35 322 28 140 208 35 99 163 291), lower := (rows 35 322 28 140 208 32 64 128 256), losses := [] }

theorem u36376 : Upper (D 7) (R 7) [34,320,24,132,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36376 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36377 : Route 9 := (fun mask => (mask,id))

def c36377 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36377 : Upper (D 7) (R 7) [34,320,24,160,192] 13 := by
  apply FastRouting.sound _ _ [34,320,24,160,192] 13 (by decide) (choices 1) [1,2,4] r36377 c36377
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21946
  · exact u21947
  · exact u21948

def b36378 : PairBound 9 := { available := 156, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 322 37 73 146 188 220 156 412), lower := (rows 35 322 37 73 146 32 64 128 256), losses := [] }

theorem u36378 : Upper (D 7) (R 7) [34,320,33,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36378 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36379 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 322 37 73 148 186 218 154 410), lower := (rows 35 322 37 73 148 32 64 128 256), losses := [] }

theorem u36379 : Upper (D 7) (R 7) [34,320,33,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36379 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36380 : PairBound 9 := { available := 150, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 322 37 73 152 182 214 150 406), lower := (rows 35 322 37 73 152 32 64 128 256), losses := [] }

theorem u36380 : Upper (D 7) (R 7) [34,320,33,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36380 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36381 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 322 37 76 145 186 218 154 410), lower := (rows 35 322 37 76 145 32 64 128 256), losses := [] }

theorem u36381 : Upper (D 7) (R 7) [34,320,33,68,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36381 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36382 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 322 37 76 146 185 217 153 409), lower := (rows 35 322 37 76 146 32 64 128 256), losses := [] }

theorem u36382 : Upper (D 7) (R 7) [34,320,33,68,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36382 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36383 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 322 37 76 152 179 211 147 403), lower := (rows 35 322 37 76 152 32 64 128 256), losses := [] }

theorem u36383 : Upper (D 7) (R 7) [34,320,33,68,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36383 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36384 : PairBound 9 := { available := 142, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 322 37 88 145 174 206 142 398), lower := (rows 35 322 37 88 145 32 64 128 256), losses := [] }

theorem u36384 : Upper (D 7) (R 7) [34,320,33,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36384 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36385 : PairBound 9 := { available := 141, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 322 37 88 146 173 205 141 397), lower := (rows 35 322 37 88 146 32 64 128 256), losses := [] }

theorem u36385 : Upper (D 7) (R 7) [34,320,33,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36385 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36386 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 322 37 88 148 171 203 139 395), lower := (rows 35 322 37 88 148 32 64 128 256), losses := [] }

theorem u36386 : Upper (D 7) (R 7) [34,320,33,80,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36386 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36387 : PairBound 9 := { available := 135, camps := [{ cop := 2, region := 474, targets := 32 },{ cop := 0, region := 4, targets := 2 }], pairs := [(1,5),(2,1),(3,5),(4,5)], upper := (rows 35 322 37 88 152 167 199 135 391), lower := (rows 35 322 37 88 152 32 64 128 256), losses := [] }

theorem u36387 : Upper (D 7) (R 7) [34,320,33,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36387 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36388 : PairBound 9 := { available := 92, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 322 37 137 146 124 92 220 348), lower := (rows 35 322 37 137 146 32 64 128 256), losses := [] }

theorem u36388 : Upper (D 7) (R 7) [34,320,33,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36388 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36389 : PairBound 9 := { available := 90, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 322 37 137 148 122 90 218 346), lower := (rows 35 322 37 137 148 32 64 128 256), losses := [] }

theorem u36389 : Upper (D 7) (R 7) [34,320,33,129,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36389 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36390 : PairBound 9 := { available := 30, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 322 37 137 208 62 94 158 286), lower := (rows 35 322 37 137 208 32 64 128 256), losses := [] }

theorem u36390 : Upper (D 7) (R 7) [34,320,33,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36390 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36391 : PairBound 9 := { available := 89, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 322 37 138 148 121 89 217 345), lower := (rows 35 322 37 138 148 32 64 128 256), losses := [] }

theorem u36391 : Upper (D 7) (R 7) [34,320,33,130,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36391 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36392 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 322 37 138 208 61 93 157 285), lower := (rows 35 322 37 138 208 32 64 128 256), losses := [] }

theorem u36392 : Upper (D 7) (R 7) [34,320,33,130,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36392 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36393 : PairBound 9 := { available := 27, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 35 322 37 140 208 59 91 155 283), lower := (rows 35 322 37 140 208 32 64 128 256), losses := [] }

theorem u36393 : Upper (D 7) (R 7) [34,320,33,132,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36393 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36394 : PairBound 9 := { available := 156, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 322 38 73 145 188 220 156 412), lower := (rows 35 322 38 73 145 32 64 128 256), losses := [] }

theorem u36394 : Upper (D 7) (R 7) [34,320,34,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36394 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36395 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 322 38 73 148 185 217 153 409), lower := (rows 35 322 38 73 148 32 64 128 256), losses := [] }

theorem u36395 : Upper (D 7) (R 7) [34,320,34,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36395 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36396 : PairBound 9 := { available := 149, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 322 38 73 152 181 213 149 405), lower := (rows 35 322 38 73 152 32 64 128 256), losses := [] }

theorem u36396 : Upper (D 7) (R 7) [34,320,34,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36396 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36397 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 322 38 76 145 185 217 153 409), lower := (rows 35 322 38 76 145 32 64 128 256), losses := [] }

theorem u36397 : Upper (D 7) (R 7) [34,320,34,68,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36397 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36398 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 322 38 76 152 177 209 145 401), lower := (rows 35 322 38 76 152 32 64 128 256), losses := [] }

theorem u36398 : Upper (D 7) (R 7) [34,320,34,68,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36398 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36399 : PairBound 9 := { available := 141, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 322 38 88 145 173 205 141 397), lower := (rows 35 322 38 88 145 32 64 128 256), losses := [] }

theorem u36399 : Upper (D 7) (R 7) [34,320,34,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36399 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36400 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 322 38 88 148 169 201 137 393), lower := (rows 35 322 38 88 148 32 64 128 256), losses := [] }

theorem u36400 : Upper (D 7) (R 7) [34,320,34,80,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36400 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36401 : PairBound 9 := { available := 133, camps := [{ cop := 1, region := 165, targets := 64 },{ cop := 0, region := 4, targets := 1 },{ cop := 0, region := 4, targets := 128 }], pairs := [(0,6),(2,0),(2,6),(2,7)], upper := (rows 35 322 38 88 152 165 197 133 389), lower := (rows 35 322 38 88 152 32 64 128 256), losses := [] }

theorem u36401 : Upper (D 7) (R 7) [34,320,34,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36401 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36402 : PairBound 9 := { available := 89, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 322 38 137 148 121 89 217 345), lower := (rows 35 322 38 137 148 32 64 128 256), losses := [] }

theorem u36402 : Upper (D 7) (R 7) [34,320,34,129,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36402 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36403 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 322 38 137 208 61 93 157 285), lower := (rows 35 322 38 137 208 32 64 128 256), losses := [] }

theorem u36403 : Upper (D 7) (R 7) [34,320,34,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36403 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36404 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 4, targets := 192 },{ cop := 2, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 322 38 140 208 57 89 153 281), lower := (rows 35 322 38 140 208 32 64 128 256), losses := [] }

theorem u36404 : Upper (D 7) (R 7) [34,320,34,132,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36404 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36405 : Route 9 := (fun mask => (mask,id))

def c36405 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36405 : Upper (D 7) (R 7) [34,320,40,65,129] 13 := by
  apply FastRouting.sound _ _ [34,320,40,65,129] 13 (by decide) (choices 1) [2,4,16,128] r36405 c36405
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21949
  · exact u21950
  · exact u21951
  · exact u21952

def r36406 : Route 9 := (fun mask => (mask,id))

def c36406 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36406 : Upper (D 7) (R 7) [34,320,40,65,130] 13 := by
  apply FastRouting.sound _ _ [34,320,40,65,130] 13 (by decide) (choices 1) [1,4,16,128] r36406 c36406
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21953
  · exact u21954
  · exact u21955
  · exact u21956

def r36407 : Route 9 := (fun mask => (mask,id))

def c36407 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36407 : Upper (D 7) (R 7) [34,320,40,65,132] 13 := by
  apply FastRouting.sound _ _ [34,320,40,65,132] 13 (by decide) (choices 1) [1,2,16,128] r36407 c36407
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21957
  · exact u21958
  · exact u21959
  · exact u21960

def b36408 : PairBound 9 := { available := 149, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 181, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 35 322 44 74 145 181 213 149 405), lower := (rows 35 322 44 74 145 32 64 128 256), losses := [] }

theorem u36408 : Upper (D 7) (R 7) [34,320,40,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36408 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36409 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 181, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 35 322 44 74 148 177 209 145 401), lower := (rows 35 322 44 74 148 32 64 128 256), losses := [] }

theorem u36409 : Upper (D 7) (R 7) [34,320,40,66,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36409 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36410 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6),(1,5),(4,5),(4,6)], upper := (rows 35 322 44 76 145 179 211 147 403), lower := (rows 35 322 44 76 145 32 64 128 256), losses := [] }

theorem u36410 : Upper (D 7) (R 7) [34,320,40,68,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36410 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36411 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6),(1,5),(4,5),(4,6)], upper := (rows 35 322 44 76 146 177 209 145 401), lower := (rows 35 322 44 76 146 32 64 128 256), losses := [] }

theorem u36411 : Upper (D 7) (R 7) [34,320,40,68,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36411 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36412 : Route 9 := (fun mask => (mask,id))

def c36412 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36412 : Upper (D 7) (R 7) [34,320,40,80,129] 13 := by
  apply FastRouting.sound _ _ [34,320,40,80,129] 13 (by decide) (choices 1) [1,2,4,128] r36412 c36412
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21961
  · exact u21962
  · exact u21963
  · exact u21964

def r36413 : Route 9 := (fun mask => (mask,id))

def c36413 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36413 : Upper (D 7) (R 7) [34,320,40,80,130] 13 := by
  apply FastRouting.sound _ _ [34,320,40,80,130] 13 (by decide) (choices 1) [1,4,128] r36413 c36413
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21965
  · exact u21966
  · exact u21967

def r36414 : Route 9 := (fun mask => (mask,id))

def c36414 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36414 : Upper (D 7) (R 7) [34,320,40,80,132] 13 := by
  apply FastRouting.sound _ _ [34,320,40,80,132] 13 (by decide) (choices 1) [1,2,128] r36414 c36414
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21968
  · exact u21969
  · exact u21970

def r36415 : Route 9 := (fun mask => (mask,id))

def c36415 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36415 : Upper (D 7) (R 7) [34,320,40,129,65] 13 := by
  apply FastRouting.sound _ _ [34,320,40,129,65] 13 (by decide) (choices 1) [2,4,16,128] r36415 c36415
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21971
  · exact u21972
  · exact u21973
  · exact u21974

def b36416 : PairBound 9 := { available := 149, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 173, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 35 322 44 137 82 181 213 149 405), lower := (rows 35 322 44 137 82 32 64 128 256), losses := [] }

theorem u36416 : Upper (D 7) (R 7) [34,320,40,129,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36416 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36417 : Route 9 := (fun mask => (mask,id))

def c36417 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36417 : Upper (D 7) (R 7) [34,320,40,129,68] 13 := by
  apply FastRouting.sound _ _ [34,320,40,129,68] 13 (by decide) (choices 1) [1,2,16,128] r36417 c36417
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21975
  · exact u21976
  · exact u21977
  · exact u21978

def b36418 : PairBound 9 := { available := 86, camps := [{ cop := 3, region := 16, targets := 98 },{ cop := 4, region := 8, targets := 2 }], pairs := [(3,1),(4,1),(4,5),(4,6)], upper := (rows 35 322 44 137 145 118 86 214 342), lower := (rows 35 322 44 137 145 32 64 128 256), losses := [] }

theorem u36418 : Upper (D 7) (R 7) [34,320,40,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36418 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36419 : Route 9 := (fun mask => (mask,id))

def c36419 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36419 : Upper (D 7) (R 7) [34,320,40,129,130] 13 := by
  apply FastRouting.sound _ _ [34,320,40,129,130] 13 (by decide) (choices 1) [1,4,16,64] r36419 c36419
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21979
  · exact u21980
  · exact u21981
  · exact u21982

#print axioms u36419
end Delivery.IrregularNine14.P07

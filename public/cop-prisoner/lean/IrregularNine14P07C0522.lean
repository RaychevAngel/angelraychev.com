import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0230
import IrregularNine14P07C0231
import IrregularNine14P07C0232

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b31320 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 8, targets := 129 },{ cop := 3, region := 2, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 7 98 28 104 273 163 195 131 387), lower := (rows 7 98 28 104 273 32 64 128 256), losses := [] }

theorem u31320 : Upper (D 7) (R 7) [6,96,24,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31320 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31321 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 8, targets := 129 },{ cop := 3, region := 2, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 7 98 28 104 274 161 193 129 385), lower := (rows 7 98 28 104 274 32 64 128 256), losses := [] }

theorem u31321 : Upper (D 7) (R 7) [6,96,24,96,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31321 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31322 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 8, targets := 129 },{ cop := 3, region := 2, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 7 98 28 104 400 163 195 131 387), lower := (rows 7 98 28 104 400 32 64 128 256), losses := [] }

theorem u31322 : Upper (D 7) (R 7) [6,96,24,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31322 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31323 : PairBound 9 := { available := 354, camps := [{ cop := 3, region := 20, targets := 98 }], pairs := [(2,1),(2,5),(2,6),(4,1)], upper := (rows 7 98 28 137 145 354 354 482 354), lower := (rows 7 98 28 137 145 32 64 128 256), losses := [] }

theorem u31323 : Upper (D 7) (R 7) [6,96,24,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31323 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31324 : PairBound 9 := { available := 353, camps := [{ cop := 4, region := 13, targets := 96 }], pairs := [(0,5),(0,6),(2,5),(2,6)], upper := (rows 7 98 28 137 146 353 353 481 353), lower := (rows 7 98 28 137 146 32 64 128 256), losses := [] }

theorem u31324 : Upper (D 7) (R 7) [6,96,24,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31324 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31325 : Route 9 := (fun mask => (mask,id))

def c31325 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u31325 : Upper (D 7) (R 7) [6,96,24,129,160] 13 := by
  apply FastRouting.sound _ _ [6,96,24,129,160] 13 (by decide) (choices 1) [1,2,64,256] r31325 c31325
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13808
  · exact u13809
  · exact u13810
  · exact u13811

def r31326 : Route 9 := (fun mask => (mask,id))

def c31326 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31326 : Upper (D 7) (R 7) [6,96,24,129,257] 13 := by
  apply FastRouting.sound _ _ [6,96,24,129,257] 13 (by decide) (choices 1) [2,64,128] r31326 c31326
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13812
  · exact u13813
  · exact u13814

def r31327 : Route 9 := (fun mask => (mask,id))

def c31327 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31327 : Upper (D 7) (R 7) [6,96,24,129,258] 13 := by
  apply FastRouting.sound _ _ [6,96,24,129,258] 13 (by decide) (choices 1) [1,64,128] r31327 c31327
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13815
  · exact u13816
  · exact u13817

def r31328 : Route 9 := (fun mask => (mask,id))

def c31328 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31328 : Upper (D 7) (R 7) [6,96,24,129,288] 13 := by
  apply FastRouting.sound _ _ [6,96,24,129,288] 13 (by decide) (choices 1) [1,2,64,128] r31328 c31328
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13818
  · exact u13819
  · exact u13820
  · exact u13821

def r31329 : Route 9 := (fun mask => (mask,id))

def c31329 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31329 : Upper (D 7) (R 7) [6,96,24,129,384] 13 := by
  apply FastRouting.sound _ _ [6,96,24,129,384] 13 (by decide) (choices 1) [1,2,64] r31329 c31329
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13822
  · exact u13823
  · exact u13824

def b31330 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 0, region := 496, targets := 2 },{ cop := 0, region := 456, targets := 32 }], pairs := [(0,7),(1,7),(3,5),(4,1)], upper := (rows 7 98 28 138 176 353 321 449 321), lower := (rows 7 98 28 138 176 32 64 128 256), losses := [] }

theorem u31330 : Upper (D 7) (R 7) [6,96,24,130,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31330 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31331 : Route 9 := (fun mask => (mask,id))

def c31331 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31331 : Upper (D 7) (R 7) [6,96,24,130,257] 13 := by
  apply FastRouting.sound _ _ [6,96,24,130,257] 13 (by decide) (choices 1) [1,64,128] r31331 c31331
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13825
  · exact u13826
  · exact u13827

def r31332 : Route 9 := (fun mask => (mask,id))

def c31332 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31332 : Upper (D 7) (R 7) [6,96,24,130,288] 13 := by
  apply FastRouting.sound _ _ [6,96,24,130,288] 13 (by decide) (choices 1) [1,64,128] r31332 c31332
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13828
  · exact u13829
  · exact u13830

def r31333 : Route 9 := (fun mask => (mask,id))

def c31333 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31333 : Upper (D 7) (R 7) [6,96,24,130,384] 13 := by
  apply FastRouting.sound _ _ [6,96,24,130,384] 13 (by decide) (choices 1) [1,64] r31333 c31333
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u13831
  · exact u13832

def b31334 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 0, region := 464, targets := 32 },{ cop := 0, region := 424, targets := 64 }], pairs := [(0,7),(1,7),(3,6),(4,5)], upper := (rows 7 98 28 168 208 291 323 387 259), lower := (rows 7 98 28 168 208 32 64 128 256), losses := [] }

theorem u31334 : Upper (D 7) (R 7) [6,96,24,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31334 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31335 : Route 9 := (fun mask => (mask,id))

def c31335 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31335 : Upper (D 7) (R 7) [6,96,24,160,257] 13 := by
  apply FastRouting.sound _ _ [6,96,24,160,257] 13 (by decide) (choices 1) [1,2,64,128] r31335 c31335
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13833
  · exact u13834
  · exact u13835
  · exact u13836

def r31336 : Route 9 := (fun mask => (mask,id))

def c31336 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31336 : Upper (D 7) (R 7) [6,96,24,160,258] 13 := by
  apply FastRouting.sound _ _ [6,96,24,160,258] 13 (by decide) (choices 1) [1,64,128] r31336 c31336
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13837
  · exact u13838
  · exact u13839

def r31337 : Route 9 := (fun mask => (mask,id))

def c31337 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31337 : Upper (D 7) (R 7) [6,96,24,160,320] 13 := by
  apply FastRouting.sound _ _ [6,96,24,160,320] 13 (by decide) (choices 1) [1,2,128] r31337 c31337
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13840
  · exact u13841
  · exact u13842

def r31338 : Route 9 := (fun mask => (mask,id))

def c31338 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31338 : Upper (D 7) (R 7) [6,96,24,160,384] 13 := by
  apply FastRouting.sound _ _ [6,96,24,160,384] 13 (by decide) (choices 1) [1,2,64] r31338 c31338
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13843
  · exact u13844
  · exact u13845

def b31339 : PairBound 9 := { available := 448, camps := [{ cop := 1, region := 29, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 98 44 25 19 480 448 448 448), lower := (rows 7 98 44 25 19 32 64 128 256), losses := [] }

theorem u31339 : Upper (D 7) (R 7) [6,96,40,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31339 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31340 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 29, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 7 98 44 25 81 418 450 386 386), lower := (rows 7 98 44 25 81 32 64 128 256), losses := [] }

theorem u31340 : Upper (D 7) (R 7) [6,96,40,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31340 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31341 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 29, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 7 98 44 25 82 417 449 385 385), lower := (rows 7 98 44 25 82 32 64 128 256), losses := [] }

theorem u31341 : Upper (D 7) (R 7) [6,96,40,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31341 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31342 : PairBound 9 := { available := 450, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 7 98 44 25 145 482 450 450 450), lower := (rows 7 98 44 25 145 32 64 128 256), losses := [] }

theorem u31342 : Upper (D 7) (R 7) [6,96,40,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31342 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31343 : Route 9 := (fun mask => (mask,id))

def c31343 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u31343 : Upper (D 7) (R 7) [6,96,40,17,130] 13 := by
  apply FastRouting.sound _ _ [6,96,40,17,130] 13 (by decide) (choices 1) [1,64,128,256] r31343 c31343
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13846
  · exact u13847
  · exact u13848
  · exact u13849

def r31344 : Route 9 := (fun mask => (mask,id))

def c31344 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u31344 : Upper (D 7) (R 7) [6,96,40,17,192] 13 := by
  apply FastRouting.sound _ _ [6,96,40,17,192] 13 (by decide) (choices 1) [1,2,128,256] r31344 c31344
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13850
  · exact u13851
  · exact u13852
  · exact u13853

def b31345 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 7 98 44 25 273 226 194 194 450), lower := (rows 7 98 44 25 273 32 64 128 256), losses := [] }

theorem u31345 : Upper (D 7) (R 7) [6,96,40,17,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31345 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31346 : Route 9 := (fun mask => (mask,id))

def c31346 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31346 : Upper (D 7) (R 7) [6,96,40,17,258] 13 := by
  apply FastRouting.sound _ _ [6,96,40,17,258] 13 (by decide) (choices 1) [1,64,128] r31346 c31346
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13854
  · exact u13855
  · exact u13856

def r31347 : Route 9 := (fun mask => (mask,id))

def c31347 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31347 : Upper (D 7) (R 7) [6,96,40,17,320] 13 := by
  apply FastRouting.sound _ _ [6,96,40,17,320] 13 (by decide) (choices 1) [1,2,128] r31347 c31347
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13857
  · exact u13858
  · exact u13859

def r31348 : Route 9 := (fun mask => (mask,id))

def c31348 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31348 : Upper (D 7) (R 7) [6,96,40,17,384] 13 := by
  apply FastRouting.sound _ _ [6,96,40,17,384] 13 (by decide) (choices 1) [1,2,64,128] r31348 c31348
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13860
  · exact u13861
  · exact u13862
  · exact u13863

def b31349 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 29, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 7 98 44 26 81 417 449 385 385), lower := (rows 7 98 44 26 81 32 64 128 256), losses := [] }

theorem u31349 : Upper (D 7) (R 7) [6,96,40,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31349 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31350 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 464, targets := 2 }], pairs := [(2,1),(3,5),(4,1),(4,5)], upper := (rows 7 98 44 26 145 481 449 449 449), lower := (rows 7 98 44 26 145 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 17 49 81 145 273), good := (rows 501 96 44 508 497 32 64 128 256) }] }

theorem u31350 : Upper (D 7) (R 7) [6,96,40,18,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31350 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31351 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 421, targets := 64 }], pairs := [(0,6),(2,6),(3,5),(4,5)], upper := (rows 7 98 44 26 208 417 449 385 385), lower := (rows 7 98 44 26 208 32 64 128 256), losses := [] }

theorem u31351 : Upper (D 7) (R 7) [6,96,40,18,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31351 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31352 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 464, targets := 2 }], pairs := [(2,1),(3,5),(4,1),(4,5)], upper := (rows 7 98 44 26 273 225 193 193 449), lower := (rows 7 98 44 26 273 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 17 49 81 145 273), good := (rows 501 96 44 508 497 32 64 128 256) }] }

theorem u31352 : Upper (D 7) (R 7) [6,96,40,18,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31352 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31353 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 165, targets := 64 }], pairs := [(0,6),(2,6),(3,5),(4,5)], upper := (rows 7 98 44 26 336 161 193 129 385), lower := (rows 7 98 44 26 336 32 64 128 256), losses := [] }

theorem u31353 : Upper (D 7) (R 7) [6,96,40,18,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31353 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31354 : Route 9 := (fun mask => (mask,id))

def c31354 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31354 : Upper (D 7) (R 7) [6,96,40,18,384] 13 := by
  apply FastRouting.sound _ _ [6,96,40,18,384] 13 (by decide) (choices 1) [1,64,128] r31354 c31354
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13864
  · exact u13865
  · exact u13866

def b31355 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 29, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 7 98 44 88 19 417 449 385 385), lower := (rows 7 98 44 88 19 32 64 128 256), losses := [] }

theorem u31355 : Upper (D 7) (R 7) [6,96,40,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31355 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31356 : Route 9 := (fun mask => (mask,id))

def c31356 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u31356 : Upper (D 7) (R 7) [6,96,40,80,129] 13 := by
  apply FastRouting.sound _ _ [6,96,40,80,129] 13 (by decide) (choices 1) [1,2,128,256] r31356 c31356
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13867
  · exact u13868
  · exact u13869
  · exact u13870

def r31357 : Route 9 := (fun mask => (mask,id))

def c31357 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u31357 : Upper (D 7) (R 7) [6,96,40,80,130] 13 := by
  apply FastRouting.sound _ _ [6,96,40,80,130] 13 (by decide) (choices 1) [1,128,256] r31357 c31357
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13871
  · exact u13872
  · exact u13873

def r31358 : Route 9 := (fun mask => (mask,id))

def c31358 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31358 : Upper (D 7) (R 7) [6,96,40,80,257] 13 := by
  apply FastRouting.sound _ _ [6,96,40,80,257] 13 (by decide) (choices 1) [1,2,128] r31358 c31358
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13874
  · exact u13875
  · exact u13876

def r31359 : Route 9 := (fun mask => (mask,id))

def c31359 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31359 : Upper (D 7) (R 7) [6,96,40,80,258] 13 := by
  apply FastRouting.sound _ _ [6,96,40,80,258] 13 (by decide) (choices 1) [1,128] r31359 c31359
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u13877
  · exact u13878

def r31360 : Route 9 := (fun mask => (mask,id))

def c31360 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31360 : Upper (D 7) (R 7) [6,96,40,80,384] 13 := by
  apply FastRouting.sound _ _ [6,96,40,80,384] 13 (by decide) (choices 1) [1,2,128] r31360 c31360
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13879
  · exact u13880
  · exact u13881

def b31361 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 16, targets := 192 }], pairs := [(3,5),(4,5),(4,6),(4,7)], upper := (rows 7 98 44 137 19 496 464 464 464), lower := (rows 7 98 44 137 19 32 64 128 256), losses := [] }

theorem u31361 : Upper (D 7) (R 7) [6,96,40,129,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31361 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31362 : Route 9 := (fun mask => (mask,id))

def c31362 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u31362 : Upper (D 7) (R 7) [6,96,40,129,65] 13 := by
  apply FastRouting.sound _ _ [6,96,40,129,65] 13 (by decide) (choices 1) [2,16,128,256] r31362 c31362
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13882
  · exact u13883
  · exact u13884
  · exact u13885

def b31363 : PairBound 9 := { available := 401, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 7 98 44 137 82 433 465 401 401), lower := (rows 7 98 44 137 82 32 64 128 256), losses := [] }

theorem u31363 : Upper (D 7) (R 7) [6,96,40,129,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31363 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31364 : PairBound 9 := { available := 338, camps := [{ cop := 3, region := 16, targets := 98 },{ cop := 4, region := 8, targets := 2 }], pairs := [(3,1),(4,1),(4,5),(4,6)], upper := (rows 7 98 44 137 145 370 338 466 338), lower := (rows 7 98 44 137 145 32 64 128 256), losses := [] }

theorem u31364 : Upper (D 7) (R 7) [6,96,40,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31364 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31365 : Route 9 := (fun mask => (mask,id))

def c31365 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u31365 : Upper (D 7) (R 7) [6,96,40,129,130] 13 := by
  apply FastRouting.sound _ _ [6,96,40,129,130] 13 (by decide) (choices 1) [1,16,64,256] r31365 c31365
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13886
  · exact u13887
  · exact u13888
  · exact u13889

def r31366 : Route 9 := (fun mask => (mask,id))

def c31366 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31366 : Upper (D 7) (R 7) [6,96,40,129,192] 13 := by
  apply FastRouting.sound _ _ [6,96,40,129,192] 13 (by decide) (choices 1) [1,2,16,256] r31366 c31366
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13890
  · exact u13891
  · exact u13892
  · exact u13893

def r31367 : Route 9 := (fun mask => (mask,id))

def c31367 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u31367 : Upper (D 7) (R 7) [6,96,40,129,257] 13 := by
  apply FastRouting.sound _ _ [6,96,40,129,257] 13 (by decide) (choices 1) [2,16,64,128] r31367 c31367
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13894
  · exact u13895
  · exact u13896
  · exact u13897

def r31368 : Route 9 := (fun mask => (mask,id))

def c31368 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u31368 : Upper (D 7) (R 7) [6,96,40,129,258] 13 := by
  apply FastRouting.sound _ _ [6,96,40,129,258] 13 (by decide) (choices 1) [1,16,64,128] r31368 c31368
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13898
  · exact u13899
  · exact u13900
  · exact u13901

def r31369 : Route 9 := (fun mask => (mask,id))

def c31369 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31369 : Upper (D 7) (R 7) [6,96,40,129,320] 13 := by
  apply FastRouting.sound _ _ [6,96,40,129,320] 13 (by decide) (choices 1) [1,2,16,128] r31369 c31369
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13902
  · exact u13903
  · exact u13904
  · exact u13905

def r31370 : Route 9 := (fun mask => (mask,id))

def c31370 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31370 : Upper (D 7) (R 7) [6,96,40,129,384] 13 := by
  apply FastRouting.sound _ _ [6,96,40,129,384] 13 (by decide) (choices 1) [1,2,16,64] r31370 c31370
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13906
  · exact u13907
  · exact u13908
  · exact u13909

def r31371 : Route 9 := (fun mask => (mask,id))

def c31371 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u31371 : Upper (D 7) (R 7) [6,96,40,130,65] 13 := by
  apply FastRouting.sound _ _ [6,96,40,130,65] 13 (by decide) (choices 1) [1,16,128,256] r31371 c31371
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13910
  · exact u13911
  · exact u13912
  · exact u13913

def b31372 : PairBound 9 := { available := 337, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 464, targets := 2 },{ cop := 4, region := 354, targets := 128 }], pairs := [(1,7),(3,5),(4,1),(4,5)], upper := (rows 7 98 44 138 145 369 337 465 337), lower := (rows 7 98 44 138 145 32 64 128 256), losses := [] }

theorem u31372 : Upper (D 7) (R 7) [6,96,40,130,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31372 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31373 : Route 9 := (fun mask => (mask,id))

def c31373 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31373 : Upper (D 7) (R 7) [6,96,40,130,192] 13 := by
  apply FastRouting.sound _ _ [6,96,40,130,192] 13 (by decide) (choices 1) [1,16,256] r31373 c31373
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13914
  · exact u13915
  · exact u13916

def r31374 : Route 9 := (fun mask => (mask,id))

def c31374 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u31374 : Upper (D 7) (R 7) [6,96,40,130,257] 13 := by
  apply FastRouting.sound _ _ [6,96,40,130,257] 13 (by decide) (choices 1) [1,16,64,128] r31374 c31374
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13917
  · exact u13918
  · exact u13919
  · exact u13920

def r31375 : Route 9 := (fun mask => (mask,id))

def c31375 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31375 : Upper (D 7) (R 7) [6,96,40,130,320] 13 := by
  apply FastRouting.sound _ _ [6,96,40,130,320] 13 (by decide) (choices 1) [1,16,128] r31375 c31375
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13921
  · exact u13922
  · exact u13923

def r31376 : Route 9 := (fun mask => (mask,id))

def c31376 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31376 : Upper (D 7) (R 7) [6,96,40,130,384] 13 := by
  apply FastRouting.sound _ _ [6,96,40,130,384] 13 (by decide) (choices 1) [1,16,64] r31376 c31376
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13924
  · exact u13925
  · exact u13926

def b31377 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 16, targets := 192 }], pairs := [(3,5),(4,5),(4,6),(4,7)], upper := (rows 7 98 44 152 19 481 449 449 449), lower := (rows 7 98 44 152 19 32 64 128 256), losses := [] }

theorem u31377 : Upper (D 7) (R 7) [6,96,40,144,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31377 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31378 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 472, targets := 32 }], pairs := [(2,6),(3,5),(3,6),(4,5)], upper := (rows 7 98 44 152 81 419 451 387 387), lower := (rows 7 98 44 152 81 32 64 128 256), losses := [{ target := 6, region := (rows 1 2 20 24 16 33 0 129 257), good := (rows 423 34 44 156 445 32 0 128 256) }] }

theorem u31378 : Upper (D 7) (R 7) [6,96,40,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31378 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31379 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 7 98 44 152 82 417 449 385 385), lower := (rows 7 98 44 152 82 32 64 128 256), losses := [] }

theorem u31379 : Upper (D 7) (R 7) [6,96,40,144,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31379 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u31379
end Delivery.IrregularNine14.P07

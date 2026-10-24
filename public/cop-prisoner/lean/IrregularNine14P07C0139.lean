import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0011

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b8340 : PairBound 9 := { available := 136, camps := [{ cop := 8, region := 103, targets := 128 },{ cop := 2, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 37 98 324 26 145 34 65 136 392), lower := (rows 37 98 324 26 145 34 65 128 256), losses := [] }

theorem u8340 : Upper (D 7) (R 7) [36,96,320,18,129,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8340 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8341 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 106, targets := 129 }], pairs := [(1,0),(1,7),(3,0)], upper := (rows 37 98 324 26 145 34 72 129 385), lower := (rows 37 98 324 26 145 34 72 128 256), losses := [] }

theorem u8341 : Upper (D 7) (R 7) [36,96,320,18,129,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8341 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8342 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 35, targets := 128 },{ cop := 4, region := 106, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(3,0)], upper := (rows 37 98 324 26 145 34 192 137 265), lower := (rows 37 98 324 26 145 34 192 128 256), losses := [] }

theorem u8342 : Upper (D 7) (R 7) [36,96,320,18,129,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8342 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8343 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 388, targets := 33 },{ cop := 4, region := 106, targets := 128 }], pairs := [(1,7),(2,0),(2,5)], upper := (rows 37 98 324 26 145 40 65 130 386), lower := (rows 37 98 324 26 145 40 65 128 256), losses := [] }

theorem u8343 : Upper (D 7) (R 7) [36,96,320,18,129,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8343 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8344 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 106, targets := 129 }], pairs := [(1,0),(1,7),(3,0)], upper := (rows 37 98 324 26 145 40 66 129 385), lower := (rows 37 98 324 26 145 40 66 128 256), losses := [] }

theorem u8344 : Upper (D 7) (R 7) [36,96,320,18,129,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8344 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8345 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 261, targets := 128 },{ cop := 4, region := 106, targets := 1 }], pairs := [(0,7),(1,0),(2,7)], upper := (rows 37 98 324 26 145 40 192 131 259), lower := (rows 37 98 324 26 145 40 192 128 256), losses := [] }

theorem u8345 : Upper (D 7) (R 7) [36,96,320,18,129,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8345 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8346 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 66, targets := 128 }], pairs := [(1,7),(2,5),(2,7),(3,7)], upper := (rows 37 98 324 26 145 160 65 138 266), lower := (rows 37 98 324 26 145 160 65 128 256), losses := [{ target := 5, region := (rows 1 2 12 8 16 0 81 136 264), good := (rows 69 66 324 478 209 128 65 128 256) },{ target := 7, region := (rows 1 3 28 24 16 32 81 0 280), good := (rows 103 98 324 350 351 32 67 0 256) }] }

theorem u8346 : Upper (D 7) (R 7) [36,96,320,18,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8346 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8347 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 106, targets := 1 },{ cop := 0, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(2,7),(3,0)], upper := (rows 37 98 324 26 145 160 66 137 265), lower := (rows 37 98 324 26 145 160 66 128 256), losses := [{ target := 7, region := (rows 1 35 28 24 16 32 123 0 272), good := (rows 103 98 324 350 351 98 66 0 256) }] }

theorem u8347 : Upper (D 7) (R 7) [36,96,320,18,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8347 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8348 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 261, targets := 128 },{ cop := 4, region := 106, targets := 1 }], pairs := [(0,7),(1,0),(2,7)], upper := (rows 37 98 324 26 145 160 72 131 259), lower := (rows 37 98 324 26 145 160 72 128 256), losses := [] }

theorem u8348 : Upper (D 7) (R 7) [36,96,320,18,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8348 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r8349 : Route 9 := (fun mask => (mask,id))

def c8349 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8349 : Upper (D 7) (R 7) [36,96,320,18,136,128,1] 13 := by
  apply FastRouting.sound _ _ [36,96,320,18,136,128,1] 13 (by decide) (choices 1) [1,2] r8349 c8349
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u664
  · exact u665

def b8350 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 90, targets := 1 },{ cop := 5, region := 327, targets := 128 }], pairs := [(0,7),(1,0),(3,0),(4,0)], upper := (rows 37 98 324 26 152 160 66 129 257), lower := (rows 37 98 324 26 152 160 66 128 256), losses := [] }

theorem u8350 : Upper (D 7) (R 7) [36,96,320,18,136,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8350 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8351 : PairBound 9 := { available := 24, camps := [{ cop := 8, region := 103, targets := 128 },{ cop := 2, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 37 98 324 137 146 34 65 152 280), lower := (rows 37 98 324 137 146 34 65 128 256), losses := [] }

theorem u8351 : Upper (D 7) (R 7) [36,96,320,129,130,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8351 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8352 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 35, targets := 128 },{ cop := 3, region := 98, targets := 1 }], pairs := [(0,7),(1,0),(1,7)], upper := (rows 37 98 324 137 146 34 72 145 273), lower := (rows 37 98 324 137 146 34 72 128 256), losses := [] }

theorem u8352 : Upper (D 7) (R 7) [36,96,320,129,130,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8352 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8353 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 136, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 37 98 324 137 146 34 80 137 265), lower := (rows 37 98 324 137 146 34 80 128 256), losses := [] }

theorem u8353 : Upper (D 7) (R 7) [36,96,320,129,130,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8353 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8354 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 404, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 37 98 324 137 146 40 65 146 274), lower := (rows 37 98 324 137 146 40 65 128 256), losses := [] }

theorem u8354 : Upper (D 7) (R 7) [36,96,320,129,130,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8354 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8355 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 114, targets := 1 },{ cop := 0, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 37 98 324 137 146 40 66 145 273), lower := (rows 37 98 324 137 146 40 66 128 256), losses := [] }

theorem u8355 : Upper (D 7) (R 7) [36,96,320,129,130,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8355 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8356 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 261, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 37 98 324 137 146 40 80 131 259), lower := (rows 37 98 324 137 146 40 80 128 256), losses := [] }

theorem u8356 : Upper (D 7) (R 7) [36,96,320,129,130,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8356 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r8357 : Route 9 := (fun mask => (mask,id))

def c8357 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8357 : Upper (D 7) (R 7) [36,96,320,129,130,16,1] 13 := by
  apply FastRouting.sound _ _ [36,96,320,129,130,16,1] 13 (by decide) (choices 1) [2,8] r8357 c8357
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u666
  · exact u667

def b8358 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 136, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 37 98 324 137 146 48 66 137 265), lower := (rows 37 98 324 137 146 48 66 128 256), losses := [] }

theorem u8358 : Upper (D 7) (R 7) [36,96,320,129,130,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8358 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8359 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 261, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 37 98 324 137 146 48 72 131 259), lower := (rows 37 98 324 137 146 48 72 128 256), losses := [] }

theorem u8359 : Upper (D 7) (R 7) [36,96,320,129,130,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8359 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8360 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 404, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 37 98 388 11 146 40 65 208 336), lower := (rows 37 98 388 11 146 40 65 128 256), losses := [] }

theorem u8360 : Upper (D 7) (R 7) [36,96,384,3,130,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8360 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8361 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 389, targets := 2 }], pairs := [(0,1),(2,1)], upper := (rows 37 98 388 11 146 40 80 193 321), lower := (rows 37 98 388 11 146 40 80 128 256), losses := [] }

theorem u8361 : Upper (D 7) (R 7) [36,96,384,3,130,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8361 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8362 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 404, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 37 98 388 11 208 40 65 146 274), lower := (rows 37 98 388 11 208 40 65 128 256), losses := [] }

theorem u8362 : Upper (D 7) (R 7) [36,96,384,3,192,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8362 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8363 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 405, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 37 98 388 11 208 40 66 145 273), lower := (rows 37 98 388 11 208 40 66 128 256), losses := [] }

theorem u8363 : Upper (D 7) (R 7) [36,96,384,3,192,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8363 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8364 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 37 98 388 11 208 40 80 131 259), lower := (rows 37 98 388 11 208 40 80 128 256), losses := [] }

theorem u8364 : Upper (D 7) (R 7) [36,96,384,3,192,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8364 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8365 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 404, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 37 98 388 25 146 40 65 194 322), lower := (rows 37 98 388 25 146 40 65 128 256), losses := [] }

theorem u8365 : Upper (D 7) (R 7) [36,96,384,17,130,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8365 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8366 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 389, targets := 2 },{ cop := 5, region := 66, targets := 1 }], pairs := [(0,1),(1,0),(2,1)], upper := (rows 37 98 388 25 146 40 66 193 321), lower := (rows 37 98 388 25 146 40 66 128 256), losses := [] }

theorem u8366 : Upper (D 7) (R 7) [36,96,384,17,130,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8366 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8367 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 6, region := 422, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,0)], upper := (rows 37 98 388 25 152 34 65 194 322), lower := (rows 37 98 388 25 152 34 65 128 256), losses := [] }

theorem u8367 : Upper (D 7) (R 7) [36,96,384,17,136,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8367 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8368 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 413, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 37 98 388 25 152 34 66 193 321), lower := (rows 37 98 388 25 152 34 66 128 256), losses := [] }

theorem u8368 : Upper (D 7) (R 7) [36,96,384,17,136,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8368 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8369 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,0)], upper := (rows 37 98 388 25 208 34 65 138 266), lower := (rows 37 98 388 25 208 34 65 128 256), losses := [{ target := 0, region := (rows 0 82 12 8 16 122 64 136 264), good := (rows 36 98 388 446 242 34 98 128 256) }] }

theorem u8369 : Upper (D 7) (R 7) [36,96,384,17,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8369 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8370 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 413, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 37 98 388 25 208 34 66 137 265), lower := (rows 37 98 388 25 208 34 66 128 256), losses := [] }

theorem u8370 : Upper (D 7) (R 7) [36,96,384,17,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8370 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8371 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 389, targets := 64 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,6),(1,0),(2,6)], upper := (rows 37 98 388 25 208 34 72 131 259), lower := (rows 37 98 388 25 208 34 72 128 256), losses := [] }

theorem u8371 : Upper (D 7) (R 7) [36,96,384,17,192,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8371 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8372 : PairBound 9 := { available := 72, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 4, region := 106, targets := 128 },{ cop := 6, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(3,7)], upper := (rows 37 98 388 26 145 34 65 200 328), lower := (rows 37 98 388 26 145 34 65 128 256), losses := [] }

theorem u8372 : Upper (D 7) (R 7) [36,96,384,18,129,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8372 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8373 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 405, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 37 98 388 26 145 34 72 193 321), lower := (rows 37 98 388 26 145 34 72 128 256), losses := [] }

theorem u8373 : Upper (D 7) (R 7) [36,96,384,18,129,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8373 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8374 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 388, targets := 33 },{ cop := 4, region := 106, targets := 128 }], pairs := [(1,7),(2,0),(2,5)], upper := (rows 37 98 388 26 145 40 65 194 322), lower := (rows 37 98 388 26 145 40 65 128 256), losses := [] }

theorem u8374 : Upper (D 7) (R 7) [36,96,384,18,129,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8374 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8375 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 405, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 37 98 388 26 145 40 66 193 321), lower := (rows 37 98 388 26 145 40 66 128 256), losses := [] }

theorem u8375 : Upper (D 7) (R 7) [36,96,384,18,129,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8375 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8376 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 404, targets := 98 }], pairs := [(2,1),(2,5),(2,6),(4,1)], upper := (rows 37 98 388 73 145 34 66 152 280), lower := (rows 37 98 388 73 145 34 66 128 256), losses := [] }

theorem u8376 : Upper (D 7) (R 7) [36,96,384,65,129,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8376 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8377 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 37 98 388 73 145 34 72 146 274), lower := (rows 37 98 388 73 145 34 72 128 256), losses := [] }

theorem u8377 : Upper (D 7) (R 7) [36,96,384,65,129,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8377 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8378 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 422, targets := 1 },{ cop := 4, region := 72, targets := 2 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 37 98 388 73 145 34 80 138 266), lower := (rows 37 98 388 73 145 34 80 128 256), losses := [] }

theorem u8378 : Upper (D 7) (R 7) [36,96,384,65,129,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8378 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8379 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 107, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(3,7)], upper := (rows 37 98 388 73 146 34 65 152 280), lower := (rows 37 98 388 73 146 34 65 128 256), losses := [] }

theorem u8379 : Upper (D 7) (R 7) [36,96,384,65,130,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8379 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8380 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 37 98 388 73 146 34 72 145 273), lower := (rows 37 98 388 73 146 34 72 128 256), losses := [] }

theorem u8380 : Upper (D 7) (R 7) [36,96,384,65,130,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8380 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8381 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 397, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 37 98 388 73 146 34 80 137 265), lower := (rows 37 98 388 73 146 34 80 128 256), losses := [] }

theorem u8381 : Upper (D 7) (R 7) [36,96,384,65,130,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8381 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8382 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 37 98 388 73 146 48 65 138 266), lower := (rows 37 98 388 73 146 48 65 128 256), losses := [] }

theorem u8382 : Upper (D 7) (R 7) [36,96,384,65,130,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8382 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8383 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 397, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 37 98 388 73 146 48 66 137 265), lower := (rows 37 98 388 73 146 48 66 128 256), losses := [] }

theorem u8383 : Upper (D 7) (R 7) [36,96,384,65,130,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8383 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8384 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 37 98 388 73 146 48 72 131 259), lower := (rows 37 98 388 73 146 48 72 128 256), losses := [] }

theorem u8384 : Upper (D 7) (R 7) [36,96,384,65,130,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8384 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8385 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 107, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(3,7)], upper := (rows 37 98 388 73 152 34 65 146 274), lower := (rows 37 98 388 73 152 34 65 128 256), losses := [] }

theorem u8385 : Upper (D 7) (R 7) [36,96,384,65,136,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8385 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8386 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 404, targets := 98 }], pairs := [(2,1),(2,5),(2,6),(4,1)], upper := (rows 37 98 388 73 152 34 66 145 273), lower := (rows 37 98 388 73 152 34 66 128 256), losses := [] }

theorem u8386 : Upper (D 7) (R 7) [36,96,384,65,136,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8386 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8387 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 389, targets := 64 },{ cop := 4, region := 98, targets := 1 }], pairs := [(0,6),(1,0),(2,6)], upper := (rows 37 98 388 73 152 34 80 131 259), lower := (rows 37 98 388 73 152 34 80 128 256), losses := [] }

theorem u8387 : Upper (D 7) (R 7) [36,96,384,65,136,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8387 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8388 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 3, region := 422, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,0)], upper := (rows 37 98 388 88 145 34 65 138 266), lower := (rows 37 98 388 88 145 34 65 128 256), losses := [] }

theorem u8388 : Upper (D 7) (R 7) [36,96,384,80,129,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8388 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8389 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 413, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 37 98 388 88 145 34 66 137 265), lower := (rows 37 98 388 88 145 34 66 128 256), losses := [] }

theorem u8389 : Upper (D 7) (R 7) [36,96,384,80,129,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8389 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8390 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 37 98 388 88 145 34 72 131 259), lower := (rows 37 98 388 88 145 34 72 128 256), losses := [] }

theorem u8390 : Upper (D 7) (R 7) [36,96,384,80,129,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8390 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8391 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 412, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 37 98 388 88 146 33 65 138 266), lower := (rows 37 98 388 88 146 33 65 128 256), losses := [] }

theorem u8391 : Upper (D 7) (R 7) [36,96,384,80,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8391 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8392 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 421, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 98 388 88 146 33 66 137 265), lower := (rows 37 98 388 88 146 33 66 128 256), losses := [] }

theorem u8392 : Upper (D 7) (R 7) [36,96,384,80,130,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8392 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8393 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 72, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 37 98 388 88 146 33 72 131 259), lower := (rows 37 98 388 88 146 33 72 128 256), losses := [] }

theorem u8393 : Upper (D 7) (R 7) [36,96,384,80,130,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8393 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8394 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 466, targets := 1 },{ cop := 7, region := 66, targets := 32 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 37 194 7 25 336 40 66 160 416), lower := (rows 37 194 7 25 336 40 66 128 256), losses := [] }

theorem u8394 : Upper (D 7) (R 7) [36,192,3,17,320,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8394 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8395 : PairBound 9 := { available := 130, camps := [{ cop := 6, region := 402, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 37 194 7 25 336 40 96 130 386), lower := (rows 37 194 7 25 336 40 96 128 256), losses := [] }

theorem u8395 : Upper (D 7) (R 7) [36,192,3,17,320,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8395 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8396 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 7 25 336 40 192 162 290), lower := (rows 37 194 7 25 336 40 192 128 256), losses := [] }

theorem u8396 : Upper (D 7) (R 7) [36,192,3,17,320,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8396 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8397 : PairBound 9 := { available := 136, camps := [{ cop := 6, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 37 194 7 26 112 288 65 136 392), lower := (rows 37 194 7 26 112 288 65 128 256), losses := [] }

theorem u8397 : Upper (D 7) (R 7) [36,192,3,18,96,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8397 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8398 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 293, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 37 194 7 26 112 288 72 129 385), lower := (rows 37 194 7 26 112 288 72 128 256), losses := [] }

theorem u8398 : Upper (D 7) (R 7) [36,192,3,18,96,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8398 [(5,8),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8399 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 7 26 112 288 192 137 265), lower := (rows 37 194 7 26 112 288 192 128 256), losses := [] }

theorem u8399 : Upper (D 7) (R 7) [36,192,3,18,96,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8399 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u8399
end Delivery.IrregularNine14.P07

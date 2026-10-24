import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0032

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b13440 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 34, targets := 193 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,0),(1,6),(1,7),(3,6)], upper := (rows 7 42 196 280 81 34 225 161 417), lower := (rows 7 42 196 280 81 34 64 128 256), losses := [] }

theorem u13440 : Upper (D 7) (R 7) [6,40,192,272,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13440 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13441 : Route 9 := (fun mask => (mask,id))

def c13441 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13441 : Upper (D 7) (R 7) [6,40,192,272,65,128] 13 := by
  apply FastRouting.sound _ _ [6,40,192,272,65,128] 13 (by decide) (choices 1) [1,2,32] r13441 c13441
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1920
  · exact u1921
  · exact u1922

def r13442 : Route 9 := (fun mask => (mask,id))

def c13442 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13442 : Upper (D 7) (R 7) [6,40,192,272,66,1] 13 := by
  apply FastRouting.sound _ _ [6,40,192,272,66,1] 13 (by decide) (choices 1) [1,32,128] r13442 c13442
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1923
  · exact u1924
  · exact u1925

def r13443 : Route 9 := (fun mask => (mask,id))

def c13443 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13443 : Upper (D 7) (R 7) [6,40,192,272,66,128] 13 := by
  apply FastRouting.sound _ _ [6,40,192,272,66,128] 13 (by decide) (choices 1) [1,32] r13443 c13443
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1926
  · exact u1927

def r13444 : Route 9 := (fun mask => (mask,id))

def c13444 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13444 : Upper (D 7) (R 7) [6,40,192,272,96,1] 13 := by
  apply FastRouting.sound _ _ [6,40,192,272,96,1] 13 (by decide) (choices 1) [1,2,128] r13444 c13444
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1928
  · exact u1929
  · exact u1930

def b13445 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 34, targets := 193 },{ cop := 0, region := 196, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(2,1)], upper := (rows 7 42 196 280 112 34 193 129 385), lower := (rows 7 42 196 280 112 34 64 128 256), losses := [] }

theorem u13445 : Upper (D 7) (R 7) [6,40,192,272,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13445 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13446 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 197, targets := 32 },{ cop := 2, region := 48, targets := 3 }], pairs := [(0,5),(2,5),(4,0),(4,1)], upper := (rows 7 42 196 280 112 160 67 131 259), lower := (rows 7 42 196 280 112 160 64 128 256), losses := [] }

theorem u13446 : Upper (D 7) (R 7) [6,40,192,272,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13446 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13447 : PairBound 9 := { available := 146, camps := [{ cop := 4, region := 462, targets := 1 },{ cop := 5, region := 16, targets := 2 }], pairs := [(1,0),(2,0),(3,0),(4,1)], upper := (rows 7 42 196 328 49 33 210 146 402), lower := (rows 7 42 196 328 49 33 64 128 256), losses := [] }

theorem u13447 : Upper (D 7) (R 7) [6,40,192,320,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13447 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13448 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,5)], upper := (rows 7 42 196 328 49 34 209 145 401), lower := (rows 7 42 196 328 49 34 64 128 256), losses := [] }

theorem u13448 : Upper (D 7) (R 7) [6,40,192,320,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13448 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13449 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 42 196 328 49 48 195 131 387), lower := (rows 7 42 196 328 49 48 64 128 256), losses := [] }

theorem u13449 : Upper (D 7) (R 7) [6,40,192,320,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13449 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13450 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 330, targets := 128 },{ cop := 0, region := 176, targets := 64 }], pairs := [(1,7),(3,7),(4,1),(4,6)], upper := (rows 7 42 196 328 49 160 83 147 275), lower := (rows 7 42 196 328 49 160 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 164 64 128 256), good := (rows 53 40 228 328 49 160 64 160 256) }] }

theorem u13450 : Upper (D 7) (R 7) [6,40,192,320,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13450 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13451 : Route 9 := (fun mask => (mask,id))

def c13451 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13451 : Upper (D 7) (R 7) [6,40,192,320,129,1] 13 := by
  apply FastRouting.sound _ _ [6,40,192,320,129,1] 13 (by decide) (choices 1) [2,16,32] r13451 c13451
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1931
  · exact u1932
  · exact u1933

def b13452 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 34, targets := 193 },{ cop := 0, region := 176, targets := 64 }], pairs := [(1,0),(1,6),(1,7),(4,6)], upper := (rows 7 42 196 328 145 34 113 177 305), lower := (rows 7 42 196 328 145 34 64 128 256), losses := [] }

theorem u13452 : Upper (D 7) (R 7) [6,40,192,320,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13452 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13453 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 362, targets := 128 },{ cop := 0, region := 176, targets := 64 }], pairs := [(1,7),(3,7),(4,6)], upper := (rows 7 42 196 328 145 48 99 163 291), lower := (rows 7 42 196 328 145 48 64 128 256), losses := [] }

theorem u13453 : Upper (D 7) (R 7) [6,40,192,320,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13453 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13454 : Route 9 := (fun mask => (mask,id))

def c13454 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13454 : Upper (D 7) (R 7) [6,40,192,320,130,1] 13 := by
  apply FastRouting.sound _ _ [6,40,192,320,130,1] 13 (by decide) (choices 1) [1,16,32] r13454 c13454
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1934
  · exact u1935
  · exact u1936

def r13455 : Route 9 := (fun mask => (mask,id))

def c13455 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13455 : Upper (D 7) (R 7) [6,40,192,320,130,16] 13 := by
  apply FastRouting.sound _ _ [6,40,192,320,130,16] 13 (by decide) (choices 1) [1,32] r13455 c13455
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1937
  · exact u1938

def r13456 : Route 9 := (fun mask => (mask,id))

def c13456 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13456 : Upper (D 7) (R 7) [6,40,192,320,160,1] 13 := by
  apply FastRouting.sound _ _ [6,40,192,320,160,1] 13 (by decide) (choices 1) [1,2,16] r13456 c13456
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1939
  · exact u1940
  · exact u1941

def b13457 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 34, targets := 193 },{ cop := 0, region := 176, targets := 64 }], pairs := [(1,0),(1,6),(1,7),(4,6)], upper := (rows 7 42 196 328 176 34 81 145 273), lower := (rows 7 42 196 328 176 34 64 128 256), losses := [] }

theorem u13457 : Upper (D 7) (R 7) [6,40,192,320,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13457 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13458 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 42 196 328 176 48 67 131 259), lower := (rows 7 42 196 328 176 48 64 128 256), losses := [] }

theorem u13458 : Upper (D 7) (R 7) [6,40,192,320,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13458 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13459 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 389, targets := 64 },{ cop := 3, region := 242, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,0)], upper := (rows 7 42 261 25 82 96 224 160 416), lower := (rows 7 42 261 25 82 96 64 128 256), losses := [] }

theorem u13459 : Upper (D 7) (R 7) [6,40,257,17,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13459 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13460 : Route 9 := (fun mask => (mask,id))

def c13460 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13460 : Upper (D 7) (R 7) [6,40,257,17,66,128] 13 := by
  apply FastRouting.sound _ _ [6,40,257,17,66,128] 13 (by decide) (choices 1) [32,128] r13460 c13460
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1942
  · exact u1943

def b13461 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 242, targets := 1 },{ cop := 3, region := 34, targets := 192 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 7 42 261 25 208 34 224 224 480), lower := (rows 7 42 261 25 208 34 64 128 256), losses := [] }

theorem u13461 : Upper (D 7) (R 7) [6,40,257,17,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13461 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13462 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 389, targets := 64 },{ cop := 3, region := 242, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,0)], upper := (rows 7 42 261 25 208 96 226 162 418), lower := (rows 7 42 261 25 208 96 64 128 256), losses := [] }

theorem u13462 : Upper (D 7) (R 7) [6,40,257,17,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13462 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13463 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 218, targets := 1 },{ cop := 0, region := 484, targets := 2 }], pairs := [(1,0),(2,1),(3,0),(4,0)], upper := (rows 7 42 261 26 208 33 224 224 480), lower := (rows 7 42 261 26 208 33 64 128 256), losses := [] }

theorem u13463 : Upper (D 7) (R 7) [6,40,257,18,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13463 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13464 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 42, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 7 42 261 26 208 96 225 161 417), lower := (rows 7 42 261 26 208 96 64 128 256), losses := [] }

theorem u13464 : Upper (D 7) (R 7) [6,40,257,18,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13464 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13465 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 50, targets := 1 },{ cop := 3, region := 50, targets := 128 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 7 42 261 73 112 34 208 144 400), lower := (rows 7 42 261 73 112 34 64 128 256), losses := [] }

theorem u13465 : Upper (D 7) (R 7) [6,40,257,65,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13465 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13466 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 42 261 73 112 48 194 130 386), lower := (rows 7 42 261 73 112 48 64 128 256), losses := [] }

theorem u13466 : Upper (D 7) (R 7) [6,40,257,65,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13466 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13467 : Route 9 := (fun mask => (mask,id))

def c13467 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13467 : Upper (D 7) (R 7) [6,40,257,65,96,128] 13 := by
  apply FastRouting.sound _ _ [6,40,257,65,96,128] 13 (by decide) (choices 1) [2,16,128] r13467 c13467
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1944
  · exact u1945
  · exact u1946

def b13468 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 178, targets := 1 }], pairs := [(1,0),(2,1),(4,0)], upper := (rows 7 42 261 73 146 48 224 224 480), lower := (rows 7 42 261 73 146 48 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 9 16 48 114 178 306), good := (rows 461 488 269 77 496 496 64 128 256) }] }

theorem u13468 : Upper (D 7) (R 7) [6,40,257,65,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13468 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13469 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 405, targets := 64 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,6)], upper := (rows 7 42 261 73 146 96 240 176 432), lower := (rows 7 42 261 73 146 96 64 128 256), losses := [] }

theorem u13469 : Upper (D 7) (R 7) [6,40,257,65,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13469 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13470 : Route 9 := (fun mask => (mask,id))

def c13470 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13470 : Upper (D 7) (R 7) [6,40,257,65,130,128] 13 := by
  apply FastRouting.sound _ _ [6,40,257,65,130,128] 13 (by decide) (choices 1) [16,32] r13470 c13470
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1947
  · exact u1948

def b13471 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 178, targets := 1 },{ cop := 3, region := 34, targets := 192 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 7 42 261 73 176 34 208 208 464), lower := (rows 7 42 261 73 176 34 64 128 256), losses := [] }

theorem u13471 : Upper (D 7) (R 7) [6,40,257,65,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13471 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13472 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 42 261 73 176 48 194 194 450), lower := (rows 7 42 261 73 176 48 64 128 256), losses := [] }

theorem u13472 : Upper (D 7) (R 7) [6,40,257,65,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13472 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13473 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 405, targets := 64 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,6)], upper := (rows 7 42 261 73 176 96 210 146 402), lower := (rows 7 42 261 73 176 96 64 128 256), losses := [] }

theorem u13473 : Upper (D 7) (R 7) [6,40,257,65,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13473 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13474 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 42 261 73 176 160 82 210 338), lower := (rows 7 42 261 73 176 160 64 128 256), losses := [] }

theorem u13474 : Upper (D 7) (R 7) [6,40,257,65,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13474 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13475 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 178, targets := 1 },{ cop := 3, region := 34, targets := 192 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 7 42 261 73 208 34 240 176 432), lower := (rows 7 42 261 73 208 34 64 128 256), losses := [] }

theorem u13475 : Upper (D 7) (R 7) [6,40,257,65,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13475 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13476 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 389, targets := 64 },{ cop := 3, region := 178, targets := 1 }], pairs := [(0,6),(1,0),(2,6)], upper := (rows 7 42 261 73 208 48 226 162 418), lower := (rows 7 42 261 73 208 48 64 128 256), losses := [] }

theorem u13476 : Upper (D 7) (R 7) [6,40,257,65,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13476 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13477 : Route 9 := (fun mask => (mask,id))

def c13477 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13477 : Upper (D 7) (R 7) [6,40,257,65,192,128] 13 := by
  apply FastRouting.sound _ _ [6,40,257,65,192,128] 13 (by decide) (choices 1) [2,16,32] r13477 c13477
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1949
  · exact u1950
  · exact u1951

def b13478 : PairBound 9 := { available := 208, camps := [{ cop := 5, region := 218, targets := 1 },{ cop := 0, region := 500, targets := 2 }], pairs := [(1,0),(2,1),(3,0),(4,0)], upper := (rows 7 42 261 74 176 33 208 208 464), lower := (rows 7 42 261 74 176 33 64 128 256), losses := [] }

theorem u13478 : Upper (D 7) (R 7) [6,40,257,66,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13478 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13479 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 42 261 74 176 48 193 193 449), lower := (rows 7 42 261 74 176 48 64 128 256), losses := [] }

theorem u13479 : Upper (D 7) (R 7) [6,40,257,66,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13479 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13480 : PairBound 9 := { available := 145, camps := [{ cop := 5, region := 10, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 7 42 261 74 176 96 209 145 401), lower := (rows 7 42 261 74 176 96 64 128 256), losses := [] }

theorem u13480 : Upper (D 7) (R 7) [6,40,257,66,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13480 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13481 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 42 261 74 176 160 81 209 337), lower := (rows 7 42 261 74 176 160 64 128 256), losses := [] }

theorem u13481 : Upper (D 7) (R 7) [6,40,257,66,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13481 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13482 : PairBound 9 := { available := 176, camps := [{ cop := 5, region := 218, targets := 1 },{ cop := 0, region := 500, targets := 2 }], pairs := [(1,0),(2,1),(3,0),(4,0)], upper := (rows 7 42 261 74 208 33 240 176 432), lower := (rows 7 42 261 74 208 33 64 128 256), losses := [] }

theorem u13482 : Upper (D 7) (R 7) [6,40,257,66,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13482 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13483 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 42, targets := 129 }], pairs := [(1,0),(1,7),(3,0)], upper := (rows 7 42 261 74 208 48 225 161 417), lower := (rows 7 42 261 74 208 48 64 128 256), losses := [] }

theorem u13483 : Upper (D 7) (R 7) [6,40,257,66,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13483 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13484 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 4, region := 42, targets := 1 }], pairs := [(1,0),(2,1),(3,0),(4,1)], upper := (rows 7 42 261 74 208 160 113 177 305), lower := (rows 7 42 261 74 208 160 64 128 256), losses := [] }

theorem u13484 : Upper (D 7) (R 7) [6,40,257,66,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13484 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13485 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 34, targets := 192 },{ cop := 4, region := 106, targets := 1 }], pairs := [(1,0),(1,6),(1,7),(3,0)], upper := (rows 7 42 261 88 145 34 224 224 480), lower := (rows 7 42 261 88 145 34 64 128 256), losses := [] }

theorem u13485 : Upper (D 7) (R 7) [6,40,257,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13485 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13486 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 405, targets := 64 },{ cop := 4, region := 106, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,6)], upper := (rows 7 42 261 88 145 96 226 162 418), lower := (rows 7 42 261 88 145 96 64 128 256), losses := [] }

theorem u13486 : Upper (D 7) (R 7) [6,40,257,80,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13486 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13487 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 325, targets := 128 },{ cop := 4, region := 106, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,0)], upper := (rows 7 42 261 88 145 160 98 226 354), lower := (rows 7 42 261 88 145 160 64 128 256), losses := [] }

theorem u13487 : Upper (D 7) (R 7) [6,40,257,80,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13487 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13488 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 218, targets := 1 },{ cop := 0, region := 484, targets := 2 }], pairs := [(1,0),(2,1),(3,0),(4,0)], upper := (rows 7 42 261 88 146 33 224 224 480), lower := (rows 7 42 261 88 146 33 64 128 256), losses := [] }

theorem u13488 : Upper (D 7) (R 7) [6,40,257,80,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13488 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13489 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 405, targets := 64 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,6)], upper := (rows 7 42 261 88 146 96 225 161 417), lower := (rows 7 42 261 88 146 96 64 128 256), losses := [] }

theorem u13489 : Upper (D 7) (R 7) [6,40,257,80,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13489 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13490 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 325, targets := 128 },{ cop := 0, region := 484, targets := 2 }], pairs := [(0,7),(1,0),(2,1),(2,7)], upper := (rows 7 42 261 88 146 160 97 225 353), lower := (rows 7 42 261 88 146 160 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 176 64 128 256), good := (rows 6 42 260 122 178 160 64 160 256) }] }

theorem u13490 : Upper (D 7) (R 7) [6,40,257,80,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13490 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13491 : PairBound 9 := { available := 194, camps := [{ cop := 5, region := 218, targets := 1 },{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(1,0),(3,0),(4,0)], upper := (rows 7 42 261 88 176 33 194 194 450), lower := (rows 7 42 261 88 176 33 64 128 256), losses := [] }

theorem u13491 : Upper (D 7) (R 7) [6,40,257,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13491 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13492 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 34, targets := 193 },{ cop := 0, region := 452, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(2,1)], upper := (rows 7 42 261 88 176 34 193 193 449), lower := (rows 7 42 261 88 176 34 64 128 256), losses := [] }

theorem u13492 : Upper (D 7) (R 7) [6,40,257,80,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13492 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13493 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 405, targets := 64 },{ cop := 1, region := 389, targets := 32 }], pairs := [(0,5),(0,6),(2,6),(4,6)], upper := (rows 7 42 261 88 176 96 195 131 387), lower := (rows 7 42 261 88 176 96 64 128 256), losses := [] }

theorem u13493 : Upper (D 7) (R 7) [6,40,257,80,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13493 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13494 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 42 261 88 176 160 67 195 323), lower := (rows 7 42 261 88 176 160 64 128 256), losses := [] }

theorem u13494 : Upper (D 7) (R 7) [6,40,257,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13494 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13495 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,5)], upper := (rows 7 42 261 200 49 34 208 208 464), lower := (rows 7 42 261 200 49 34 64 128 256), losses := [] }

theorem u13495 : Upper (D 7) (R 7) [6,40,257,192,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13495 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13496 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 48, targets := 194 }], pairs := [(4,1),(4,6),(4,7)], upper := (rows 7 42 261 200 49 48 194 194 450), lower := (rows 7 42 261 200 49 48 64 128 256), losses := [] }

theorem u13496 : Upper (D 7) (R 7) [6,40,257,192,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13496 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13497 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 405, targets := 64 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,6)], upper := (rows 7 42 261 200 49 96 210 146 402), lower := (rows 7 42 261 200 49 96 64 128 256), losses := [] }

theorem u13497 : Upper (D 7) (R 7) [6,40,257,192,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13497 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13498 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 34, targets := 193 },{ cop := 4, region := 170, targets := 1 }], pairs := [(1,0),(1,6),(1,7),(3,0)], upper := (rows 7 42 261 200 81 34 240 176 432), lower := (rows 7 42 261 200 81 34 64 128 256), losses := [] }

theorem u13498 : Upper (D 7) (R 7) [6,40,257,192,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13498 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13499 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 389, targets := 64 },{ cop := 4, region := 170, targets := 1 }], pairs := [(0,6),(1,0),(2,6)], upper := (rows 7 42 261 200 81 48 226 162 418), lower := (rows 7 42 261 200 81 48 64 128 256), losses := [] }

theorem u13499 : Upper (D 7) (R 7) [6,40,257,192,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13499 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u13499
end Delivery.IrregularNine14.P07

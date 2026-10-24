import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0129
import IrregularNine14P07C0130

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b23940 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 33, targets := 66 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 76 392 146 33 83 147 275), lower := (rows 37 98 76 392 146 33 64 128 256), losses := [] }

theorem u23940 : Upper (D 7) (R 7) [36,96,72,384,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23940 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23941 : Route 9 := (fun mask => (mask,id))

def c23941 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23941 : Upper (D 7) (R 7) [36,96,72,384,130,2] 13 := by
  apply FastRouting.sound _ _ [36,96,72,384,130,2] 13 (by decide) (choices 1) [1,16] r23941 c23941
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7799
  · exact u7800

def r23942 : Route 9 := (fun mask => (mask,id))

def c23942 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23942 : Upper (D 7) (R 7) [36,96,72,384,130,16] 13 := by
  apply FastRouting.sound _ _ [36,96,72,384,130,16] 13 (by decide) (choices 1) [1,2] r23942 c23942
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7801
  · exact u7802

def b23943 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 452, targets := 34 },{ cop := 3, region := 498, targets := 1 }], pairs := [(1,0),(2,1),(2,5),(4,0)], upper := (rows 37 98 133 25 26 34 448 448 448), lower := (rows 37 98 133 25 26 34 64 128 256), losses := [] }

theorem u23943 : Upper (D 7) (R 7) [36,96,129,17,10,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23943 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23944 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 133 25 26 96 450 386 386), lower := (rows 37 98 133 25 26 96 64 128 256), losses := [] }

theorem u23944 : Upper (D 7) (R 7) [36,96,129,17,10,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23944 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23945 : PairBound 9 := { available := 322, camps := [{ cop := 5, region := 5, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 98 133 25 26 160 322 450 322), lower := (rows 37 98 133 25 26 160 64 128 256), losses := [] }

theorem u23945 : Upper (D 7) (R 7) [36,96,129,17,10,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23945 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23946 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 498, targets := 1 }], pairs := [(1,0),(2,5),(4,0)], upper := (rows 37 98 133 25 26 288 194 194 450), lower := (rows 37 98 133 25 26 288 64 128 256), losses := [{ target := 5, region := (rows 1 2 12 8 16 0 82 146 274), good := (rows 5 450 133 477 478 256 64 128 256) }] }

theorem u23946 : Upper (D 7) (R 7) [36,96,129,17,10,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23946 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23947 : PairBound 9 := { available := 328, camps := [{ cop := 4, region := 45, targets := 64 },{ cop := 3, region := 354, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,6)], upper := (rows 37 98 133 25 146 34 328 456 328), lower := (rows 37 98 133 25 146 34 64 128 256), losses := [] }

theorem u23947 : Upper (D 7) (R 7) [36,96,129,17,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23947 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23948 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 45, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 37 98 133 25 146 40 322 450 322), lower := (rows 37 98 133 25 146 40 64 128 256), losses := [] }

theorem u23948 : Upper (D 7) (R 7) [36,96,129,17,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23948 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23949 : PairBound 9 := { available := 266, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 133 25 146 96 330 394 266), lower := (rows 37 98 133 25 146 96 64 128 256), losses := [] }

theorem u23949 : Upper (D 7) (R 7) [36,96,129,17,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23949 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23950 : PairBound 9 := { available := 74, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 3, region := 354, targets := 128 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 37 98 133 25 146 288 74 202 330), lower := (rows 37 98 133 25 146 288 64 128 256), losses := [] }

theorem u23950 : Upper (D 7) (R 7) [36,96,129,17,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23950 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23951 : Route 9 := (fun mask => (mask,id))

def c23951 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u23951 : Upper (D 7) (R 7) [36,96,129,17,192,2] 13 := by
  apply FastRouting.sound _ _ [36,96,129,17,192,2] 13 (by decide) (choices 1) [2,8,256] r23951 c23951
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7803
  · exact u7804
  · exact u7805

def b23952 : PairBound 9 := { available := 258, camps := [{ cop := 4, region := 45, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 37 98 133 25 208 40 322 386 258), lower := (rows 37 98 133 25 208 40 64 128 256), losses := [] }

theorem u23952 : Upper (D 7) (R 7) [36,96,129,17,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23952 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23953 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 3, region := 354, targets := 128 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 37 98 133 25 208 288 74 138 266), lower := (rows 37 98 133 25 208 288 64 128 256), losses := [] }

theorem u23953 : Upper (D 7) (R 7) [36,96,129,17,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23953 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23954 : PairBound 9 := { available := 200, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 3, region := 196, targets := 34 }], pairs := [(1,0),(2,1),(2,5),(4,0)], upper := (rows 37 98 133 25 274 34 200 200 456), lower := (rows 37 98 133 25 274 34 64 128 256), losses := [] }

theorem u23954 : Upper (D 7) (R 7) [36,96,129,17,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23954 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23955 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 466, targets := 1 },{ cop := 1, region := 400, targets := 32 }], pairs := [(1,0),(4,0),(4,5)], upper := (rows 37 98 133 25 274 40 194 194 450), lower := (rows 37 98 133 25 274 40 64 128 256), losses := [] }

theorem u23955 : Upper (D 7) (R 7) [36,96,129,17,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23955 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23956 : PairBound 9 := { available := 138, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 133 25 274 96 202 138 394), lower := (rows 37 98 133 25 274 96 64 128 256), losses := [] }

theorem u23956 : Upper (D 7) (R 7) [36,96,129,17,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23956 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23957 : PairBound 9 := { available := 74, camps := [{ cop := 5, region := 5, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 98 133 25 274 160 74 202 330), lower := (rows 37 98 133 25 274 160 64 128 256), losses := [] }

theorem u23957 : Upper (D 7) (R 7) [36,96,129,17,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23957 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23958 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 6, region := 34, targets := 128 }], pairs := [(1,0),(1,7),(2,5),(4,0)], upper := (rows 37 98 133 25 280 34 194 194 450), lower := (rows 37 98 133 25 280 34 64 128 256), losses := [{ target := 5, region := (rows 1 2 5 13 17 0 98 162 290), good := (rows 477 450 157 29 280 450 64 128 256) }] }

theorem u23958 : Upper (D 7) (R 7) [36,96,129,17,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23958 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23959 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 133 25 280 96 194 130 386), lower := (rows 37 98 133 25 280 96 64 128 256), losses := [] }

theorem u23959 : Upper (D 7) (R 7) [36,96,129,17,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23959 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23960 : PairBound 9 := { available := 66, camps := [{ cop := 5, region := 5, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 98 133 25 280 160 66 194 322), lower := (rows 37 98 133 25 280 160 64 128 256), losses := [] }

theorem u23960 : Upper (D 7) (R 7) [36,96,129,17,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23960 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23961 : Route 9 := (fun mask => (mask,id))

def c23961 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23961 : Upper (D 7) (R 7) [36,96,129,17,320,2] 13 := by
  apply FastRouting.sound _ _ [36,96,129,17,320,2] 13 (by decide) (choices 1) [2,8,128] r23961 c23961
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7806
  · exact u7807
  · exact u7808

def b23962 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 466, targets := 1 },{ cop := 1, region := 133, targets := 64 }], pairs := [(0,6),(1,0),(4,0)], upper := (rows 37 98 133 25 336 40 194 130 386), lower := (rows 37 98 133 25 336 40 64 128 256), losses := [] }

theorem u23962 : Upper (D 7) (R 7) [36,96,129,17,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23962 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23963 : PairBound 9 := { available := 10, camps := [{ cop := 5, region := 5, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 98 133 25 336 160 74 138 266), lower := (rows 37 98 133 25 336 160 64 128 256), losses := [] }

theorem u23963 : Upper (D 7) (R 7) [36,96,129,17,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23963 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23964 : Route 9 := (fun mask => (mask,id))

def c23964 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23964 : Upper (D 7) (R 7) [36,96,129,17,384,2] 13 := by
  apply FastRouting.sound _ _ [36,96,129,17,384,2] 13 (by decide) (choices 1) [2,8] r23964 c23964
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7809
  · exact u7810

def b23965 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 45, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 37 98 133 25 400 40 66 194 322), lower := (rows 37 98 133 25 400 40 64 128 256), losses := [] }

theorem u23965 : Upper (D 7) (R 7) [36,96,129,17,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23965 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23966 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 133 25 400 96 74 138 266), lower := (rows 37 98 133 25 400 96 64 128 256), losses := [] }

theorem u23966 : Upper (D 7) (R 7) [36,96,129,17,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23966 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23967 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 408, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 98 133 26 152 33 322 450 322), lower := (rows 37 98 133 26 152 33 64 128 256), losses := [] }

theorem u23967 : Upper (D 7) (R 7) [36,96,129,18,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23967 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23968 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 452, targets := 34 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,7),(2,1),(2,5)], upper := (rows 37 98 133 26 152 34 321 449 321), lower := (rows 37 98 133 26 152 34 64 128 256), losses := [] }

theorem u23968 : Upper (D 7) (R 7) [36,96,129,18,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23968 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23969 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 133 26 152 96 323 387 259), lower := (rows 37 98 133 26 152 96 64 128 256), losses := [] }

theorem u23969 : Upper (D 7) (R 7) [36,96,129,18,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23969 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23970 : Route 9 := (fun mask => (mask,id))

def c23970 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23970 : Upper (D 7) (R 7) [36,96,129,18,136,256] 13 := by
  apply FastRouting.sound _ _ [36,96,129,18,136,256] 13 (by decide) (choices 1) [1,2] r23970 c23970
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7811
  · exact u7812

def b23971 : PairBound 9 := { available := 266, camps := [{ cop := 1, region := 408, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 98 133 26 208 33 330 394 266), lower := (rows 37 98 133 26 208 33 64 128 256), losses := [] }

theorem u23971 : Upper (D 7) (R 7) [36,96,129,18,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23971 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23972 : PairBound 9 := { available := 265, camps := [{ cop := 4, region := 42, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 37 98 133 26 208 34 329 393 265), lower := (rows 37 98 133 26 208 34 64 128 256), losses := [] }

theorem u23972 : Upper (D 7) (R 7) [36,96,129,18,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23972 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23973 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 42, targets := 129 }], pairs := [(1,0),(1,7),(3,0)], upper := (rows 37 98 133 26 208 40 323 387 259), lower := (rows 37 98 133 26 208 40 64 128 256), losses := [] }

theorem u23973 : Upper (D 7) (R 7) [36,96,129,18,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23973 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23974 : Route 9 := (fun mask => (mask,id))

def c23974 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23974 : Upper (D 7) (R 7) [36,96,129,18,192,256] 13 := by
  apply FastRouting.sound _ _ [36,96,129,18,192,256] 13 (by decide) (choices 1) [1,2,8] r23974 c23974
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7813
  · exact u7814
  · exact u7815

def r23975 : Route 9 := (fun mask => (mask,id))

def c23975 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23975 : Upper (D 7) (R 7) [36,96,129,18,257,2] 13 := by
  apply FastRouting.sound _ _ [36,96,129,18,257,2] 13 (by decide) (choices 1) [8,128] r23975 c23975
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7816
  · exact u7817

def r23976 : Route 9 := (fun mask => (mask,id))

def c23976 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23976 : Upper (D 7) (R 7) [36,96,129,18,257,8] 13 := by
  apply FastRouting.sound _ _ [36,96,129,18,257,8] 13 (by decide) (choices 1) [2,128] r23976 c23976
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7818
  · exact u7819

def b23977 : PairBound 9 := { available := 138, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 133 26 273 96 202 138 394), lower := (rows 37 98 133 26 273 96 64 128 256), losses := [] }

theorem u23977 : Upper (D 7) (R 7) [36,96,129,18,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23977 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23978 : PairBound 9 := { available := 74, camps := [{ cop := 5, region := 5, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 98 133 26 273 160 74 202 330), lower := (rows 37 98 133 26 273 160 64 128 256), losses := [] }

theorem u23978 : Upper (D 7) (R 7) [36,96,129,18,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23978 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23979 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 408, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 98 133 26 280 33 194 194 450), lower := (rows 37 98 133 26 280 33 64 128 256), losses := [] }

theorem u23979 : Upper (D 7) (R 7) [36,96,129,18,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23979 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23980 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 196, targets := 34 },{ cop := 6, region := 34, targets := 129 }], pairs := [(1,0),(1,7),(2,1),(2,5)], upper := (rows 37 98 133 26 280 34 193 193 449), lower := (rows 37 98 133 26 280 34 64 128 256), losses := [] }

theorem u23980 : Upper (D 7) (R 7) [36,96,129,18,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23980 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23981 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 133 26 280 96 195 131 387), lower := (rows 37 98 133 26 280 96 64 128 256), losses := [] }

theorem u23981 : Upper (D 7) (R 7) [36,96,129,18,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23981 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23982 : PairBound 9 := { available := 67, camps := [{ cop := 5, region := 5, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 98 133 26 280 160 67 195 323), lower := (rows 37 98 133 26 280 160 64 128 256), losses := [] }

theorem u23982 : Upper (D 7) (R 7) [36,96,129,18,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23982 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23983 : PairBound 9 := { available := 138, camps := [{ cop := 1, region := 408, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 98 133 26 336 33 202 138 394), lower := (rows 37 98 133 26 336 33 64 128 256), losses := [] }

theorem u23983 : Upper (D 7) (R 7) [36,96,129,18,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23983 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23984 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 42, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 37 98 133 26 336 34 201 137 393), lower := (rows 37 98 133 26 336 34 64 128 256), losses := [] }

theorem u23984 : Upper (D 7) (R 7) [36,96,129,18,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23984 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23985 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 42, targets := 129 }], pairs := [(1,0),(1,7),(3,0)], upper := (rows 37 98 133 26 336 40 195 131 387), lower := (rows 37 98 133 26 336 40 64 128 256), losses := [] }

theorem u23985 : Upper (D 7) (R 7) [36,96,129,18,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23985 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23986 : PairBound 9 := { available := 11, camps := [{ cop := 5, region := 5, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 98 133 26 336 160 75 139 267), lower := (rows 37 98 133 26 336 160 64 128 256), losses := [] }

theorem u23986 : Upper (D 7) (R 7) [36,96,129,18,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23986 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23987 : PairBound 9 := { available := 74, camps := [{ cop := 1, region := 408, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 98 133 26 400 33 74 202 330), lower := (rows 37 98 133 26 400 33 64 128 256), losses := [] }

theorem u23987 : Upper (D 7) (R 7) [36,96,129,18,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23987 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23988 : Route 9 := (fun mask => (mask,id))

def c23988 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23988 : Upper (D 7) (R 7) [36,96,129,18,384,2] 13 := by
  apply FastRouting.sound _ _ [36,96,129,18,384,2] 13 (by decide) (choices 1) [1,8] r23988 c23988
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7820
  · exact u7821

def r23989 : Route 9 := (fun mask => (mask,id))

def c23989 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23989 : Upper (D 7) (R 7) [36,96,129,18,384,8] 13 := by
  apply FastRouting.sound _ _ [36,96,129,18,384,8] 13 (by decide) (choices 1) [1,2] r23989 c23989
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7822
  · exact u7823

def b23990 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 133 26 400 96 75 139 267), lower := (rows 37 98 133 26 400 96 64 128 256), losses := [] }

theorem u23990 : Upper (D 7) (R 7) [36,96,129,18,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23990 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23991 : PairBound 9 := { available := 280, camps := [{ cop := 3, region := 434, targets := 1 },{ cop := 4, region := 37, targets := 64 }], pairs := [(0,6),(1,0),(2,6),(4,0)], upper := (rows 37 98 133 73 146 34 344 408 280), lower := (rows 37 98 133 73 146 34 64 128 256), losses := [] }

theorem u23991 : Upper (D 7) (R 7) [36,96,129,65,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23991 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23992 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 37 98 133 73 146 40 338 402 274), lower := (rows 37 98 133 73 146 40 64 128 256), losses := [] }

theorem u23992 : Upper (D 7) (R 7) [36,96,129,65,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23992 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23993 : PairBound 9 := { available := 266, camps := [{ cop := 4, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 37 98 133 73 146 48 330 394 266), lower := (rows 37 98 133 73 146 48 64 128 256), losses := [] }

theorem u23993 : Upper (D 7) (R 7) [36,96,129,65,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23993 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23994 : Route 9 := (fun mask => (mask,id))

def c23994 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23994 : Upper (D 7) (R 7) [36,96,129,65,130,256] 13 := by
  apply FastRouting.sound _ _ [36,96,129,65,130,256] 13 (by decide) (choices 1) [2,8,16] r23994 c23994
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7824
  · exact u7825
  · exact u7826

def r23995 : Route 9 := (fun mask => (mask,id))

def c23995 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u23995 : Upper (D 7) (R 7) [36,96,129,65,136,2] 13 := by
  apply FastRouting.sound _ _ [36,96,129,65,136,2] 13 (by decide) (choices 1) [2,16,256] r23995 c23995
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7827
  · exact u7828
  · exact u7829

def b23996 : PairBound 9 := { available := 258, camps := [{ cop := 4, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 37 98 133 73 152 48 322 386 258), lower := (rows 37 98 133 73 152 48 64 128 256), losses := [] }

theorem u23996 : Upper (D 7) (R 7) [36,96,129,65,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23996 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23997 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 434, targets := 1 },{ cop := 4, region := 354, targets := 128 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 37 98 133 73 152 288 82 146 274), lower := (rows 37 98 133 73 152 288 64 128 256), losses := [] }

theorem u23997 : Upper (D 7) (R 7) [36,96,129,65,136,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23997 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23998 : Route 9 := (fun mask => (mask,id))

def c23998 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23998 : Upper (D 7) (R 7) [36,96,129,65,258,2] 13 := by
  apply FastRouting.sound _ _ [36,96,129,65,258,2] 13 (by decide) (choices 1) [8,16,128] r23998 c23998
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7830
  · exact u7831
  · exact u7832

def b23999 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 37 98 133 73 274 40 210 146 402), lower := (rows 37 98 133 73 274 40 64 128 256), losses := [] }

theorem u23999 : Upper (D 7) (R 7) [36,96,129,65,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23999 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u23999
end Delivery.IrregularNine14.P07

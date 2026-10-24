import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0056
import IrregularNine14P06C0057

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b14940 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 2, region := 41, targets := 64 }], pairs := [(0,6),(2,5),(4,5)], upper := (rows 11 98 134 44 276 33 81 209 337), lower := (rows 11 98 134 44 276 33 64 128 256), losses := [] }

theorem u14940 : Upper (D 6) (R 6) [10,96,130,36,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14940 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14941 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 98 134 44 276 48 65 193 321), lower := (rows 11 98 134 44 276 48 64 128 256), losses := [] }

theorem u14941 : Upper (D 6) (R 6) [10,96,130,36,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14941 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14942 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 134 44 276 96 81 145 273), lower := (rows 11 98 134 44 276 96 64 128 256), losses := [] }

theorem u14942 : Upper (D 6) (R 6) [10,96,130,36,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14942 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14943 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 2, region := 41, targets := 64 }], pairs := [(0,6),(2,5),(4,5)], upper := (rows 11 98 134 44 336 33 85 149 277), lower := (rows 11 98 134 44 336 33 64 128 256), losses := [] }

theorem u14943 : Upper (D 6) (R 6) [10,96,130,36,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14943 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14944 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 339, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 98 134 44 336 36 81 145 273), lower := (rows 11 98 134 44 336 36 64 128 256), losses := [] }

theorem u14944 : Upper (D 6) (R 6) [10,96,130,36,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14944 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14945 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 141, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 11 98 134 44 336 48 69 133 261), lower := (rows 11 98 134 44 336 48 64 128 256), losses := [] }

theorem u14945 : Upper (D 6) (R 6) [10,96,130,36,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14945 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14946 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 40, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 11 98 134 56 273 33 68 196 324), lower := (rows 11 98 134 56 273 33 64 128 256), losses := [] }

theorem u14946 : Upper (D 6) (R 6) [10,96,130,48,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14946 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14947 : Route 9 := (fun mask => (mask,id))

def c14947 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14947 : Upper (D 6) (R 6) [10,96,130,48,257,4] 13 := by
  apply FastRouting.sound _ _ [10,96,130,48,257,4] 13 (by decide) (choices 1) [1,4] r14947 c14947
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3398
  · exact u3399

def b14948 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 134 56 273 96 69 133 261), lower := (rows 11 98 134 56 273 96 64 128 256), losses := [] }

theorem u14948 : Upper (D 6) (R 6) [10,96,130,48,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14948 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14949 : Route 9 := (fun mask => (mask,id))

def c14949 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14949 : Upper (D 6) (R 6) [10,96,130,48,260,1] 13 := by
  apply FastRouting.sound _ _ [10,96,130,48,260,1] 13 (by decide) (choices 1) [1,4] r14949 c14949
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3400
  · exact u3401

def b14950 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 98 134 56 276 36 65 193 321), lower := (rows 11 98 134 56 276 36 64 128 256), losses := [] }

theorem u14950 : Upper (D 6) (R 6) [10,96,130,48,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14950 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14951 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 134 56 276 96 69 133 261), lower := (rows 11 98 134 56 276 96 64 128 256), losses := [] }

theorem u14951 : Upper (D 6) (R 6) [10,96,130,48,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14951 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14952 : Route 9 := (fun mask => (mask,id))

def c14952 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14952 : Upper (D 6) (R 6) [10,96,130,257,33,4] 13 := by
  apply FastRouting.sound _ _ [10,96,130,257,33,4] 13 (by decide) (choices 1) [4,16] r14952 c14952
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3402
  · exact u3403

def b14953 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 48, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 98 134 265 49 48 68 196 324), lower := (rows 11 98 134 265 49 48 64 128 256), losses := [] }

theorem u14953 : Upper (D 6) (R 6) [10,96,130,257,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14953 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14954 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 134 265 49 96 84 148 276), lower := (rows 11 98 134 265 49 96 64 128 256), losses := [] }

theorem u14954 : Upper (D 6) (R 6) [10,96,130,257,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14954 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14955 : PairBound 9 := { available := 84, camps := [{ cop := 5, region := 214, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 98 134 265 52 33 84 212 340), lower := (rows 11 98 134 265 52 33 64 128 256), losses := [] }

theorem u14955 : Upper (D 6) (R 6) [10,96,130,257,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14955 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14956 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 98 134 265 52 36 81 209 337), lower := (rows 11 98 134 265 52 36 64 128 256), losses := [] }

theorem u14956 : Upper (D 6) (R 6) [10,96,130,257,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14956 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14957 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 397, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 98 134 265 52 48 69 197 325), lower := (rows 11 98 134 265 52 48 64 128 256), losses := [] }

theorem u14957 : Upper (D 6) (R 6) [10,96,130,257,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14957 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14958 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 134 265 52 96 85 149 277), lower := (rows 11 98 134 265 52 96 64 128 256), losses := [] }

theorem u14958 : Upper (D 6) (R 6) [10,96,130,257,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14958 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14959 : Route 9 := (fun mask => (mask,id))

def c14959 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14959 : Upper (D 6) (R 6) [10,96,130,260,5,1] 13 := by
  apply FastRouting.sound _ _ [10,96,130,260,5,1] 13 (by decide) (choices 1) [16,32] r14959 c14959
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3404
  · exact u3405

def b14960 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 360, targets := 2 },{ cop := 4, region := 98, targets := 4 }], pairs := [(1,2),(3,1)], upper := (rows 11 98 134 268 21 48 97 225 353), lower := (rows 11 98 134 268 21 48 64 128 256), losses := [] }

theorem u14960 : Upper (D 6) (R 6) [10,96,130,260,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14960 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14961 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 134 268 21 96 113 177 305), lower := (rows 11 98 134 268 21 96 64 128 256), losses := [] }

theorem u14961 : Upper (D 6) (R 6) [10,96,130,260,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14961 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14962 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 48, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 11 98 134 268 49 33 84 212 340), lower := (rows 11 98 134 268 49 33 64 128 256), losses := [] }

theorem u14962 : Upper (D 6) (R 6) [10,96,130,260,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14962 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14963 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 66, targets := 4 }], pairs := [(1,2),(4,1),(4,6)], upper := (rows 11 98 134 268 49 36 81 209 337), lower := (rows 11 98 134 268 49 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 44 81 145 273), good := (rows 505 96 164 300 497 36 64 128 256) },{ target := 6, region := (rows 1 2 4 8 17 44 0 128 256), good := (rows 59 34 166 300 49 36 0 128 256) }] }

theorem u14963 : Upper (D 6) (R 6) [10,96,130,260,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14963 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14964 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 48, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 98 134 268 49 48 69 197 325), lower := (rows 11 98 134 268 49 48 64 128 256), losses := [] }

theorem u14964 : Upper (D 6) (R 6) [10,96,130,260,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14964 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14965 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 134 268 49 96 85 149 277), lower := (rows 11 98 134 268 49 96 64 128 256), losses := [] }

theorem u14965 : Upper (D 6) (R 6) [10,96,130,260,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14965 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14966 : Route 9 := (fun mask => (mask,id))

def c14966 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14966 : Upper (D 6) (R 6) [10,96,130,260,36,1] 13 := by
  apply FastRouting.sound _ _ [10,96,130,260,36,1] 13 (by decide) (choices 1) [1,16] r14966 c14966
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3406
  · exact u3407

def b14967 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 397, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 98 134 268 52 48 65 193 321), lower := (rows 11 98 134 268 52 48 64 128 256), losses := [] }

theorem u14967 : Upper (D 6) (R 6) [10,96,130,260,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14967 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14968 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 134 268 52 96 81 145 273), lower := (rows 11 98 134 268 52 96 64 128 256), losses := [] }

theorem u14968 : Upper (D 6) (R 6) [10,96,130,260,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14968 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14969 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 198, targets := 1 },{ cop := 4, region := 360, targets := 2 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 11 98 134 280 21 33 100 228 356), lower := (rows 11 98 134 280 21 33 64 128 256), losses := [] }

theorem u14969 : Upper (D 6) (R 6) [10,96,130,272,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14969 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m14970_1 : Upper (D 6) (R 6) [10,96,130,272,5,4,1] 13 :=
  permutation_upper _ _ _ [10,96,130,272,5,1,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3408

def r14970 : Route 9 := (fun mask => (mask,id))

def c14970 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14970 : Upper (D 6) (R 6) [10,96,130,272,5,4] 13 := by
  apply FastRouting.sound _ _ [10,96,130,272,5,4] 13 (by decide) (choices 1) [1,32] r14970 c14970
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m14970_1
  · exact u3409

def b14971 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 134 280 21 96 101 165 293), lower := (rows 11 98 134 280 21 96 64 128 256), losses := [] }

theorem u14971 : Upper (D 6) (R 6) [10,96,130,272,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14971 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14972 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 48, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 11 98 134 280 49 33 68 196 324), lower := (rows 11 98 134 280 49 33 64 128 256), losses := [] }

theorem u14972 : Upper (D 6) (R 6) [10,96,130,272,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14972 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14973 : Route 9 := (fun mask => (mask,id))

def c14973 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14973 : Upper (D 6) (R 6) [10,96,130,272,33,4] 13 := by
  apply FastRouting.sound _ _ [10,96,130,272,33,4] 13 (by decide) (choices 1) [1,4] r14973 c14973
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3410
  · exact u3411

def b14974 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 134 280 49 96 69 133 261), lower := (rows 11 98 134 280 49 96 64 128 256), losses := [] }

theorem u14974 : Upper (D 6) (R 6) [10,96,130,272,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14974 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14975 : Route 9 := (fun mask => (mask,id))

def c14975 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14975 : Upper (D 6) (R 6) [10,96,130,272,36,1] 13 := by
  apply FastRouting.sound _ _ [10,96,130,272,36,1] 13 (by decide) (choices 1) [1,4] r14975 c14975
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3412
  · exact u3413

def b14976 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 98 134 280 52 36 65 193 321), lower := (rows 11 98 134 280 52 36 64 128 256), losses := [] }

theorem u14976 : Upper (D 6) (R 6) [10,96,130,272,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14976 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14977 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 134 280 52 96 69 133 261), lower := (rows 11 98 134 280 52 96 64 128 256), losses := [] }

theorem u14977 : Upper (D 6) (R 6) [10,96,130,272,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14977 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14978 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 212, targets := 32 },{ cop := 4, region := 34, targets := 4 }], pairs := [(1,2),(2,5),(4,5)], upper := (rows 11 98 134 296 81 33 84 148 276), lower := (rows 11 98 134 296 81 33 64 128 256), losses := [] }

theorem u14978 : Upper (D 6) (R 6) [10,96,130,288,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14978 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14979 : Route 9 := (fun mask => (mask,id))

def c14979 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14979 : Upper (D 6) (R 6) [10,96,130,288,65,4] 13 := by
  apply FastRouting.sound _ _ [10,96,130,288,65,4] 13 (by decide) (choices 1) [1,4,16] r14979 c14979
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3414
  · exact u3415
  · exact u3416

def b14980 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 11 98 134 296 81 48 69 133 261), lower := (rows 11 98 134 296 81 48 64 128 256), losses := [] }

theorem u14980 : Upper (D 6) (R 6) [10,96,130,288,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14980 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14981 : Route 9 := (fun mask => (mask,id))

def c14981 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14981 : Upper (D 6) (R 6) [10,96,130,288,68,1] 13 := by
  apply FastRouting.sound _ _ [10,96,130,288,68,1] 13 (by decide) (choices 1) [1,4,16] r14981 c14981
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3417
  · exact u3418
  · exact u3419

def b14982 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 212, targets := 32 },{ cop := 4, region := 34, targets := 1 }], pairs := [(1,0),(2,5),(4,5)], upper := (rows 11 98 134 296 84 36 81 145 273), lower := (rows 11 98 134 296 84 36 64 128 256), losses := [] }

theorem u14982 : Upper (D 6) (R 6) [10,96,130,288,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14982 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14983 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 11 98 134 296 84 48 69 133 261), lower := (rows 11 98 134 296 84 48 64 128 256), losses := [] }

theorem u14983 : Upper (D 6) (R 6) [10,96,130,288,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14983 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14984 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 11 98 148 13 49 34 324 452 324), lower := (rows 11 98 148 13 49 34 64 128 256), losses := [] }

theorem u14984 : Upper (D 6) (R 6) [10,96,144,5,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14984 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14985 : PairBound 9 := { available := 322, camps := [{ cop := 3, region := 48, targets := 66 },{ cop := 4, region := 322, targets := 1 }], pairs := [(1,0),(4,1),(4,6)], upper := (rows 11 98 148 13 49 36 322 450 322), lower := (rows 11 98 148 13 49 36 64 128 256), losses := [] }

theorem u14985 : Upper (D 6) (R 6) [10,96,144,5,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14985 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14986 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 148 13 49 96 326 390 262), lower := (rows 11 98 148 13 49 96 64 128 256), losses := [] }

theorem u14986 : Upper (D 6) (R 6) [10,96,144,5,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14986 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14987 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 198, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 98 148 13 49 288 70 198 326), lower := (rows 11 98 148 13 49 288 64 128 256), losses := [] }

theorem u14987 : Upper (D 6) (R 6) [10,96,144,5,33,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14987 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14988 : PairBound 9 := { available := 322, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 98 148 13 52 33 322 450 322), lower := (rows 11 98 148 13 52 33 64 128 256), losses := [] }

theorem u14988 : Upper (D 6) (R 6) [10,96,144,5,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14988 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14989 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 355, targets := 4 },{ cop := 6, region := 34, targets := 1 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 11 98 148 13 52 34 321 449 321), lower := (rows 11 98 148 13 52 34 64 128 256), losses := [] }

theorem u14989 : Upper (D 6) (R 6) [10,96,144,5,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14989 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14990 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 148 13 52 96 323 387 259), lower := (rows 11 98 148 13 52 96 64 128 256), losses := [] }

theorem u14990 : Upper (D 6) (R 6) [10,96,144,5,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14990 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14991 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 355, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 11 98 148 13 52 288 67 195 323), lower := (rows 11 98 148 13 52 288 64 128 256), losses := [] }

theorem u14991 : Upper (D 6) (R 6) [10,96,144,5,36,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14991 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14992 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 6, region := 34, targets := 4 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 11 98 148 13 273 34 100 228 356), lower := (rows 11 98 148 13 273 34 64 128 256), losses := [] }

theorem u14992 : Upper (D 6) (R 6) [10,96,144,5,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14992 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14993 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 5, region := 66, targets := 4 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 11 98 148 13 273 36 98 226 354), lower := (rows 11 98 148 13 273 36 64 128 256), losses := [] }

theorem u14993 : Upper (D 6) (R 6) [10,96,144,5,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14993 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14994 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 148 13 273 96 102 166 294), lower := (rows 11 98 148 13 273 96 64 128 256), losses := [] }

theorem u14994 : Upper (D 6) (R 6) [10,96,144,5,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14994 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14995 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 98 148 13 274 33 100 228 356), lower := (rows 11 98 148 13 274 33 64 128 256), losses := [] }

theorem u14995 : Upper (D 6) (R 6) [10,96,144,5,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14995 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m14996_1 : Upper (D 6) (R 6) [10,96,144,5,258,4,1] 13 :=
  permutation_upper _ _ _ [10,96,144,5,258,1,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3420

def r14996 : Route 9 := (fun mask => (mask,id))

def c14996 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14996 : Upper (D 6) (R 6) [10,96,144,5,258,4] 13 := by
  apply FastRouting.sound _ _ [10,96,144,5,258,4] 13 (by decide) (choices 1) [1,32] r14996 c14996
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m14996_1
  · exact u3421

def b14997 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 148 13 274 96 101 165 293), lower := (rows 11 98 148 13 274 96 64 128 256), losses := [] }

theorem u14997 : Upper (D 6) (R 6) [10,96,144,5,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14997 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14998 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 98 148 13 276 33 98 226 354), lower := (rows 11 98 148 13 276 33 64 128 256), losses := [] }

theorem u14998 : Upper (D 6) (R 6) [10,96,144,5,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14998 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14999 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 99, targets := 4 },{ cop := 6, region := 34, targets := 1 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 11 98 148 13 276 34 97 225 353), lower := (rows 11 98 148 13 276 34 64 128 256), losses := [] }

theorem u14999 : Upper (D 6) (R 6) [10,96,144,5,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14999 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u14999
end Delivery.IrregularNine14.P06

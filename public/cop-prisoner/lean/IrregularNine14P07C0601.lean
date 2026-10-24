import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0358
import IrregularNine14P07C0359

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r36060 : Route 9 := (fun mask => (mask,id))

def c36060 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36060 : Upper (D 7) (R 7) [34,260,192,18,72] 13 := by
  apply FastRouting.sound _ _ [34,260,192,18,72] 13 (by decide) (choices 1) [1,128] r36060 c36060
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u21531
  · exact u21532

def r36061 : Route 9 := (fun mask => (mask,id))

def c36061 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36061 : Upper (D 7) (R 7) [34,260,192,18,96] 13 := by
  apply FastRouting.sound _ _ [34,260,192,18,96] 13 (by decide) (choices 1) [1,8,128] r36061 c36061
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21533
  · exact u21534
  · exact u21535

def b36062 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 16, targets := 35 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,1),(4,5)], upper := (rows 35 262 196 26 208 41 105 169 297), lower := (rows 35 262 196 26 208 32 64 128 256), losses := [] }

theorem u36062 : Upper (D 7) (R 7) [34,260,192,18,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36062 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36063 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 35 262 196 41 81 186 218 154 410), lower := (rows 35 262 196 41 81 32 64 128 256), losses := [] }

theorem u36063 : Upper (D 7) (R 7) [34,260,192,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36063 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36064 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 35 262 196 41 82 185 217 153 409), lower := (rows 35 262 196 41 82 32 64 128 256), losses := [] }

theorem u36064 : Upper (D 7) (R 7) [34,260,192,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36064 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36065 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 35 262 196 41 88 179 211 147 403), lower := (rows 35 262 196 41 88 32 64 128 256), losses := [] }

theorem u36065 : Upper (D 7) (R 7) [34,260,192,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36065 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36066 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 8, targets := 192 },{ cop := 3, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 262 196 42 81 185 217 153 409), lower := (rows 35 262 196 42 81 32 64 128 256), losses := [] }

theorem u36066 : Upper (D 7) (R 7) [34,260,192,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36066 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36067 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 8, targets := 192 },{ cop := 3, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 262 196 42 88 177 209 145 401), lower := (rows 35 262 196 42 88 32 64 128 256), losses := [] }

theorem u36067 : Upper (D 7) (R 7) [34,260,192,34,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36067 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36068 : Route 9 := (fun mask => (mask,id))

def c36068 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36068 : Upper (D 7) (R 7) [34,260,192,48,65] 13 := by
  apply FastRouting.sound _ _ [34,260,192,48,65] 13 (by decide) (choices 1) [1,2,8,128] r36068 c36068
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21536
  · exact u21537
  · exact u21538
  · exact u21539

def r36069 : Route 9 := (fun mask => (mask,id))

def c36069 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36069 : Upper (D 7) (R 7) [34,260,192,48,66] 13 := by
  apply FastRouting.sound _ _ [34,260,192,48,66] 13 (by decide) (choices 1) [1,8,128] r36069 c36069
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21540
  · exact u21541
  · exact u21542

def b36070 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 2, region := 291, targets := 64 }], pairs := [(0,6),(1,5),(1,6),(2,5)], upper := (rows 35 262 196 56 88 163 195 131 387), lower := (rows 35 262 196 56 88 32 64 128 256), losses := [] }

theorem u36070 : Upper (D 7) (R 7) [34,260,192,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36070 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36071 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 16, targets := 35 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,1),(4,5)], upper := (rows 35 262 196 56 208 43 75 139 267), lower := (rows 35 262 196 56 208 32 64 128 256), losses := [] }

theorem u36071 : Upper (D 7) (R 7) [34,260,192,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36071 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m36072_16 : Upper (D 7) (R 7) [34,260,192,65,129,16] 13 :=
  permutation_upper _ _ _ [34,260,192,65,129,8] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u21544

def r36072 : Route 9 := (fun mask => (mask,id))

def c36072 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36072 : Upper (D 7) (R 7) [34,260,192,65,129] 13 := by
  apply FastRouting.sound _ _ [34,260,192,65,129] 13 (by decide) (choices 1) [2,8,16] r36072 c36072
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21543
  · exact u21544
  · exact m36072_16

def r36073 : Route 9 := (fun mask => (mask,id))

def c36073 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36073 : Upper (D 7) (R 7) [34,260,192,65,130] 13 := by
  apply FastRouting.sound _ _ [34,260,192,65,130] 13 (by decide) (choices 1) [1,8,16] r36073 c36073
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21545
  · exact u21546
  · exact u21547

def r36074 : Route 9 := (fun mask => (mask,id))

def c36074 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36074 : Upper (D 7) (R 7) [34,260,192,65,136] 13 := by
  apply FastRouting.sound _ _ [34,260,192,65,136] 13 (by decide) (choices 1) [1,2,16] r36074 c36074
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21548
  · exact u21549
  · exact u21550

def r36075 : Route 9 := (fun mask => (mask,id))

def c36075 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36075 : Upper (D 7) (R 7) [34,260,192,65,160] 13 := by
  apply FastRouting.sound _ _ [34,260,192,65,160] 13 (by decide) (choices 1) [1,2,8,16] r36075 c36075
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21551
  · exact u21552
  · exact u21553
  · exact u21554

def r36076 : Route 9 := (fun mask => (mask,id))

def c36076 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36076 : Upper (D 7) (R 7) [34,260,192,66,136] 13 := by
  apply FastRouting.sound _ _ [34,260,192,66,136] 13 (by decide) (choices 1) [1,16] r36076 c36076
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u21555
  · exact u21556

def r36077 : Route 9 := (fun mask => (mask,id))

def c36077 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36077 : Upper (D 7) (R 7) [34,260,192,66,160] 13 := by
  apply FastRouting.sound _ _ [34,260,192,66,160] 13 (by decide) (choices 1) [1,8,16] r36077 c36077
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21557
  · exact u21558
  · exact u21559

def b36078 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 24, targets := 35 }], pairs := [(3,0),(3,1),(3,5),(4,0)], upper := (rows 35 262 196 88 152 35 99 163 291), lower := (rows 35 262 196 88 152 32 64 128 256), losses := [] }

theorem u36078 : Upper (D 7) (R 7) [34,260,192,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36078 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36079 : Route 9 := (fun mask => (mask,id))

def c36079 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36079 : Upper (D 7) (R 7) [34,260,192,80,160] 13 := by
  apply FastRouting.sound _ _ [34,260,192,80,160] 13 (by decide) (choices 1) [1,2,8] r36079 c36079
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21560
  · exact u21561
  · exact u21562

def b36080 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 322 7 13 56 240 208 208 464), lower := (rows 35 322 7 13 56 32 64 128 256), losses := [] }

theorem u36080 : Upper (D 7) (R 7) [34,320,3,5,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36080 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36081 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 12, targets := 224 }], pairs := [(2,5),(2,6),(2,7),(3,5)], upper := (rows 35 322 7 13 88 176 240 176 432), lower := (rows 35 322 7 13 88 32 64 128 256), losses := [] }

theorem u36081 : Upper (D 7) (R 7) [34,320,3,5,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36081 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36082 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 12, targets := 224 }], pairs := [(2,5),(2,6),(2,7),(3,5)], upper := (rows 35 322 7 13 112 184 216 152 408), lower := (rows 35 322 7 13 112 32 64 128 256), losses := [] }

theorem u36082 : Upper (D 7) (R 7) [34,320,3,5,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36082 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36083 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 12, targets := 224 }], pairs := [(2,5),(2,6),(2,7),(3,5)], upper := (rows 35 322 7 13 152 240 240 240 496), lower := (rows 35 322 7 13 152 32 64 128 256), losses := [] }

theorem u36083 : Upper (D 7) (R 7) [34,320,3,5,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36083 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36084 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 12, targets := 224 }], pairs := [(2,5),(2,6),(2,7),(3,5)], upper := (rows 35 322 7 13 176 248 216 216 472), lower := (rows 35 322 7 13 176 32 64 128 256), losses := [] }

theorem u36084 : Upper (D 7) (R 7) [34,320,3,5,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36084 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36085 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 12, targets := 224 }], pairs := [(2,5),(2,6),(2,7),(3,5)], upper := (rows 35 322 7 13 208 184 248 184 440), lower := (rows 35 322 7 13 208 32 64 128 256), losses := [] }

theorem u36085 : Upper (D 7) (R 7) [34,320,3,5,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36085 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36086 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 28, targets := 224 }], pairs := [(2,5),(2,6),(2,7),(3,5)], upper := (rows 35 322 7 25 28 224 224 224 480), lower := (rows 35 322 7 25 28 32 64 128 256), losses := [] }

theorem u36086 : Upper (D 7) (R 7) [34,320,3,17,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36086 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36087 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 28, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 322 7 25 52 232 200 200 456), lower := (rows 35 322 7 25 52 32 64 128 256), losses := [] }

theorem u36087 : Upper (D 7) (R 7) [34,320,3,17,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36087 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36088 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 322 7 25 84 168 232 168 424), lower := (rows 35 322 7 25 84 32 64 128 256), losses := [] }

theorem u36088 : Upper (D 7) (R 7) [34,320,3,17,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36088 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36089 : PairBound 9 := { available := 164, camps := [{ cop := 0, region := 4, targets := 160 },{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6),(2,5),(2,6),(2,7)], upper := (rows 35 322 7 25 88 164 228 164 420), lower := (rows 35 322 7 25 88 32 64 128 256), losses := [] }

theorem u36089 : Upper (D 7) (R 7) [34,320,3,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36089 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36090 : PairBound 9 := { available := 140, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 322 7 25 112 172 204 140 396), lower := (rows 35 322 7 25 112 32 64 128 256), losses := [] }

theorem u36090 : Upper (D 7) (R 7) [34,320,3,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36090 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36091 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 322 7 25 148 232 232 232 488), lower := (rows 35 322 7 25 148 32 64 128 256), losses := [] }

theorem u36091 : Upper (D 7) (R 7) [34,320,3,17,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36091 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36092 : PairBound 9 := { available := 228, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 322 7 25 152 228 228 228 484), lower := (rows 35 322 7 25 152 32 64 128 256), losses := [] }

theorem u36092 : Upper (D 7) (R 7) [34,320,3,17,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36092 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36093 : PairBound 9 := { available := 204, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 322 7 25 176 236 204 204 460), lower := (rows 35 322 7 25 176 32 64 128 256), losses := [] }

theorem u36093 : Upper (D 7) (R 7) [34,320,3,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36093 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36094 : PairBound 9 := { available := 172, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 322 7 25 208 172 236 172 428), lower := (rows 35 322 7 25 208 32 64 128 256), losses := [] }

theorem u36094 : Upper (D 7) (R 7) [34,320,3,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36094 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36095 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 28, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 322 7 28 56 225 193 193 449), lower := (rows 35 322 7 28 56 32 64 128 256), losses := [] }

theorem u36095 : Upper (D 7) (R 7) [34,320,3,20,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36095 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36096 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 322 7 28 81 168 232 168 424), lower := (rows 35 322 7 28 81 32 64 128 256), losses := [] }

theorem u36096 : Upper (D 7) (R 7) [34,320,3,20,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36096 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36097 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 4, targets := 160 },{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6),(2,5),(2,6),(2,7)], upper := (rows 35 322 7 28 88 161 225 161 417), lower := (rows 35 322 7 28 88 32 64 128 256), losses := [] }

theorem u36097 : Upper (D 7) (R 7) [34,320,3,20,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36097 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36098 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 322 7 28 112 169 201 137 393), lower := (rows 35 322 7 28 112 32 64 128 256), losses := [] }

theorem u36098 : Upper (D 7) (R 7) [34,320,3,20,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36098 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36099 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 322 7 28 145 232 232 232 488), lower := (rows 35 322 7 28 145 32 64 128 256), losses := [] }

theorem u36099 : Upper (D 7) (R 7) [34,320,3,20,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36099 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36100 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 322 7 28 152 225 225 225 481), lower := (rows 35 322 7 28 152 32 64 128 256), losses := [] }

theorem u36100 : Upper (D 7) (R 7) [34,320,3,20,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36100 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36101 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 322 7 28 176 233 201 201 457), lower := (rows 35 322 7 28 176 32 64 128 256), losses := [] }

theorem u36101 : Upper (D 7) (R 7) [34,320,3,20,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36101 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36102 : PairBound 9 := { available := 169, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 322 7 28 208 169 233 169 425), lower := (rows 35 322 7 28 208 32 64 128 256), losses := [] }

theorem u36102 : Upper (D 7) (R 7) [34,320,3,20,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36102 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36103 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 322 7 44 81 184 216 152 408), lower := (rows 35 322 7 44 81 32 64 128 256), losses := [] }

theorem u36103 : Upper (D 7) (R 7) [34,320,3,36,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36103 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36104 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 322 7 44 88 177 209 145 401), lower := (rows 35 322 7 44 88 32 64 128 256), losses := [] }

theorem u36104 : Upper (D 7) (R 7) [34,320,3,36,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36104 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36105 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 322 7 44 145 248 216 216 472), lower := (rows 35 322 7 44 145 32 64 128 256), losses := [] }

theorem u36105 : Upper (D 7) (R 7) [34,320,3,36,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36105 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36106 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 322 7 44 152 241 209 209 465), lower := (rows 35 322 7 44 152 32 64 128 256), losses := [] }

theorem u36106 : Upper (D 7) (R 7) [34,320,3,36,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36106 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36107 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 322 7 44 208 185 217 153 409), lower := (rows 35 322 7 44 208 32 64 128 256), losses := [] }

theorem u36107 : Upper (D 7) (R 7) [34,320,3,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36107 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36108 : PairBound 9 := { available := 140, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 322 7 56 81 172 204 140 396), lower := (rows 35 322 7 56 81 32 64 128 256), losses := [] }

theorem u36108 : Upper (D 7) (R 7) [34,320,3,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36108 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36109 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 322 7 56 84 169 201 137 393), lower := (rows 35 322 7 56 84 32 64 128 256), losses := [] }

theorem u36109 : Upper (D 7) (R 7) [34,320,3,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36109 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36110 : PairBound 9 := { available := 204, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 322 7 56 145 236 204 204 460), lower := (rows 35 322 7 56 145 32 64 128 256), losses := [] }

theorem u36110 : Upper (D 7) (R 7) [34,320,3,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36110 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36111 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 322 7 56 148 233 201 201 457), lower := (rows 35 322 7 56 148 32 64 128 256), losses := [] }

theorem u36111 : Upper (D 7) (R 7) [34,320,3,48,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36111 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36112 : PairBound 9 := { available := 197, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 0, region := 4, targets := 192 }], pairs := [(1,5),(2,5),(2,6),(2,7)], upper := (rows 35 322 7 56 152 229 197 197 453), lower := (rows 35 322 7 56 152 32 64 128 256), losses := [] }

theorem u36112 : Upper (D 7) (R 7) [34,320,3,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36112 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36113 : PairBound 9 := { available := 141, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 322 7 56 208 173 205 141 397), lower := (rows 35 322 7 56 208 32 64 128 256), losses := [] }

theorem u36113 : Upper (D 7) (R 7) [34,320,3,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36113 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36114 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 322 7 73 148 184 248 184 440), lower := (rows 35 322 7 73 148 32 64 128 256), losses := [] }

theorem u36114 : Upper (D 7) (R 7) [34,320,3,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36114 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36115 : PairBound 9 := { available := 180, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 322 7 73 152 180 244 180 436), lower := (rows 35 322 7 73 152 32 64 128 256), losses := [] }

theorem u36115 : Upper (D 7) (R 7) [34,320,3,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36115 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36116 : PairBound 9 := { available := 156, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 322 7 73 176 188 220 156 412), lower := (rows 35 322 7 73 176 32 64 128 256), losses := [] }

theorem u36116 : Upper (D 7) (R 7) [34,320,3,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36116 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36117 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 322 7 76 145 184 248 184 440), lower := (rows 35 322 7 76 145 32 64 128 256), losses := [] }

theorem u36117 : Upper (D 7) (R 7) [34,320,3,68,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36117 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36118 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 322 7 76 152 177 241 177 433), lower := (rows 35 322 7 76 152 32 64 128 256), losses := [] }

theorem u36118 : Upper (D 7) (R 7) [34,320,3,68,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36118 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36119 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 322 7 76 176 185 217 153 409), lower := (rows 35 322 7 76 176 32 64 128 256), losses := [] }

theorem u36119 : Upper (D 7) (R 7) [34,320,3,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36119 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u36119
end Delivery.IrregularNine14.P07

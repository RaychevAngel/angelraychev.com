import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0026
import IrregularNine14P08C0027

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b8160 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 7 28 41 336 224 224 224 480), lower := (rows 35 7 28 41 336 32 64 128 256), losses := [] }

theorem u8160 : Upper (D 8) (R 8) [34,5,24,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8160 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8161 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 15, targets := 128 }], pairs := [(0,7)], upper := (rows 35 7 28 73 112 416 480 416 416), lower := (rows 35 7 28 73 112 32 64 128 256), losses := [] }

theorem u8161 : Upper (D 8) (R 8) [34,5,24,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8161 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8162 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 436, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 28 73 176 480 480 480 480), lower := (rows 35 7 28 73 176 32 64 128 256), losses := [] }

theorem u8162 : Upper (D 8) (R 8) [34,5,24,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8162 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8163 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 28 73 208 416 480 416 416), lower := (rows 35 7 28 73 208 32 64 128 256), losses := [] }

theorem u8163 : Upper (D 8) (R 8) [34,5,24,65,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8163 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8164 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 436, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 28 73 304 224 224 224 480), lower := (rows 35 7 28 73 304 32 64 128 256), losses := [] }

theorem u8164 : Upper (D 8) (R 8) [34,5,24,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8164 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8165 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 28 73 336 160 224 160 416), lower := (rows 35 7 28 73 336 32 64 128 256), losses := [] }

theorem u8165 : Upper (D 8) (R 8) [34,5,24,65,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8165 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8166 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 436, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 28 73 400 224 224 224 480), lower := (rows 35 7 28 73 400 32 64 128 256), losses := [] }

theorem u8166 : Upper (D 8) (R 8) [34,5,24,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8166 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8167 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 23, targets := 128 }], pairs := [(0,7)], upper := (rows 35 7 28 104 112 417 449 385 385), lower := (rows 35 7 28 104 112 32 64 128 256), losses := [] }

theorem u8167 : Upper (D 8) (R 8) [34,5,24,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8167 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m8168_128 : Upper (D 8) (R 8) [34,5,24,96,160,128] 13 :=
  permutation_upper _ _ _ [34,5,24,96,160,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1619

def r8168 : Route 9 := (fun mask => (mask,id))

def c8168 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u8168 : Upper (D 8) (R 8) [34,5,24,96,160] 13 := by
  apply FastRouting.sound _ _ [34,5,24,96,160] 13 (by decide) (choices 1) [1,64,128,256] r8168 c8168
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1618
  · exact u1619
  · exact m8168_128
  · exact u1620

def b8169 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 28 104 208 417 481 417 417), lower := (rows 35 7 28 104 208 32 64 128 256), losses := [] }

theorem u8169 : Upper (D 8) (R 8) [34,5,24,96,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8169 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8170 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 28 104 273 224 224 224 480), lower := (rows 35 7 28 104 273 32 64 128 256), losses := [] }

theorem u8170 : Upper (D 8) (R 8) [34,5,24,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8170 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8171 : Route 9 := (fun mask => (mask,id))

def c8171 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u8171 : Upper (D 8) (R 8) [34,5,24,96,288] 13 := by
  apply FastRouting.sound _ _ [34,5,24,96,288] 13 (by decide) (choices 1) [1,64,128] r8171 c8171
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1621
  · exact u1622
  · exact u1623

def b8172 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 28 104 336 161 225 161 417), lower := (rows 35 7 28 104 336 32 64 128 256), losses := [] }

theorem u8172 : Upper (D 8) (R 8) [34,5,24,96,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8172 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8173 : Route 9 := (fun mask => (mask,id))

def c8173 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u8173 : Upper (D 8) (R 8) [34,5,24,96,384] 13 := by
  apply FastRouting.sound _ _ [34,5,24,96,384] 13 (by decide) (choices 1) [1,64,128] r8173 c8173
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1624
  · exact u1625
  · exact u1626

def b8174 : PairBound 9 := { available := 289, camps := [{ cop := 3, region := 20, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 28 200 208 289 353 417 289), lower := (rows 35 7 28 200 208 32 64 128 256), losses := [] }

theorem u8174 : Upper (D 8) (R 8) [34,5,24,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8174 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8175 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 28 200 273 224 224 224 480), lower := (rows 35 7 28 200 273 32 64 128 256), losses := [] }

theorem u8175 : Upper (D 8) (R 8) [34,5,24,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8175 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8176 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8176 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u8176 : Upper (D 8) (R 8) [34,5,24,192,288] 13 := by
  apply FastRouting.sound _ _ [34,5,24,192,288] 13 (by decide) (choices 1) [1,64] r8176 c8176
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1627
  · exact u1628

def b8177 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 28 200 336 161 225 161 417), lower := (rows 35 7 28 200 336 32 64 128 256), losses := [] }

theorem u8177 : Upper (D 8) (R 8) [34,5,24,192,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8177 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8178 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 24, targets := 64 }], pairs := [(3,6)], upper := (rows 35 7 76 56 49 480 448 448 448), lower := (rows 35 7 76 56 49 32 64 128 256), losses := [] }

theorem u8178 : Upper (D 8) (R 8) [34,5,72,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8178 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8179 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 76 56 81 416 480 416 416), lower := (rows 35 7 76 56 81 32 64 128 256), losses := [] }

theorem u8179 : Upper (D 8) (R 8) [34,5,72,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8179 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8180 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 15, targets := 128 }], pairs := [(0,7)], upper := (rows 35 7 76 56 112 417 449 385 385), lower := (rows 35 7 76 56 112 32 64 128 256), losses := [] }

theorem u8180 : Upper (D 8) (R 8) [34,5,72,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8180 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8181 : PairBound 9 := { available := 480, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 76 56 145 480 480 480 480), lower := (rows 35 7 76 56 145 32 64 128 256), losses := [] }

theorem u8181 : Upper (D 8) (R 8) [34,5,72,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8181 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8182 : PairBound 9 := { available := 449, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 7 76 56 176 481 449 449 449), lower := (rows 35 7 76 56 176 32 64 128 256), losses := [] }

theorem u8182 : Upper (D 8) (R 8) [34,5,72,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8182 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8183 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 76 56 208 417 481 417 417), lower := (rows 35 7 76 56 208 32 64 128 256), losses := [] }

theorem u8183 : Upper (D 8) (R 8) [34,5,72,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8183 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8184 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 76 56 273 224 224 224 480), lower := (rows 35 7 76 56 273 32 64 128 256), losses := [] }

theorem u8184 : Upper (D 8) (R 8) [34,5,72,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8184 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8185 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 7 76 56 304 225 193 193 449), lower := (rows 35 7 76 56 304 32 64 128 256), losses := [] }

theorem u8185 : Upper (D 8) (R 8) [34,5,72,48,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8185 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8186 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 76 56 336 161 225 161 417), lower := (rows 35 7 76 56 336 32 64 128 256), losses := [] }

theorem u8186 : Upper (D 8) (R 8) [34,5,72,48,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8186 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8187 : Route 9 := (fun mask => (mask,id))

def c8187 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u8187 : Upper (D 8) (R 8) [34,5,72,48,384] 13 := by
  apply FastRouting.sound _ _ [34,5,72,48,384] 13 (by decide) (choices 1) [1,64,128] r8187 c8187
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1629
  · exact u1630
  · exact u1631

def b8188 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 35 7 76 152 49 480 480 480 480), lower := (rows 35 7 76 152 49 32 64 128 256), losses := [] }

theorem u8188 : Upper (D 8) (R 8) [34,5,72,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8188 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8189 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 76 152 81 416 480 416 416), lower := (rows 35 7 76 152 81 32 64 128 256), losses := [] }

theorem u8189 : Upper (D 8) (R 8) [34,5,72,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8189 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8190 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 76 152 112 417 481 417 417), lower := (rows 35 7 76 152 112 32 64 128 256), losses := [] }

theorem u8190 : Upper (D 8) (R 8) [34,5,72,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8190 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8191 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 7 76 152 145 352 352 480 352), lower := (rows 35 7 76 152 145 32 64 128 256), losses := [] }

theorem u8191 : Upper (D 8) (R 8) [34,5,72,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8191 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8192 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 7 76 152 176 353 353 481 353), lower := (rows 35 7 76 152 176 32 64 128 256), losses := [] }

theorem u8192 : Upper (D 8) (R 8) [34,5,72,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8192 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8193 : PairBound 9 := { available := 289, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 76 152 208 289 353 417 289), lower := (rows 35 7 76 152 208 32 64 128 256), losses := [] }

theorem u8193 : Upper (D 8) (R 8) [34,5,72,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8193 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8194 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 76 152 273 224 224 224 480), lower := (rows 35 7 76 152 273 32 64 128 256), losses := [] }

theorem u8194 : Upper (D 8) (R 8) [34,5,72,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8194 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8195 : Route 9 := (fun mask => (mask,id))

def c8195 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u8195 : Upper (D 8) (R 8) [34,5,72,144,288] 13 := by
  apply FastRouting.sound _ _ [34,5,72,144,288] 13 (by decide) (choices 1) [1,64,128] r8195 c8195
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1632
  · exact u1633
  · exact u1634

def b8196 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 76 152 336 161 225 161 417), lower := (rows 35 7 76 152 336 32 64 128 256), losses := [] }

theorem u8196 : Upper (D 8) (R 8) [34,5,72,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8196 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8197 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 103, targets := 128 }], pairs := [(0,7)], upper := (rows 35 7 76 152 400 97 97 225 353), lower := (rows 35 7 76 152 400 32 64 128 256), losses := [] }

theorem u8197 : Upper (D 8) (R 8) [34,5,72,144,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8197 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8198 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 35 7 76 168 49 496 464 464 464), lower := (rows 35 7 76 168 49 32 64 128 256), losses := [] }

theorem u8198 : Upper (D 8) (R 8) [34,5,72,160,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8198 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8199 : PairBound 9 := { available := 432, camps := [{ cop := 4, region := 428, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 76 168 81 432 496 432 432), lower := (rows 35 7 76 168 81 32 64 128 256), losses := [] }

theorem u8199 : Upper (D 8) (R 8) [34,5,72,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8199 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8200 : Route 9 := (fun mask => (mask,id))

def c8200 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u8200 : Upper (D 8) (R 8) [34,5,72,160,96] 13 := by
  apply FastRouting.sound _ _ [34,5,72,160,96] 13 (by decide) (choices 1) [1,16,128,256] r8200 c8200
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1635
  · exact u1636
  · exact u1637
  · exact u1638

def b8201 : PairBound 9 := { available := 368, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 76 168 145 368 368 496 368), lower := (rows 35 7 76 168 145 32 64 128 256), losses := [] }

theorem u8201 : Upper (D 8) (R 8) [34,5,72,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8201 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8202 : PairBound 9 := { available := 337, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 7 76 168 176 369 337 465 337), lower := (rows 35 7 76 168 176 32 64 128 256), losses := [] }

theorem u8202 : Upper (D 8) (R 8) [34,5,72,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8202 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8203 : Route 9 := (fun mask => (mask,id))

def c8203 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8203 : Upper (D 8) (R 8) [34,5,72,160,192] 13 := by
  apply FastRouting.sound _ _ [34,5,72,160,192] 13 (by decide) (choices 1) [1,16,256] r8203 c8203
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1639
  · exact u1640
  · exact u1641

def b8204 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 76 168 273 240 240 240 496), lower := (rows 35 7 76 168 273 32 64 128 256), losses := [] }

theorem u8204 : Upper (D 8) (R 8) [34,5,72,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8204 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8205 : Route 9 := (fun mask => (mask,id))

def c8205 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8205 : Upper (D 8) (R 8) [34,5,72,160,288] 13 := by
  apply FastRouting.sound _ _ [34,5,72,160,288] 13 (by decide) (choices 1) [1,16,64,128] r8205 c8205
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1642
  · exact u1643
  · exact u1644
  · exact u1645

def r8206 : Route 9 := (fun mask => (mask,id))

def c8206 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8206 : Upper (D 8) (R 8) [34,5,72,160,320] 13 := by
  apply FastRouting.sound _ _ [34,5,72,160,320] 13 (by decide) (choices 1) [1,16,128] r8206 c8206
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1646
  · exact u1647
  · exact u1648

def r8207 : Route 9 := (fun mask => (mask,id))

def c8207 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8207 : Upper (D 8) (R 8) [34,5,72,160,384] 13 := by
  apply FastRouting.sound _ _ [34,5,72,160,384] 13 (by decide) (choices 1) [1,16,64] r8207 c8207
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1649
  · exact u1650
  · exact u1651

def b8208 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 35 7 76 280 49 224 224 224 480), lower := (rows 35 7 76 280 49 32 64 128 256), losses := [] }

theorem u8208 : Upper (D 8) (R 8) [34,5,72,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8208 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8209 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 76 280 81 160 224 160 416), lower := (rows 35 7 76 280 81 32 64 128 256), losses := [] }

theorem u8209 : Upper (D 8) (R 8) [34,5,72,272,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8209 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8210 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 76 280 112 161 225 161 417), lower := (rows 35 7 76 280 112 32 64 128 256), losses := [] }

theorem u8210 : Upper (D 8) (R 8) [34,5,72,272,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8210 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8211 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 76 280 145 224 224 224 480), lower := (rows 35 7 76 280 145 32 64 128 256), losses := [] }

theorem u8211 : Upper (D 8) (R 8) [34,5,72,272,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8211 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8212 : Route 9 := (fun mask => (mask,id))

def c8212 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u8212 : Upper (D 8) (R 8) [34,5,72,272,160] 13 := by
  apply FastRouting.sound _ _ [34,5,72,272,160] 13 (by decide) (choices 1) [1,64,128] r8212 c8212
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1652
  · exact u1653
  · exact u1654

def b8213 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 76 280 208 161 225 161 417), lower := (rows 35 7 76 280 208 32 64 128 256), losses := [] }

theorem u8213 : Upper (D 8) (R 8) [34,5,72,272,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8213 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8214 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 35 7 76 296 49 240 208 208 464), lower := (rows 35 7 76 296 49 32 64 128 256), losses := [] }

theorem u8214 : Upper (D 8) (R 8) [34,5,72,288,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8214 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8215 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 428, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 76 296 81 176 240 176 432), lower := (rows 35 7 76 296 81 32 64 128 256), losses := [] }

theorem u8215 : Upper (D 8) (R 8) [34,5,72,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8215 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8216 : Route 9 := (fun mask => (mask,id))

def c8216 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8216 : Upper (D 8) (R 8) [34,5,72,288,96] 13 := by
  apply FastRouting.sound _ _ [34,5,72,288,96] 13 (by decide) (choices 1) [1,16,128] r8216 c8216
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1655
  · exact u1656
  · exact u1657

def b8217 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 76 296 145 240 240 240 496), lower := (rows 35 7 76 296 145 32 64 128 256), losses := [] }

theorem u8217 : Upper (D 8) (R 8) [34,5,72,288,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8217 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8218 : Route 9 := (fun mask => (mask,id))

def c8218 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8218 : Upper (D 8) (R 8) [34,5,72,288,160] 13 := by
  apply FastRouting.sound _ _ [34,5,72,288,160] 13 (by decide) (choices 1) [1,16,64,128] r8218 c8218
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1658
  · exact u1659
  · exact u1660
  · exact u1661

def r8219 : Route 9 := (fun mask => (mask,id))

def c8219 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8219 : Upper (D 8) (R 8) [34,5,72,288,192] 13 := by
  apply FastRouting.sound _ _ [34,5,72,288,192] 13 (by decide) (choices 1) [1,16,128] r8219 c8219
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1662
  · exact u1663
  · exact u1664

#print axioms u8219
end Delivery.IrregularNine14.P08

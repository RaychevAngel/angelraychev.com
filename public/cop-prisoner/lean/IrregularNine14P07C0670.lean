import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0478
import IrregularNine14P07C0479
import IrregularNine14P07C0480

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b40200 : PairBound 9 := { available := 216, camps := [{ cop := 2, region := 8, targets := 224 },{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5),(3,5),(3,6),(3,7)], upper := (rows 97 262 7 11 176 248 216 216 472), lower := (rows 97 262 7 11 176 32 64 128 256), losses := [] }

theorem u40200 : Upper (D 7) (R 7) [96,260,3,3,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40200 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40201 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 24, targets := 224 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 97 262 7 25 26 224 224 224 480), lower := (rows 97 262 7 25 26 32 64 128 256), losses := [] }

theorem u40201 : Upper (D 7) (R 7) [96,260,3,17,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40201 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40202 : PairBound 9 := { available := 200, camps := [{ cop := 3, region := 454, targets := 32 },{ cop := 4, region := 201, targets := 2 }], pairs := [(0,1),(1,5),(2,5),(3,1)], upper := (rows 97 262 7 25 50 232 200 200 456), lower := (rows 97 262 7 25 50 32 64 128 256), losses := [] }

theorem u40202 : Upper (D 7) (R 7) [96,260,3,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40202 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40203 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 24, targets := 194 }], pairs := [(3,1),(3,6),(3,7),(4,1)], upper := (rows 97 262 7 25 56 226 194 194 450), lower := (rows 97 262 7 25 56 32 64 128 256), losses := [] }

theorem u40203 : Upper (D 7) (R 7) [96,260,3,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40203 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40204 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 24, targets := 130 }], pairs := [(3,1),(3,7),(4,1),(4,7)], upper := (rows 97 262 7 25 112 170 202 138 394), lower := (rows 97 262 7 25 112 32 64 128 256), losses := [] }

theorem u40204 : Upper (D 7) (R 7) [96,260,3,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40204 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40205 : Route 9 := (fun mask => (mask,id))

def c40205 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40205 : Upper (D 7) (R 7) [96,260,3,17,130] 13 := by
  apply FastRouting.sound _ _ [96,260,3,17,130] 13 (by decide) (choices 1) [8,64,128] r40205 c40205
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28731
  · exact u28732
  · exact u28733

def r40206 : Route 9 := (fun mask => (mask,id))

def c40206 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40206 : Upper (D 7) (R 7) [96,260,3,17,136] 13 := by
  apply FastRouting.sound _ _ [96,260,3,17,136] 13 (by decide) (choices 1) [2,64,128] r40206 c40206
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28734
  · exact u28735
  · exact u28736

def r40207 : Route 9 := (fun mask => (mask,id))

def c40207 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40207 : Upper (D 7) (R 7) [96,260,3,17,160] 13 := by
  apply FastRouting.sound _ _ [96,260,3,17,160] 13 (by decide) (choices 1) [2,8,64,128] r40207 c40207
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28737
  · exact u28738
  · exact u28739
  · exact u28740

def b40208 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 97 262 7 26 49 232 200 200 456), lower := (rows 97 262 7 26 49 32 64 128 256), losses := [] }

theorem u40208 : Upper (D 7) (R 7) [96,260,3,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40208 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40209 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 390, targets := 32 },{ cop := 3, region := 241, targets := 2 }], pairs := [(0,1),(1,5),(2,5),(4,1)], upper := (rows 97 262 7 26 56 225 193 193 449), lower := (rows 97 262 7 26 56 32 64 128 256), losses := [] }

theorem u40209 : Upper (D 7) (R 7) [96,260,3,18,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40209 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40210 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 16, targets := 130 },{ cop := 4, region := 1, targets := 130 }], pairs := [(0,1),(0,7),(4,1),(4,7)], upper := (rows 97 262 7 26 112 169 201 137 393), lower := (rows 97 262 7 26 112 32 64 128 256), losses := [] }

theorem u40210 : Upper (D 7) (R 7) [96,260,3,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40210 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40211 : Route 9 := (fun mask => (mask,id))

def c40211 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40211 : Upper (D 7) (R 7) [96,260,3,18,129] 13 := by
  apply FastRouting.sound _ _ [96,260,3,18,129] 13 (by decide) (choices 1) [8,64,128] r40211 c40211
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28741
  · exact u28742
  · exact u28743

def r40212 : Route 9 := (fun mask => (mask,id))

def c40212 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40212 : Upper (D 7) (R 7) [96,260,3,18,136] 13 := by
  apply FastRouting.sound _ _ [96,260,3,18,136] 13 (by decide) (choices 1) [1,64,128] r40212 c40212
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28744
  · exact u28745
  · exact u28746

def r40213 : Route 9 := (fun mask => (mask,id))

def c40213 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40213 : Upper (D 7) (R 7) [96,260,3,18,160] 13 := by
  apply FastRouting.sound _ _ [96,260,3,18,160] 13 (by decide) (choices 1) [1,8,64,128] r40213 c40213
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28747
  · exact u28748
  · exact u28749
  · exact u28750

def b40214 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 97 262 7 41 82 184 216 152 408), lower := (rows 97 262 7 41 82 32 64 128 256), losses := [] }

theorem u40214 : Upper (D 7) (R 7) [96,260,3,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40214 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40215 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 24, targets := 130 }], pairs := [(3,1),(3,7),(4,1),(4,7)], upper := (rows 97 262 7 41 88 178 210 146 402), lower := (rows 97 262 7 41 88 32 64 128 256), losses := [] }

theorem u40215 : Upper (D 7) (R 7) [96,260,3,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40215 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40216 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 97 262 7 41 146 248 216 216 472), lower := (rows 97 262 7 41 146 32 64 128 256), losses := [] }

theorem u40216 : Upper (D 7) (R 7) [96,260,3,33,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40216 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40217 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 97 262 7 41 152 242 210 210 466), lower := (rows 97 262 7 41 152 32 64 128 256), losses := [] }

theorem u40217 : Upper (D 7) (R 7) [96,260,3,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40217 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40218 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 97 262 7 41 208 186 218 154 410), lower := (rows 97 262 7 41 208 32 64 128 256), losses := [] }

theorem u40218 : Upper (D 7) (R 7) [96,260,3,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40218 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40219 : Route 9 := (fun mask => (mask,id))

def c40219 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40219 : Upper (D 7) (R 7) [96,260,3,34,72] 13 := by
  apply FastRouting.sound _ _ [96,260,3,34,72] 13 (by decide) (choices 1) [1,16,128] r40219 c40219
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28751
  · exact u28752
  · exact u28753

def r40220 : Route 9 := (fun mask => (mask,id))

def c40220 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u40220 : Upper (D 7) (R 7) [96,260,3,34,129] 13 := by
  apply FastRouting.sound _ _ [96,260,3,34,129] 13 (by decide) (choices 1) [8,16,64,128] r40220 c40220
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28754
  · exact u28755
  · exact u28756
  · exact u28757

def r40221 : Route 9 := (fun mask => (mask,id))

def c40221 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u40221 : Upper (D 7) (R 7) [96,260,3,34,136] 13 := by
  apply FastRouting.sound _ _ [96,260,3,34,136] 13 (by decide) (choices 1) [1,16,64,128] r40221 c40221
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28758
  · exact u28759
  · exact u28760
  · exact u28761

def r40222 : Route 9 := (fun mask => (mask,id))

def c40222 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40222 : Upper (D 7) (R 7) [96,260,3,34,192] 13 := by
  apply FastRouting.sound _ _ [96,260,3,34,192] 13 (by decide) (choices 1) [1,8,16,128] r40222 c40222
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28762
  · exact u28763
  · exact u28764
  · exact u28765

def b40223 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 24, targets := 130 }], pairs := [(3,1),(3,7),(4,1),(4,7)], upper := (rows 97 262 7 56 88 163 195 131 387), lower := (rows 97 262 7 56 88 32 64 128 256), losses := [] }

theorem u40223 : Upper (D 7) (R 7) [96,260,3,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40223 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40224 : Route 9 := (fun mask => (mask,id))

def c40224 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40224 : Upper (D 7) (R 7) [96,260,3,48,129] 13 := by
  apply FastRouting.sound _ _ [96,260,3,48,129] 13 (by decide) (choices 1) [2,8,64,128] r40224 c40224
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28766
  · exact u28767
  · exact u28768
  · exact u28769

def r40225 : Route 9 := (fun mask => (mask,id))

def c40225 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40225 : Upper (D 7) (R 7) [96,260,3,48,130] 13 := by
  apply FastRouting.sound _ _ [96,260,3,48,130] 13 (by decide) (choices 1) [1,8,64,128] r40225 c40225
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28770
  · exact u28771
  · exact u28772
  · exact u28773

def r40226 : Route 9 := (fun mask => (mask,id))

def c40226 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40226 : Upper (D 7) (R 7) [96,260,3,48,136] 13 := by
  apply FastRouting.sound _ _ [96,260,3,48,136] 13 (by decide) (choices 1) [1,2,64,128] r40226 c40226
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28774
  · exact u28775
  · exact u28776
  · exact u28777

def r40227 : Route 9 := (fun mask => (mask,id))

def c40227 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40227 : Upper (D 7) (R 7) [96,260,3,48,192] 13 := by
  apply FastRouting.sound _ _ [96,260,3,48,192] 13 (by decide) (choices 1) [1,2,8,128] r40227 c40227
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28778
  · exact u28779
  · exact u28780
  · exact u28781

def b40228 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 8, targets := 130 },{ cop := 3, region := 1, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 97 262 7 104 145 186 218 154 410), lower := (rows 97 262 7 104 145 32 64 128 256), losses := [] }

theorem u40228 : Upper (D 7) (R 7) [96,260,3,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40228 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40229 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 8, targets := 130 },{ cop := 3, region := 1, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 97 262 7 104 146 185 217 153 409), lower := (rows 97 262 7 104 146 32 64 128 256), losses := [] }

theorem u40229 : Upper (D 7) (R 7) [96,260,3,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40229 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40230 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 8, targets := 130 },{ cop := 3, region := 1, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 97 262 7 104 152 179 211 147 403), lower := (rows 97 262 7 104 152 32 64 128 256), losses := [] }

theorem u40230 : Upper (D 7) (R 7) [96,260,3,96,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40230 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40231 : Route 9 := (fun mask => (mask,id))

def c40231 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40231 : Upper (D 7) (R 7) [96,260,3,129,130] 13 := by
  apply FastRouting.sound _ _ [96,260,3,129,130] 13 (by decide) (choices 1) [8,16,64] r40231 c40231
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28782
  · exact u28783
  · exact u28784

def b40232 : PairBound 9 := { available := 114, camps := [{ cop := 3, region := 16, targets := 99 }], pairs := [(4,0),(4,1),(4,5),(4,6)], upper := (rows 97 262 7 137 152 114 114 242 370), lower := (rows 97 262 7 137 152 32 64 128 256), losses := [] }

theorem u40232 : Upper (D 7) (R 7) [96,260,3,129,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40232 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40233 : Route 9 := (fun mask => (mask,id))

def c40233 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40233 : Upper (D 7) (R 7) [96,260,3,129,160] 13 := by
  apply FastRouting.sound _ _ [96,260,3,129,160] 13 (by decide) (choices 1) [2,8,16,64] r40233 c40233
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28785
  · exact u28786
  · exact u28787
  · exact u28788

def b40234 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 16, targets := 97 },{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7),(4,0),(4,5),(4,6)], upper := (rows 97 262 7 138 152 113 113 241 369), lower := (rows 97 262 7 138 152 32 64 128 256), losses := [] }

theorem u40234 : Upper (D 7) (R 7) [96,260,3,130,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40234 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40235 : Route 9 := (fun mask => (mask,id))

def c40235 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40235 : Upper (D 7) (R 7) [96,260,3,130,160] 13 := by
  apply FastRouting.sound _ _ [96,260,3,130,160] 13 (by decide) (choices 1) [1,8,16,64] r40235 c40235
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28789
  · exact u28790
  · exact u28791
  · exact u28792

def b40236 : PairBound 9 := { available := 99, camps := [{ cop := 7, region := 24, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 97 262 7 152 152 99 99 227 355), lower := (rows 97 262 7 152 152 32 64 128 256), losses := [] }

theorem u40236 : Upper (D 7) (R 7) [96,260,3,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40236 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40237 : PairBound 9 := { available := 75, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 97 262 7 152 176 107 75 203 331), lower := (rows 97 262 7 152 176 32 64 128 256), losses := [] }

theorem u40237 : Upper (D 7) (R 7) [96,260,3,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40237 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40238 : Route 9 := (fun mask => (mask,id))

def c40238 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40238 : Upper (D 7) (R 7) [96,260,3,160,192] 13 := by
  apply FastRouting.sound _ _ [96,260,3,160,192] 13 (by decide) (choices 1) [1,2,8,16] r40238 c40238
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28793
  · exact u28794
  · exact u28795
  · exact u28796

def b40239 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 12, targets := 224 }], pairs := [(2,5),(2,6),(2,7),(3,5)], upper := (rows 97 262 13 26 19 224 224 224 480), lower := (rows 97 262 13 26 19 32 64 128 256), losses := [] }

theorem u40239 : Upper (D 7) (R 7) [96,260,9,18,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40239 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40240 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 97 262 13 26 49 226 194 194 450), lower := (rows 97 262 13 26 49 32 64 128 256), losses := [] }

theorem u40240 : Upper (D 7) (R 7) [96,260,9,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40240 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40241 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 97 262 13 26 50 225 193 193 449), lower := (rows 97 262 13 26 50 32 64 128 256), losses := [] }

theorem u40241 : Upper (D 7) (R 7) [96,260,9,18,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40241 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40242 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 16, targets := 130 },{ cop := 4, region := 1, targets := 130 }], pairs := [(0,1),(0,7),(4,1),(4,7)], upper := (rows 97 262 13 26 112 163 195 131 387), lower := (rows 97 262 13 26 112 32 64 128 256), losses := [] }

theorem u40242 : Upper (D 7) (R 7) [96,260,9,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40242 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40243 : Route 9 := (fun mask => (mask,id))

def c40243 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40243 : Upper (D 7) (R 7) [96,260,9,18,129] 13 := by
  apply FastRouting.sound _ _ [96,260,9,18,129] 13 (by decide) (choices 1) [2,64,128] r40243 c40243
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28797
  · exact u28798
  · exact u28799

def b40244 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 97 262 13 26 146 225 225 225 481), lower := (rows 97 262 13 26 146 32 64 128 256), losses := [] }

theorem u40244 : Upper (D 7) (R 7) [96,260,9,18,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40244 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40245 : Route 9 := (fun mask => (mask,id))

def c40245 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40245 : Upper (D 7) (R 7) [96,260,9,18,160] 13 := by
  apply FastRouting.sound _ _ [96,260,9,18,160] 13 (by decide) (choices 1) [1,2,64,128] r40245 c40245
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28800
  · exact u28801
  · exact u28802
  · exact u28803

def b40246 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 4, region := 232, targets := 1 },{ cop := 4, region := 225, targets := 2 }], pairs := [(0,1),(1,5),(3,0),(4,5)], upper := (rows 97 262 13 42 19 240 208 208 464), lower := (rows 97 262 13 42 19 32 64 128 256), losses := [] }

theorem u40246 : Upper (D 7) (R 7) [96,260,9,34,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40246 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40247 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 16, targets := 162 },{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6),(4,1),(4,5),(4,7)], upper := (rows 97 262 13 42 81 178 210 146 402), lower := (rows 97 262 13 42 81 32 64 128 256), losses := [] }

theorem u40247 : Upper (D 7) (R 7) [96,260,9,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40247 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40248 : Route 9 := (fun mask => (mask,id))

def c40248 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40248 : Upper (D 7) (R 7) [96,260,9,34,66] 13 := by
  apply FastRouting.sound _ _ [96,260,9,34,66] 13 (by decide) (choices 1) [1,16,128] r40248 c40248
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28804
  · exact u28805
  · exact u28806

def r40249 : Route 9 := (fun mask => (mask,id))

def c40249 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u40249 : Upper (D 7) (R 7) [96,260,9,34,129] 13 := by
  apply FastRouting.sound _ _ [96,260,9,34,129] 13 (by decide) (choices 1) [2,16,64,128] r40249 c40249
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28807
  · exact u28808
  · exact u28809
  · exact u28810

def r40250 : Route 9 := (fun mask => (mask,id))

def c40250 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u40250 : Upper (D 7) (R 7) [96,260,9,34,130] 13 := by
  apply FastRouting.sound _ _ [96,260,9,34,130] 13 (by decide) (choices 1) [1,16,64,128] r40250 c40250
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28811
  · exact u28812
  · exact u28813
  · exact u28814

def r40251 : Route 9 := (fun mask => (mask,id))

def c40251 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40251 : Upper (D 7) (R 7) [96,260,9,34,192] 13 := by
  apply FastRouting.sound _ _ [96,260,9,34,192] 13 (by decide) (choices 1) [1,2,16,128] r40251 c40251
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28815
  · exact u28816
  · exact u28817
  · exact u28818

def b40252 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 2, region := 450, targets := 1 },{ cop := 4, region := 232, targets := 1 }], pairs := [(1,0),(1,5),(3,0),(4,5)], upper := (rows 97 262 13 56 19 226 194 194 450), lower := (rows 97 262 13 56 19 32 64 128 256), losses := [] }

theorem u40252 : Upper (D 7) (R 7) [96,260,9,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40252 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40253 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 28, targets := 130 }], pairs := [(2,1),(2,7),(3,1),(3,7)], upper := (rows 97 262 13 56 81 162 194 130 386), lower := (rows 97 262 13 56 81 32 64 128 256), losses := [] }

theorem u40253 : Upper (D 7) (R 7) [96,260,9,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40253 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40254 : Route 9 := (fun mask => (mask,id))

def c40254 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40254 : Upper (D 7) (R 7) [96,260,9,48,66] 13 := by
  apply FastRouting.sound _ _ [96,260,9,48,66] 13 (by decide) (choices 1) [1,2,128] r40254 c40254
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28819
  · exact u28820
  · exact u28821

def r40255 : Route 9 := (fun mask => (mask,id))

def c40255 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40255 : Upper (D 7) (R 7) [96,260,9,48,129] 13 := by
  apply FastRouting.sound _ _ [96,260,9,48,129] 13 (by decide) (choices 1) [2,64,128] r40255 c40255
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28822
  · exact u28823
  · exact u28824

def r40256 : Route 9 := (fun mask => (mask,id))

def c40256 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40256 : Upper (D 7) (R 7) [96,260,9,48,130] 13 := by
  apply FastRouting.sound _ _ [96,260,9,48,130] 13 (by decide) (choices 1) [1,2,64,128] r40256 c40256
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28825
  · exact u28826
  · exact u28827
  · exact u28828

def r40257 : Route 9 := (fun mask => (mask,id))

def c40257 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40257 : Upper (D 7) (R 7) [96,260,9,48,192] 13 := by
  apply FastRouting.sound _ _ [96,260,9,48,192] 13 (by decide) (choices 1) [1,2,128] r40257 c40257
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28829
  · exact u28830
  · exact u28831

def r40258 : Route 9 := (fun mask => (mask,id))

def c40258 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u40258 : Upper (D 7) (R 7) [96,260,9,130,3] 13 := by
  apply FastRouting.sound _ _ [96,260,9,130,3] 13 (by decide) (choices 1) [16,64,128] r40258 c40258
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28832
  · exact u28833
  · exact u28834

def b40259 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 97 262 13 138 49 242 210 210 466), lower := (rows 97 262 13 138 49 32 64 128 256), losses := [] }

theorem u40259 : Upper (D 7) (R 7) [96,260,9,130,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40259 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u40259
end Delivery.IrregularNine14.P07

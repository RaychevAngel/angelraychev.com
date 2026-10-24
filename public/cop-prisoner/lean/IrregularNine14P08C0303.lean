import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0111
import IrregularNine14P08C0112

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b18180 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 140 168 82 49 113 177 305), lower := (rows 321 7 140 168 82 32 64 128 256), losses := [] }

theorem u18180 : Upper (D 8) (R 8) [320,5,136,160,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18180 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18181 : PairBound 9 := { available := 51, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 140 168 112 51 115 179 307), lower := (rows 321 7 140 168 112 32 64 128 256), losses := [] }

theorem u18181 : Upper (D 8) (R 8) [320,5,136,160,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18181 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18182 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 140 200 49 50 114 178 306), lower := (rows 321 7 140 200 49 32 64 128 256), losses := [] }

theorem u18182 : Upper (D 8) (R 8) [320,5,136,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18182 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18183 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 140 200 50 49 113 177 305), lower := (rows 321 7 140 200 50 32 64 128 256), losses := [] }

theorem u18183 : Upper (D 8) (R 8) [320,5,136,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18183 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18184 : PairBound 9 := { available := 106, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 321 7 164 25 176 106 106 234 362), lower := (rows 321 7 164 25 176 32 64 128 256), losses := [] }

theorem u18184 : Upper (D 8) (R 8) [320,5,160,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18184 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18185 : PairBound 9 := { available := 42, camps := [{ cop := 3, region := 166, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 164 25 208 42 106 170 298), lower := (rows 321 7 164 25 208 32 64 128 256), losses := [] }

theorem u18185 : Upper (D 8) (R 8) [320,5,160,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18185 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18186 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 228, targets := 1 }], pairs := [(2,0)], upper := (rows 321 7 164 26 49 232 232 232 488), lower := (rows 321 7 164 26 49 32 64 128 256), losses := [] }

theorem u18186 : Upper (D 8) (R 8) [320,5,160,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18186 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18187 : Route 9 := (fun mask => (mask,id))

def c18187 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u18187 : Upper (D 8) (R 8) [320,5,160,18,40] 13 := by
  apply FastRouting.sound _ _ [320,5,160,18,40] 13 (by decide) (choices 1) [1,64,128] r18187 c18187
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6671
  · exact u6672
  · exact u6673

def b18188 : PairBound 9 := { available := 168, camps := [{ cop := 4, region := 174, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 164 26 81 168 232 168 424), lower := (rows 321 7 164 26 81 32 64 128 256), losses := [] }

theorem u18188 : Upper (D 8) (R 8) [320,5,160,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18188 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18189 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 166, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 164 26 88 161 225 161 417), lower := (rows 321 7 164 26 88 32 64 128 256), losses := [] }

theorem u18189 : Upper (D 8) (R 8) [320,5,160,18,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18189 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18190 : Route 9 := (fun mask => (mask,id))

def c18190 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u18190 : Upper (D 8) (R 8) [320,5,160,18,96] 13 := by
  apply FastRouting.sound _ _ [320,5,160,18,96] 13 (by decide) (choices 1) [1,8,128] r18190 c18190
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6674
  · exact u6675
  · exact u6676

def b18191 : PairBound 9 := { available := 104, camps := [{ cop := 3, region := 228, targets := 1 }], pairs := [(2,0)], upper := (rows 321 7 164 26 145 104 104 232 360), lower := (rows 321 7 164 26 145 32 64 128 256), losses := [] }

theorem u18191 : Upper (D 8) (R 8) [320,5,160,18,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18191 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18192 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 164 26 152 97 97 225 353), lower := (rows 321 7 164 26 152 32 64 128 256), losses := [] }

theorem u18192 : Upper (D 8) (R 8) [320,5,160,18,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18192 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18193 : PairBound 9 := { available := 105, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 321 7 164 26 176 105 105 233 361), lower := (rows 321 7 164 26 176 32 64 128 256), losses := [] }

theorem u18193 : Upper (D 8) (R 8) [320,5,160,18,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18193 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18194 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 164 26 208 41 105 169 297), lower := (rows 321 7 164 26 208 32 64 128 256), losses := [] }

theorem u18194 : Upper (D 8) (R 8) [320,5,160,18,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18194 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18195 : Route 9 := (fun mask => (mask,id))

def c18195 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u18195 : Upper (D 8) (R 8) [320,5,160,33,34] 13 := by
  apply FastRouting.sound _ _ [320,5,160,33,34] 13 (by decide) (choices 1) [8,16,64,128] r18195 c18195
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6677
  · exact u6678
  · exact u6679
  · exact u6680

def b18196 : PairBound 9 := { available := 210, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 321 7 164 41 56 242 210 210 466), lower := (rows 321 7 164 41 56 32 64 128 256), losses := [] }

theorem u18196 : Upper (D 8) (R 8) [320,5,160,33,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18196 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18197 : Route 9 := (fun mask => (mask,id))

def c18197 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u18197 : Upper (D 8) (R 8) [320,5,160,33,66] 13 := by
  apply FastRouting.sound _ _ [320,5,160,33,66] 13 (by decide) (choices 1) [8,16,128] r18197 c18197
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6681
  · exact u6682
  · exact u6683

def r18198 : Route 9 := (fun mask => (mask,id))

def c18198 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u18198 : Upper (D 8) (R 8) [320,5,160,33,72] 13 := by
  apply FastRouting.sound _ _ [320,5,160,33,72] 13 (by decide) (choices 1) [2,16,128] r18198 c18198
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6684
  · exact u6685
  · exact u6686

def r18199 : Route 9 := (fun mask => (mask,id))

def c18199 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u18199 : Upper (D 8) (R 8) [320,5,160,33,96] 13 := by
  apply FastRouting.sound _ _ [320,5,160,33,96] 13 (by decide) (choices 1) [2,8,16,128] r18199 c18199
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6687
  · exact u6688
  · exact u6689
  · exact u6690

def b18200 : PairBound 9 := { available := 120, camps := [{ cop := 4, region := 361, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 164 41 146 120 120 248 376), lower := (rows 321 7 164 41 146 32 64 128 256), losses := [] }

theorem u18200 : Upper (D 8) (R 8) [320,5,160,33,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18200 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18201 : Route 9 := (fun mask => (mask,id))

def c18201 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18201 : Upper (D 8) (R 8) [320,5,160,33,136] 13 := by
  apply FastRouting.sound _ _ [320,5,160,33,136] 13 (by decide) (choices 1) [2,16,64] r18201 c18201
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6691
  · exact u6692
  · exact u6693

def b18202 : PairBound 9 := { available := 90, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 321 7 164 41 176 122 90 218 346), lower := (rows 321 7 164 41 176 32 64 128 256), losses := [] }

theorem u18202 : Upper (D 8) (R 8) [320,5,160,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18202 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18203 : Route 9 := (fun mask => (mask,id))

def c18203 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18203 : Upper (D 8) (R 8) [320,5,160,33,192] 13 := by
  apply FastRouting.sound _ _ [320,5,160,33,192] 13 (by decide) (choices 1) [2,8,16] r18203 c18203
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6694
  · exact u6695
  · exact u6696

def b18204 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 321 7 164 42 56 241 209 209 465), lower := (rows 321 7 164 42 56 32 64 128 256), losses := [] }

theorem u18204 : Upper (D 8) (R 8) [320,5,160,34,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18204 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18205 : PairBound 9 := { available := 184, camps := [{ cop := 4, region := 174, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 164 42 81 184 248 184 440), lower := (rows 321 7 164 42 81 32 64 128 256), losses := [] }

theorem u18205 : Upper (D 8) (R 8) [320,5,160,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18205 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18206 : Route 9 := (fun mask => (mask,id))

def c18206 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u18206 : Upper (D 8) (R 8) [320,5,160,34,72] 13 := by
  apply FastRouting.sound _ _ [320,5,160,34,72] 13 (by decide) (choices 1) [1,16,128] r18206 c18206
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6697
  · exact u6698
  · exact u6699

def r18207 : Route 9 := (fun mask => (mask,id))

def c18207 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u18207 : Upper (D 8) (R 8) [320,5,160,34,96] 13 := by
  apply FastRouting.sound _ _ [320,5,160,34,96] 13 (by decide) (choices 1) [1,8,16,128] r18207 c18207
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6700
  · exact u6701
  · exact u6702
  · exact u6703

def r18208 : Route 9 := (fun mask => (mask,id))

def c18208 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18208 : Upper (D 8) (R 8) [320,5,160,34,129] 13 := by
  apply FastRouting.sound _ _ [320,5,160,34,129] 13 (by decide) (choices 1) [8,16,64] r18208 c18208
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6704
  · exact u6705
  · exact u6706

def b18209 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 164 42 152 113 113 241 369), lower := (rows 321 7 164 42 152 32 64 128 256), losses := [] }

theorem u18209 : Upper (D 8) (R 8) [320,5,160,34,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18209 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18210 : PairBound 9 := { available := 89, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 321 7 164 42 176 121 89 217 345), lower := (rows 321 7 164 42 176 32 64 128 256), losses := [] }

theorem u18210 : Upper (D 8) (R 8) [320,5,160,34,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18210 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18211 : Route 9 := (fun mask => (mask,id))

def c18211 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18211 : Upper (D 8) (R 8) [320,5,160,34,192] 13 := by
  apply FastRouting.sound _ _ [320,5,160,34,192] 13 (by decide) (choices 1) [1,8,16] r18211 c18211
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6707
  · exact u6708
  · exact u6709

def b18212 : PairBound 9 := { available := 195, camps := [{ cop := 2, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 321 7 164 56 56 227 195 195 451), lower := (rows 321 7 164 56 56 32 64 128 256), losses := [] }

theorem u18212 : Upper (D 8) (R 8) [320,5,160,48,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18212 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18213 : PairBound 9 := { available := 170, camps := [{ cop := 4, region := 174, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 164 56 81 170 234 170 426), lower := (rows 321 7 164 56 81 32 64 128 256), losses := [] }

theorem u18213 : Upper (D 8) (R 8) [320,5,160,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18213 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18214 : Route 9 := (fun mask => (mask,id))

def c18214 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u18214 : Upper (D 8) (R 8) [320,5,160,48,66] 13 := by
  apply FastRouting.sound _ _ [320,5,160,48,66] 13 (by decide) (choices 1) [1,8,128] r18214 c18214
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6710
  · exact u6711
  · exact u6712

def b18215 : PairBound 9 := { available := 163, camps := [{ cop := 0, region := 166, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 164 56 88 163 227 163 419), lower := (rows 321 7 164 56 88 32 64 128 256), losses := [] }

theorem u18215 : Upper (D 8) (R 8) [320,5,160,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18215 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18216 : PairBound 9 := { available := 139, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 321 7 164 56 112 171 203 139 395), lower := (rows 321 7 164 56 112 32 64 128 256), losses := [] }

theorem u18216 : Upper (D 8) (R 8) [320,5,160,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18216 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18217 : Route 9 := (fun mask => (mask,id))

def c18217 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18217 : Upper (D 8) (R 8) [320,5,160,48,129] 13 := by
  apply FastRouting.sound _ _ [320,5,160,48,129] 13 (by decide) (choices 1) [2,8,64] r18217 c18217
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6713
  · exact u6714
  · exact u6715

def b18218 : PairBound 9 := { available := 105, camps := [{ cop := 4, region := 361, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 164 56 146 105 105 233 361), lower := (rows 321 7 164 56 146 32 64 128 256), losses := [] }

theorem u18218 : Upper (D 8) (R 8) [320,5,160,48,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18218 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18219 : PairBound 9 := { available := 99, camps := [{ cop := 2, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 321 7 164 56 152 99 99 227 355), lower := (rows 321 7 164 56 152 32 64 128 256), losses := [] }

theorem u18219 : Upper (D 8) (R 8) [320,5,160,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18219 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18220 : PairBound 9 := { available := 75, camps := [{ cop := 2, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 321 7 164 56 176 107 75 203 331), lower := (rows 321 7 164 56 176 32 64 128 256), losses := [] }

theorem u18220 : Upper (D 8) (R 8) [320,5,160,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18220 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18221 : Route 9 := (fun mask => (mask,id))

def c18221 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18221 : Upper (D 8) (R 8) [320,5,160,48,192] 13 := by
  apply FastRouting.sound _ _ [320,5,160,48,192] 13 (by decide) (choices 1) [1,2,8] r18221 c18221
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6716
  · exact u6717
  · exact u6718

def b18222 : PairBound 9 := { available := 50, camps := [{ cop := 3, region := 182, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 164 73 152 50 114 178 306), lower := (rows 321 7 164 73 152 32 64 128 256), losses := [] }

theorem u18222 : Upper (D 8) (R 8) [320,5,160,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18222 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18223 : Route 9 := (fun mask => (mask,id))

def c18223 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18223 : Upper (D 8) (R 8) [320,5,160,66,129] 13 := by
  apply FastRouting.sound _ _ [320,5,160,66,129] 13 (by decide) (choices 1) [8,16] r18223 c18223
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6719
  · exact u6720

def b18224 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 164 74 152 49 113 177 305), lower := (rows 321 7 164 74 152 32 64 128 256), losses := [] }

theorem u18224 : Upper (D 8) (R 8) [320,5,160,66,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18224 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18225 : PairBound 9 := { available := 57, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 321 7 164 74 176 57 121 185 313), lower := (rows 321 7 164 74 176 32 64 128 256), losses := [] }

theorem u18225 : Upper (D 8) (R 8) [320,5,160,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18225 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18226 : Route 9 := (fun mask => (mask,id))

def c18226 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18226 : Upper (D 8) (R 8) [320,5,160,80,129] 13 := by
  apply FastRouting.sound _ _ [320,5,160,80,129] 13 (by decide) (choices 1) [2,8] r18226 c18226
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6721
  · exact u6722

def b18227 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 361, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 164 88 146 41 105 169 297), lower := (rows 321 7 164 88 146 32 64 128 256), losses := [] }

theorem u18227 : Upper (D 8) (R 8) [320,5,160,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18227 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18228 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 166, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 164 88 152 35 99 163 291), lower := (rows 321 7 164 88 152 32 64 128 256), losses := [] }

theorem u18228 : Upper (D 8) (R 8) [320,5,160,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18228 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18229 : PairBound 9 := { available := 43, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 321 7 164 88 176 43 107 171 299), lower := (rows 321 7 164 88 176 32 64 128 256), losses := [] }

theorem u18229 : Upper (D 8) (R 8) [320,5,160,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18229 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18230 : Route 9 := (fun mask => (mask,id))

def c18230 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18230 : Upper (D 8) (R 8) [320,5,160,96,129] 13 := by
  apply FastRouting.sound _ _ [320,5,160,96,129] 13 (by decide) (choices 1) [2,8,16] r18230 c18230
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6723
  · exact u6724
  · exact u6725

def b18231 : PairBound 9 := { available := 57, camps := [{ cop := 4, region := 361, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 164 104 146 57 121 185 313), lower := (rows 321 7 164 104 146 32 64 128 256), losses := [] }

theorem u18231 : Upper (D 8) (R 8) [320,5,160,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18231 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18232 : Route 9 := (fun mask => (mask,id))

def c18232 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18232 : Upper (D 8) (R 8) [320,5,160,96,136] 13 := by
  apply FastRouting.sound _ _ [320,5,160,96,136] 13 (by decide) (choices 1) [1,2,16] r18232 c18232
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6726
  · exact u6727
  · exact u6728

def b18233 : PairBound 9 := { available := 27, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 321 7 164 104 176 59 91 155 283), lower := (rows 321 7 164 104 176 32 64 128 256), losses := [] }

theorem u18233 : Upper (D 8) (R 8) [320,5,160,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18233 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18234 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 196 26 49 168 232 168 424), lower := (rows 321 7 196 26 49 32 64 128 256), losses := [] }

theorem u18234 : Upper (D 8) (R 8) [320,5,192,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18234 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18235 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 196 26 56 161 225 161 417), lower := (rows 321 7 196 26 56 32 64 128 256), losses := [] }

theorem u18235 : Upper (D 8) (R 8) [320,5,192,18,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18235 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18236 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 196 26 145 40 104 168 296), lower := (rows 321 7 196 26 145 32 64 128 256), losses := [] }

theorem u18236 : Upper (D 8) (R 8) [320,5,192,18,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18236 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18237 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 196 26 152 33 97 161 289), lower := (rows 321 7 196 26 152 32 64 128 256), losses := [] }

theorem u18237 : Upper (D 8) (R 8) [320,5,192,18,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18237 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18238 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 196 26 176 41 105 169 297), lower := (rows 321 7 196 26 176 32 64 128 256), losses := [] }

theorem u18238 : Upper (D 8) (R 8) [320,5,192,18,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18238 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18239 : PairBound 9 := { available := 184, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 196 41 50 184 248 184 440), lower := (rows 321 7 196 41 50 32 64 128 256), losses := [] }

theorem u18239 : Upper (D 8) (R 8) [320,5,192,33,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18239 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u18239
end Delivery.IrregularNine14.P08

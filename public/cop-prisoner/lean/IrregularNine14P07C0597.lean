import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0352
import IrregularNine14P07C0353
import IrregularNine14P07C0354

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r35820 : Route 9 := (fun mask => (mask,id))

def c35820 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35820 : Upper (D 7) (R 7) [34,260,24,65,192] 13 := by
  apply FastRouting.sound _ _ [34,260,24,65,192] 13 (by decide) (choices 1) [1,2,128] r35820 c35820
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21162
  · exact u21163
  · exact u21164

def b35821 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 0, region := 208, targets := 2 },{ cop := 0, region := 200, targets := 32 }], pairs := [(0,6),(1,6),(3,5),(4,1)], upper := (rows 35 262 28 74 112 161 193 129 385), lower := (rows 35 262 28 74 112 32 64 128 256), losses := [] }

theorem u35821 : Upper (D 7) (R 7) [34,260,24,66,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35821 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35822 : Route 9 := (fun mask => (mask,id))

def c35822 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35822 : Upper (D 7) (R 7) [34,260,24,66,160] 13 := by
  apply FastRouting.sound _ _ [34,260,24,66,160] 13 (by decide) (choices 1) [1,64,128] r35822 c35822
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21165
  · exact u21166
  · exact u21167

def r35823 : Route 9 := (fun mask => (mask,id))

def c35823 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35823 : Upper (D 7) (R 7) [34,260,24,66,192] 13 := by
  apply FastRouting.sound _ _ [34,260,24,66,192] 13 (by decide) (choices 1) [1,128] r35823 c35823
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u21168
  · exact u21169

def r35824 : Route 9 := (fun mask => (mask,id))

def c35824 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35824 : Upper (D 7) (R 7) [34,260,24,96,192] 13 := by
  apply FastRouting.sound _ _ [34,260,24,96,192] 13 (by decide) (choices 1) [1,2,128] r35824 c35824
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21170
  · exact u21171
  · exact u21172

def b35825 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 20, targets := 35 }], pairs := [(2,0),(2,1),(2,5),(4,0)], upper := (rows 35 262 28 200 208 35 99 163 291), lower := (rows 35 262 28 200 208 32 64 128 256), losses := [] }

theorem u35825 : Upper (D 7) (R 7) [34,260,24,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35825 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35826 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 28, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 262 44 25 19 224 192 192 448), lower := (rows 35 262 44 25 19 32 64 128 256), losses := [] }

theorem u35826 : Upper (D 7) (R 7) [34,260,40,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35826 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35827 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 35 262 44 25 81 226 194 194 450), lower := (rows 35 262 44 25 81 32 64 128 256), losses := [] }

theorem u35827 : Upper (D 7) (R 7) [34,260,40,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35827 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35828 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 3, region := 228, targets := 2 }], pairs := [(1,5),(2,1),(3,5),(4,5)], upper := (rows 35 262 44 25 82 225 193 193 449), lower := (rows 35 262 44 25 82 32 64 128 256), losses := [{ target := 5, region := (rows 1 6 4 9 21 0 73 137 265), good := (rows 475 278 478 473 82 0 64 128 256) }] }

theorem u35828 : Upper (D 7) (R 7) [34,260,40,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35828 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35829 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c35829 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35829 : Upper (D 7) (R 7) [34,260,40,17,192] 13 := by
  apply FastRouting.sound _ _ [34,260,40,17,192] 13 (by decide) (choices 1) [1,2,64] r35829 c35829
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21173
  · exact u21174
  · exact u21175

def b35830 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 208, targets := 2 }], pairs := [(2,1),(3,5),(4,1),(4,5)], upper := (rows 35 262 44 26 81 225 193 193 449), lower := (rows 35 262 44 26 81 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 17 49 81 145 273), good := (rows 497 260 44 508 497 32 64 128 256) }] }

theorem u35830 : Upper (D 7) (R 7) [34,260,40,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35830 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35831 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c35831 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35831 : Upper (D 7) (R 7) [34,260,40,18,192] 13 := by
  apply FastRouting.sound _ _ [34,260,40,18,192] 13 (by decide) (choices 1) [1,64] r35831 c35831
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u21176
  · exact u21177

def b35832 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 16, targets := 192 }], pairs := [(3,5),(4,5),(4,6),(4,7)], upper := (rows 35 262 44 73 19 240 208 208 464), lower := (rows 35 262 44 73 19 32 64 128 256), losses := [] }

theorem u35832 : Upper (D 7) (R 7) [34,260,40,65,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35832 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35833 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 16, targets := 162 },{ cop := 4, region := 8, targets := 2 }], pairs := [(3,1),(4,1),(4,5),(4,7)], upper := (rows 35 262 44 73 81 178 210 146 402), lower := (rows 35 262 44 73 81 32 64 128 256), losses := [] }

theorem u35833 : Upper (D 7) (R 7) [34,260,40,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35833 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35834 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 4, region := 161, targets := 64 }], pairs := [(0,6),(1,5),(3,5),(4,5)], upper := (rows 35 262 44 73 82 177 209 145 401), lower := (rows 35 262 44 73 82 32 64 128 256), losses := [{ target := 5, region := (rows 1 6 4 9 21 0 73 137 265), good := (rows 475 278 478 473 82 0 64 128 256) }] }

theorem u35834 : Upper (D 7) (R 7) [34,260,40,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35834 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35835 : Route 9 := (fun mask => (mask,id))

def c35835 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u35835 : Upper (D 7) (R 7) [34,260,40,65,129] 13 := by
  apply FastRouting.sound _ _ [34,260,40,65,129] 13 (by decide) (choices 1) [2,16,64,128] r35835 c35835
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21178
  · exact u21179
  · exact u21180
  · exact u21181

def r35836 : Route 9 := (fun mask => (mask,id))

def c35836 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u35836 : Upper (D 7) (R 7) [34,260,40,65,130] 13 := by
  apply FastRouting.sound _ _ [34,260,40,65,130] 13 (by decide) (choices 1) [1,16,64,128] r35836 c35836
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21182
  · exact u21183
  · exact u21184
  · exact u21185

def r35837 : Route 9 := (fun mask => (mask,id))

def c35837 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35837 : Upper (D 7) (R 7) [34,260,40,65,192] 13 := by
  apply FastRouting.sound _ _ [34,260,40,65,192] 13 (by decide) (choices 1) [1,2,16,128] r35837 c35837
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21186
  · exact u21187
  · exact u21188
  · exact u21189

def r35838 : Route 9 := (fun mask => (mask,id))

def c35838 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35838 : Upper (D 7) (R 7) [34,260,40,66,65] 13 := by
  apply FastRouting.sound _ _ [34,260,40,66,65] 13 (by decide) (choices 1) [1,16,128] r35838 c35838
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21190
  · exact u21191
  · exact u21192

def r35839 : Route 9 := (fun mask => (mask,id))

def c35839 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u35839 : Upper (D 7) (R 7) [34,260,40,66,129] 13 := by
  apply FastRouting.sound _ _ [34,260,40,66,129] 13 (by decide) (choices 1) [1,16,64,128] r35839 c35839
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21193
  · exact u21194
  · exact u21195
  · exact u21196

def r35840 : Route 9 := (fun mask => (mask,id))

def c35840 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35840 : Upper (D 7) (R 7) [34,260,40,66,192] 13 := by
  apply FastRouting.sound _ _ [34,260,40,66,192] 13 (by decide) (choices 1) [1,16,128] r35840 c35840
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21197
  · exact u21198
  · exact u21199

def b35841 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 16, targets := 192 }], pairs := [(3,5),(4,5),(4,6),(4,7)], upper := (rows 35 262 44 88 19 225 193 193 449), lower := (rows 35 262 44 88 19 32 64 128 256), losses := [] }

theorem u35841 : Upper (D 7) (R 7) [34,260,40,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35841 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35842 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 35 262 44 88 81 163 195 131 387), lower := (rows 35 262 44 88 81 32 64 128 256), losses := [] }

theorem u35842 : Upper (D 7) (R 7) [34,260,40,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35842 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35843 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 35 262 44 88 82 161 193 129 385), lower := (rows 35 262 44 88 82 32 64 128 256), losses := [] }

theorem u35843 : Upper (D 7) (R 7) [34,260,40,80,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35843 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35844 : Route 9 := (fun mask => (mask,id))

def c35844 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35844 : Upper (D 7) (R 7) [34,260,40,80,129] 13 := by
  apply FastRouting.sound _ _ [34,260,40,80,129] 13 (by decide) (choices 1) [1,2,64,128] r35844 c35844
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21200
  · exact u21201
  · exact u21202
  · exact u21203

def r35845 : Route 9 := (fun mask => (mask,id))

def c35845 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35845 : Upper (D 7) (R 7) [34,260,40,80,130] 13 := by
  apply FastRouting.sound _ _ [34,260,40,80,130] 13 (by decide) (choices 1) [1,64,128] r35845 c35845
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21204
  · exact u21205
  · exact u21206

def b35846 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 35 262 44 88 208 163 195 131 387), lower := (rows 35 262 44 88 208 32 64 128 256), losses := [] }

theorem u35846 : Upper (D 7) (R 7) [34,260,40,80,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35846 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35847 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 16, targets := 192 }], pairs := [(3,5),(4,5),(4,6),(4,7)], upper := (rows 35 262 44 200 19 241 209 209 465), lower := (rows 35 262 44 200 19 32 64 128 256), losses := [] }

theorem u35847 : Upper (D 7) (R 7) [34,260,40,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35847 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35848 : Route 9 := (fun mask => (mask,id))

def c35848 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35848 : Upper (D 7) (R 7) [34,260,40,192,65] 13 := by
  apply FastRouting.sound _ _ [34,260,40,192,65] 13 (by decide) (choices 1) [1,2,16,128] r35848 c35848
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21207
  · exact u21208
  · exact u21209
  · exact u21210

def r35849 : Route 9 := (fun mask => (mask,id))

def c35849 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35849 : Upper (D 7) (R 7) [34,260,40,192,66] 13 := by
  apply FastRouting.sound _ _ [34,260,40,192,66] 13 (by decide) (choices 1) [1,16,128] r35849 c35849
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21211
  · exact u21212
  · exact u21213

def b35850 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 16, targets := 35 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,1),(4,5)], upper := (rows 35 262 44 200 208 51 83 147 275), lower := (rows 35 262 44 200 208 32 64 128 256), losses := [] }

theorem u35850 : Upper (D 7) (R 7) [34,260,40,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35850 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35851 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 35 262 69 11 56 240 208 208 464), lower := (rows 35 262 69 11 56 32 64 128 256), losses := [] }

theorem u35851 : Upper (D 7) (R 7) [34,260,65,3,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35851 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35852 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 244, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 35 262 69 11 88 176 240 176 432), lower := (rows 35 262 69 11 88 32 64 128 256), losses := [] }

theorem u35852 : Upper (D 7) (R 7) [34,260,65,3,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35852 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35853 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 244, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 35 262 69 11 112 184 216 152 408), lower := (rows 35 262 69 11 112 32 64 128 256), losses := [] }

theorem u35853 : Upper (D 7) (R 7) [34,260,65,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35853 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35854 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 244, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 35 262 69 11 152 240 240 240 496), lower := (rows 35 262 69 11 152 32 64 128 256), losses := [] }

theorem u35854 : Upper (D 7) (R 7) [34,260,65,3,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35854 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35855 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 244, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 35 262 69 11 176 248 216 216 472), lower := (rows 35 262 69 11 176 32 64 128 256), losses := [] }

theorem u35855 : Upper (D 7) (R 7) [34,260,65,3,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35855 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35856 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 244, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 35 262 69 11 208 184 248 184 440), lower := (rows 35 262 69 11 208 32 64 128 256), losses := [] }

theorem u35856 : Upper (D 7) (R 7) [34,260,65,3,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35856 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35857 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 24, targets := 224 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 35 262 69 25 26 224 224 224 480), lower := (rows 35 262 69 25 26 32 64 128 256), losses := [] }

theorem u35857 : Upper (D 7) (R 7) [34,260,65,17,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35857 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35858 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 35 262 69 25 50 232 200 200 456), lower := (rows 35 262 69 25 50 32 64 128 256), losses := [] }

theorem u35858 : Upper (D 7) (R 7) [34,260,65,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35858 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35859 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 24, targets := 194 }], pairs := [(3,1),(3,6),(3,7),(4,1)], upper := (rows 35 262 69 25 56 226 194 194 450), lower := (rows 35 262 69 25 56 32 64 128 256), losses := [] }

theorem u35859 : Upper (D 7) (R 7) [34,260,65,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35859 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35860 : Route 9 := (fun mask => (mask,id))

def c35860 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35860 : Upper (D 7) (R 7) [34,260,65,17,66] 13 := by
  apply FastRouting.sound _ _ [34,260,65,17,66] 13 (by decide) (choices 1) [8,128] r35860 c35860
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u21214
  · exact u21215

def b35861 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 24, targets := 162 }], pairs := [(3,1),(3,5),(3,7),(4,1)], upper := (rows 35 262 69 25 88 162 226 162 418), lower := (rows 35 262 69 25 88 32 64 128 256), losses := [] }

theorem u35861 : Upper (D 7) (R 7) [34,260,65,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35861 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35862 : Route 9 := (fun mask => (mask,id))

def c35862 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35862 : Upper (D 7) (R 7) [34,260,65,17,96] 13 := by
  apply FastRouting.sound _ _ [34,260,65,17,96] 13 (by decide) (choices 1) [2,8,128] r35862 c35862
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21216
  · exact u21217
  · exact u21218

def r35863 : Route 9 := (fun mask => (mask,id))

def c35863 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35863 : Upper (D 7) (R 7) [34,260,65,17,130] 13 := by
  apply FastRouting.sound _ _ [34,260,65,17,130] 13 (by decide) (choices 1) [8,64,128] r35863 c35863
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21219
  · exact u21220
  · exact u21221

def r35864 : Route 9 := (fun mask => (mask,id))

def c35864 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35864 : Upper (D 7) (R 7) [34,260,65,17,136] 13 := by
  apply FastRouting.sound _ _ [34,260,65,17,136] 13 (by decide) (choices 1) [2,64,128] r35864 c35864
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21222
  · exact u21223
  · exact u21224

def r35865 : Route 9 := (fun mask => (mask,id))

def c35865 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35865 : Upper (D 7) (R 7) [34,260,65,17,160] 13 := by
  apply FastRouting.sound _ _ [34,260,65,17,160] 13 (by decide) (choices 1) [2,8,64,128] r35865 c35865
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21225
  · exact u21226
  · exact u21227
  · exact u21228

def r35866 : Route 9 := (fun mask => (mask,id))

def c35866 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35866 : Upper (D 7) (R 7) [34,260,65,17,192] 13 := by
  apply FastRouting.sound _ _ [34,260,65,17,192] 13 (by decide) (choices 1) [2,8,128] r35866 c35866
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21229
  · exact u21230
  · exact u21231

def b35867 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 35 262 69 26 49 232 200 200 456), lower := (rows 35 262 69 26 49 32 64 128 256), losses := [] }

theorem u35867 : Upper (D 7) (R 7) [34,260,65,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35867 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35868 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 35 262 69 26 56 225 193 193 449), lower := (rows 35 262 69 26 56 32 64 128 256), losses := [] }

theorem u35868 : Upper (D 7) (R 7) [34,260,65,18,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35868 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35869 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 16, targets := 162 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,5),(4,7)], upper := (rows 35 262 69 26 81 168 232 168 424), lower := (rows 35 262 69 26 81 32 64 128 256), losses := [] }

theorem u35869 : Upper (D 7) (R 7) [34,260,65,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35869 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35870 : Route 9 := (fun mask => (mask,id))

def c35870 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35870 : Upper (D 7) (R 7) [34,260,65,18,72] 13 := by
  apply FastRouting.sound _ _ [34,260,65,18,72] 13 (by decide) (choices 1) [1,128] r35870 c35870
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u21232
  · exact u21233

def r35871 : Route 9 := (fun mask => (mask,id))

def c35871 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35871 : Upper (D 7) (R 7) [34,260,65,18,96] 13 := by
  apply FastRouting.sound _ _ [34,260,65,18,96] 13 (by decide) (choices 1) [1,8,128] r35871 c35871
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21234
  · exact u21235
  · exact u21236

def r35872 : Route 9 := (fun mask => (mask,id))

def c35872 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35872 : Upper (D 7) (R 7) [34,260,65,18,129] 13 := by
  apply FastRouting.sound _ _ [34,260,65,18,129] 13 (by decide) (choices 1) [8,64,128] r35872 c35872
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21237
  · exact u21238
  · exact u21239

def r35873 : Route 9 := (fun mask => (mask,id))

def c35873 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35873 : Upper (D 7) (R 7) [34,260,65,18,136] 13 := by
  apply FastRouting.sound _ _ [34,260,65,18,136] 13 (by decide) (choices 1) [1,64,128] r35873 c35873
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21240
  · exact u21241
  · exact u21242

def r35874 : Route 9 := (fun mask => (mask,id))

def c35874 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35874 : Upper (D 7) (R 7) [34,260,65,18,160] 13 := by
  apply FastRouting.sound _ _ [34,260,65,18,160] 13 (by decide) (choices 1) [1,8,64,128] r35874 c35874
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21243
  · exact u21244
  · exact u21245
  · exact u21246

def r35875 : Route 9 := (fun mask => (mask,id))

def c35875 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35875 : Upper (D 7) (R 7) [34,260,65,18,192] 13 := by
  apply FastRouting.sound _ _ [34,260,65,18,192] 13 (by decide) (choices 1) [1,8,128] r35875 c35875
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21247
  · exact u21248
  · exact u21249

def b35876 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 35 262 69 41 82 184 216 152 408), lower := (rows 35 262 69 41 82 32 64 128 256), losses := [] }

theorem u35876 : Upper (D 7) (R 7) [34,260,65,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35876 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35877 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 35 262 69 41 88 178 210 146 402), lower := (rows 35 262 69 41 88 32 64 128 256), losses := [] }

theorem u35877 : Upper (D 7) (R 7) [34,260,65,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35877 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35878 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 35 262 69 41 146 248 216 216 472), lower := (rows 35 262 69 41 146 32 64 128 256), losses := [] }

theorem u35878 : Upper (D 7) (R 7) [34,260,65,33,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35878 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35879 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 35 262 69 41 152 242 210 210 466), lower := (rows 35 262 69 41 152 32 64 128 256), losses := [] }

theorem u35879 : Upper (D 7) (R 7) [34,260,65,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35879 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u35879
end Delivery.IrregularNine14.P07

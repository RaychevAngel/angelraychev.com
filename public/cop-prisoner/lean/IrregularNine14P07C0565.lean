import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0302
import IrregularNine14P07C0303
import IrregularNine14P07C0304

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r33900 : Route 9 := (fun mask => (mask,id))

def c33900 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33900 : Upper (D 7) (R 7) [34,65,9,288,68] 13 := by
  apply FastRouting.sound _ _ [34,65,9,288,68] 13 (by decide) (choices 1) [2,16,128] r33900 c33900
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18139
  · exact u18140
  · exact u18141

def r33901 : Route 9 := (fun mask => (mask,id))

def c33901 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 256 => 8 | _ => 0)

theorem u33901 : Upper (D 7) (R 7) [34,65,9,288,130] 13 := by
  apply FastRouting.sound _ _ [34,65,9,288,130] 13 (by decide) (choices 1) [4,16,64,128] r33901 c33901
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18142
  · exact u18143
  · exact u18144
  · exact u18145

def r33902 : Route 9 := (fun mask => (mask,id))

def c33902 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u33902 : Upper (D 7) (R 7) [34,65,9,288,132] 13 := by
  apply FastRouting.sound _ _ [34,65,9,288,132] 13 (by decide) (choices 1) [2,16,64,128] r33902 c33902
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18146
  · exact u18147
  · exact u18148
  · exact u18149

def r33903 : Route 9 := (fun mask => (mask,id))

def c33903 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33903 : Upper (D 7) (R 7) [34,65,9,288,192] 13 := by
  apply FastRouting.sound _ _ [34,65,9,288,192] 13 (by decide) (choices 1) [2,4,16,128] r33903 c33903
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18150
  · exact u18151
  · exact u18152
  · exact u18153

def b33904 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 16, targets := 192 },{ cop := 4, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(4,6),(4,7)], upper := (rows 35 67 13 328 50 180 212 148 404), lower := (rows 35 67 13 328 50 32 64 128 256), losses := [] }

theorem u33904 : Upper (D 7) (R 7) [34,65,9,320,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33904 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33905 : Route 9 := (fun mask => (mask,id))

def c33905 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33905 : Upper (D 7) (R 7) [34,65,9,320,36] 13 := by
  apply FastRouting.sound _ _ [34,65,9,320,36] 13 (by decide) (choices 1) [2,16,128] r33905 c33905
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18154
  · exact u18155
  · exact u18156

def r33906 : Route 9 := (fun mask => (mask,id))

def c33906 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33906 : Upper (D 7) (R 7) [34,65,9,320,130] 13 := by
  apply FastRouting.sound _ _ [34,65,9,320,130] 13 (by decide) (choices 1) [4,16,128] r33906 c33906
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18157
  · exact u18158
  · exact u18159

def r33907 : Route 9 := (fun mask => (mask,id))

def c33907 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33907 : Upper (D 7) (R 7) [34,65,9,320,132] 13 := by
  apply FastRouting.sound _ _ [34,65,9,320,132] 13 (by decide) (choices 1) [2,16,128] r33907 c33907
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18160
  · exact u18161
  · exact u18162

def r33908 : Route 9 := (fun mask => (mask,id))

def c33908 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33908 : Upper (D 7) (R 7) [34,65,9,320,160] 13 := by
  apply FastRouting.sound _ _ [34,65,9,320,160] 13 (by decide) (choices 1) [2,4,16,128] r33908 c33908
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18163
  · exact u18164
  · exact u18165
  · exact u18166

def b33909 : PairBound 9 := { available := 212, camps := [{ cop := 0, region := 16, targets := 192 },{ cop := 4, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(4,6),(4,7)], upper := (rows 35 67 13 392 50 244 212 212 468), lower := (rows 35 67 13 392 50 32 64 128 256), losses := [] }

theorem u33909 : Upper (D 7) (R 7) [34,65,9,384,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33909 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33910 : Route 9 := (fun mask => (mask,id))

def c33910 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u33910 : Upper (D 7) (R 7) [34,65,9,384,36] 13 := by
  apply FastRouting.sound _ _ [34,65,9,384,36] 13 (by decide) (choices 1) [2,16,64,128] r33910 c33910
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18167
  · exact u18168
  · exact u18169
  · exact u18170

def b33911 : PairBound 9 := { available := 180, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 35 67 13 392 82 180 244 180 436), lower := (rows 35 67 13 392 82 32 64 128 256), losses := [] }

theorem u33911 : Upper (D 7) (R 7) [34,65,9,384,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33911 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33912 : Route 9 := (fun mask => (mask,id))

def c33912 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33912 : Upper (D 7) (R 7) [34,65,9,384,68] 13 := by
  apply FastRouting.sound _ _ [34,65,9,384,68] 13 (by decide) (choices 1) [2,16,128] r33912 c33912
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18171
  · exact u18172
  · exact u18173

def r33913 : Route 9 := (fun mask => (mask,id))

def c33913 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33913 : Upper (D 7) (R 7) [34,65,9,384,96] 13 := by
  apply FastRouting.sound _ _ [34,65,9,384,96] 13 (by decide) (choices 1) [2,4,16,128] r33913 c33913
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18174
  · exact u18175
  · exact u18176
  · exact u18177

def r33914 : Route 9 := (fun mask => (mask,id))

def c33914 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33914 : Upper (D 7) (R 7) [34,65,9,384,130] 13 := by
  apply FastRouting.sound _ _ [34,65,9,384,130] 13 (by decide) (choices 1) [4,16,64] r33914 c33914
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18178
  · exact u18179
  · exact u18180

def r33915 : Route 9 := (fun mask => (mask,id))

def c33915 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33915 : Upper (D 7) (R 7) [34,65,9,384,132] 13 := by
  apply FastRouting.sound _ _ [34,65,9,384,132] 13 (by decide) (choices 1) [2,16,64] r33915 c33915
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18181
  · exact u18182
  · exact u18183

def r33916 : Route 9 := (fun mask => (mask,id))

def c33916 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33916 : Upper (D 7) (R 7) [34,65,9,384,160] 13 := by
  apply FastRouting.sound _ _ [34,65,9,384,160] 13 (by decide) (choices 1) [2,4,16,64] r33916 c33916
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18184
  · exact u18185
  · exact u18186
  · exact u18187

def r33917 : Route 9 := (fun mask => (mask,id))

def c33917 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33917 : Upper (D 7) (R 7) [34,65,9,384,192] 13 := by
  apply FastRouting.sound _ _ [34,65,9,384,192] 13 (by decide) (choices 1) [2,4,16] r33917 c33917
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18188
  · exact u18189
  · exact u18190

def b33918 : PairBound 9 := { available := 386, camps := [{ cop := 3, region := 470, targets := 32 },{ cop := 0, region := 8, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 35 67 28 41 84 418 450 386 386), lower := (rows 35 67 28 41 84 32 64 128 256), losses := [] }

theorem u33918 : Upper (D 7) (R 7) [34,65,24,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33918 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33919 : PairBound 9 := { available := 452, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 35 67 28 41 146 484 452 452 452), lower := (rows 35 67 28 41 146 32 64 128 256), losses := [] }

theorem u33919 : Upper (D 7) (R 7) [34,65,24,33,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33919 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33920 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 450, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 35 67 28 41 148 482 450 450 450), lower := (rows 35 67 28 41 148 32 64 128 256), losses := [] }

theorem u33920 : Upper (D 7) (R 7) [34,65,24,33,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33920 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33921 : PairBound 9 := { available := 390, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 35 67 28 41 208 422 454 390 390), lower := (rows 35 67 28 41 208 32 64 128 256), losses := [] }

theorem u33921 : Upper (D 7) (R 7) [34,65,24,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33921 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33922 : PairBound 9 := { available := 196, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 35 67 28 41 274 228 196 196 452), lower := (rows 35 67 28 41 274 32 64 128 256), losses := [] }

theorem u33922 : Upper (D 7) (R 7) [34,65,24,33,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33922 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33923 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 194, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 35 67 28 41 276 226 194 194 450), lower := (rows 35 67 28 41 276 32 64 128 256), losses := [] }

theorem u33923 : Upper (D 7) (R 7) [34,65,24,33,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33923 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33924 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 35 67 28 41 336 166 198 134 390), lower := (rows 35 67 28 41 336 32 64 128 256), losses := [] }

theorem u33924 : Upper (D 7) (R 7) [34,65,24,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33924 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33925 : PairBound 9 := { available := 198, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 35 67 28 41 400 230 198 198 454), lower := (rows 35 67 28 41 400 32 64 128 256), losses := [] }

theorem u33925 : Upper (D 7) (R 7) [34,65,24,33,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33925 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33926 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 425, targets := 64 },{ cop := 0, region := 8, targets := 1 },{ cop := 0, region := 450, targets := 32 }], pairs := [(0,6),(1,5),(3,0),(3,6)], upper := (rows 35 67 28 42 84 417 449 385 385), lower := (rows 35 67 28 42 84 32 64 128 256), losses := [] }

theorem u33926 : Upper (D 7) (R 7) [34,65,24,34,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33926 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33927 : PairBound 9 := { available := 452, camps := [{ cop := 0, region := 8, targets := 192 },{ cop := 3, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 67 28 42 145 484 452 452 452), lower := (rows 35 67 28 42 145 32 64 128 256), losses := [] }

theorem u33927 : Upper (D 7) (R 7) [34,65,24,34,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33927 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33928 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 8, targets := 192 },{ cop := 3, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 67 28 42 148 481 449 449 449), lower := (rows 35 67 28 42 148 32 64 128 256), losses := [] }

theorem u33928 : Upper (D 7) (R 7) [34,65,24,34,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33928 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33929 : PairBound 9 := { available := 389, camps := [{ cop := 0, region := 8, targets := 192 },{ cop := 3, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 67 28 42 208 421 453 389 389), lower := (rows 35 67 28 42 208 32 64 128 256), losses := [] }

theorem u33929 : Upper (D 7) (R 7) [34,65,24,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33929 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33930 : PairBound 9 := { available := 196, camps := [{ cop := 0, region := 8, targets := 192 },{ cop := 3, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 67 28 42 273 228 196 196 452), lower := (rows 35 67 28 42 273 32 64 128 256), losses := [] }

theorem u33930 : Upper (D 7) (R 7) [34,65,24,34,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33930 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33931 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 8, targets := 192 },{ cop := 3, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 67 28 42 276 225 193 193 449), lower := (rows 35 67 28 42 276 32 64 128 256), losses := [] }

theorem u33931 : Upper (D 7) (R 7) [34,65,24,34,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33931 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33932 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 8, targets := 192 },{ cop := 3, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 67 28 42 336 165 197 133 389), lower := (rows 35 67 28 42 336 32 64 128 256), losses := [] }

theorem u33932 : Upper (D 7) (R 7) [34,65,24,34,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33932 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33933 : PairBound 9 := { available := 197, camps := [{ cop := 0, region := 8, targets := 192 },{ cop := 3, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 67 28 42 400 229 197 197 453), lower := (rows 35 67 28 42 400 32 64 128 256), losses := [] }

theorem u33933 : Upper (D 7) (R 7) [34,65,24,34,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33933 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33934 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5),(2,0),(3,0),(4,5)], upper := (rows 35 67 28 44 145 482 450 450 450), lower := (rows 35 67 28 44 145 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 35 67 131 259), good := (rows 482 482 28 44 508 32 64 128 256) }] }

theorem u33934 : Upper (D 7) (R 7) [34,65,24,36,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33934 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33935 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5),(2,1),(3,1),(4,5)], upper := (rows 35 67 28 44 146 481 449 449 449), lower := (rows 35 67 28 44 146 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 24 16 35 67 131 259), good := (rows 481 481 28 44 508 32 64 128 256) }] }

theorem u33935 : Upper (D 7) (R 7) [34,65,24,36,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33935 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33936 : Route 9 := (fun mask => (mask,id))

def c33936 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u33936 : Upper (D 7) (R 7) [34,65,24,36,192] 13 := by
  apply FastRouting.sound _ _ [34,65,24,36,192] 13 (by decide) (choices 1) [1,2,128,256] r33936 c33936
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18191
  · exact u18192
  · exact u18193
  · exact u18194

def b33937 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5),(2,0),(3,0),(4,5)], upper := (rows 35 67 28 44 273 226 194 194 450), lower := (rows 35 67 28 44 273 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 35 67 131 259), good := (rows 482 482 28 44 508 32 64 128 256) }] }

theorem u33937 : Upper (D 7) (R 7) [34,65,24,36,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33937 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33938 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5),(2,1),(3,1),(4,5)], upper := (rows 35 67 28 44 274 225 193 193 449), lower := (rows 35 67 28 44 274 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 24 16 35 67 131 259), good := (rows 481 481 28 44 508 32 64 128 256) }] }

theorem u33938 : Upper (D 7) (R 7) [34,65,24,36,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33938 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33939 : Route 9 := (fun mask => (mask,id))

def c33939 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33939 : Upper (D 7) (R 7) [34,65,24,36,320] 13 := by
  apply FastRouting.sound _ _ [34,65,24,36,320] 13 (by decide) (choices 1) [1,2,128] r33939 c33939
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18195
  · exact u18196
  · exact u18197

def r33940 : Route 9 := (fun mask => (mask,id))

def c33940 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33940 : Upper (D 7) (R 7) [34,65,24,36,384] 13 := by
  apply FastRouting.sound _ _ [34,65,24,36,384] 13 (by decide) (choices 1) [1,2,64,128] r33940 c33940
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18198
  · exact u18199
  · exact u18200
  · exact u18201

def r33941 : Route 9 := (fun mask => (mask,id))

def c33941 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u33941 : Upper (D 7) (R 7) [34,65,24,96,129] 13 := by
  apply FastRouting.sound _ _ [34,65,24,96,129] 13 (by decide) (choices 1) [2,4,128,256] r33941 c33941
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18202
  · exact u18203
  · exact u18204
  · exact u18205

def b33942 : PairBound 9 := { available := 387, camps := [{ cop := 3, region := 3, targets := 128 },{ cop := 0, region := 450, targets := 32 },{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6),(0,7),(1,5),(1,7)], upper := (rows 35 67 28 104 148 419 451 387 387), lower := (rows 35 67 28 104 148 32 64 128 256), losses := [] }

theorem u33942 : Upper (D 7) (R 7) [34,65,24,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33942 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33943 : Route 9 := (fun mask => (mask,id))

def c33943 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33943 : Upper (D 7) (R 7) [34,65,24,96,257] 13 := by
  apply FastRouting.sound _ _ [34,65,24,96,257] 13 (by decide) (choices 1) [2,4,128] r33943 c33943
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18206
  · exact u18207
  · exact u18208

def b33944 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 3, targets := 128 },{ cop := 0, region := 194, targets := 32 },{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6),(0,7),(1,5),(1,7)], upper := (rows 35 67 28 104 276 163 195 131 387), lower := (rows 35 67 28 104 276 32 64 128 256), losses := [] }

theorem u33944 : Upper (D 7) (R 7) [34,65,24,96,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33944 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33945 : Route 9 := (fun mask => (mask,id))

def c33945 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33945 : Upper (D 7) (R 7) [34,65,24,96,384] 13 := by
  apply FastRouting.sound _ _ [34,65,24,96,384] 13 (by decide) (choices 1) [1,2,4,128] r33945 c33945
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18209
  · exact u18210
  · exact u18211
  · exact u18212

def r33946 : Route 9 := (fun mask => (mask,id))

def c33946 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u33946 : Upper (D 7) (R 7) [34,65,24,129,130] 13 := by
  apply FastRouting.sound _ _ [34,65,24,129,130] 13 (by decide) (choices 1) [4,64,256] r33946 c33946
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18213
  · exact u18214
  · exact u18215

def b33947 : PairBound 9 := { available := 354, camps := [{ cop := 3, region := 20, targets := 99 }], pairs := [(2,0),(2,1),(2,5),(2,6)], upper := (rows 35 67 28 137 148 354 354 482 354), lower := (rows 35 67 28 137 148 32 64 128 256), losses := [] }

theorem u33947 : Upper (D 7) (R 7) [34,65,24,129,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33947 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33948 : Route 9 := (fun mask => (mask,id))

def c33948 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u33948 : Upper (D 7) (R 7) [34,65,24,129,160] 13 := by
  apply FastRouting.sound _ _ [34,65,24,129,160] 13 (by decide) (choices 1) [2,4,64,256] r33948 c33948
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18216
  · exact u18217
  · exact u18218
  · exact u18219

def r33949 : Route 9 := (fun mask => (mask,id))

def c33949 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u33949 : Upper (D 7) (R 7) [34,65,24,129,192] 13 := by
  apply FastRouting.sound _ _ [34,65,24,129,192] 13 (by decide) (choices 1) [2,4,256] r33949 c33949
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18220
  · exact u18221
  · exact u18222

def r33950 : Route 9 := (fun mask => (mask,id))

def c33950 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33950 : Upper (D 7) (R 7) [34,65,24,129,258] 13 := by
  apply FastRouting.sound _ _ [34,65,24,129,258] 13 (by decide) (choices 1) [4,64,128] r33950 c33950
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18223
  · exact u18224
  · exact u18225

def r33951 : Route 9 := (fun mask => (mask,id))

def c33951 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33951 : Upper (D 7) (R 7) [34,65,24,129,260] 13 := by
  apply FastRouting.sound _ _ [34,65,24,129,260] 13 (by decide) (choices 1) [2,64,128] r33951 c33951
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18226
  · exact u18227
  · exact u18228

def r33952 : Route 9 := (fun mask => (mask,id))

def c33952 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33952 : Upper (D 7) (R 7) [34,65,24,129,288] 13 := by
  apply FastRouting.sound _ _ [34,65,24,129,288] 13 (by decide) (choices 1) [2,4,64,128] r33952 c33952
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18229
  · exact u18230
  · exact u18231
  · exact u18232

def r33953 : Route 9 := (fun mask => (mask,id))

def c33953 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33953 : Upper (D 7) (R 7) [34,65,24,129,320] 13 := by
  apply FastRouting.sound _ _ [34,65,24,129,320] 13 (by decide) (choices 1) [2,4,128] r33953 c33953
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18233
  · exact u18234
  · exact u18235

def r33954 : Route 9 := (fun mask => (mask,id))

def c33954 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33954 : Upper (D 7) (R 7) [34,65,24,129,384] 13 := by
  apply FastRouting.sound _ _ [34,65,24,129,384] 13 (by decide) (choices 1) [2,4,64] r33954 c33954
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18236
  · exact u18237
  · exact u18238

def b33955 : PairBound 9 := { available := 323, camps := [{ cop := 4, region := 12, targets := 99 }], pairs := [(2,0),(2,1),(2,5),(2,6)], upper := (rows 35 67 28 140 176 355 323 451 323), lower := (rows 35 67 28 140 176 32 64 128 256), losses := [] }

theorem u33955 : Upper (D 7) (R 7) [34,65,24,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33955 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33956 : Route 9 := (fun mask => (mask,id))

def c33956 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33956 : Upper (D 7) (R 7) [34,65,24,132,257] 13 := by
  apply FastRouting.sound _ _ [34,65,24,132,257] 13 (by decide) (choices 1) [2,64,128] r33956 c33956
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18239
  · exact u18240
  · exact u18241

def r33957 : Route 9 := (fun mask => (mask,id))

def c33957 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33957 : Upper (D 7) (R 7) [34,65,24,132,288] 13 := by
  apply FastRouting.sound _ _ [34,65,24,132,288] 13 (by decide) (choices 1) [1,2,64,128] r33957 c33957
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18242
  · exact u18243
  · exact u18244
  · exact u18245

def b33958 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 12, targets := 99 }], pairs := [(2,0),(2,1),(2,5),(2,6)], upper := (rows 35 67 28 140 400 99 99 227 355), lower := (rows 35 67 28 140 400 32 64 128 256), losses := [] }

theorem u33958 : Upper (D 7) (R 7) [34,65,24,132,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33958 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33959 : Route 9 := (fun mask => (mask,id))

def c33959 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u33959 : Upper (D 7) (R 7) [34,65,24,160,192] 13 := by
  apply FastRouting.sound _ _ [34,65,24,160,192] 13 (by decide) (choices 1) [1,2,4,256] r33959 c33959
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18246
  · exact u18247
  · exact u18248
  · exact u18249

#print axioms u33959
end Delivery.IrregularNine14.P07

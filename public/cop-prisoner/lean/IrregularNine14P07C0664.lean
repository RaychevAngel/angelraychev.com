import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0469
import IrregularNine14P07C0470

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b39840 : PairBound 9 := { available := 323, camps := [{ cop := 1, region := 16, targets := 97 },{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7),(4,0),(4,5),(4,6)], upper := (rows 97 162 13 28 146 355 323 451 323), lower := (rows 97 162 13 28 146 32 64 128 256), losses := [] }

theorem u39840 : Upper (D 7) (R 7) [96,160,9,20,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39840 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39841 : Route 9 := (fun mask => (mask,id))

def c39841 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u39841 : Upper (D 7) (R 7) [96,160,9,20,192] 13 := by
  apply FastRouting.sound _ _ [96,160,9,20,192] 13 (by decide) (choices 1) [1,2,256] r39841 c39841
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28144
  · exact u28145
  · exact u28146

def b39842 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 12, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 97 162 13 28 273 226 194 194 450), lower := (rows 97 162 13 28 273 32 64 128 256), losses := [] }

theorem u39842 : Upper (D 7) (R 7) [96,160,9,20,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39842 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39843 : Route 9 := (fun mask => (mask,id))

def c39843 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39843 : Upper (D 7) (R 7) [96,160,9,20,258] 13 := by
  apply FastRouting.sound _ _ [96,160,9,20,258] 13 (by decide) (choices 1) [1,2,64,128] r39843 c39843
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28147
  · exact u28148
  · exact u28149
  · exact u28150

def r39844 : Route 9 := (fun mask => (mask,id))

def c39844 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39844 : Upper (D 7) (R 7) [96,160,9,20,320] 13 := by
  apply FastRouting.sound _ _ [96,160,9,20,320] 13 (by decide) (choices 1) [1,2,128] r39844 c39844
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28151
  · exact u28152
  · exact u28153

def r39845 : Route 9 := (fun mask => (mask,id))

def c39845 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39845 : Upper (D 7) (R 7) [96,160,9,20,384] 13 := by
  apply FastRouting.sound _ _ [96,160,9,20,384] 13 (by decide) (choices 1) [1,2,64] r39845 c39845
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28154
  · exact u28155
  · exact u28156

def b39846 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 12, targets := 162 }], pairs := [(2,1),(2,5),(2,7),(3,1)], upper := (rows 97 162 13 73 148 306 338 402 274), lower := (rows 97 162 13 73 148 32 64 128 256), losses := [] }

theorem u39846 : Upper (D 7) (R 7) [96,160,9,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39846 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39847 : PairBound 9 := { available := 150, camps := [{ cop := 0, region := 12, targets := 162 }], pairs := [(2,1),(2,5),(2,7),(3,1)], upper := (rows 97 162 13 73 274 182 214 150 406), lower := (rows 97 162 13 73 274 32 64 128 256), losses := [] }

theorem u39847 : Upper (D 7) (R 7) [96,160,9,65,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39847 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39848 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 12, targets := 162 }], pairs := [(2,1),(2,5),(2,7),(3,1)], upper := (rows 97 162 13 73 276 178 210 146 402), lower := (rows 97 162 13 73 276 32 64 128 256), losses := [] }

theorem u39848 : Upper (D 7) (R 7) [96,160,9,65,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39848 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39849 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 12, targets := 162 }], pairs := [(2,1),(2,5),(2,7),(3,1)], upper := (rows 97 162 13 73 400 54 86 150 278), lower := (rows 97 162 13 73 400 32 64 128 256), losses := [] }

theorem u39849 : Upper (D 7) (R 7) [96,160,9,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39849 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39850 : Route 9 := (fun mask => (mask,id))

def c39850 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u39850 : Upper (D 7) (R 7) [96,160,9,66,129] 13 := by
  apply FastRouting.sound _ _ [96,160,9,66,129] 13 (by decide) (choices 1) [2,4,16,256] r39850 c39850
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28157
  · exact u28158
  · exact u28159
  · exact u28160

def b39851 : PairBound 9 := { available := 277, camps := [{ cop := 1, region := 16, targets := 97 },{ cop := 4, region := 365, targets := 128 }], pairs := [(0,7),(4,0),(4,5),(4,6)], upper := (rows 97 162 13 74 146 309 341 405 277), lower := (rows 97 162 13 74 146 32 64 128 256), losses := [] }

theorem u39851 : Upper (D 7) (R 7) [96,160,9,66,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39851 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39852 : Route 9 := (fun mask => (mask,id))

def c39852 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u39852 : Upper (D 7) (R 7) [96,160,9,66,132] 13 := by
  apply FastRouting.sound _ _ [96,160,9,66,132] 13 (by decide) (choices 1) [1,2,16,256] r39852 c39852
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28161
  · exact u28162
  · exact u28163
  · exact u28164

def r39853 : Route 9 := (fun mask => (mask,id))

def c39853 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39853 : Upper (D 7) (R 7) [96,160,9,66,257] 13 := by
  apply FastRouting.sound _ _ [96,160,9,66,257] 13 (by decide) (choices 1) [2,4,16,128] r39853 c39853
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28165
  · exact u28166
  · exact u28167
  · exact u28168

def r39854 : Route 9 := (fun mask => (mask,id))

def c39854 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39854 : Upper (D 7) (R 7) [96,160,9,66,258] 13 := by
  apply FastRouting.sound _ _ [96,160,9,66,258] 13 (by decide) (choices 1) [1,4,16,128] r39854 c39854
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28169
  · exact u28170
  · exact u28171
  · exact u28172

def r39855 : Route 9 := (fun mask => (mask,id))

def c39855 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39855 : Upper (D 7) (R 7) [96,160,9,66,260] 13 := by
  apply FastRouting.sound _ _ [96,160,9,66,260] 13 (by decide) (choices 1) [1,2,16,128] r39855 c39855
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28173
  · exact u28174
  · exact u28175
  · exact u28176

def r39856 : Route 9 := (fun mask => (mask,id))

def c39856 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39856 : Upper (D 7) (R 7) [96,160,9,66,384] 13 := by
  apply FastRouting.sound _ _ [96,160,9,66,384] 13 (by decide) (choices 1) [1,2,4,16] r39856 c39856
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28177
  · exact u28178
  · exact u28179
  · exact u28180

def b39857 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 12, targets := 162 }], pairs := [(2,1),(2,5),(2,7),(3,1)], upper := (rows 97 162 13 76 145 306 338 402 274), lower := (rows 97 162 13 76 145 32 64 128 256), losses := [] }

theorem u39857 : Upper (D 7) (R 7) [96,160,9,68,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39857 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39858 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 12, targets := 162 }], pairs := [(2,1),(2,5),(2,7),(3,1)], upper := (rows 97 162 13 76 273 178 210 146 402), lower := (rows 97 162 13 76 273 32 64 128 256), losses := [] }

theorem u39858 : Upper (D 7) (R 7) [96,160,9,68,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39858 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39859 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 12, targets := 162 }], pairs := [(2,1),(2,5),(2,7),(3,1)], upper := (rows 97 162 13 76 274 179 211 147 403), lower := (rows 97 162 13 76 274 32 64 128 256), losses := [] }

theorem u39859 : Upper (D 7) (R 7) [96,160,9,68,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39859 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39860 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 12, targets := 162 }], pairs := [(2,1),(2,5),(2,7),(3,1)], upper := (rows 97 162 13 76 400 51 83 147 275), lower := (rows 97 162 13 76 400 32 64 128 256), losses := [] }

theorem u39860 : Upper (D 7) (R 7) [96,160,9,68,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39860 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39861 : Route 9 := (fun mask => (mask,id))

def c39861 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u39861 : Upper (D 7) (R 7) [96,160,9,80,129] 13 := by
  apply FastRouting.sound _ _ [96,160,9,80,129] 13 (by decide) (choices 1) [2,4,256] r39861 c39861
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28181
  · exact u28182
  · exact u28183

def b39862 : PairBound 9 := { available := 263, camps := [{ cop := 1, region := 16, targets := 97 },{ cop := 4, region := 365, targets := 128 }], pairs := [(0,7),(4,0),(4,5),(4,6)], upper := (rows 97 162 13 88 146 295 327 391 263), lower := (rows 97 162 13 88 146 32 64 128 256), losses := [] }

theorem u39862 : Upper (D 7) (R 7) [96,160,9,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39862 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39863 : Route 9 := (fun mask => (mask,id))

def c39863 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u39863 : Upper (D 7) (R 7) [96,160,9,80,132] 13 := by
  apply FastRouting.sound _ _ [96,160,9,80,132] 13 (by decide) (choices 1) [1,2,256] r39863 c39863
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28184
  · exact u28185
  · exact u28186

def r39864 : Route 9 := (fun mask => (mask,id))

def c39864 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39864 : Upper (D 7) (R 7) [96,160,9,80,257] 13 := by
  apply FastRouting.sound _ _ [96,160,9,80,257] 13 (by decide) (choices 1) [2,4,128] r39864 c39864
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28187
  · exact u28188
  · exact u28189

def r39865 : Route 9 := (fun mask => (mask,id))

def c39865 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39865 : Upper (D 7) (R 7) [96,160,9,80,258] 13 := by
  apply FastRouting.sound _ _ [96,160,9,80,258] 13 (by decide) (choices 1) [1,2,4,128] r39865 c39865
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28190
  · exact u28191
  · exact u28192
  · exact u28193

def r39866 : Route 9 := (fun mask => (mask,id))

def c39866 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39866 : Upper (D 7) (R 7) [96,160,9,80,260] 13 := by
  apply FastRouting.sound _ _ [96,160,9,80,260] 13 (by decide) (choices 1) [1,2,128] r39866 c39866
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28194
  · exact u28195
  · exact u28196

def r39867 : Route 9 := (fun mask => (mask,id))

def c39867 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39867 : Upper (D 7) (R 7) [96,160,9,80,384] 13 := by
  apply FastRouting.sound _ _ [96,160,9,80,384] 13 (by decide) (choices 1) [1,2,4] r39867 c39867
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28197
  · exact u28198
  · exact u28199

def b39868 : PairBound 9 := { available := 278, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 97 162 13 137 82 310 342 406 278), lower := (rows 97 162 13 137 82 32 64 128 256), losses := [] }

theorem u39868 : Upper (D 7) (R 7) [96,160,9,129,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39868 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39869 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 97 162 13 137 84 306 338 402 274), lower := (rows 97 162 13 137 84 32 64 128 256), losses := [] }

theorem u39869 : Upper (D 7) (R 7) [96,160,9,129,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39869 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39870 : PairBound 9 := { available := 86, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 97 162 13 137 274 118 86 214 342), lower := (rows 97 162 13 137 274 32 64 128 256), losses := [] }

theorem u39870 : Upper (D 7) (R 7) [96,160,9,129,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39870 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39871 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 97 162 13 137 276 114 82 210 338), lower := (rows 97 162 13 137 276 32 64 128 256), losses := [] }

theorem u39871 : Upper (D 7) (R 7) [96,160,9,129,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39871 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39872 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 97 162 13 137 336 54 86 150 278), lower := (rows 97 162 13 137 336 32 64 128 256), losses := [] }

theorem u39872 : Upper (D 7) (R 7) [96,160,9,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39872 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39873 : PairBound 9 := { available := 277, camps := [{ cop := 1, region := 8, targets := 97 },{ cop := 3, region := 373, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(3,6)], upper := (rows 97 162 13 138 82 309 341 405 277), lower := (rows 97 162 13 138 82 32 64 128 256), losses := [] }

theorem u39873 : Upper (D 7) (R 7) [96,160,9,130,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39873 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39874 : PairBound 9 := { available := 275, camps := [{ cop := 1, region := 8, targets := 97 },{ cop := 3, region := 373, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(3,6)], upper := (rows 97 162 13 138 84 307 339 403 275), lower := (rows 97 162 13 138 84 32 64 128 256), losses := [] }

theorem u39874 : Upper (D 7) (R 7) [96,160,9,130,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39874 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39875 : PairBound 9 := { available := 86, camps := [{ cop := 1, region := 8, targets := 97 },{ cop := 3, region := 373, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(3,6)], upper := (rows 97 162 13 138 273 118 86 214 342), lower := (rows 97 162 13 138 273 32 64 128 256), losses := [] }

theorem u39875 : Upper (D 7) (R 7) [96,160,9,130,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39875 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39876 : PairBound 9 := { available := 85, camps := [{ cop := 1, region := 8, targets := 97 },{ cop := 3, region := 373, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(3,6)], upper := (rows 97 162 13 138 274 117 85 213 341), lower := (rows 97 162 13 138 274 32 64 128 256), losses := [] }

theorem u39876 : Upper (D 7) (R 7) [96,160,9,130,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39876 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39877 : PairBound 9 := { available := 83, camps := [{ cop := 1, region := 8, targets := 97 },{ cop := 3, region := 373, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(3,6)], upper := (rows 97 162 13 138 276 115 83 211 339), lower := (rows 97 162 13 138 276 32 64 128 256), losses := [] }

theorem u39877 : Upper (D 7) (R 7) [96,160,9,130,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39877 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39878 : PairBound 9 := { available := 23, camps := [{ cop := 1, region := 8, targets := 97 },{ cop := 3, region := 373, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(3,6)], upper := (rows 97 162 13 138 336 55 87 151 279), lower := (rows 97 162 13 138 336 32 64 128 256), losses := [] }

theorem u39878 : Upper (D 7) (R 7) [96,160,9,130,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39878 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39879 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 16, targets := 162 },{ cop := 4, region := 418, targets := 64 }], pairs := [(1,6),(4,1),(4,5),(4,7)], upper := (rows 97 162 13 140 81 306 338 402 274), lower := (rows 97 162 13 140 81 32 64 128 256), losses := [] }

theorem u39879 : Upper (D 7) (R 7) [96,160,9,132,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39879 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39880 : Route 9 := (fun mask => (mask,id))

def c39880 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u39880 : Upper (D 7) (R 7) [96,160,9,132,66] 13 := by
  apply FastRouting.sound _ _ [96,160,9,132,66] 13 (by decide) (choices 1) [1,2,16,256] r39880 c39880
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28200
  · exact u28201
  · exact u28202
  · exact u28203

def r39881 : Route 9 := (fun mask => (mask,id))

def c39881 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39881 : Upper (D 7) (R 7) [96,160,9,132,257] 13 := by
  apply FastRouting.sound _ _ [96,160,9,132,257] 13 (by decide) (choices 1) [2,16,64] r39881 c39881
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28204
  · exact u28205
  · exact u28206

def r39882 : Route 9 := (fun mask => (mask,id))

def c39882 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39882 : Upper (D 7) (R 7) [96,160,9,132,258] 13 := by
  apply FastRouting.sound _ _ [96,160,9,132,258] 13 (by decide) (choices 1) [1,2,16,64] r39882 c39882
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28207
  · exact u28208
  · exact u28209
  · exact u28210

def r39883 : Route 9 := (fun mask => (mask,id))

def c39883 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39883 : Upper (D 7) (R 7) [96,160,9,132,320] 13 := by
  apply FastRouting.sound _ _ [96,160,9,132,320] 13 (by decide) (choices 1) [1,2,16] r39883 c39883
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28211
  · exact u28212
  · exact u28213

def b39884 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 16, targets := 162 },{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6),(4,1),(4,5),(4,7)], upper := (rows 97 162 13 152 81 294 326 390 262), lower := (rows 97 162 13 152 81 32 64 128 256), losses := [] }

theorem u39884 : Upper (D 7) (R 7) [96,160,9,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39884 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39885 : Route 9 := (fun mask => (mask,id))

def c39885 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u39885 : Upper (D 7) (R 7) [96,160,9,144,66] 13 := by
  apply FastRouting.sound _ _ [96,160,9,144,66] 13 (by decide) (choices 1) [1,2,4,256] r39885 c39885
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28214
  · exact u28215
  · exact u28216
  · exact u28217

def r39886 : Route 9 := (fun mask => (mask,id))

def c39886 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u39886 : Upper (D 7) (R 7) [96,160,9,144,68] 13 := by
  apply FastRouting.sound _ _ [96,160,9,144,68] 13 (by decide) (choices 1) [1,2,256] r39886 c39886
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28218
  · exact u28219
  · exact u28220

def r39887 : Route 9 := (fun mask => (mask,id))

def c39887 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39887 : Upper (D 7) (R 7) [96,160,9,144,257] 13 := by
  apply FastRouting.sound _ _ [96,160,9,144,257] 13 (by decide) (choices 1) [2,4,64] r39887 c39887
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28221
  · exact u28222
  · exact u28223

def r39888 : Route 9 := (fun mask => (mask,id))

def c39888 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39888 : Upper (D 7) (R 7) [96,160,9,144,258] 13 := by
  apply FastRouting.sound _ _ [96,160,9,144,258] 13 (by decide) (choices 1) [1,2,4,64] r39888 c39888
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28224
  · exact u28225
  · exact u28226
  · exact u28227

def r39889 : Route 9 := (fun mask => (mask,id))

def c39889 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39889 : Upper (D 7) (R 7) [96,160,9,144,260] 13 := by
  apply FastRouting.sound _ _ [96,160,9,144,260] 13 (by decide) (choices 1) [1,2,64] r39889 c39889
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28228
  · exact u28229
  · exact u28230

def r39890 : Route 9 := (fun mask => (mask,id))

def c39890 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39890 : Upper (D 7) (R 7) [96,160,9,144,320] 13 := by
  apply FastRouting.sound _ _ [96,160,9,144,320] 13 (by decide) (choices 1) [1,2,4] r39890 c39890
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28231
  · exact u28232
  · exact u28233

def r39891 : Route 9 := (fun mask => (mask,id))

def c39891 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39891 : Upper (D 7) (R 7) [96,160,9,192,257] 13 := by
  apply FastRouting.sound _ _ [96,160,9,192,257] 13 (by decide) (choices 1) [2,4,16] r39891 c39891
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28234
  · exact u28235
  · exact u28236

def r39892 : Route 9 := (fun mask => (mask,id))

def c39892 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39892 : Upper (D 7) (R 7) [96,160,9,192,258] 13 := by
  apply FastRouting.sound _ _ [96,160,9,192,258] 13 (by decide) (choices 1) [1,2,4,16] r39892 c39892
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28237
  · exact u28238
  · exact u28239
  · exact u28240

def r39893 : Route 9 := (fun mask => (mask,id))

def c39893 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39893 : Upper (D 7) (R 7) [96,160,9,192,260] 13 := by
  apply FastRouting.sound _ _ [96,160,9,192,260] 13 (by decide) (choices 1) [1,2,16] r39893 c39893
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28241
  · exact u28242
  · exact u28243

def b39894 : PairBound 9 := { available := 150, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 97 162 13 265 82 182 214 150 406), lower := (rows 97 162 13 265 82 32 64 128 256), losses := [] }

theorem u39894 : Upper (D 7) (R 7) [96,160,9,257,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39894 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39895 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 97 162 13 265 84 178 210 146 402), lower := (rows 97 162 13 265 84 32 64 128 256), losses := [] }

theorem u39895 : Upper (D 7) (R 7) [96,160,9,257,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39895 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39896 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 97 162 13 265 148 114 82 210 338), lower := (rows 97 162 13 265 148 32 64 128 256), losses := [] }

theorem u39896 : Upper (D 7) (R 7) [96,160,9,257,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39896 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39897 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 97 162 13 265 208 54 86 150 278), lower := (rows 97 162 13 265 208 32 64 128 256), losses := [] }

theorem u39897 : Upper (D 7) (R 7) [96,160,9,257,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39897 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39898 : PairBound 9 := { available := 150, camps := [{ cop := 0, region := 16, targets := 162 },{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6),(4,1),(4,5),(4,7)], upper := (rows 97 162 13 266 81 182 214 150 406), lower := (rows 97 162 13 266 81 32 64 128 256), losses := [] }

theorem u39898 : Upper (D 7) (R 7) [96,160,9,258,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39898 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39899 : Route 9 := (fun mask => (mask,id))

def c39899 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39899 : Upper (D 7) (R 7) [96,160,9,258,66] 13 := by
  apply FastRouting.sound _ _ [96,160,9,258,66] 13 (by decide) (choices 1) [1,4,16,128] r39899 c39899
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28244
  · exact u28245
  · exact u28246
  · exact u28247

#print axioms u39899
end Delivery.IrregularNine14.P07

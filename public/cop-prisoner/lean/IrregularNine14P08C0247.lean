import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0085
import IrregularNine14P08C0086

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b14820 : PairBound 9 := { available := 163, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 261 88 152 163 227 163 419), lower := (rows 97 38 261 88 152 32 64 128 256), losses := [] }

theorem u14820 : Upper (D 8) (R 8) [96,36,257,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14820 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14821 : Route 9 := (fun mask => (mask,id))

def c14821 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14821 : Upper (D 8) (R 8) [96,36,257,80,160] 13 := by
  apply FastRouting.sound _ _ [96,36,257,80,160] 13 (by decide) (choices 1) [1,2,8,128] r14821 c14821
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5157
  · exact u5158
  · exact u5159
  · exact u5160

def b14822 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 38 261 104 145 186 218 154 410), lower := (rows 97 38 261 104 145 32 64 128 256), losses := [] }

theorem u14822 : Upper (D 8) (R 8) [96,36,257,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14822 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14823 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 38 261 104 146 185 217 153 409), lower := (rows 97 38 261 104 146 32 64 128 256), losses := [] }

theorem u14823 : Upper (D 8) (R 8) [96,36,257,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14823 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14824 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 38 261 104 152 179 211 147 403), lower := (rows 97 38 261 104 152 32 64 128 256), losses := [] }

theorem u14824 : Upper (D 8) (R 8) [96,36,257,96,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14824 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14825 : Route 9 := (fun mask => (mask,id))

def c14825 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14825 : Upper (D 8) (R 8) [96,36,257,129,130] 13 := by
  apply FastRouting.sound _ _ [96,36,257,129,130] 13 (by decide) (choices 1) [8,16,64] r14825 c14825
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5161
  · exact u5162
  · exact u5163

def b14826 : PairBound 9 := { available := 114, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 38 261 137 152 114 114 242 370), lower := (rows 97 38 261 137 152 32 64 128 256), losses := [] }

theorem u14826 : Upper (D 8) (R 8) [96,36,257,129,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14826 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14827 : Route 9 := (fun mask => (mask,id))

def c14827 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14827 : Upper (D 8) (R 8) [96,36,257,129,160] 13 := by
  apply FastRouting.sound _ _ [96,36,257,129,160] 13 (by decide) (choices 1) [2,8,16,64] r14827 c14827
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5164
  · exact u5165
  · exact u5166
  · exact u5167

def r14828 : Route 9 := (fun mask => (mask,id))

def c14828 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14828 : Upper (D 8) (R 8) [96,36,257,129,192] 13 := by
  apply FastRouting.sound _ _ [96,36,257,129,192] 13 (by decide) (choices 1) [2,8,16] r14828 c14828
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5168
  · exact u5169
  · exact u5170

def b14829 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 38 261 138 152 113 113 241 369), lower := (rows 97 38 261 138 152 32 64 128 256), losses := [] }

theorem u14829 : Upper (D 8) (R 8) [96,36,257,130,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14829 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14830 : Route 9 := (fun mask => (mask,id))

def c14830 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14830 : Upper (D 8) (R 8) [96,36,257,130,160] 13 := by
  apply FastRouting.sound _ _ [96,36,257,130,160] 13 (by decide) (choices 1) [1,8,16,64] r14830 c14830
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5171
  · exact u5172
  · exact u5173
  · exact u5174

def r14831 : Route 9 := (fun mask => (mask,id))

def c14831 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14831 : Upper (D 8) (R 8) [96,36,257,130,192] 13 := by
  apply FastRouting.sound _ _ [96,36,257,130,192] 13 (by decide) (choices 1) [1,8,16] r14831 c14831
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5175
  · exact u5176
  · exact u5177

def b14832 : PairBound 9 := { available := 99, camps := [{ cop := 7, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 97 38 261 152 152 99 99 227 355), lower := (rows 97 38 261 152 152 32 64 128 256), losses := [] }

theorem u14832 : Upper (D 8) (R 8) [96,36,257,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14832 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14833 : PairBound 9 := { available := 75, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 261 152 176 107 75 203 331), lower := (rows 97 38 261 152 176 32 64 128 256), losses := [] }

theorem u14833 : Upper (D 8) (R 8) [96,36,257,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14833 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14834 : PairBound 9 := { available := 43, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 261 152 208 43 107 171 299), lower := (rows 97 38 261 152 208 32 64 128 256), losses := [] }

theorem u14834 : Upper (D 8) (R 8) [96,36,257,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14834 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14835 : Route 9 := (fun mask => (mask,id))

def c14835 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14835 : Upper (D 8) (R 8) [96,36,257,160,192] 13 := by
  apply FastRouting.sound _ _ [96,36,257,160,192] 13 (by decide) (choices 1) [1,2,8,16] r14835 c14835
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5178
  · exact u5179
  · exact u5180
  · exact u5181

def b14836 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 262 73 145 184 248 184 440), lower := (rows 97 38 262 73 145 32 64 128 256), losses := [] }

theorem u14836 : Upper (D 8) (R 8) [96,36,258,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14836 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14837 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 262 73 152 177 241 177 433), lower := (rows 97 38 262 73 152 32 64 128 256), losses := [] }

theorem u14837 : Upper (D 8) (R 8) [96,36,258,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14837 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14838 : PairBound 9 := { available := 153, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 262 73 176 185 217 153 409), lower := (rows 97 38 262 73 176 32 64 128 256), losses := [] }

theorem u14838 : Upper (D 8) (R 8) [96,36,258,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14838 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14839 : Route 9 := (fun mask => (mask,id))

def c14839 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14839 : Upper (D 8) (R 8) [96,36,258,80,129] 13 := by
  apply FastRouting.sound _ _ [96,36,258,80,129] 13 (by decide) (choices 1) [1,8,128] r14839 c14839
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5182
  · exact u5183
  · exact u5184

def b14840 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 262 88 152 161 225 161 417), lower := (rows 97 38 262 88 152 32 64 128 256), losses := [] }

theorem u14840 : Upper (D 8) (R 8) [96,36,258,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14840 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14841 : Route 9 := (fun mask => (mask,id))

def c14841 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14841 : Upper (D 8) (R 8) [96,36,258,80,160] 13 := by
  apply FastRouting.sound _ _ [96,36,258,80,160] 13 (by decide) (choices 1) [1,8,128] r14841 c14841
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5185
  · exact u5186
  · exact u5187

def b14842 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 38 262 104 145 185 217 153 409), lower := (rows 97 38 262 104 145 32 64 128 256), losses := [] }

theorem u14842 : Upper (D 8) (R 8) [96,36,258,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14842 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14843 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 38 262 104 152 177 209 145 401), lower := (rows 97 38 262 104 152 32 64 128 256), losses := [] }

theorem u14843 : Upper (D 8) (R 8) [96,36,258,96,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14843 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14844 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 97 38 262 137 145 120 120 248 376), lower := (rows 97 38 262 137 145 32 64 128 256), losses := [] }

theorem u14844 : Upper (D 8) (R 8) [96,36,258,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14844 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14845 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 38 262 137 152 113 113 241 369), lower := (rows 97 38 262 137 152 32 64 128 256), losses := [] }

theorem u14845 : Upper (D 8) (R 8) [96,36,258,129,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14845 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14846 : Route 9 := (fun mask => (mask,id))

def c14846 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14846 : Upper (D 8) (R 8) [96,36,258,129,160] 13 := by
  apply FastRouting.sound _ _ [96,36,258,129,160] 13 (by decide) (choices 1) [1,8,16,64] r14846 c14846
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5188
  · exact u5189
  · exact u5190
  · exact u5191

def r14847 : Route 9 := (fun mask => (mask,id))

def c14847 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14847 : Upper (D 8) (R 8) [96,36,258,129,192] 13 := by
  apply FastRouting.sound _ _ [96,36,258,129,192] 13 (by decide) (choices 1) [1,8,16] r14847 c14847
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5192
  · exact u5193
  · exact u5194

def b14848 : PairBound 9 := { available := 97, camps := [{ cop := 7, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 97 38 262 152 152 97 97 225 353), lower := (rows 97 38 262 152 152 32 64 128 256), losses := [] }

theorem u14848 : Upper (D 8) (R 8) [96,36,258,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14848 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14849 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 262 152 176 105 73 201 329), lower := (rows 97 38 262 152 176 32 64 128 256), losses := [] }

theorem u14849 : Upper (D 8) (R 8) [96,36,258,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14849 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14850 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 262 152 208 41 105 169 297), lower := (rows 97 38 262 152 208 32 64 128 256), losses := [] }

theorem u14850 : Upper (D 8) (R 8) [96,36,258,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14850 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14851 : Route 9 := (fun mask => (mask,id))

def c14851 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14851 : Upper (D 8) (R 8) [96,36,258,160,192] 13 := by
  apply FastRouting.sound _ _ [96,36,258,160,192] 13 (by decide) (choices 1) [1,8,16] r14851 c14851
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5195
  · exact u5196
  · exact u5197

def b14852 : PairBound 9 := { available := 178, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 268 73 145 178 242 178 434), lower := (rows 97 38 268 73 145 32 64 128 256), losses := [] }

theorem u14852 : Upper (D 8) (R 8) [96,36,264,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14852 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14853 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 268 73 146 177 241 177 433), lower := (rows 97 38 268 73 146 32 64 128 256), losses := [] }

theorem u14853 : Upper (D 8) (R 8) [96,36,264,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14853 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14854 : PairBound 9 := { available := 147, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 268 73 176 179 211 147 403), lower := (rows 97 38 268 73 176 32 64 128 256), losses := [] }

theorem u14854 : Upper (D 8) (R 8) [96,36,264,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14854 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14855 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 144, targets := 64 }], pairs := [(4,6)], upper := (rows 97 38 268 74 145 177 241 177 433), lower := (rows 97 38 268 74 145 32 64 128 256), losses := [] }

theorem u14855 : Upper (D 8) (R 8) [96,36,264,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14855 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14856 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 144, targets := 64 }], pairs := [(4,6)], upper := (rows 97 38 268 74 176 177 209 145 401), lower := (rows 97 38 268 74 176 32 64 128 256), losses := [] }

theorem u14856 : Upper (D 8) (R 8) [96,36,264,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14856 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14857 : Route 9 := (fun mask => (mask,id))

def c14857 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14857 : Upper (D 8) (R 8) [96,36,264,80,129] 13 := by
  apply FastRouting.sound _ _ [96,36,264,80,129] 13 (by decide) (choices 1) [1,2,128] r14857 c14857
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5198
  · exact u5199
  · exact u5200

def r14858 : Route 9 := (fun mask => (mask,id))

def c14858 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14858 : Upper (D 8) (R 8) [96,36,264,80,130] 13 := by
  apply FastRouting.sound _ _ [96,36,264,80,130] 13 (by decide) (choices 1) [1,128] r14858 c14858
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5201
  · exact u5202

def r14859 : Route 9 := (fun mask => (mask,id))

def c14859 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14859 : Upper (D 8) (R 8) [96,36,264,80,160] 13 := by
  apply FastRouting.sound _ _ [96,36,264,80,160] 13 (by decide) (choices 1) [1,2,128] r14859 c14859
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5203
  · exact u5204
  · exact u5205

def b14860 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 38 268 104 145 179 211 147 403), lower := (rows 97 38 268 104 145 32 64 128 256), losses := [] }

theorem u14860 : Upper (D 8) (R 8) [96,36,264,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14860 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14861 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 38 268 104 146 177 209 145 401), lower := (rows 97 38 268 104 146 32 64 128 256), losses := [] }

theorem u14861 : Upper (D 8) (R 8) [96,36,264,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14861 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14862 : PairBound 9 := { available := 178, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 268 137 81 178 242 178 434), lower := (rows 97 38 268 137 81 32 64 128 256), losses := [] }

theorem u14862 : Upper (D 8) (R 8) [96,36,264,129,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14862 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14863 : Route 9 := (fun mask => (mask,id))

def c14863 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14863 : Upper (D 8) (R 8) [96,36,264,129,66] 13 := by
  apply FastRouting.sound _ _ [96,36,264,129,66] 13 (by decide) (choices 1) [1,16,128] r14863 c14863
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5206
  · exact u5207
  · exact u5208

def b14864 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 38 268 137 112 179 211 147 403), lower := (rows 97 38 268 137 112 32 64 128 256), losses := [] }

theorem u14864 : Upper (D 8) (R 8) [96,36,264,129,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14864 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14865 : PairBound 9 := { available := 114, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 97 38 268 137 145 114 114 242 370), lower := (rows 97 38 268 137 145 32 64 128 256), losses := [] }

theorem u14865 : Upper (D 8) (R 8) [96,36,264,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14865 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14866 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 268 137 146 113 113 241 369), lower := (rows 97 38 268 137 146 32 64 128 256), losses := [] }

theorem u14866 : Upper (D 8) (R 8) [96,36,264,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14866 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14867 : Route 9 := (fun mask => (mask,id))

def c14867 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14867 : Upper (D 8) (R 8) [96,36,264,129,160] 13 := by
  apply FastRouting.sound _ _ [96,36,264,129,160] 13 (by decide) (choices 1) [1,2,16,64] r14867 c14867
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5209
  · exact u5210
  · exact u5211
  · exact u5212

def r14868 : Route 9 := (fun mask => (mask,id))

def c14868 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14868 : Upper (D 8) (R 8) [96,36,264,129,192] 13 := by
  apply FastRouting.sound _ _ [96,36,264,129,192] 13 (by decide) (choices 1) [1,2,16] r14868 c14868
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5213
  · exact u5214
  · exact u5215

def b14869 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 268 138 81 177 241 177 433), lower := (rows 97 38 268 138 81 32 64 128 256), losses := [] }

theorem u14869 : Upper (D 8) (R 8) [96,36,264,130,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14869 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14870 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 38 268 138 112 177 209 145 401), lower := (rows 97 38 268 138 112 32 64 128 256), losses := [] }

theorem u14870 : Upper (D 8) (R 8) [96,36,264,130,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14870 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14871 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 268 138 145 113 113 241 369), lower := (rows 97 38 268 138 145 32 64 128 256), losses := [] }

theorem u14871 : Upper (D 8) (R 8) [96,36,264,130,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14871 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14872 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 268 138 176 113 81 209 337), lower := (rows 97 38 268 138 176 32 64 128 256), losses := [] }

theorem u14872 : Upper (D 8) (R 8) [96,36,264,130,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14872 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14873 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 268 138 208 49 113 177 305), lower := (rows 97 38 268 138 208 32 64 128 256), losses := [] }

theorem u14873 : Upper (D 8) (R 8) [96,36,264,130,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14873 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14874 : PairBound 9 := { available := 163, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 268 152 81 163 227 163 419), lower := (rows 97 38 268 152 81 32 64 128 256), losses := [] }

theorem u14874 : Upper (D 8) (R 8) [96,36,264,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14874 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14875 : Route 9 := (fun mask => (mask,id))

def c14875 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14875 : Upper (D 8) (R 8) [96,36,264,144,66] 13 := by
  apply FastRouting.sound _ _ [96,36,264,144,66] 13 (by decide) (choices 1) [1,128] r14875 c14875
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5216
  · exact u5217

def b14876 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 38 268 152 112 163 195 131 387), lower := (rows 97 38 268 152 112 32 64 128 256), losses := [] }

theorem u14876 : Upper (D 8) (R 8) [96,36,264,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14876 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14877 : PairBound 9 := { available := 99, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 268 152 145 99 99 227 355), lower := (rows 97 38 268 152 145 32 64 128 256), losses := [] }

theorem u14877 : Upper (D 8) (R 8) [96,36,264,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14877 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14878 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 268 152 146 97 97 225 353), lower := (rows 97 38 268 152 146 32 64 128 256), losses := [] }

theorem u14878 : Upper (D 8) (R 8) [96,36,264,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14878 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14879 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 268 152 176 99 67 195 323), lower := (rows 97 38 268 152 176 32 64 128 256), losses := [] }

theorem u14879 : Upper (D 8) (R 8) [96,36,264,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14879 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u14879
end Delivery.IrregularNine14.P08

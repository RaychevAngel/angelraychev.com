import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0354
import IrregularNine14P07C0355

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b35880 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 35 262 69 41 208 186 218 154 410), lower := (rows 35 262 69 41 208 32 64 128 256), losses := [] }

theorem u35880 : Upper (D 7) (R 7) [34,260,65,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35880 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35881 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 8, targets := 192 },{ cop := 3, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 262 69 42 88 177 209 145 401), lower := (rows 35 262 69 42 88 32 64 128 256), losses := [] }

theorem u35881 : Upper (D 7) (R 7) [34,260,65,34,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35881 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35882 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 8, targets := 192 },{ cop := 3, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 262 69 42 145 248 216 216 472), lower := (rows 35 262 69 42 145 32 64 128 256), losses := [] }

theorem u35882 : Upper (D 7) (R 7) [34,260,65,34,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35882 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35883 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 8, targets := 192 },{ cop := 3, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 262 69 42 152 241 209 209 465), lower := (rows 35 262 69 42 152 32 64 128 256), losses := [] }

theorem u35883 : Upper (D 7) (R 7) [34,260,65,34,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35883 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35884 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 8, targets := 192 },{ cop := 3, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 262 69 42 208 185 217 153 409), lower := (rows 35 262 69 42 208 32 64 128 256), losses := [] }

theorem u35884 : Upper (D 7) (R 7) [34,260,65,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35884 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35885 : PairBound 9 := { available := 138, camps := [{ cop := 2, region := 16, targets := 162 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,5),(4,7)], upper := (rows 35 262 69 56 81 170 202 138 394), lower := (rows 35 262 69 56 81 32 64 128 256), losses := [] }

theorem u35885 : Upper (D 7) (R 7) [34,260,65,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35885 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35886 : Route 9 := (fun mask => (mask,id))

def c35886 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35886 : Upper (D 7) (R 7) [34,260,65,48,66] 13 := by
  apply FastRouting.sound _ _ [34,260,65,48,66] 13 (by decide) (choices 1) [1,8,128] r35886 c35886
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21250
  · exact u21251
  · exact u21252

def b35887 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,5),(1,6),(2,5)], upper := (rows 35 262 69 56 88 163 195 131 387), lower := (rows 35 262 69 56 88 32 64 128 256), losses := [] }

theorem u35887 : Upper (D 7) (R 7) [34,260,65,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35887 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35888 : Route 9 := (fun mask => (mask,id))

def c35888 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35888 : Upper (D 7) (R 7) [34,260,65,48,129] 13 := by
  apply FastRouting.sound _ _ [34,260,65,48,129] 13 (by decide) (choices 1) [2,8,64,128] r35888 c35888
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21253
  · exact u21254
  · exact u21255
  · exact u21256

def r35889 : Route 9 := (fun mask => (mask,id))

def c35889 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35889 : Upper (D 7) (R 7) [34,260,65,48,130] 13 := by
  apply FastRouting.sound _ _ [34,260,65,48,130] 13 (by decide) (choices 1) [1,8,64,128] r35889 c35889
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21257
  · exact u21258
  · exact u21259
  · exact u21260

def r35890 : Route 9 := (fun mask => (mask,id))

def c35890 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35890 : Upper (D 7) (R 7) [34,260,65,48,136] 13 := by
  apply FastRouting.sound _ _ [34,260,65,48,136] 13 (by decide) (choices 1) [1,2,64,128] r35890 c35890
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21261
  · exact u21262
  · exact u21263
  · exact u21264

def r35891 : Route 9 := (fun mask => (mask,id))

def c35891 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35891 : Upper (D 7) (R 7) [34,260,65,48,192] 13 := by
  apply FastRouting.sound _ _ [34,260,65,48,192] 13 (by decide) (choices 1) [1,2,8,128] r35891 c35891
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21265
  · exact u21266
  · exact u21267
  · exact u21268

def b35892 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 8, targets := 162 },{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1),(3,1),(3,5),(3,7)], upper := (rows 35 262 69 73 146 184 248 184 440), lower := (rows 35 262 69 73 146 32 64 128 256), losses := [] }

theorem u35892 : Upper (D 7) (R 7) [34,260,65,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35892 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35893 : PairBound 9 := { available := 178, camps := [{ cop := 2, region := 8, targets := 162 },{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1),(3,1),(3,5),(3,7)], upper := (rows 35 262 69 73 152 178 242 178 434), lower := (rows 35 262 69 73 152 32 64 128 256), losses := [] }

theorem u35893 : Upper (D 7) (R 7) [34,260,65,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35893 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35894 : PairBound 9 := { available := 154, camps := [{ cop := 2, region := 8, targets := 162 },{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1),(3,1),(3,5),(3,7)], upper := (rows 35 262 69 73 176 186 218 154 410), lower := (rows 35 262 69 73 176 32 64 128 256), losses := [] }

theorem u35894 : Upper (D 7) (R 7) [34,260,65,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35894 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35895 : Route 9 := (fun mask => (mask,id))

def c35895 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35895 : Upper (D 7) (R 7) [34,260,65,66,129] 13 := by
  apply FastRouting.sound _ _ [34,260,65,66,129] 13 (by decide) (choices 1) [8,16,128] r35895 c35895
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21269
  · exact u21270
  · exact u21271

def r35896 : Route 9 := (fun mask => (mask,id))

def c35896 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35896 : Upper (D 7) (R 7) [34,260,65,66,136] 13 := by
  apply FastRouting.sound _ _ [34,260,65,66,136] 13 (by decide) (choices 1) [1,16,128] r35896 c35896
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21272
  · exact u21273
  · exact u21274

def r35897 : Route 9 := (fun mask => (mask,id))

def c35897 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35897 : Upper (D 7) (R 7) [34,260,65,66,160] 13 := by
  apply FastRouting.sound _ _ [34,260,65,66,160] 13 (by decide) (choices 1) [1,8,16,128] r35897 c35897
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21275
  · exact u21276
  · exact u21277
  · exact u21278

def r35898 : Route 9 := (fun mask => (mask,id))

def c35898 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35898 : Upper (D 7) (R 7) [34,260,65,80,129] 13 := by
  apply FastRouting.sound _ _ [34,260,65,80,129] 13 (by decide) (choices 1) [2,8,128] r35898 c35898
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21279
  · exact u21280
  · exact u21281

def r35899 : Route 9 := (fun mask => (mask,id))

def c35899 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35899 : Upper (D 7) (R 7) [34,260,65,80,130] 13 := by
  apply FastRouting.sound _ _ [34,260,65,80,130] 13 (by decide) (choices 1) [1,8,128] r35899 c35899
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21282
  · exact u21283
  · exact u21284

def r35900 : Route 9 := (fun mask => (mask,id))

def c35900 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35900 : Upper (D 7) (R 7) [34,260,65,80,136] 13 := by
  apply FastRouting.sound _ _ [34,260,65,80,136] 13 (by decide) (choices 1) [1,2,128] r35900 c35900
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21285
  · exact u21286
  · exact u21287

def r35901 : Route 9 := (fun mask => (mask,id))

def c35901 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35901 : Upper (D 7) (R 7) [34,260,65,80,160] 13 := by
  apply FastRouting.sound _ _ [34,260,65,80,160] 13 (by decide) (choices 1) [1,2,8,128] r35901 c35901
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21288
  · exact u21289
  · exact u21290
  · exact u21291

def r35902 : Route 9 := (fun mask => (mask,id))

def c35902 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35902 : Upper (D 7) (R 7) [34,260,65,96,129] 13 := by
  apply FastRouting.sound _ _ [34,260,65,96,129] 13 (by decide) (choices 1) [2,8,16,128] r35902 c35902
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21292
  · exact u21293
  · exact u21294
  · exact u21295

def r35903 : Route 9 := (fun mask => (mask,id))

def c35903 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35903 : Upper (D 7) (R 7) [34,260,65,96,130] 13 := by
  apply FastRouting.sound _ _ [34,260,65,96,130] 13 (by decide) (choices 1) [1,8,16,128] r35903 c35903
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21296
  · exact u21297
  · exact u21298
  · exact u21299

def r35904 : Route 9 := (fun mask => (mask,id))

def c35904 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35904 : Upper (D 7) (R 7) [34,260,65,96,136] 13 := by
  apply FastRouting.sound _ _ [34,260,65,96,136] 13 (by decide) (choices 1) [1,2,16,128] r35904 c35904
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21300
  · exact u21301
  · exact u21302
  · exact u21303

def r35905 : Route 9 := (fun mask => (mask,id))

def c35905 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35905 : Upper (D 7) (R 7) [34,260,65,129,130] 13 := by
  apply FastRouting.sound _ _ [34,260,65,129,130] 13 (by decide) (choices 1) [8,16,64] r35905 c35905
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21304
  · exact u21305
  · exact u21306

def b35906 : PairBound 9 := { available := 114, camps := [{ cop := 3, region := 16, targets := 99 }], pairs := [(4,0),(4,1),(4,5),(4,6)], upper := (rows 35 262 69 137 152 114 114 242 370), lower := (rows 35 262 69 137 152 32 64 128 256), losses := [] }

theorem u35906 : Upper (D 7) (R 7) [34,260,65,129,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35906 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35907 : Route 9 := (fun mask => (mask,id))

def c35907 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35907 : Upper (D 7) (R 7) [34,260,65,129,160] 13 := by
  apply FastRouting.sound _ _ [34,260,65,129,160] 13 (by decide) (choices 1) [2,8,16,64] r35907 c35907
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21307
  · exact u21308
  · exact u21309
  · exact u21310

def r35908 : Route 9 := (fun mask => (mask,id))

def c35908 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35908 : Upper (D 7) (R 7) [34,260,65,129,192] 13 := by
  apply FastRouting.sound _ _ [34,260,65,129,192] 13 (by decide) (choices 1) [2,8,16] r35908 c35908
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21311
  · exact u21312
  · exact u21313

def b35909 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 16, targets := 99 }], pairs := [(4,0),(4,1),(4,5),(4,6)], upper := (rows 35 262 69 138 152 113 113 241 369), lower := (rows 35 262 69 138 152 32 64 128 256), losses := [] }

theorem u35909 : Upper (D 7) (R 7) [34,260,65,130,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35909 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35910 : Route 9 := (fun mask => (mask,id))

def c35910 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35910 : Upper (D 7) (R 7) [34,260,65,130,160] 13 := by
  apply FastRouting.sound _ _ [34,260,65,130,160] 13 (by decide) (choices 1) [1,8,16,64] r35910 c35910
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21314
  · exact u21315
  · exact u21316
  · exact u21317

def r35911 : Route 9 := (fun mask => (mask,id))

def c35911 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35911 : Upper (D 7) (R 7) [34,260,65,130,192] 13 := by
  apply FastRouting.sound _ _ [34,260,65,130,192] 13 (by decide) (choices 1) [1,8,16] r35911 c35911
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21318
  · exact u21319
  · exact u21320

def b35912 : PairBound 9 := { available := 99, camps := [{ cop := 7, region := 24, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 262 69 152 152 99 99 227 355), lower := (rows 35 262 69 152 152 32 64 128 256), losses := [] }

theorem u35912 : Upper (D 7) (R 7) [34,260,65,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35912 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35913 : PairBound 9 := { available := 75, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 262 69 152 176 107 75 203 331), lower := (rows 35 262 69 152 176 32 64 128 256), losses := [] }

theorem u35913 : Upper (D 7) (R 7) [34,260,65,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35913 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35914 : PairBound 9 := { available := 43, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 262 69 152 208 43 107 171 299), lower := (rows 35 262 69 152 208 32 64 128 256), losses := [] }

theorem u35914 : Upper (D 7) (R 7) [34,260,65,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35914 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35915 : Route 9 := (fun mask => (mask,id))

def c35915 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35915 : Upper (D 7) (R 7) [34,260,65,160,192] 13 := by
  apply FastRouting.sound _ _ [34,260,65,160,192] 13 (by decide) (choices 1) [1,2,8,16] r35915 c35915
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21321
  · exact u21322
  · exact u21323
  · exact u21324

def b35916 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 24, targets := 224 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 35 262 70 25 25 224 224 224 480), lower := (rows 35 262 70 25 25 32 64 128 256), losses := [] }

theorem u35916 : Upper (D 7) (R 7) [34,260,66,17,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35916 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35917 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 35 262 70 25 49 232 200 200 456), lower := (rows 35 262 70 25 49 32 64 128 256), losses := [] }

theorem u35917 : Upper (D 7) (R 7) [34,260,66,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35917 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35918 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 35 262 70 25 56 225 193 193 449), lower := (rows 35 262 70 25 56 32 64 128 256), losses := [] }

theorem u35918 : Upper (D 7) (R 7) [34,260,66,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35918 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35919 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 3, region := 486, targets := 1 }], pairs := [(1,0),(2,0),(3,1),(4,1)], upper := (rows 35 262 70 25 81 168 232 168 424), lower := (rows 35 262 70 25 81 32 64 128 256), losses := [] }

theorem u35919 : Upper (D 7) (R 7) [34,260,66,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35919 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35920 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,6),(3,1),(4,1)], upper := (rows 35 262 70 25 88 161 225 161 417), lower := (rows 35 262 70 25 88 32 64 128 256), losses := [] }

theorem u35920 : Upper (D 7) (R 7) [34,260,66,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35920 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35921 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5),(2,5),(3,1),(4,1)], upper := (rows 35 262 70 25 112 169 201 137 393), lower := (rows 35 262 70 25 112 32 64 128 256), losses := [] }

theorem u35921 : Upper (D 7) (R 7) [34,260,66,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35921 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35922 : PairBound 9 := { available := 232, camps := [{ cop := 4, region := 8, targets := 224 },{ cop := 0, region := 216, targets := 2 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 35 262 70 25 145 232 232 232 488), lower := (rows 35 262 70 25 145 32 64 128 256), losses := [] }

theorem u35922 : Upper (D 7) (R 7) [34,260,66,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35922 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35923 : Route 9 := (fun mask => (mask,id))

def c35923 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35923 : Upper (D 7) (R 7) [34,260,66,17,136] 13 := by
  apply FastRouting.sound _ _ [34,260,66,17,136] 13 (by decide) (choices 1) [1,64,128] r35923 c35923
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21325
  · exact u21326
  · exact u21327

def b35924 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5),(2,5),(3,1),(4,1)], upper := (rows 35 262 70 25 176 233 201 201 457), lower := (rows 35 262 70 25 176 32 64 128 256), losses := [] }

theorem u35924 : Upper (D 7) (R 7) [34,260,66,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35924 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35925 : Route 9 := (fun mask => (mask,id))

def c35925 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35925 : Upper (D 7) (R 7) [34,260,66,17,192] 13 := by
  apply FastRouting.sound _ _ [34,260,66,17,192] 13 (by decide) (choices 1) [1,8,128] r35925 c35925
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21328
  · exact u21329
  · exact u21330

def b35926 : PairBound 9 := { available := 152, camps := [{ cop := 3, region := 470, targets := 32 },{ cop := 0, region := 8, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 35 262 70 41 81 184 216 152 408), lower := (rows 35 262 70 41 81 32 64 128 256), losses := [] }

theorem u35926 : Upper (D 7) (R 7) [34,260,66,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35926 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35927 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 470, targets := 32 },{ cop := 0, region := 8, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 35 262 70 41 88 177 209 145 401), lower := (rows 35 262 70 41 88 32 64 128 256), losses := [] }

theorem u35927 : Upper (D 7) (R 7) [34,260,66,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35927 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35928 : PairBound 9 := { available := 216, camps := [{ cop := 3, region := 470, targets := 32 },{ cop := 0, region := 8, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 35 262 70 41 145 248 216 216 472), lower := (rows 35 262 70 41 145 32 64 128 256), losses := [] }

theorem u35928 : Upper (D 7) (R 7) [34,260,66,33,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35928 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35929 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 470, targets := 32 },{ cop := 0, region := 8, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 35 262 70 41 152 241 209 209 465), lower := (rows 35 262 70 41 152 32 64 128 256), losses := [] }

theorem u35929 : Upper (D 7) (R 7) [34,260,66,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35929 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35930 : PairBound 9 := { available := 153, camps := [{ cop := 3, region := 470, targets := 32 },{ cop := 0, region := 8, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 35 262 70 41 208 185 217 153 409), lower := (rows 35 262 70 41 208 32 64 128 256), losses := [] }

theorem u35930 : Upper (D 7) (R 7) [34,260,66,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35930 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35931 : Route 9 := (fun mask => (mask,id))

def c35931 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35931 : Upper (D 7) (R 7) [34,260,66,48,65] 13 := by
  apply FastRouting.sound _ _ [34,260,66,48,65] 13 (by decide) (choices 1) [1,8,128] r35931 c35931
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21331
  · exact u21332
  · exact u21333

def b35932 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5),(3,1),(4,1)], upper := (rows 35 262 70 56 88 161 193 129 385), lower := (rows 35 262 70 56 88 32 64 128 256), losses := [] }

theorem u35932 : Upper (D 7) (R 7) [34,260,66,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35932 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35933 : Route 9 := (fun mask => (mask,id))

def c35933 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35933 : Upper (D 7) (R 7) [34,260,66,48,129] 13 := by
  apply FastRouting.sound _ _ [34,260,66,48,129] 13 (by decide) (choices 1) [1,8,64,128] r35933 c35933
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21334
  · exact u21335
  · exact u21336
  · exact u21337

def b35934 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5),(3,1),(4,1)], upper := (rows 35 262 70 56 152 225 193 193 449), lower := (rows 35 262 70 56 152 32 64 128 256), losses := [] }

theorem u35934 : Upper (D 7) (R 7) [34,260,66,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35934 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35935 : Route 9 := (fun mask => (mask,id))

def c35935 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35935 : Upper (D 7) (R 7) [34,260,66,48,192] 13 := by
  apply FastRouting.sound _ _ [34,260,66,48,192] 13 (by decide) (choices 1) [1,8,128] r35935 c35935
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21338
  · exact u21339
  · exact u21340

def r35936 : Route 9 := (fun mask => (mask,id))

def c35936 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35936 : Upper (D 7) (R 7) [34,260,66,65,129] 13 := by
  apply FastRouting.sound _ _ [34,260,66,65,129] 13 (by decide) (choices 1) [8,16,128] r35936 c35936
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21341
  · exact u21342
  · exact u21343

def r35937 : Route 9 := (fun mask => (mask,id))

def c35937 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35937 : Upper (D 7) (R 7) [34,260,66,65,136] 13 := by
  apply FastRouting.sound _ _ [34,260,66,65,136] 13 (by decide) (choices 1) [1,16,128] r35937 c35937
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21344
  · exact u21345
  · exact u21346

def r35938 : Route 9 := (fun mask => (mask,id))

def c35938 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35938 : Upper (D 7) (R 7) [34,260,66,65,160] 13 := by
  apply FastRouting.sound _ _ [34,260,66,65,160] 13 (by decide) (choices 1) [1,8,16,128] r35938 c35938
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21347
  · exact u21348
  · exact u21349
  · exact u21350

def r35939 : Route 9 := (fun mask => (mask,id))

def c35939 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35939 : Upper (D 7) (R 7) [34,260,66,80,129] 13 := by
  apply FastRouting.sound _ _ [34,260,66,80,129] 13 (by decide) (choices 1) [1,8,128] r35939 c35939
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21351
  · exact u21352
  · exact u21353

#print axioms u35939
end Delivery.IrregularNine14.P07

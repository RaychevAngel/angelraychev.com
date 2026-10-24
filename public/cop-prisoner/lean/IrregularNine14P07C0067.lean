import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0004
import IrregularNine14P07C0005

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4020 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 66, targets := 129 },{ cop := 4, region := 72, targets := 33 }], pairs := [(1,0),(1,7),(3,0),(3,5)], upper := (rows 13 98 52 200 146 33 66 385 257), lower := (rows 13 98 52 200 146 33 66 128 256), losses := [] }

theorem u4020 : Upper (D 7) (R 7) [12,96,48,192,130,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4020 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r4021 : Route 9 := (fun mask => (mask,id))

def c4021 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4021 : Upper (D 7) (R 7) [12,96,48,192,130,1,256] 13 := by
  apply FastRouting.sound _ _ [12,96,48,192,130,1,256] 13 (by decide) (choices 1) [1,2] r4021 c4021
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u296
  · exact u297

def r4022 : Route 9 := (fun mask => (mask,id))

def c4022 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4022 : Upper (D 7) (R 7) [12,96,48,192,130,256,1] 13 := by
  apply FastRouting.sound _ _ [12,96,48,192,130,256,1] 13 (by decide) (choices 1) [1,2] r4022 c4022
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u298
  · exact u299

def b4023 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 66, targets := 129 },{ cop := 4, region := 72, targets := 1 }], pairs := [(1,0),(1,7),(3,0)], upper := (rows 13 98 52 200 146 288 66 129 257), lower := (rows 13 98 52 200 146 288 66 128 256), losses := [] }

theorem u4023 : Upper (D 7) (R 7) [12,96,48,192,130,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4023 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4024 : PairBound 9 := { available := 2, camps := [{ cop := 6, region := 170, targets := 1 },{ cop := 1, region := 136, targets := 32 }], pairs := [(1,0),(2,0),(3,0),(3,5)], upper := (rows 13 98 52 200 273 160 65 130 258), lower := (rows 13 98 52 200 273 160 65 128 256), losses := [{ target := 0, region := (rows 0 74 20 74 16 251 64 203 331), good := (rows 430 490 52 490 436 160 490 160 256) }] }

theorem u4024 : Upper (D 7) (R 7) [12,96,48,192,257,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4024 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4025 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 66, targets := 129 },{ cop := 5, region := 74, targets := 1 }], pairs := [(1,0),(1,7),(3,0),(4,7)], upper := (rows 13 98 52 200 273 160 66 131 259), lower := (rows 13 98 52 200 273 160 66 128 256), losses := [{ target := 7, region := (rows 1 38 4 8 17 32 103 0 257), good := (rows 351 98 118 72 337 98 66 0 256) }] }

theorem u4025 : Upper (D 7) (R 7) [12,96,48,192,257,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4025 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4026 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 1, region := 136, targets := 32 }], pairs := [(2,0),(3,0),(3,5),(4,0)], upper := (rows 13 98 52 200 274 33 65 130 386), lower := (rows 13 98 52 200 274 33 65 128 256), losses := [] }

theorem u4026 : Upper (D 7) (R 7) [12,96,48,192,258,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4026 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4027 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 66, targets := 129 }], pairs := [(0,1),(1,0),(1,7),(2,1)], upper := (rows 13 98 52 200 274 33 66 129 385), lower := (rows 13 98 52 200 274 33 66 128 256), losses := [{ target := 1, region := (rows 17 0 20 10 16 53 64 181 309), good := (rows 429 488 437 200 445 417 72 128 256) }] }

theorem u4027 : Upper (D 7) (R 7) [12,96,48,192,258,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4027 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4028 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 98 52 200 274 33 192 131 259), lower := (rows 13 98 52 200 274 33 192 128 256), losses := [] }

theorem u4028 : Upper (D 7) (R 7) [12,96,48,192,258,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4028 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r4029 : Route 9 := (fun mask => (mask,id))

def c4029 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4029 : Upper (D 7) (R 7) [12,96,48,192,258,128,1] 13 := by
  apply FastRouting.sound _ _ [12,96,48,192,258,128,1] 13 (by decide) (choices 1) [1,2] r4029 c4029
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u300
  · exact u301

def b4030 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 66, targets := 129 },{ cop := 5, region := 74, targets := 1 }], pairs := [(0,5),(1,0),(1,7),(3,0)], upper := (rows 13 98 52 200 274 160 66 129 257), lower := (rows 13 98 52 200 274 160 66 128 256), losses := [{ target := 5, region := (rows 5 2 4 12 16 0 82 133 261), good := (rows 397 66 477 200 338 128 66 128 256) }] }

theorem u4030 : Upper (D 7) (R 7) [12,96,48,192,258,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4030 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4031 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 4, region := 109, targets := 2 }], pairs := [(0,1),(2,0),(3,0),(4,0)], upper := (rows 13 98 52 200 400 33 65 130 258), lower := (rows 13 98 52 200 400 33 65 128 256), losses := [] }

theorem u4031 : Upper (D 7) (R 7) [12,96,48,192,384,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4031 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r4032 : Route 9 := (fun mask => (mask,id))

def c4032 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4032 : Upper (D 7) (R 7) [12,96,48,192,384,1,2] 13 := by
  apply FastRouting.sound _ _ [12,96,48,192,384,1,2] 13 (by decide) (choices 1) [1,2] r4032 c4032
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u302
  · exact u303

def r4033 : Route 9 := (fun mask => (mask,id))

def c4033 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4033 : Upper (D 7) (R 7) [12,96,48,192,384,2,1] 13 := by
  apply FastRouting.sound _ _ [12,96,48,192,384,2,1] 13 (by decide) (choices 1) [1,2] r4033 c4033
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u304
  · exact u305

def b4034 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 413, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 13 98 52 200 400 34 66 129 257), lower := (rows 13 98 52 200 400 34 66 128 256), losses := [] }

theorem u4034 : Upper (D 7) (R 7) [12,96,48,192,384,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4034 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4035 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 166, targets := 1 },{ cop := 2, region := 66, targets := 128 }], pairs := [(0,5),(1,0),(1,7),(2,0)], upper := (rows 13 98 52 265 81 160 66 130 386), lower := (rows 13 98 52 265 81 160 66 128 256), losses := [{ target := 5, region := (rows 5 2 4 24 16 0 66 194 322), good := (rows 13 450 29 265 473 128 450 128 256) }] }

theorem u4035 : Upper (D 7) (R 7) [12,96,48,257,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4035 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4036 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 13 98 52 265 81 160 192 130 258), lower := (rows 13 98 52 265 81 160 192 128 256), losses := [] }

theorem u4036 : Upper (D 7) (R 7) [12,96,48,257,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4036 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4037 : PairBound 9 := { available := 192, camps := [{ cop := 6, region := 426, targets := 1 },{ cop := 1, region := 392, targets := 32 },{ cop := 4, region := 228, targets := 2 }], pairs := [(1,0),(2,1),(3,0),(3,5)], upper := (rows 13 98 52 266 19 160 65 192 448), lower := (rows 13 98 52 266 19 160 65 128 256), losses := [] }

theorem u4037 : Upper (D 7) (R 7) [12,96,48,258,3,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4037 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4038 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 13 98 52 266 19 160 192 193 321), lower := (rows 13 98 52 266 19 160 192 128 256), losses := [] }

theorem u4038 : Upper (D 7) (R 7) [12,96,48,258,3,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4038 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4039 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 80, targets := 162 },{ cop := 4, region := 162, targets := 1 }], pairs := [(1,0),(4,1),(4,5),(4,7)], upper := (rows 13 98 52 266 81 160 65 130 386), lower := (rows 13 98 52 266 81 160 65 128 256), losses := [] }

theorem u4039 : Upper (D 7) (R 7) [12,96,48,258,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4039 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4040 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 66, targets := 129 },{ cop := 4, region := 164, targets := 66 }], pairs := [(1,0),(1,7),(2,1),(2,6)], upper := (rows 13 98 52 266 81 160 66 129 385), lower := (rows 13 98 52 266 81 160 66 128 256), losses := [] }

theorem u4040 : Upper (D 7) (R 7) [12,96,48,258,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4040 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4041 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 13 98 52 266 81 160 192 131 259), lower := (rows 13 98 52 266 81 160 192 128 256), losses := [] }

theorem u4041 : Upper (D 7) (R 7) [12,96,48,258,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4041 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4042 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 1, region := 392, targets := 32 }], pairs := [(2,0),(3,0),(3,5),(4,0)], upper := (rows 13 98 52 266 146 33 65 192 448), lower := (rows 13 98 52 266 146 33 65 128 256), losses := [] }

theorem u4042 : Upper (D 7) (R 7) [12,96,48,258,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4042 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r4043 : Route 9 := (fun mask => (mask,id))

def c4043 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4043 : Upper (D 7) (R 7) [12,96,48,258,130,1,128] 13 := by
  apply FastRouting.sound _ _ [12,96,48,258,130,1,128] 13 (by decide) (choices 1) [1,64] r4043 c4043
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u306
  · exact u307

def b4044 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 1, region := 392, targets := 32 }], pairs := [(2,0),(3,0),(3,5),(4,0)], upper := (rows 13 98 52 266 208 33 65 130 386), lower := (rows 13 98 52 266 208 33 65 128 256), losses := [] }

theorem u4044 : Upper (D 7) (R 7) [12,96,48,258,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4044 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4045 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 66, targets := 129 }], pairs := [(0,1),(1,0),(1,7),(2,1)], upper := (rows 13 98 52 266 208 33 66 129 385), lower := (rows 13 98 52 266 208 33 66 128 256), losses := [{ target := 1, region := (rows 9 0 14 8 18 41 64 169 297), good := (rows 429 500 436 445 208 417 84 128 256) }] }

theorem u4045 : Upper (D 7) (R 7) [12,96,48,258,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4045 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4046 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 98 52 266 208 33 192 131 259), lower := (rows 13 98 52 266 208 33 192 128 256), losses := [] }

theorem u4046 : Upper (D 7) (R 7) [12,96,48,258,192,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4046 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4047 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 164, targets := 65 },{ cop := 6, region := 426, targets := 1 }], pairs := [(1,0),(2,0),(2,6),(3,0)], upper := (rows 13 98 52 328 19 160 65 130 386), lower := (rows 13 98 52 328 19 160 65 128 256), losses := [] }

theorem u4047 : Upper (D 7) (R 7) [12,96,48,320,3,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4047 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4048 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 66, targets := 129 },{ cop := 4, region := 164, targets := 66 }], pairs := [(1,0),(1,7),(2,1),(2,6)], upper := (rows 13 98 52 328 19 160 66 129 385), lower := (rows 13 98 52 328 19 160 66 128 256), losses := [] }

theorem u4048 : Upper (D 7) (R 7) [12,96,48,320,3,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4048 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4049 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 13 98 52 328 19 160 192 131 259), lower := (rows 13 98 52 328 19 160 192 128 256), losses := [] }

theorem u4049 : Upper (D 7) (R 7) [12,96,48,320,3,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4049 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4050 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 1, region := 392, targets := 32 }], pairs := [(2,0),(3,0),(3,5),(4,0)], upper := (rows 13 98 52 328 146 33 65 130 386), lower := (rows 13 98 52 328 146 33 65 128 256), losses := [] }

theorem u4050 : Upper (D 7) (R 7) [12,96,48,320,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4050 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4051 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 66, targets := 129 }], pairs := [(0,1),(1,0),(1,7),(2,1)], upper := (rows 13 98 52 328 146 33 66 129 385), lower := (rows 13 98 52 328 146 33 66 128 256), losses := [{ target := 1, region := (rows 17 0 20 10 16 53 64 181 309), good := (rows 429 488 437 328 445 417 72 128 256) }] }

theorem u4051 : Upper (D 7) (R 7) [12,96,48,320,130,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4051 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r4052 : Route 9 := (fun mask => (mask,id))

def c4052 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4052 : Upper (D 7) (R 7) [12,96,48,320,130,1,128] 13 := by
  apply FastRouting.sound _ _ [12,96,48,320,130,1,128] 13 (by decide) (choices 1) [1,2] r4052 c4052
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u308
  · exact u309

def b4053 : PairBound 9 := { available := 2, camps := [{ cop := 0, region := 80, targets := 162 },{ cop := 4, region := 162, targets := 1 }], pairs := [(1,0),(4,1),(4,5),(4,7)], upper := (rows 13 98 52 392 81 160 65 130 258), lower := (rows 13 98 52 392 81 160 65 128 256), losses := [] }

theorem u4053 : Upper (D 7) (R 7) [12,96,48,384,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4053 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r4054 : Route 9 := (fun mask => (mask,id))

def c4054 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4054 : Upper (D 7) (R 7) [12,96,48,384,65,128,2] 13 := by
  apply FastRouting.sound _ _ [12,96,48,384,65,128,2] 13 (by decide) (choices 1) [1,2] r4054 c4054
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u310
  · exact u311

def b4055 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 102, targets := 128 },{ cop := 6, region := 426, targets := 1 }], pairs := [(1,0),(1,7),(2,7),(3,0)], upper := (rows 13 98 52 392 145 34 65 194 322), lower := (rows 13 98 52 392 145 34 65 128 256), losses := [] }

theorem u4055 : Upper (D 7) (R 7) [12,96,48,384,129,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4055 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4056 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 413, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 13 98 52 392 145 34 66 193 321), lower := (rows 13 98 52 392 145 34 66 128 256), losses := [] }

theorem u4056 : Upper (D 7) (R 7) [12,96,48,384,129,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4056 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4057 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 1, region := 392, targets := 32 }], pairs := [(2,0),(3,0),(3,5),(4,0)], upper := (rows 13 98 52 392 146 33 65 194 322), lower := (rows 13 98 52 392 146 33 65 128 256), losses := [] }

theorem u4057 : Upper (D 7) (R 7) [12,96,48,384,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4057 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4058 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 66, targets := 129 }], pairs := [(0,5),(1,0),(1,7),(3,5)], upper := (rows 13 98 52 392 146 33 66 193 321), lower := (rows 13 98 52 392 146 33 66 128 256), losses := [{ target := 5, region := (rows 5 2 4 13 16 0 82 132 260), good := (rows 397 66 477 392 210 9 66 128 256) }] }

theorem u4058 : Upper (D 7) (R 7) [12,96,48,384,130,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4058 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4059 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 3, region := 117, targets := 2 }], pairs := [(0,1),(2,0),(3,0),(4,0)], upper := (rows 13 98 52 392 208 33 65 130 258), lower := (rows 13 98 52 392 208 33 65 128 256), losses := [] }

theorem u4059 : Upper (D 7) (R 7) [12,96,48,384,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4059 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r4060 : Route 9 := (fun mask => (mask,id))

def c4060 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4060 : Upper (D 7) (R 7) [12,96,48,384,192,1,2] 13 := by
  apply FastRouting.sound _ _ [12,96,48,384,192,1,2] 13 (by decide) (choices 1) [1,2] r4060 c4060
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u312
  · exact u313

def b4061 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 397, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 13 98 133 265 146 34 80 224 352), lower := (rows 13 98 133 265 146 34 80 128 256), losses := [] }

theorem u4061 : Upper (D 7) (R 7) [12,96,129,257,130,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4061 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4062 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5),(4,5)], upper := (rows 13 98 133 265 146 34 96 208 336), lower := (rows 13 98 133 265 146 34 96 128 256), losses := [] }

theorem u4062 : Upper (D 7) (R 7) [12,96,129,257,130,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4062 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4063 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 413, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 13 98 133 265 176 34 66 208 336), lower := (rows 13 98 133 265 176 34 66 128 256), losses := [] }

theorem u4063 : Upper (D 7) (R 7) [12,96,129,257,160,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4063 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4064 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 397, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 13 98 133 265 176 34 80 194 322), lower := (rows 13 98 133 265 176 34 80 128 256), losses := [] }

theorem u4064 : Upper (D 7) (R 7) [12,96,129,257,160,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4064 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4065 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 1, region := 264, targets := 128 }], pairs := [(1,0),(3,0),(3,7)], upper := (rows 13 98 133 266 19 48 192 224 352), lower := (rows 13 98 133 266 19 48 192 128 256), losses := [] }

theorem u4065 : Upper (D 7) (R 7) [12,96,129,258,3,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4065 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4066 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 133 266 19 96 192 176 304), lower := (rows 13 98 133 266 19 96 192 128 256), losses := [] }

theorem u4066 : Upper (D 7) (R 7) [12,96,129,258,3,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4066 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4067 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 13 98 133 266 146 33 80 224 352), lower := (rows 13 98 133 266 146 33 80 128 256), losses := [] }

theorem u4067 : Upper (D 7) (R 7) [12,96,129,258,130,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4067 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4068 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5),(4,5)], upper := (rows 13 98 133 266 146 33 96 208 336), lower := (rows 13 98 133 266 146 33 96 128 256), losses := [] }

theorem u4068 : Upper (D 7) (R 7) [12,96,129,258,130,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4068 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4069 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 397, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 13 98 133 266 146 48 96 193 321), lower := (rows 13 98 133 266 146 48 96 128 256), losses := [] }

theorem u4069 : Upper (D 7) (R 7) [12,96,129,258,130,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4069 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4070 : PairBound 9 := { available := 80, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 0, region := 98, targets := 128 }], pairs := [(1,0),(1,7),(3,0),(4,0)], upper := (rows 13 98 133 266 176 34 65 208 336), lower := (rows 13 98 133 266 176 34 65 128 256), losses := [] }

theorem u4070 : Upper (D 7) (R 7) [12,96,129,258,160,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4070 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4071 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 397, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 13 98 133 266 176 34 80 193 321), lower := (rows 13 98 133 266 176 34 80 128 256), losses := [] }

theorem u4071 : Upper (D 7) (R 7) [12,96,129,258,160,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4071 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4072 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 0, region := 98, targets := 128 }], pairs := [(1,0),(1,7),(3,0),(4,0)], upper := (rows 13 98 133 280 146 33 66 224 352), lower := (rows 13 98 133 280 146 33 66 128 256), losses := [] }

theorem u4072 : Upper (D 7) (R 7) [12,96,129,272,130,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4072 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4073 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5),(4,5)], upper := (rows 13 98 133 280 146 34 96 193 321), lower := (rows 13 98 133 280 146 34 96 128 256), losses := [] }

theorem u4073 : Upper (D 7) (R 7) [12,96,129,272,130,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4073 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4074 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 0, region := 98, targets := 128 }], pairs := [(1,0),(1,7),(3,0),(4,0)], upper := (rows 13 98 133 280 176 34 65 194 322), lower := (rows 13 98 133 280 176 34 65 128 256), losses := [] }

theorem u4074 : Upper (D 7) (R 7) [12,96,129,272,160,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4074 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4075 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 413, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 13 98 133 280 176 34 66 193 321), lower := (rows 13 98 133 280 176 34 66 128 256), losses := [] }

theorem u4075 : Upper (D 7) (R 7) [12,96,129,272,160,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4075 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4076 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 66, targets := 129 },{ cop := 4, region := 488, targets := 1 },{ cop := 4, region := 196, targets := 32 }], pairs := [(1,0),(1,7),(2,5),(3,0)], upper := (rows 13 98 133 296 19 160 66 208 336), lower := (rows 13 98 133 296 19 160 66 128 256), losses := [] }

theorem u4076 : Upper (D 7) (R 7) [12,96,129,288,3,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4076 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4077 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 1, region := 264, targets := 128 }], pairs := [(1,0),(3,0),(3,7)], upper := (rows 13 98 133 296 19 160 80 194 322), lower := (rows 13 98 133 296 19 160 80 128 256), losses := [] }

theorem u4077 : Upper (D 7) (R 7) [12,96,129,288,3,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4077 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4078 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 413, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 13 98 133 296 81 34 66 144 400), lower := (rows 13 98 133 296 81 34 66 128 256), losses := [] }

theorem u4078 : Upper (D 7) (R 7) [12,96,129,288,65,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4078 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4079 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 13 98 133 296 81 34 80 130 386), lower := (rows 13 98 133 296 81 34 80 128 256), losses := [] }

theorem u4079 : Upper (D 7) (R 7) [12,96,129,288,65,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4079 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u4079
end Delivery.IrregularNine14.P07

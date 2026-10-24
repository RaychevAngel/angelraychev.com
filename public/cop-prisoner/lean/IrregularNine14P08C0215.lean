import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0070
import IrregularNine14P08C0071

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b12900 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 7 44 168 274 241 209 209 465), lower := (rows 97 7 44 168 274 32 64 128 256), losses := [] }

theorem u12900 : Upper (D 8) (R 8) [96,5,40,160,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12900 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12901 : PairBound 9 := { available := 147, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 7 44 168 336 179 211 147 403), lower := (rows 97 7 44 168 336 32 64 128 256), losses := [] }

theorem u12901 : Upper (D 8) (R 8) [96,5,40,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12901 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12902 : PairBound 9 := { available := 83, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 7 44 168 400 115 83 211 339), lower := (rows 97 7 44 168 400 32 64 128 256), losses := [] }

theorem u12902 : Upper (D 8) (R 8) [96,5,40,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12902 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12903 : PairBound 9 := { available := 401, camps := [{ cop := 1, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 44 200 50 433 465 401 401), lower := (rows 97 7 44 200 50 32 64 128 256), losses := [] }

theorem u12903 : Upper (D 8) (R 8) [96,5,40,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12903 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12904 : PairBound 9 := { available := 306, camps := [{ cop := 1, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 44 200 145 306 370 434 306), lower := (rows 97 7 44 200 145 32 64 128 256), losses := [] }

theorem u12904 : Upper (D 8) (R 8) [96,5,40,192,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12904 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12905 : PairBound 9 := { available := 305, camps := [{ cop := 1, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 44 200 146 305 369 433 305), lower := (rows 97 7 44 200 146 32 64 128 256), losses := [] }

theorem u12905 : Upper (D 8) (R 8) [96,5,40,192,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12905 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12906 : PairBound 9 := { available := 275, camps := [{ cop := 1, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 44 200 176 307 339 403 275), lower := (rows 97 7 44 200 176 32 64 128 256), losses := [] }

theorem u12906 : Upper (D 8) (R 8) [96,5,40,192,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12906 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12907 : PairBound 9 := { available := 178, camps := [{ cop := 1, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 44 200 273 178 242 178 434), lower := (rows 97 7 44 200 273 32 64 128 256), losses := [] }

theorem u12907 : Upper (D 8) (R 8) [96,5,40,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12907 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12908 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 44 200 274 177 241 177 433), lower := (rows 97 7 44 200 274 32 64 128 256), losses := [] }

theorem u12908 : Upper (D 8) (R 8) [96,5,40,192,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12908 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12909 : PairBound 9 := { available := 147, camps := [{ cop := 1, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 44 200 304 179 211 147 403), lower := (rows 97 7 44 200 304 32 64 128 256), losses := [] }

theorem u12909 : Upper (D 8) (R 8) [96,5,40,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12909 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12910 : PairBound 9 := { available := 51, camps := [{ cop := 1, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 44 200 400 51 115 179 307), lower := (rows 97 7 44 200 400 32 64 128 256), losses := [] }

theorem u12910 : Upper (D 8) (R 8) [96,5,40,192,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12910 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12911 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 44 265 50 240 208 208 464), lower := (rows 97 7 44 265 50 32 64 128 256), losses := [] }

theorem u12911 : Upper (D 8) (R 8) [96,5,40,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12911 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12912 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 44 265 82 176 240 176 432), lower := (rows 97 7 44 265 82 32 64 128 256), losses := [] }

theorem u12912 : Upper (D 8) (R 8) [96,5,40,257,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12912 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12913 : PairBound 9 := { available := 240, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 44 265 146 240 240 240 496), lower := (rows 97 7 44 265 146 32 64 128 256), losses := [] }

theorem u12913 : Upper (D 8) (R 8) [96,5,40,257,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12913 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12914 : PairBound 9 := { available := 210, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 44 265 176 242 210 210 466), lower := (rows 97 7 44 265 176 32 64 128 256), losses := [] }

theorem u12914 : Upper (D 8) (R 8) [96,5,40,257,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12914 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12915 : PairBound 9 := { available := 178, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 44 265 208 178 242 178 434), lower := (rows 97 7 44 265 208 32 64 128 256), losses := [] }

theorem u12915 : Upper (D 8) (R 8) [96,5,40,257,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12915 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12916 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 44 266 49 240 208 208 464), lower := (rows 97 7 44 266 49 32 64 128 256), losses := [] }

theorem u12916 : Upper (D 8) (R 8) [96,5,40,258,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12916 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12917 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 44 266 81 176 240 176 432), lower := (rows 97 7 44 266 81 32 64 128 256), losses := [] }

theorem u12917 : Upper (D 8) (R 8) [96,5,40,258,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12917 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12918 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 44 266 112 177 209 145 401), lower := (rows 97 7 44 266 112 32 64 128 256), losses := [] }

theorem u12918 : Upper (D 8) (R 8) [96,5,40,258,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12918 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12919 : Route 9 := (fun mask => (mask,id))

def c12919 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u12919 : Upper (D 8) (R 8) [96,5,40,258,129] 13 := by
  apply FastRouting.sound _ _ [96,5,40,258,129] 13 (by decide) (choices 1) [16,64,128] r12919 c12919
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4230
  · exact u4231
  · exact u4232

def r12920 : Route 9 := (fun mask => (mask,id))

def c12920 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u12920 : Upper (D 8) (R 8) [96,5,40,258,160] 13 := by
  apply FastRouting.sound _ _ [96,5,40,258,160] 13 (by decide) (choices 1) [1,16,64,128] r12920 c12920
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4233
  · exact u4234
  · exact u4235
  · exact u4236

def r12921 : Route 9 := (fun mask => (mask,id))

def c12921 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u12921 : Upper (D 8) (R 8) [96,5,40,258,192] 13 := by
  apply FastRouting.sound _ _ [96,5,40,258,192] 13 (by decide) (choices 1) [1,16,128] r12921 c12921
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4237
  · exact u4238
  · exact u4239

def b12922 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 44 280 49 226 194 194 450), lower := (rows 97 7 44 280 49 32 64 128 256), losses := [] }

theorem u12922 : Upper (D 8) (R 8) [96,5,40,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12922 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12923 : PairBound 9 := { available := 193, camps := [], pairs := [(3,5)], upper := (rows 97 7 44 280 50 225 193 193 449), lower := (rows 97 7 44 280 50 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 4 24 16 0 67 131 259), good := (rows 449 455 12 280 474 0 64 128 256) }] }

theorem u12923 : Upper (D 8) (R 8) [96,5,40,272,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12923 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12924 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 44 280 81 162 226 162 418), lower := (rows 97 7 44 280 81 32 64 128 256), losses := [] }

theorem u12924 : Upper (D 8) (R 8) [96,5,40,272,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12924 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12925 : PairBound 9 := { available := 161, camps := [], pairs := [(2,6)], upper := (rows 97 7 44 280 82 161 225 161 417), lower := (rows 97 7 44 280 82 32 64 128 256), losses := [{ target := 6, region := (rows 1 2 20 24 16 35 0 131 259), good := (rows 417 423 44 284 446 32 0 128 256) }] }

theorem u12925 : Upper (D 8) (R 8) [96,5,40,272,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12925 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12926 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 44 280 112 163 195 131 387), lower := (rows 97 7 44 280 112 32 64 128 256), losses := [] }

theorem u12926 : Upper (D 8) (R 8) [96,5,40,272,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12926 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12927 : Route 9 := (fun mask => (mask,id))

def c12927 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u12927 : Upper (D 8) (R 8) [96,5,40,272,129] 13 := by
  apply FastRouting.sound _ _ [96,5,40,272,129] 13 (by decide) (choices 1) [2,64,128] r12927 c12927
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4240
  · exact u4241
  · exact u4242

def r12928 : Route 9 := (fun mask => (mask,id))

def c12928 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u12928 : Upper (D 8) (R 8) [96,5,40,272,130] 13 := by
  apply FastRouting.sound _ _ [96,5,40,272,130] 13 (by decide) (choices 1) [1,64,128] r12928 c12928
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4243
  · exact u4244
  · exact u4245

def r12929 : Route 9 := (fun mask => (mask,id))

def c12929 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u12929 : Upper (D 8) (R 8) [96,5,40,272,160] 13 := by
  apply FastRouting.sound _ _ [96,5,40,272,160] 13 (by decide) (choices 1) [1,2,64,128] r12929 c12929
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4246
  · exact u4247
  · exact u4248
  · exact u4249

def r12930 : Route 9 := (fun mask => (mask,id))

def c12930 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u12930 : Upper (D 8) (R 8) [96,5,40,272,192] 13 := by
  apply FastRouting.sound _ _ [96,5,40,272,192] 13 (by decide) (choices 1) [1,2,128] r12930 c12930
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4250
  · exact u4251
  · exact u4252

def b12931 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 7 44 296 82 177 209 145 401), lower := (rows 97 7 44 296 82 32 64 128 256), losses := [] }

theorem u12931 : Upper (D 8) (R 8) [96,5,40,288,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12931 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12932 : PairBound 9 := { available := 210, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 7 44 296 145 242 210 210 466), lower := (rows 97 7 44 296 145 32 64 128 256), losses := [] }

theorem u12932 : Upper (D 8) (R 8) [96,5,40,288,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12932 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12933 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 7 44 296 146 241 209 209 465), lower := (rows 97 7 44 296 146 32 64 128 256), losses := [] }

theorem u12933 : Upper (D 8) (R 8) [96,5,40,288,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12933 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12934 : PairBound 9 := { available := 147, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 7 44 296 208 179 211 147 403), lower := (rows 97 7 44 296 208 32 64 128 256), losses := [] }

theorem u12934 : Upper (D 8) (R 8) [96,5,40,288,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12934 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12935 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 44 328 50 177 209 145 401), lower := (rows 97 7 44 328 50 32 64 128 256), losses := [] }

theorem u12935 : Upper (D 8) (R 8) [96,5,40,320,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12935 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12936 : PairBound 9 := { available := 178, camps := [{ cop := 1, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 44 328 145 178 242 178 434), lower := (rows 97 7 44 328 145 32 64 128 256), losses := [] }

theorem u12936 : Upper (D 8) (R 8) [96,5,40,320,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12936 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12937 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 44 328 146 177 241 177 433), lower := (rows 97 7 44 328 146 32 64 128 256), losses := [] }

theorem u12937 : Upper (D 8) (R 8) [96,5,40,320,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12937 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12938 : PairBound 9 := { available := 147, camps := [{ cop := 1, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 44 328 176 179 211 147 403), lower := (rows 97 7 44 328 176 32 64 128 256), losses := [] }

theorem u12938 : Upper (D 8) (R 8) [96,5,40,320,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12938 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12939 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 44 392 49 242 210 210 466), lower := (rows 97 7 44 392 49 32 64 128 256), losses := [] }

theorem u12939 : Upper (D 8) (R 8) [96,5,40,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12939 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12940 : Route 9 := (fun mask => (mask,id))

def c12940 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u12940 : Upper (D 8) (R 8) [96,5,40,384,34] 13 := by
  apply FastRouting.sound _ _ [96,5,40,384,34] 13 (by decide) (choices 1) [1,16,64,128] r12940 c12940
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4253
  · exact u4254
  · exact u4255
  · exact u4256

def b12941 : PairBound 9 := { available := 178, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 44 392 81 178 242 178 434), lower := (rows 97 7 44 392 81 32 64 128 256), losses := [] }

theorem u12941 : Upper (D 8) (R 8) [96,5,40,384,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12941 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12942 : Route 9 := (fun mask => (mask,id))

def c12942 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u12942 : Upper (D 8) (R 8) [96,5,40,384,66] 13 := by
  apply FastRouting.sound _ _ [96,5,40,384,66] 13 (by decide) (choices 1) [1,16,128] r12942 c12942
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4257
  · exact u4258
  · exact u4259

def b12943 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 44 392 112 179 211 147 403), lower := (rows 97 7 44 392 112 32 64 128 256), losses := [] }

theorem u12943 : Upper (D 8) (R 8) [96,5,40,384,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12943 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12944 : Route 9 := (fun mask => (mask,id))

def c12944 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12944 : Upper (D 8) (R 8) [96,5,40,384,129] 13 := by
  apply FastRouting.sound _ _ [96,5,40,384,129] 13 (by decide) (choices 1) [2,16,64] r12944 c12944
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4260
  · exact u4261
  · exact u4262

def b12945 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 44 392 146 113 113 241 369), lower := (rows 97 7 44 392 146 32 64 128 256), losses := [] }

theorem u12945 : Upper (D 8) (R 8) [96,5,40,384,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12945 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12946 : Route 9 := (fun mask => (mask,id))

def c12946 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12946 : Upper (D 8) (R 8) [96,5,40,384,160] 13 := by
  apply FastRouting.sound _ _ [96,5,40,384,160] 13 (by decide) (choices 1) [1,2,16,64] r12946 c12946
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4263
  · exact u4264
  · exact u4265
  · exact u4266

def r12947 : Route 9 := (fun mask => (mask,id))

def c12947 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12947 : Upper (D 8) (R 8) [96,5,40,384,192] 13 := by
  apply FastRouting.sound _ _ [96,5,40,384,192] 13 (by decide) (choices 1) [1,2,16] r12947 c12947
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4267
  · exact u4268
  · exact u4269

def b12948 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 69 26 56 416 480 416 416), lower := (rows 97 7 69 26 56 32 64 128 256), losses := [] }

theorem u12948 : Upper (D 8) (R 8) [96,5,65,18,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12948 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12949 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 69 26 152 416 480 416 416), lower := (rows 97 7 69 26 152 32 64 128 256), losses := [] }

theorem u12949 : Upper (D 8) (R 8) [96,5,65,18,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12949 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12950 : PairBound 9 := { available := 424, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 69 26 176 424 488 424 424), lower := (rows 97 7 69 26 176 32 64 128 256), losses := [] }

theorem u12950 : Upper (D 8) (R 8) [96,5,65,18,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12950 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12951 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 69 26 280 160 224 160 416), lower := (rows 97 7 69 26 280 32 64 128 256), losses := [] }

theorem u12951 : Upper (D 8) (R 8) [96,5,65,18,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12951 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12952 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 69 26 304 168 232 168 424), lower := (rows 97 7 69 26 304 32 64 128 256), losses := [] }

theorem u12952 : Upper (D 8) (R 8) [96,5,65,18,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12952 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12953 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 69 26 400 168 232 168 424), lower := (rows 97 7 69 26 400 32 64 128 256), losses := [] }

theorem u12953 : Upper (D 8) (R 8) [96,5,65,18,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12953 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12954 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 69 42 152 432 496 432 432), lower := (rows 97 7 69 42 152 32 64 128 256), losses := [] }

theorem u12954 : Upper (D 8) (R 8) [96,5,65,34,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12954 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12955 : PairBound 9 := { available := 408, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 69 42 176 440 472 408 408), lower := (rows 97 7 69 42 176 32 64 128 256), losses := [] }

theorem u12955 : Upper (D 8) (R 8) [96,5,65,34,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12955 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12956 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 69 42 280 176 240 176 432), lower := (rows 97 7 69 42 280 32 64 128 256), losses := [] }

theorem u12956 : Upper (D 8) (R 8) [96,5,65,34,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12956 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12957 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 69 42 304 184 216 152 408), lower := (rows 97 7 69 42 304 32 64 128 256), losses := [] }

theorem u12957 : Upper (D 8) (R 8) [96,5,65,34,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12957 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12958 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 69 42 400 184 248 184 440), lower := (rows 97 7 69 42 400 32 64 128 256), losses := [] }

theorem u12958 : Upper (D 8) (R 8) [96,5,65,34,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12958 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12959 : PairBound 9 := { available := 424, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 69 56 146 424 488 424 424), lower := (rows 97 7 69 56 146 32 64 128 256), losses := [] }

theorem u12959 : Upper (D 8) (R 8) [96,5,65,48,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12959 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u12959
end Delivery.IrregularNine14.P08

import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0110
import IrregularNine14P08C0111

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r18000 : Route 9 := (fun mask => (mask,id))

def c18000 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u18000 : Upper (D 8) (R 8) [320,5,40,144,33] 13 := by
  apply FastRouting.sound _ _ [320,5,40,144,33] 13 (by decide) (choices 1) [2,64,128] r18000 c18000
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6656
  · exact u6657
  · exact u6658

def r18001 : Route 9 := (fun mask => (mask,id))

def c18001 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u18001 : Upper (D 8) (R 8) [320,5,40,144,34] 13 := by
  apply FastRouting.sound _ _ [320,5,40,144,34] 13 (by decide) (choices 1) [1,64,128] r18001 c18001
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6659
  · exact u6660
  · exact u6661

def b18002 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 174, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 44 152 81 162 226 162 418), lower := (rows 321 7 44 152 81 32 64 128 256), losses := [] }

theorem u18002 : Upper (D 8) (R 8) [320,5,40,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18002 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18003 : PairBound 9 := { available := 161, camps := [], pairs := [(2,6)], upper := (rows 321 7 44 152 82 161 225 161 417), lower := (rows 321 7 44 152 82 32 64 128 256), losses := [{ target := 6, region := (rows 1 2 20 24 16 35 0 131 259), good := (rows 417 423 44 156 446 32 0 128 256) }] }

theorem u18003 : Upper (D 8) (R 8) [320,5,40,144,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18003 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18004 : Route 9 := (fun mask => (mask,id))

def c18004 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u18004 : Upper (D 8) (R 8) [320,5,40,144,96] 13 := by
  apply FastRouting.sound _ _ [320,5,40,144,96] 13 (by decide) (choices 1) [1,2,128] r18004 c18004
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6662
  · exact u6663
  · exact u6664

def b18005 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 44 152 145 98 98 226 354), lower := (rows 321 7 44 152 145 32 64 128 256), losses := [] }

theorem u18005 : Upper (D 8) (R 8) [320,5,40,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18005 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18006 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 44 152 146 97 97 225 353), lower := (rows 321 7 44 152 146 32 64 128 256), losses := [] }

theorem u18006 : Upper (D 8) (R 8) [320,5,40,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18006 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18007 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 321 7 44 152 176 99 99 227 355), lower := (rows 321 7 44 152 176 32 64 128 256), losses := [] }

theorem u18007 : Upper (D 8) (R 8) [320,5,40,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18007 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18008 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 44 152 208 35 99 163 291), lower := (rows 321 7 44 152 208 32 64 128 256), losses := [] }

theorem u18008 : Upper (D 8) (R 8) [320,5,40,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18008 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18009 : PairBound 9 := { available := 210, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 7 44 168 49 242 210 210 466), lower := (rows 321 7 44 168 49 32 64 128 256), losses := [] }

theorem u18009 : Upper (D 8) (R 8) [320,5,40,160,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18009 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18010 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 7 44 168 50 241 209 209 465), lower := (rows 321 7 44 168 50 32 64 128 256), losses := [] }

theorem u18010 : Upper (D 8) (R 8) [320,5,40,160,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18010 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18011 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 7 44 168 82 177 241 177 433), lower := (rows 321 7 44 168 82 32 64 128 256), losses := [] }

theorem u18011 : Upper (D 8) (R 8) [320,5,40,160,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18011 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18012 : PairBound 9 := { available := 147, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 7 44 168 112 179 211 147 403), lower := (rows 321 7 44 168 112 32 64 128 256), losses := [] }

theorem u18012 : Upper (D 8) (R 8) [320,5,40,160,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18012 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18013 : PairBound 9 := { available := 114, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 7 44 168 145 114 114 242 370), lower := (rows 321 7 44 168 145 32 64 128 256), losses := [] }

theorem u18013 : Upper (D 8) (R 8) [320,5,40,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18013 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18014 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 7 44 168 146 113 113 241 369), lower := (rows 321 7 44 168 146 32 64 128 256), losses := [] }

theorem u18014 : Upper (D 8) (R 8) [320,5,40,160,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18014 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18015 : PairBound 9 := { available := 83, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 7 44 168 176 115 83 211 339), lower := (rows 321 7 44 168 176 32 64 128 256), losses := [] }

theorem u18015 : Upper (D 8) (R 8) [320,5,40,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18015 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18016 : PairBound 9 := { available := 51, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 7 44 168 208 51 115 179 307), lower := (rows 321 7 44 168 208 32 64 128 256), losses := [] }

theorem u18016 : Upper (D 8) (R 8) [320,5,40,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18016 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18017 : PairBound 9 := { available := 178, camps := [{ cop := 1, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 7 44 200 49 178 242 178 434), lower := (rows 321 7 44 200 49 32 64 128 256), losses := [] }

theorem u18017 : Upper (D 8) (R 8) [320,5,40,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18017 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18018 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 7 44 200 50 177 241 177 433), lower := (rows 321 7 44 200 50 32 64 128 256), losses := [] }

theorem u18018 : Upper (D 8) (R 8) [320,5,40,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18018 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18019 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 7 44 200 145 50 114 178 306), lower := (rows 321 7 44 200 145 32 64 128 256), losses := [] }

theorem u18019 : Upper (D 8) (R 8) [320,5,40,192,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18019 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18020 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 7 44 200 146 49 113 177 305), lower := (rows 321 7 44 200 146 32 64 128 256), losses := [] }

theorem u18020 : Upper (D 8) (R 8) [320,5,40,192,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18020 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18021 : PairBound 9 := { available := 51, camps := [{ cop := 1, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 7 44 200 176 51 115 179 307), lower := (rows 321 7 44 200 176 32 64 128 256), losses := [] }

theorem u18021 : Upper (D 8) (R 8) [320,5,40,192,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18021 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18022 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 69 26 56 160 224 160 416), lower := (rows 321 7 69 26 56 32 64 128 256), losses := [] }

theorem u18022 : Upper (D 8) (R 8) [320,5,65,18,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18022 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18023 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 69 26 152 160 224 160 416), lower := (rows 321 7 69 26 152 32 64 128 256), losses := [] }

theorem u18023 : Upper (D 8) (R 8) [320,5,65,18,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18023 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18024 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 69 26 176 168 232 168 424), lower := (rows 321 7 69 26 176 32 64 128 256), losses := [] }

theorem u18024 : Upper (D 8) (R 8) [320,5,65,18,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18024 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18025 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 69 42 152 176 240 176 432), lower := (rows 321 7 69 42 152 32 64 128 256), losses := [] }

theorem u18025 : Upper (D 8) (R 8) [320,5,65,34,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18025 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18026 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 69 42 176 184 248 184 440), lower := (rows 321 7 69 42 176 32 64 128 256), losses := [] }

theorem u18026 : Upper (D 8) (R 8) [320,5,65,34,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18026 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18027 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 69 56 146 168 232 168 424), lower := (rows 321 7 69 56 146 32 64 128 256), losses := [] }

theorem u18027 : Upper (D 8) (R 8) [320,5,65,48,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18027 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18028 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 69 56 152 162 226 162 418), lower := (rows 321 7 69 56 152 32 64 128 256), losses := [] }

theorem u18028 : Upper (D 8) (R 8) [320,5,65,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18028 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18029 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 69 138 176 56 120 184 312), lower := (rows 321 7 69 138 176 32 64 128 256), losses := [] }

theorem u18029 : Upper (D 8) (R 8) [320,5,65,130,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18029 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18030 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 70 25 152 160 224 160 416), lower := (rows 321 7 70 25 152 32 64 128 256), losses := [] }

theorem u18030 : Upper (D 8) (R 8) [320,5,66,17,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18030 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18031 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 70 25 176 168 232 168 424), lower := (rows 321 7 70 25 176 32 64 128 256), losses := [] }

theorem u18031 : Upper (D 8) (R 8) [320,5,66,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18031 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18032 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 70 41 152 176 240 176 432), lower := (rows 321 7 70 41 152 32 64 128 256), losses := [] }

theorem u18032 : Upper (D 8) (R 8) [320,5,66,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18032 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18033 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 70 41 176 184 248 184 440), lower := (rows 321 7 70 41 176 32 64 128 256), losses := [] }

theorem u18033 : Upper (D 8) (R 8) [320,5,66,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18033 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18034 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 70 56 145 168 232 168 424), lower := (rows 321 7 70 56 145 32 64 128 256), losses := [] }

theorem u18034 : Upper (D 8) (R 8) [320,5,66,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18034 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18035 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 70 56 152 161 225 161 417), lower := (rows 321 7 70 56 152 32 64 128 256), losses := [] }

theorem u18035 : Upper (D 8) (R 8) [320,5,66,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18035 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18036 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 70 137 176 56 120 184 312), lower := (rows 321 7 70 137 176 32 64 128 256), losses := [] }

theorem u18036 : Upper (D 8) (R 8) [320,5,66,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18036 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18037 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 76 25 146 160 224 160 416), lower := (rows 321 7 76 25 146 32 64 128 256), losses := [] }

theorem u18037 : Upper (D 8) (R 8) [320,5,72,17,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18037 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18038 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 76 25 176 162 226 162 418), lower := (rows 321 7 76 25 176 32 64 128 256), losses := [] }

theorem u18038 : Upper (D 8) (R 8) [320,5,72,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18038 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18039 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 76 26 49 160 224 160 416), lower := (rows 321 7 76 26 49 32 64 128 256), losses := [] }

theorem u18039 : Upper (D 8) (R 8) [320,5,72,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18039 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18040 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 76 26 145 160 224 160 416), lower := (rows 321 7 76 26 145 32 64 128 256), losses := [] }

theorem u18040 : Upper (D 8) (R 8) [320,5,72,18,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18040 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18041 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 76 26 176 161 225 161 417), lower := (rows 321 7 76 26 176 32 64 128 256), losses := [] }

theorem u18041 : Upper (D 8) (R 8) [320,5,72,18,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18041 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18042 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 76 41 50 176 240 176 432), lower := (rows 321 7 76 41 50 32 64 128 256), losses := [] }

theorem u18042 : Upper (D 8) (R 8) [320,5,72,33,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18042 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18043 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 76 41 146 176 240 176 432), lower := (rows 321 7 76 41 146 32 64 128 256), losses := [] }

theorem u18043 : Upper (D 8) (R 8) [320,5,72,33,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18043 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18044 : PairBound 9 := { available := 178, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 76 41 176 178 242 178 434), lower := (rows 321 7 76 41 176 32 64 128 256), losses := [] }

theorem u18044 : Upper (D 8) (R 8) [320,5,72,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18044 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18045 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 76 42 49 176 240 176 432), lower := (rows 321 7 76 42 49 32 64 128 256), losses := [] }

theorem u18045 : Upper (D 8) (R 8) [320,5,72,34,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18045 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18046 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 76 42 145 176 240 176 432), lower := (rows 321 7 76 42 145 32 64 128 256), losses := [] }

theorem u18046 : Upper (D 8) (R 8) [320,5,72,34,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18046 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18047 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 76 42 176 177 241 177 433), lower := (rows 321 7 76 42 176 32 64 128 256), losses := [] }

theorem u18047 : Upper (D 8) (R 8) [320,5,72,34,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18047 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18048 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 76 56 145 162 226 162 418), lower := (rows 321 7 76 56 145 32 64 128 256), losses := [] }

theorem u18048 : Upper (D 8) (R 8) [320,5,72,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18048 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18049 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 76 56 146 161 225 161 417), lower := (rows 321 7 76 56 146 32 64 128 256), losses := [] }

theorem u18049 : Upper (D 8) (R 8) [320,5,72,48,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18049 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18050 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 76 137 50 176 240 176 432), lower := (rows 321 7 76 137 50 32 64 128 256), losses := [] }

theorem u18050 : Upper (D 8) (R 8) [320,5,72,129,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18050 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18051 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 76 137 146 48 112 176 304), lower := (rows 321 7 76 137 146 32 64 128 256), losses := [] }

theorem u18051 : Upper (D 8) (R 8) [320,5,72,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18051 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18052 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 76 137 176 50 114 178 306), lower := (rows 321 7 76 137 176 32 64 128 256), losses := [] }

theorem u18052 : Upper (D 8) (R 8) [320,5,72,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18052 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18053 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 76 138 49 176 240 176 432), lower := (rows 321 7 76 138 49 32 64 128 256), losses := [] }

theorem u18053 : Upper (D 8) (R 8) [320,5,72,130,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18053 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18054 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 76 138 145 48 112 176 304), lower := (rows 321 7 76 138 145 32 64 128 256), losses := [] }

theorem u18054 : Upper (D 8) (R 8) [320,5,72,130,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18054 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18055 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 76 138 176 49 113 177 305), lower := (rows 321 7 76 138 176 32 64 128 256), losses := [] }

theorem u18055 : Upper (D 8) (R 8) [320,5,72,130,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18055 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18056 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 76 152 49 162 226 162 418), lower := (rows 321 7 76 152 49 32 64 128 256), losses := [] }

theorem u18056 : Upper (D 8) (R 8) [320,5,72,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18056 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18057 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 76 152 50 161 225 161 417), lower := (rows 321 7 76 152 50 32 64 128 256), losses := [] }

theorem u18057 : Upper (D 8) (R 8) [320,5,72,144,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18057 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18058 : PairBound 9 := { available := 178, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 76 168 49 178 242 178 434), lower := (rows 321 7 76 168 49 32 64 128 256), losses := [] }

theorem u18058 : Upper (D 8) (R 8) [320,5,72,160,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18058 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18059 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 76 168 50 177 241 177 433), lower := (rows 321 7 76 168 50 32 64 128 256), losses := [] }

theorem u18059 : Upper (D 8) (R 8) [320,5,72,160,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18059 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u18059
end Delivery.IrregularNine14.P08

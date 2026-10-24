import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0084

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b14700 : PairBound 9 := { available := 306, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 140 73 145 306 370 434 306), lower := (rows 97 38 140 73 145 32 64 128 256), losses := [] }

theorem u14700 : Upper (D 8) (R 8) [96,36,136,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14700 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14701 : PairBound 9 := { available := 275, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 140 73 176 307 339 403 275), lower := (rows 97 38 140 73 176 32 64 128 256), losses := [] }

theorem u14701 : Upper (D 8) (R 8) [96,36,136,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14701 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14702 : PairBound 9 := { available := 178, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 140 73 273 178 242 178 434), lower := (rows 97 38 140 73 273 32 64 128 256), losses := [] }

theorem u14702 : Upper (D 8) (R 8) [96,36,136,65,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14702 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14703 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 140 73 274 177 241 177 433), lower := (rows 97 38 140 73 274 32 64 128 256), losses := [] }

theorem u14703 : Upper (D 8) (R 8) [96,36,136,65,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14703 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14704 : PairBound 9 := { available := 147, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 140 73 304 179 211 147 403), lower := (rows 97 38 140 73 304 32 64 128 256), losses := [] }

theorem u14704 : Upper (D 8) (R 8) [96,36,136,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14704 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14705 : PairBound 9 := { available := 51, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 140 73 400 51 115 179 307), lower := (rows 97 38 140 73 400 32 64 128 256), losses := [] }

theorem u14705 : Upper (D 8) (R 8) [96,36,136,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14705 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14706 : PairBound 9 := { available := 305, camps := [{ cop := 0, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 97 38 140 74 145 305 369 433 305), lower := (rows 97 38 140 74 145 32 64 128 256), losses := [] }

theorem u14706 : Upper (D 8) (R 8) [96,36,136,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14706 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14707 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 97 38 140 74 176 305 337 401 273), lower := (rows 97 38 140 74 176 32 64 128 256), losses := [] }

theorem u14707 : Upper (D 8) (R 8) [96,36,136,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14707 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14708 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 97 38 140 74 273 177 241 177 433), lower := (rows 97 38 140 74 273 32 64 128 256), losses := [] }

theorem u14708 : Upper (D 8) (R 8) [96,36,136,66,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14708 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14709 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 97 38 140 74 304 177 209 145 401), lower := (rows 97 38 140 74 304 32 64 128 256), losses := [] }

theorem u14709 : Upper (D 8) (R 8) [96,36,136,66,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14709 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14710 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 97 38 140 74 400 49 113 177 305), lower := (rows 97 38 140 74 400 32 64 128 256), losses := [] }

theorem u14710 : Upper (D 8) (R 8) [96,36,136,66,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14710 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14711 : PairBound 9 := { available := 291, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 88 145 291 355 419 291), lower := (rows 97 38 140 88 145 32 64 128 256), losses := [] }

theorem u14711 : Upper (D 8) (R 8) [96,36,136,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14711 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14712 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 88 146 289 353 417 289), lower := (rows 97 38 140 88 146 32 64 128 256), losses := [] }

theorem u14712 : Upper (D 8) (R 8) [96,36,136,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14712 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14713 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 88 176 291 323 387 259), lower := (rows 97 38 140 88 176 32 64 128 256), losses := [] }

theorem u14713 : Upper (D 8) (R 8) [96,36,136,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14713 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14714 : Route 9 := (fun mask => (mask,id))

def c14714 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14714 : Upper (D 8) (R 8) [96,36,136,80,257] 13 := by
  apply FastRouting.sound _ _ [96,36,136,80,257] 13 (by decide) (choices 1) [1,2,128] r14714 c14714
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5060
  · exact u5061
  · exact u5062

def r14715 : Route 9 := (fun mask => (mask,id))

def c14715 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14715 : Upper (D 8) (R 8) [96,36,136,80,258] 13 := by
  apply FastRouting.sound _ _ [96,36,136,80,258] 13 (by decide) (choices 1) [1,128] r14715 c14715
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5063
  · exact u5064

def r14716 : Route 9 := (fun mask => (mask,id))

def c14716 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14716 : Upper (D 8) (R 8) [96,36,136,80,288] 13 := by
  apply FastRouting.sound _ _ [96,36,136,80,288] 13 (by decide) (choices 1) [1,2,128] r14716 c14716
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5065
  · exact u5066
  · exact u5067

def b14717 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 88 400 35 99 163 291), lower := (rows 97 38 140 88 400 32 64 128 256), losses := [] }

theorem u14717 : Upper (D 8) (R 8) [96,36,136,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14717 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14718 : PairBound 9 := { available := 275, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 38 140 104 145 307 339 403 275), lower := (rows 97 38 140 104 145 32 64 128 256), losses := [] }

theorem u14718 : Upper (D 8) (R 8) [96,36,136,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14718 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14719 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 38 140 104 273 179 211 147 403), lower := (rows 97 38 140 104 273 32 64 128 256), losses := [] }

theorem u14719 : Upper (D 8) (R 8) [96,36,136,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14719 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14720 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 38 140 104 274 177 209 145 401), lower := (rows 97 38 140 104 274 32 64 128 256), losses := [] }

theorem u14720 : Upper (D 8) (R 8) [96,36,136,96,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14720 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14721 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 38 140 104 400 51 83 147 275), lower := (rows 97 38 140 104 400 32 64 128 256), losses := [] }

theorem u14721 : Upper (D 8) (R 8) [96,36,136,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14721 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14722 : PairBound 9 := { available := 305, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 137 82 305 369 433 305), lower := (rows 97 38 140 137 82 32 64 128 256), losses := [] }

theorem u14722 : Upper (D 8) (R 8) [96,36,136,129,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14722 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14723 : PairBound 9 := { available := 114, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 137 273 114 114 242 370), lower := (rows 97 38 140 137 273 32 64 128 256), losses := [] }

theorem u14723 : Upper (D 8) (R 8) [96,36,136,129,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14723 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14724 : PairBound 9 := { available := 113, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 137 274 113 113 241 369), lower := (rows 97 38 140 137 274 32 64 128 256), losses := [] }

theorem u14724 : Upper (D 8) (R 8) [96,36,136,129,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14724 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14725 : PairBound 9 := { available := 83, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 137 304 115 83 211 339), lower := (rows 97 38 140 137 304 32 64 128 256), losses := [] }

theorem u14725 : Upper (D 8) (R 8) [96,36,136,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14725 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14726 : PairBound 9 := { available := 51, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 137 336 51 115 179 307), lower := (rows 97 38 140 137 336 32 64 128 256), losses := [] }

theorem u14726 : Upper (D 8) (R 8) [96,36,136,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14726 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14727 : PairBound 9 := { available := 113, camps := [{ cop := 2, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 138 273 113 113 241 369), lower := (rows 97 38 140 138 273 32 64 128 256), losses := [] }

theorem u14727 : Upper (D 8) (R 8) [96,36,136,130,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14727 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14728 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 138 304 113 81 209 337), lower := (rows 97 38 140 138 304 32 64 128 256), losses := [] }

theorem u14728 : Upper (D 8) (R 8) [96,36,136,130,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14728 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14729 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 138 336 49 113 177 305), lower := (rows 97 38 140 138 336 32 64 128 256), losses := [] }

theorem u14729 : Upper (D 8) (R 8) [96,36,136,130,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14729 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14730 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 152 82 289 353 417 289), lower := (rows 97 38 140 152 82 32 64 128 256), losses := [] }

theorem u14730 : Upper (D 8) (R 8) [96,36,136,144,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14730 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14731 : PairBound 9 := { available := 99, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 152 273 99 99 227 355), lower := (rows 97 38 140 152 273 32 64 128 256), losses := [] }

theorem u14731 : Upper (D 8) (R 8) [96,36,136,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14731 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14732 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 152 274 97 97 225 353), lower := (rows 97 38 140 152 274 32 64 128 256), losses := [] }

theorem u14732 : Upper (D 8) (R 8) [96,36,136,144,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14732 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14733 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 152 304 99 67 195 323), lower := (rows 97 38 140 152 304 32 64 128 256), losses := [] }

theorem u14733 : Upper (D 8) (R 8) [96,36,136,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14733 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14734 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 152 336 35 99 163 291), lower := (rows 97 38 140 152 336 32 64 128 256), losses := [] }

theorem u14734 : Upper (D 8) (R 8) [96,36,136,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14734 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14735 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 140 168 82 305 337 401 273), lower := (rows 97 38 140 168 82 32 64 128 256), losses := [] }

theorem u14735 : Upper (D 8) (R 8) [96,36,136,160,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14735 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14736 : PairBound 9 := { available := 83, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 140 168 273 115 83 211 339), lower := (rows 97 38 140 168 273 32 64 128 256), losses := [] }

theorem u14736 : Upper (D 8) (R 8) [96,36,136,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14736 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14737 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 140 168 274 113 81 209 337), lower := (rows 97 38 140 168 274 32 64 128 256), losses := [] }

theorem u14737 : Upper (D 8) (R 8) [96,36,136,160,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14737 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14738 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 140 168 336 51 83 147 275), lower := (rows 97 38 140 168 336 32 64 128 256), losses := [] }

theorem u14738 : Upper (D 8) (R 8) [96,36,136,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14738 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14739 : PairBound 9 := { available := 51, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 200 273 51 115 179 307), lower := (rows 97 38 140 200 273 32 64 128 256), losses := [] }

theorem u14739 : Upper (D 8) (R 8) [96,36,136,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14739 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14740 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 200 274 49 113 177 305), lower := (rows 97 38 140 200 274 32 64 128 256), losses := [] }

theorem u14740 : Upper (D 8) (R 8) [96,36,136,192,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14740 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14741 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 200 304 51 83 147 275), lower := (rows 97 38 140 200 304 32 64 128 256), losses := [] }

theorem u14741 : Upper (D 8) (R 8) [96,36,136,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14741 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14742 : PairBound 9 := { available := 178, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 140 265 81 178 242 178 434), lower := (rows 97 38 140 265 81 32 64 128 256), losses := [] }

theorem u14742 : Upper (D 8) (R 8) [96,36,136,257,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14742 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14743 : Route 9 := (fun mask => (mask,id))

def c14743 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14743 : Upper (D 8) (R 8) [96,36,136,257,66] 13 := by
  apply FastRouting.sound _ _ [96,36,136,257,66] 13 (by decide) (choices 1) [1,16,128] r14743 c14743
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5068
  · exact u5069
  · exact u5070

def b14744 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 38 140 265 112 179 211 147 403), lower := (rows 97 38 140 265 112 32 64 128 256), losses := [] }

theorem u14744 : Upper (D 8) (R 8) [96,36,136,257,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14744 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14745 : Route 9 := (fun mask => (mask,id))

def c14745 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14745 : Upper (D 8) (R 8) [96,36,136,257,129] 13 := by
  apply FastRouting.sound _ _ [96,36,136,257,129] 13 (by decide) (choices 1) [2,16,64] r14745 c14745
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5071
  · exact u5072
  · exact u5073

def b14746 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 265 146 113 113 241 369), lower := (rows 97 38 140 265 146 32 64 128 256), losses := [] }

theorem u14746 : Upper (D 8) (R 8) [96,36,136,257,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14746 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14747 : Route 9 := (fun mask => (mask,id))

def c14747 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14747 : Upper (D 8) (R 8) [96,36,136,257,160] 13 := by
  apply FastRouting.sound _ _ [96,36,136,257,160] 13 (by decide) (choices 1) [1,2,16,64] r14747 c14747
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5074
  · exact u5075
  · exact u5076
  · exact u5077

def r14748 : Route 9 := (fun mask => (mask,id))

def c14748 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14748 : Upper (D 8) (R 8) [96,36,136,257,192] 13 := by
  apply FastRouting.sound _ _ [96,36,136,257,192] 13 (by decide) (choices 1) [1,2,16] r14748 c14748
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5078
  · exact u5079
  · exact u5080

def b14749 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 140 266 81 177 241 177 433), lower := (rows 97 38 140 266 81 32 64 128 256), losses := [] }

theorem u14749 : Upper (D 8) (R 8) [96,36,136,258,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14749 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14750 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 38 140 266 112 177 209 145 401), lower := (rows 97 38 140 266 112 32 64 128 256), losses := [] }

theorem u14750 : Upper (D 8) (R 8) [96,36,136,258,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14750 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14751 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 266 145 113 113 241 369), lower := (rows 97 38 140 266 145 32 64 128 256), losses := [] }

theorem u14751 : Upper (D 8) (R 8) [96,36,136,258,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14751 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14752 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 266 176 113 81 209 337), lower := (rows 97 38 140 266 176 32 64 128 256), losses := [] }

theorem u14752 : Upper (D 8) (R 8) [96,36,136,258,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14752 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14753 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 266 208 49 113 177 305), lower := (rows 97 38 140 266 208 32 64 128 256), losses := [] }

theorem u14753 : Upper (D 8) (R 8) [96,36,136,258,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14753 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14754 : PairBound 9 := { available := 163, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 140 280 81 163 227 163 419), lower := (rows 97 38 140 280 81 32 64 128 256), losses := [] }

theorem u14754 : Upper (D 8) (R 8) [96,36,136,272,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14754 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14755 : Route 9 := (fun mask => (mask,id))

def c14755 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14755 : Upper (D 8) (R 8) [96,36,136,272,66] 13 := by
  apply FastRouting.sound _ _ [96,36,136,272,66] 13 (by decide) (choices 1) [1,128] r14755 c14755
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5081
  · exact u5082

def b14756 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 38 140 280 112 163 195 131 387), lower := (rows 97 38 140 280 112 32 64 128 256), losses := [] }

theorem u14756 : Upper (D 8) (R 8) [96,36,136,272,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14756 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14757 : PairBound 9 := { available := 99, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 280 145 99 99 227 355), lower := (rows 97 38 140 280 145 32 64 128 256), losses := [] }

theorem u14757 : Upper (D 8) (R 8) [96,36,136,272,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14757 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14758 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 280 146 97 97 225 353), lower := (rows 97 38 140 280 146 32 64 128 256), losses := [] }

theorem u14758 : Upper (D 8) (R 8) [96,36,136,272,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14758 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14759 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 280 176 99 67 195 323), lower := (rows 97 38 140 280 176 32 64 128 256), losses := [] }

theorem u14759 : Upper (D 8) (R 8) [96,36,136,272,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14759 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u14759
end Delivery.IrregularNine14.P08

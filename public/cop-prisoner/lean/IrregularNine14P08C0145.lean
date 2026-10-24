import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0031
import IrregularNine14P08C0032

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b8700 : PairBound 9 := { available := 305, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 44 200 148 305 369 433 305), lower := (rows 35 67 44 200 148 32 64 128 256), losses := [] }

theorem u8700 : Upper (D 8) (R 8) [34,65,40,192,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8700 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8701 : Route 9 := (fun mask => (mask,id))

def c8701 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8701 : Upper (D 8) (R 8) [34,65,40,192,160] 13 := by
  apply FastRouting.sound _ _ [34,65,40,192,160] 13 (by decide) (choices 1) [1,4,16,256] r8701 c8701
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1889
  · exact u1890
  · exact u1891
  · exact u1892

def b8702 : PairBound 9 := { available := 180, camps := [{ cop := 4, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 200 273 180 244 180 436), lower := (rows 35 67 44 200 273 32 64 128 256), losses := [] }

theorem u8702 : Upper (D 8) (R 8) [34,65,40,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8702 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8703 : Route 9 := (fun mask => (mask,id))

def c8703 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8703 : Upper (D 8) (R 8) [34,65,40,192,260] 13 := by
  apply FastRouting.sound _ _ [34,65,40,192,260] 13 (by decide) (choices 1) [1,16,128] r8703 c8703
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1893
  · exact u1894
  · exact u1895

def r8704 : Route 9 := (fun mask => (mask,id))

def c8704 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8704 : Upper (D 8) (R 8) [34,65,40,192,288] 13 := by
  apply FastRouting.sound _ _ [34,65,40,192,288] 13 (by decide) (choices 1) [1,4,16,128] r8704 c8704
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1896
  · exact u1897
  · exact u1898
  · exact u1899

def r8705 : Route 9 := (fun mask => (mask,id))

def c8705 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8705 : Upper (D 8) (R 8) [34,65,40,192,384] 13 := by
  apply FastRouting.sound _ _ [34,65,40,192,384] 13 (by decide) (choices 1) [1,4,16] r8705 c8705
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1900
  · exact u1901
  · exact u1902

def b8706 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 265 84 176 240 176 432), lower := (rows 35 67 44 265 84 32 64 128 256), losses := [] }

theorem u8706 : Upper (D 8) (R 8) [34,65,40,257,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8706 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8707 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 265 148 240 240 240 496), lower := (rows 35 67 44 265 148 32 64 128 256), losses := [] }

theorem u8707 : Upper (D 8) (R 8) [34,65,40,257,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8707 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8708 : PairBound 9 := { available := 212, camps := [{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 265 176 244 212 212 468), lower := (rows 35 67 44 265 176 32 64 128 256), losses := [] }

theorem u8708 : Upper (D 8) (R 8) [34,65,40,257,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8708 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8709 : PairBound 9 := { available := 180, camps := [{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 265 208 180 244 180 436), lower := (rows 35 67 44 265 208 32 64 128 256), losses := [] }

theorem u8709 : Upper (D 8) (R 8) [34,65,40,257,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8709 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8710 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 35 67 44 268 81 176 240 176 432), lower := (rows 35 67 44 268 81 32 64 128 256), losses := [] }

theorem u8710 : Upper (D 8) (R 8) [34,65,40,260,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8710 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8711 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 44 268 112 177 209 145 401), lower := (rows 35 67 44 268 112 32 64 128 256), losses := [] }

theorem u8711 : Upper (D 8) (R 8) [34,65,40,260,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8711 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8712 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 268 145 240 240 240 496), lower := (rows 35 67 44 268 145 32 64 128 256), losses := [] }

theorem u8712 : Upper (D 8) (R 8) [34,65,40,260,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8712 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8713 : Route 9 := (fun mask => (mask,id))

def c8713 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8713 : Upper (D 8) (R 8) [34,65,40,260,160] 13 := by
  apply FastRouting.sound _ _ [34,65,40,260,160] 13 (by decide) (choices 1) [1,16,64,128] r8713 c8713
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1903
  · exact u1904
  · exact u1905
  · exact u1906

def r8714 : Route 9 := (fun mask => (mask,id))

def c8714 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8714 : Upper (D 8) (R 8) [34,65,40,260,192] 13 := by
  apply FastRouting.sound _ _ [34,65,40,260,192] 13 (by decide) (choices 1) [1,16,128] r8714 c8714
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1907
  · exact u1908
  · exact u1909

def b8715 : PairBound 9 := { available := 164, camps := [{ cop := 1, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 35 67 44 280 81 164 228 164 420), lower := (rows 35 67 44 280 81 32 64 128 256), losses := [] }

theorem u8715 : Upper (D 8) (R 8) [34,65,40,272,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8715 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8716 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 44 280 84 161 225 161 417), lower := (rows 35 67 44 280 84 32 64 128 256), losses := [] }

theorem u8716 : Upper (D 8) (R 8) [34,65,40,272,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8716 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8717 : PairBound 9 := { available := 133, camps := [{ cop := 4, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 44 280 112 165 197 133 389), lower := (rows 35 67 44 280 112 32 64 128 256), losses := [] }

theorem u8717 : Upper (D 8) (R 8) [34,65,40,272,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8717 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8718 : PairBound 9 := { available := 228, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 280 145 228 228 228 484), lower := (rows 35 67 44 280 145 32 64 128 256), losses := [] }

theorem u8718 : Upper (D 8) (R 8) [34,65,40,272,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8718 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8719 : Route 9 := (fun mask => (mask,id))

def c8719 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u8719 : Upper (D 8) (R 8) [34,65,40,272,132] 13 := by
  apply FastRouting.sound _ _ [34,65,40,272,132] 13 (by decide) (choices 1) [1,64,128] r8719 c8719
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1910
  · exact u1911
  · exact u1912

def r8720 : Route 9 := (fun mask => (mask,id))

def c8720 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u8720 : Upper (D 8) (R 8) [34,65,40,272,160] 13 := by
  apply FastRouting.sound _ _ [34,65,40,272,160] 13 (by decide) (choices 1) [1,4,64,128] r8720 c8720
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1913
  · exact u1914
  · exact u1915
  · exact u1916

def r8721 : Route 9 := (fun mask => (mask,id))

def c8721 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8721 : Upper (D 8) (R 8) [34,65,40,272,192] 13 := by
  apply FastRouting.sound _ _ [34,65,40,272,192] 13 (by decide) (choices 1) [1,4,128] r8721 c8721
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1917
  · exact u1918
  · exact u1919

def b8722 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 296 84 177 209 145 401), lower := (rows 35 67 44 296 84 32 64 128 256), losses := [] }

theorem u8722 : Upper (D 8) (R 8) [34,65,40,288,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8722 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8723 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 296 148 241 209 209 465), lower := (rows 35 67 44 296 148 32 64 128 256), losses := [] }

theorem u8723 : Upper (D 8) (R 8) [34,65,40,288,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8723 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8724 : PairBound 9 := { available := 149, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 296 208 181 213 149 405), lower := (rows 35 67 44 296 208 32 64 128 256), losses := [] }

theorem u8724 : Upper (D 8) (R 8) [34,65,40,288,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8724 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8725 : PairBound 9 := { available := 180, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 328 145 180 244 180 436), lower := (rows 35 67 44 328 145 32 64 128 256), losses := [] }

theorem u8725 : Upper (D 8) (R 8) [34,65,40,320,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8725 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8726 : Route 9 := (fun mask => (mask,id))

def c8726 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8726 : Upper (D 8) (R 8) [34,65,40,320,132] 13 := by
  apply FastRouting.sound _ _ [34,65,40,320,132] 13 (by decide) (choices 1) [1,16,128] r8726 c8726
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1920
  · exact u1921
  · exact u1922

def r8727 : Route 9 := (fun mask => (mask,id))

def c8727 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8727 : Upper (D 8) (R 8) [34,65,40,320,160] 13 := by
  apply FastRouting.sound _ _ [34,65,40,320,160] 13 (by decide) (choices 1) [1,4,16,128] r8727 c8727
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1923
  · exact u1924
  · exact u1925
  · exact u1926

def b8728 : PairBound 9 := { available := 180, camps := [{ cop := 1, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 35 67 44 392 81 180 244 180 436), lower := (rows 35 67 44 392 81 32 64 128 256), losses := [] }

theorem u8728 : Upper (D 8) (R 8) [34,65,40,384,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8728 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8729 : Route 9 := (fun mask => (mask,id))

def c8729 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8729 : Upper (D 8) (R 8) [34,65,40,384,68] 13 := by
  apply FastRouting.sound _ _ [34,65,40,384,68] 13 (by decide) (choices 1) [1,16,128] r8729 c8729
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1927
  · exact u1928
  · exact u1929

def b8730 : PairBound 9 := { available := 149, camps := [{ cop := 4, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 44 392 112 181 213 149 405), lower := (rows 35 67 44 392 112 32 64 128 256), losses := [] }

theorem u8730 : Upper (D 8) (R 8) [34,65,40,384,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8730 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8731 : PairBound 9 := { available := 116, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 392 145 116 116 244 372), lower := (rows 35 67 44 392 145 32 64 128 256), losses := [] }

theorem u8731 : Upper (D 8) (R 8) [34,65,40,384,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8731 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8732 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 44 392 148 113 113 241 369), lower := (rows 35 67 44 392 148 32 64 128 256), losses := [] }

theorem u8732 : Upper (D 8) (R 8) [34,65,40,384,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8732 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8733 : Route 9 := (fun mask => (mask,id))

def c8733 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8733 : Upper (D 8) (R 8) [34,65,40,384,160] 13 := by
  apply FastRouting.sound _ _ [34,65,40,384,160] 13 (by decide) (choices 1) [1,4,16,64] r8733 c8733
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1930
  · exact u1931
  · exact u1932
  · exact u1933

def r8734 : Route 9 := (fun mask => (mask,id))

def c8734 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8734 : Upper (D 8) (R 8) [34,65,40,384,192] 13 := by
  apply FastRouting.sound _ _ [34,65,40,384,192] 13 (by decide) (choices 1) [1,4,16] r8734 c8734
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1934
  · exact u1935
  · exact u1936

def b8735 : PairBound 9 := { available := 312, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 69 140 176 312 376 440 312), lower := (rows 35 67 69 140 176 32 64 128 256), losses := [] }

theorem u8735 : Upper (D 8) (R 8) [34,65,65,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8735 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8736 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 69 140 280 176 240 176 432), lower := (rows 35 67 69 140 280 32 64 128 256), losses := [] }

theorem u8736 : Upper (D 8) (R 8) [34,65,65,132,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8736 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8737 : PairBound 9 := { available := 184, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 69 140 304 184 248 184 440), lower := (rows 35 67 69 140 304 32 64 128 256), losses := [] }

theorem u8737 : Upper (D 8) (R 8) [34,65,65,132,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8737 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8738 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 69 140 400 56 120 184 312), lower := (rows 35 67 69 140 400 32 64 128 256), losses := [] }

theorem u8738 : Upper (D 8) (R 8) [34,65,65,132,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8738 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8739 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 69 152 276 168 232 168 424), lower := (rows 35 67 69 152 276 32 64 128 256), losses := [] }

theorem u8739 : Upper (D 8) (R 8) [34,65,65,144,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8739 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8740 : PairBound 9 := { available := 164, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 69 152 280 164 228 164 420), lower := (rows 35 67 69 152 280 32 64 128 256), losses := [] }

theorem u8740 : Upper (D 8) (R 8) [34,65,65,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8740 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8741 : PairBound 9 := { available := 172, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 69 152 304 172 236 172 428), lower := (rows 35 67 69 152 304 32 64 128 256), losses := [] }

theorem u8741 : Upper (D 8) (R 8) [34,65,65,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8741 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8742 : PairBound 9 := { available := 184, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 69 168 276 184 248 184 440), lower := (rows 35 67 69 168 276 32 64 128 256), losses := [] }

theorem u8742 : Upper (D 8) (R 8) [34,65,65,160,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8742 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8743 : PairBound 9 := { available := 180, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 69 168 280 180 244 180 436), lower := (rows 35 67 69 168 280 32 64 128 256), losses := [] }

theorem u8743 : Upper (D 8) (R 8) [34,65,65,160,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8743 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8744 : PairBound 9 := { available := 156, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 69 168 304 188 220 156 412), lower := (rows 35 67 69 168 304 32 64 128 256), losses := [] }

theorem u8744 : Upper (D 8) (R 8) [34,65,65,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8744 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8745 : PairBound 9 := { available := 60, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 69 168 400 60 124 188 316), lower := (rows 35 67 69 168 400 32 64 128 256), losses := [] }

theorem u8745 : Upper (D 8) (R 8) [34,65,65,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8745 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8746 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 76 137 148 304 368 432 304), lower := (rows 35 67 76 137 148 32 64 128 256), losses := [] }

theorem u8746 : Upper (D 8) (R 8) [34,65,72,129,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8746 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8747 : PairBound 9 := { available := 308, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 76 137 176 308 372 436 308), lower := (rows 35 67 76 137 176 32 64 128 256), losses := [] }

theorem u8747 : Upper (D 8) (R 8) [34,65,72,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8747 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8748 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 76 137 276 176 240 176 432), lower := (rows 35 67 76 137 276 32 64 128 256), losses := [] }

theorem u8748 : Upper (D 8) (R 8) [34,65,72,129,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8748 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8749 : PairBound 9 := { available := 180, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 76 137 304 180 244 180 436), lower := (rows 35 67 76 137 304 32 64 128 256), losses := [] }

theorem u8749 : Upper (D 8) (R 8) [34,65,72,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8749 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8750 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 76 137 400 52 116 180 308), lower := (rows 35 67 76 137 400 32 64 128 256), losses := [] }

theorem u8750 : Upper (D 8) (R 8) [34,65,72,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8750 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8751 : PairBound 9 := { available := 305, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 76 140 176 305 369 433 305), lower := (rows 35 67 76 140 176 32 64 128 256), losses := [] }

theorem u8751 : Upper (D 8) (R 8) [34,65,72,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8751 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8752 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 76 140 304 177 241 177 433), lower := (rows 35 67 76 140 304 32 64 128 256), losses := [] }

theorem u8752 : Upper (D 8) (R 8) [34,65,72,132,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8752 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8753 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 76 140 400 49 113 177 305), lower := (rows 35 67 76 140 400 32 64 128 256), losses := [] }

theorem u8753 : Upper (D 8) (R 8) [34,65,72,132,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8753 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8754 : PairBound 9 := { available := 292, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 76 152 145 292 356 420 292), lower := (rows 35 67 76 152 145 32 64 128 256), losses := [] }

theorem u8754 : Upper (D 8) (R 8) [34,65,72,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8754 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8755 : PairBound 9 := { available := 289, camps := [{ cop := 3, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 76 152 148 289 353 417 289), lower := (rows 35 67 76 152 148 32 64 128 256), losses := [] }

theorem u8755 : Upper (D 8) (R 8) [34,65,72,144,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8755 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8756 : PairBound 9 := { available := 293, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 76 152 176 293 357 421 293), lower := (rows 35 67 76 152 176 32 64 128 256), losses := [] }

theorem u8756 : Upper (D 8) (R 8) [34,65,72,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8756 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8757 : PairBound 9 := { available := 164, camps := [{ cop := 4, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 76 152 273 164 228 164 420), lower := (rows 35 67 76 152 273 32 64 128 256), losses := [] }

theorem u8757 : Upper (D 8) (R 8) [34,65,72,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8757 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8758 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 76 152 276 161 225 161 417), lower := (rows 35 67 76 152 276 32 64 128 256), losses := [] }

theorem u8758 : Upper (D 8) (R 8) [34,65,72,144,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8758 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8759 : Route 9 := (fun mask => (mask,id))

def c8759 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8759 : Upper (D 8) (R 8) [34,65,72,144,288] 13 := by
  apply FastRouting.sound _ _ [34,65,72,144,288] 13 (by decide) (choices 1) [1,4,128] r8759 c8759
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1937
  · exact u1938
  · exact u1939

#print axioms u8759
end Delivery.IrregularNine14.P08

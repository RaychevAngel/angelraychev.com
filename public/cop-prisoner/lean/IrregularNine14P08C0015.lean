import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0000

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b900 : PairBound 9 := { available := 208, camps := [{ cop := 5, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 100 168 304 33 208 208 464), lower := (rows 7 11 100 168 304 33 64 128 256), losses := [] }

theorem u900 : Upper (D 8) (R 8) [6,9,96,160,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b900 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b901 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 7 11 100 168 304 48 193 193 449), lower := (rows 7 11 100 168 304 48 64 128 256), losses := [] }

theorem u901 : Upper (D 8) (R 8) [6,9,96,160,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b901 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b902 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 100 168 304 96 209 145 401), lower := (rows 7 11 100 168 304 96 64 128 256), losses := [] }

theorem u902 : Upper (D 8) (R 8) [6,9,96,160,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b902 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b903 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 100 168 304 160 81 209 337), lower := (rows 7 11 100 168 304 160 64 128 256), losses := [] }

theorem u903 : Upper (D 8) (R 8) [6,9,96,160,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b903 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b904 : PairBound 9 := { available := 176, camps := [{ cop := 5, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 100 168 336 33 240 176 432), lower := (rows 7 11 100 168 336 33 64 128 256), losses := [] }

theorem u904 : Upper (D 8) (R 8) [6,9,96,160,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b904 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b905 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 7 11 100 168 336 48 225 161 417), lower := (rows 7 11 100 168 336 48 64 128 256), losses := [] }

theorem u905 : Upper (D 8) (R 8) [6,9,96,160,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b905 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b906 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 100 168 336 160 113 177 305), lower := (rows 7 11 100 168 336 160 64 128 256), losses := [] }

theorem u906 : Upper (D 8) (R 8) [6,9,96,160,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b906 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b907 : PairBound 9 := { available := 112, camps := [{ cop := 5, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 100 168 400 33 112 240 368), lower := (rows 7 11 100 168 400 33 64 128 256), losses := [] }

theorem u907 : Upper (D 8) (R 8) [6,9,96,160,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b907 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b908 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 7 11 100 168 400 48 97 225 353), lower := (rows 7 11 100 168 400 48 64 128 256), losses := [] }

theorem u908 : Upper (D 8) (R 8) [6,9,96,160,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b908 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b909 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 100 168 400 96 113 177 305), lower := (rows 7 11 100 168 400 96 64 128 256), losses := [] }

theorem u909 : Upper (D 8) (R 8) [6,9,96,160,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b909 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b910 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 196, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 100 280 176 33 224 224 480), lower := (rows 7 11 100 280 176 33 64 128 256), losses := [] }

theorem u910 : Upper (D 8) (R 8) [6,9,96,272,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b910 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b911 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 100 280 176 96 225 161 417), lower := (rows 7 11 100 280 176 96 64 128 256), losses := [] }

theorem u911 : Upper (D 8) (R 8) [6,9,96,272,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b911 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b912 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 100 280 176 160 97 225 353), lower := (rows 7 11 100 280 176 160 64 128 256), losses := [] }

theorem u912 : Upper (D 8) (R 8) [6,9,96,272,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b912 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b913 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 196, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 100 280 208 33 224 160 416), lower := (rows 7 11 100 280 208 33 64 128 256), losses := [] }

theorem u913 : Upper (D 8) (R 8) [6,9,96,272,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b913 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b914 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 36, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 100 280 208 160 97 161 289), lower := (rows 7 11 100 280 208 160 64 128 256), losses := [] }

theorem u914 : Upper (D 8) (R 8) [6,9,96,272,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b914 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b915 : PairBound 9 := { available := 208, camps := [{ cop := 5, region := 212, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 100 296 176 33 208 208 464), lower := (rows 7 11 100 296 176 33 64 128 256), losses := [] }

theorem u915 : Upper (D 8) (R 8) [6,9,96,288,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b915 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b916 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 7 11 100 296 176 48 193 193 449), lower := (rows 7 11 100 296 176 48 64 128 256), losses := [] }

theorem u916 : Upper (D 8) (R 8) [6,9,96,288,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b916 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b917 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 100 296 176 96 209 145 401), lower := (rows 7 11 100 296 176 96 64 128 256), losses := [] }

theorem u917 : Upper (D 8) (R 8) [6,9,96,288,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b917 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b918 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 100 296 176 160 81 209 337), lower := (rows 7 11 100 296 176 160 64 128 256), losses := [] }

theorem u918 : Upper (D 8) (R 8) [6,9,96,288,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b918 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b919 : PairBound 9 := { available := 176, camps := [{ cop := 5, region := 212, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 100 296 208 33 240 176 432), lower := (rows 7 11 100 296 208 33 64 128 256), losses := [] }

theorem u919 : Upper (D 8) (R 8) [6,9,96,288,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b919 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b920 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 7 11 100 296 208 48 225 161 417), lower := (rows 7 11 100 296 208 48 64 128 256), losses := [] }

theorem u920 : Upper (D 8) (R 8) [6,9,96,288,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b920 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b921 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 36, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 100 296 208 160 113 177 305), lower := (rows 7 11 100 296 208 160 64 128 256), losses := [] }

theorem u921 : Upper (D 8) (R 8) [6,9,96,288,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b921 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b922 : PairBound 9 := { available := 112, camps := [{ cop := 5, region := 212, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 100 392 176 33 112 240 368), lower := (rows 7 11 100 392 176 33 64 128 256), losses := [] }

theorem u922 : Upper (D 8) (R 8) [6,9,96,384,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b922 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b923 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 7 11 100 392 176 48 97 225 353), lower := (rows 7 11 100 392 176 48 64 128 256), losses := [] }

theorem u923 : Upper (D 8) (R 8) [6,9,96,384,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b923 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b924 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 100 392 176 96 113 177 305), lower := (rows 7 11 100 392 176 96 64 128 256), losses := [] }

theorem u924 : Upper (D 8) (R 8) [6,9,96,384,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b924 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b925 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 212, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 100 392 208 33 112 176 304), lower := (rows 7 11 100 392 208 33 64 128 256), losses := [] }

theorem u925 : Upper (D 8) (R 8) [6,9,96,384,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b925 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b926 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 7 11 100 392 208 48 97 161 289), lower := (rows 7 11 100 392 208 48 64 128 256), losses := [] }

theorem u926 : Upper (D 8) (R 8) [6,9,96,384,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b926 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b927 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 196, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 196 56 336 33 224 160 416), lower := (rows 7 11 196 56 336 33 64 128 256), losses := [] }

theorem u927 : Upper (D 8) (R 8) [6,9,192,48,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b927 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r928 : Route 9 := (fun mask => (mask,id))

def c928 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u928 : Upper (D 8) (R 8) [6,9,192,48,320,128] 13 := by
  apply FastRouting.sound _ _ [6,9,192,48,320,128] 13 (by decide) (choices 1) [1,32] r928 c928
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u28
  · exact u29

def b929 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 196, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 196 280 112 33 224 160 416), lower := (rows 7 11 196 280 112 33 64 128 256), losses := [] }

theorem u929 : Upper (D 8) (R 8) [6,9,192,272,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b929 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b930 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 48, targets := 1 }], pairs := [(4,0)], upper := (rows 7 11 196 280 112 160 97 161 289), lower := (rows 7 11 196 280 112 160 64 128 256), losses := [] }

theorem u930 : Upper (D 8) (R 8) [6,9,192,272,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b930 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b931 : PairBound 9 := { available := 176, camps := [{ cop := 5, region := 212, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 196 296 112 33 240 176 432), lower := (rows 7 11 196 296 112 33 64 128 256), losses := [] }

theorem u931 : Upper (D 8) (R 8) [6,9,192,288,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b931 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b932 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 7 11 196 296 112 48 225 161 417), lower := (rows 7 11 196 296 112 48 64 128 256), losses := [] }

theorem u932 : Upper (D 8) (R 8) [6,9,192,288,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b932 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b933 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 48, targets := 1 }], pairs := [(4,0)], upper := (rows 7 11 196 296 112 160 113 177 305), lower := (rows 7 11 196 296 112 160 64 128 256), losses := [] }

theorem u933 : Upper (D 8) (R 8) [6,9,192,288,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b933 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b934 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 276 104 176 33 224 224 480), lower := (rows 7 11 276 104 176 33 64 128 256), losses := [] }

theorem u934 : Upper (D 8) (R 8) [6,9,272,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b934 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b935 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 276 104 176 96 225 161 417), lower := (rows 7 11 276 104 176 96 64 128 256), losses := [] }

theorem u935 : Upper (D 8) (R 8) [6,9,272,96,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b935 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b936 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 276 104 176 160 97 225 353), lower := (rows 7 11 276 104 176 160 64 128 256), losses := [] }

theorem u936 : Upper (D 8) (R 8) [6,9,272,96,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b936 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b937 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 276 104 208 33 224 160 416), lower := (rows 7 11 276 104 208 33 64 128 256), losses := [] }

theorem u937 : Upper (D 8) (R 8) [6,9,272,96,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b937 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b938 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 40, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 276 104 208 160 97 161 289), lower := (rows 7 11 276 104 208 160 64 128 256), losses := [] }

theorem u938 : Upper (D 8) (R 8) [6,9,272,96,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b938 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b939 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 276 200 112 33 224 160 416), lower := (rows 7 11 276 200 112 33 64 128 256), losses := [] }

theorem u939 : Upper (D 8) (R 8) [6,9,272,192,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b939 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b940 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 48, targets := 1 }], pairs := [(4,0)], upper := (rows 7 11 276 200 112 160 97 161 289), lower := (rows 7 11 276 200 112 160 64 128 256), losses := [] }

theorem u940 : Upper (D 8) (R 8) [6,9,272,192,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b940 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b941 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 452, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 292 56 208 33 224 224 480), lower := (rows 7 11 292 56 208 33 64 128 256), losses := [] }

theorem u941 : Upper (D 8) (R 8) [6,9,288,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b941 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b942 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 292 56 208 96 225 161 417), lower := (rows 7 11 292 56 208 96 64 128 256), losses := [] }

theorem u942 : Upper (D 8) (R 8) [6,9,288,48,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b942 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b943 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 452, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 292 88 176 33 224 224 480), lower := (rows 7 11 292 88 176 33 64 128 256), losses := [] }

theorem u943 : Upper (D 8) (R 8) [6,9,288,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b943 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r944 : Route 9 := (fun mask => (mask,id))

def c944 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u944 : Upper (D 8) (R 8) [6,9,288,80,160,64] 13 := by
  apply FastRouting.sound _ _ [6,9,288,80,160,64] 13 (by decide) (choices 1) [1,32,128] r944 c944
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u30
  · exact u31
  · exact u32

def b945 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 292 88 176 160 97 225 353), lower := (rows 7 11 292 88 176 160 64 128 256), losses := [] }

theorem u945 : Upper (D 8) (R 8) [6,9,288,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b945 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b946 : PairBound 9 := { available := 208, camps := [{ cop := 5, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 292 104 176 33 208 208 464), lower := (rows 7 11 292 104 176 33 64 128 256), losses := [] }

theorem u946 : Upper (D 8) (R 8) [6,9,288,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b946 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b947 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 7 11 292 104 176 48 193 193 449), lower := (rows 7 11 292 104 176 48 64 128 256), losses := [] }

theorem u947 : Upper (D 8) (R 8) [6,9,288,96,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b947 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b948 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 292 104 176 96 209 145 401), lower := (rows 7 11 292 104 176 96 64 128 256), losses := [] }

theorem u948 : Upper (D 8) (R 8) [6,9,288,96,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b948 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b949 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 292 104 176 160 81 209 337), lower := (rows 7 11 292 104 176 160 64 128 256), losses := [] }

theorem u949 : Upper (D 8) (R 8) [6,9,288,96,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b949 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b950 : PairBound 9 := { available := 176, camps := [{ cop := 5, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 292 104 208 33 240 176 432), lower := (rows 7 11 292 104 208 33 64 128 256), losses := [] }

theorem u950 : Upper (D 8) (R 8) [6,9,288,96,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b950 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b951 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 7 11 292 104 208 48 225 161 417), lower := (rows 7 11 292 104 208 48 64 128 256), losses := [] }

theorem u951 : Upper (D 8) (R 8) [6,9,288,96,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b951 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b952 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 40, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 292 104 208 160 113 177 305), lower := (rows 7 11 292 104 208 160 64 128 256), losses := [] }

theorem u952 : Upper (D 8) (R 8) [6,9,288,96,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b952 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b953 : PairBound 9 := { available := 176, camps := [{ cop := 5, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 292 200 112 33 240 176 432), lower := (rows 7 11 292 200 112 33 64 128 256), losses := [] }

theorem u953 : Upper (D 8) (R 8) [6,9,288,192,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b953 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b954 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 7 11 292 200 112 48 225 161 417), lower := (rows 7 11 292 200 112 48 64 128 256), losses := [] }

theorem u954 : Upper (D 8) (R 8) [6,9,288,192,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b954 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b955 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 48, targets := 1 }], pairs := [(4,0)], upper := (rows 7 11 292 200 112 160 113 177 305), lower := (rows 7 11 292 200 112 160 64 128 256), losses := [] }

theorem u955 : Upper (D 8) (R 8) [6,9,288,192,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b955 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b956 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 452, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 324 56 208 33 224 160 416), lower := (rows 7 11 324 56 208 33 64 128 256), losses := [] }

theorem u956 : Upper (D 8) (R 8) [6,9,320,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b956 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b957 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 324 56 208 160 97 161 289), lower := (rows 7 11 324 56 208 160 64 128 256), losses := [] }

theorem u957 : Upper (D 8) (R 8) [6,9,320,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b957 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b958 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 452, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 324 152 112 33 224 160 416), lower := (rows 7 11 324 152 112 33 64 128 256), losses := [] }

theorem u958 : Upper (D 8) (R 8) [6,9,320,144,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b958 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r959 : Route 9 := (fun mask => (mask,id))

def c959 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u959 : Upper (D 8) (R 8) [6,9,320,144,96,128] 13 := by
  apply FastRouting.sound _ _ [6,9,320,144,96,128] 13 (by decide) (choices 1) [1,32] r959 c959
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u33
  · exact u34

#print axioms u959
end Delivery.IrregularNine14.P08

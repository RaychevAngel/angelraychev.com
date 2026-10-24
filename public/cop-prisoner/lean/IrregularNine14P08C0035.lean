import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2100 : PairBound 9 := { available := 289, camps := [], pairs := [], upper := (rows 35 70 133 56 208 40 353 417 289), lower := (rows 35 70 133 56 208 40 64 128 256), losses := [] }

theorem u2100 : Upper (D 8) (R 8) [34,68,129,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2100 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2101 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 35 70 133 56 208 288 105 169 297), lower := (rows 35 70 133 56 208 288 64 128 256), losses := [] }

theorem u2101 : Upper (D 8) (R 8) [34,68,129,48,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2101 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2102 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 133 56 280 33 224 224 480), lower := (rows 35 70 133 56 280 33 64 128 256), losses := [] }

theorem u2102 : Upper (D 8) (R 8) [34,68,129,48,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2102 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2103 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 132, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 133 56 280 96 225 161 417), lower := (rows 35 70 133 56 280 96 64 128 256), losses := [] }

theorem u2103 : Upper (D 8) (R 8) [34,68,129,48,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2103 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2104 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 344, targets := 128 }], pairs := [(3,7)], upper := (rows 35 70 133 56 280 160 97 225 353), lower := (rows 35 70 133 56 280 160 64 128 256), losses := [] }

theorem u2104 : Upper (D 8) (R 8) [34,68,129,48,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2104 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2105 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 133 56 336 33 232 168 424), lower := (rows 35 70 133 56 336 33 64 128 256), losses := [] }

theorem u2105 : Upper (D 8) (R 8) [34,68,129,48,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2105 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2106 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 70 133 56 336 40 225 161 417), lower := (rows 35 70 133 56 336 40 64 128 256), losses := [] }

theorem u2106 : Upper (D 8) (R 8) [34,68,129,48,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2106 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2107 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 344, targets := 128 }], pairs := [(3,7)], upper := (rows 35 70 133 56 336 160 105 169 297), lower := (rows 35 70 133 56 336 160 64 128 256), losses := [] }

theorem u2107 : Upper (D 8) (R 8) [34,68,129,48,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2107 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2108 : PairBound 9 := { available := 104, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 133 56 400 33 104 232 360), lower := (rows 35 70 133 56 400 33 64 128 256), losses := [] }

theorem u2108 : Upper (D 8) (R 8) [34,68,129,48,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2108 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2109 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 35 70 133 56 400 40 97 225 353), lower := (rows 35 70 133 56 400 40 64 128 256), losses := [] }

theorem u2109 : Upper (D 8) (R 8) [34,68,129,48,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2109 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2110 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 133 56 400 96 105 169 297), lower := (rows 35 70 133 56 400 96 64 128 256), losses := [] }

theorem u2110 : Upper (D 8) (R 8) [34,68,129,48,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2110 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2111 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 133 88 176 33 360 424 296), lower := (rows 35 70 133 88 176 33 64 128 256), losses := [] }

theorem u2111 : Upper (D 8) (R 8) [34,68,129,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2111 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2112 : PairBound 9 := { available := 289, camps := [], pairs := [], upper := (rows 35 70 133 88 176 40 353 417 289), lower := (rows 35 70 133 88 176 40 64 128 256), losses := [] }

theorem u2112 : Upper (D 8) (R 8) [34,68,129,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2112 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2113 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 35 70 133 88 176 288 105 169 297), lower := (rows 35 70 133 88 176 288 64 128 256), losses := [] }

theorem u2113 : Upper (D 8) (R 8) [34,68,129,80,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2113 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2114 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 133 88 304 33 232 168 424), lower := (rows 35 70 133 88 304 33 64 128 256), losses := [] }

theorem u2114 : Upper (D 8) (R 8) [34,68,129,80,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2114 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2115 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 70 133 88 304 40 225 161 417), lower := (rows 35 70 133 88 304 40 64 128 256), losses := [] }

theorem u2115 : Upper (D 8) (R 8) [34,68,129,80,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2115 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2116 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 344, targets := 128 }], pairs := [(3,7)], upper := (rows 35 70 133 88 304 160 105 169 297), lower := (rows 35 70 133 88 304 160 64 128 256), losses := [] }

theorem u2116 : Upper (D 8) (R 8) [34,68,129,80,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2116 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2117 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 133 88 400 33 104 168 296), lower := (rows 35 70 133 88 400 33 64 128 256), losses := [] }

theorem u2117 : Upper (D 8) (R 8) [34,68,129,80,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2117 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2118 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 70 133 88 400 40 97 161 289), lower := (rows 35 70 133 88 400 40 64 128 256), losses := [] }

theorem u2118 : Upper (D 8) (R 8) [34,68,129,80,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2118 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2119 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 133 104 152 33 368 432 304), lower := (rows 35 70 133 104 152 33 64 128 256), losses := [] }

theorem u2119 : Upper (D 8) (R 8) [34,68,129,96,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2119 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2120 : PairBound 9 := { available := 289, camps := [], pairs := [], upper := (rows 35 70 133 104 152 48 353 417 289), lower := (rows 35 70 133 104 152 48 64 128 256), losses := [] }

theorem u2120 : Upper (D 8) (R 8) [34,68,129,96,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2120 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2121 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 35 70 133 104 152 288 113 177 305), lower := (rows 35 70 133 104 152 288 64 128 256), losses := [] }

theorem u2121 : Upper (D 8) (R 8) [34,68,129,96,136,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2121 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2122 : PairBound 9 := { available := 280, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 133 104 176 33 344 408 280), lower := (rows 35 70 133 104 176 33 64 128 256), losses := [] }

theorem u2122 : Upper (D 8) (R 8) [34,68,129,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2122 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2123 : PairBound 9 := { available := 273, camps := [], pairs := [], upper := (rows 35 70 133 104 176 40 337 401 273), lower := (rows 35 70 133 104 176 40 64 128 256), losses := [] }

theorem u2123 : Upper (D 8) (R 8) [34,68,129,96,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2123 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2124 : PairBound 9 := { available := 265, camps := [], pairs := [], upper := (rows 35 70 133 104 176 48 329 393 265), lower := (rows 35 70 133 104 176 48 64 128 256), losses := [] }

theorem u2124 : Upper (D 8) (R 8) [34,68,129,96,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2124 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2125 : PairBound 9 := { available := 25, camps := [], pairs := [], upper := (rows 35 70 133 104 176 288 89 153 281), lower := (rows 35 70 133 104 176 288 64 128 256), losses := [] }

theorem u2125 : Upper (D 8) (R 8) [34,68,129,96,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2125 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2126 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 133 104 280 33 240 176 432), lower := (rows 35 70 133 104 280 33 64 128 256), losses := [] }

theorem u2126 : Upper (D 8) (R 8) [34,68,129,96,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2126 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2127 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 70 133 104 280 48 225 161 417), lower := (rows 35 70 133 104 280 48 64 128 256), losses := [] }

theorem u2127 : Upper (D 8) (R 8) [34,68,129,96,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2127 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2128 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 344, targets := 128 }], pairs := [(3,7)], upper := (rows 35 70 133 104 280 160 113 177 305), lower := (rows 35 70 133 104 280 160 64 128 256), losses := [] }

theorem u2128 : Upper (D 8) (R 8) [34,68,129,96,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2128 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2129 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 133 104 304 33 216 152 408), lower := (rows 35 70 133 104 304 33 64 128 256), losses := [] }

theorem u2129 : Upper (D 8) (R 8) [34,68,129,96,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2129 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2130 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 35 70 133 104 304 40 209 145 401), lower := (rows 35 70 133 104 304 40 64 128 256), losses := [] }

theorem u2130 : Upper (D 8) (R 8) [34,68,129,96,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2130 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2131 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 35 70 133 104 304 48 201 137 393), lower := (rows 35 70 133 104 304 48 64 128 256), losses := [] }

theorem u2131 : Upper (D 8) (R 8) [34,68,129,96,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2131 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2132 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 344, targets := 128 }], pairs := [(3,7)], upper := (rows 35 70 133 104 304 160 89 153 281), lower := (rows 35 70 133 104 304 160 64 128 256), losses := [] }

theorem u2132 : Upper (D 8) (R 8) [34,68,129,96,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2132 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2133 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 133 104 400 33 120 184 312), lower := (rows 35 70 133 104 400 33 64 128 256), losses := [] }

theorem u2133 : Upper (D 8) (R 8) [34,68,129,96,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2133 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2134 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 35 70 133 104 400 40 113 177 305), lower := (rows 35 70 133 104 400 40 64 128 256), losses := [] }

theorem u2134 : Upper (D 8) (R 8) [34,68,129,96,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2134 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2135 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 35 70 133 104 400 48 105 169 297), lower := (rows 35 70 133 104 400 48 64 128 256), losses := [] }

theorem u2135 : Upper (D 8) (R 8) [34,68,129,96,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2135 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2136 : PairBound 9 := { available := 104, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 133 152 304 33 104 232 360), lower := (rows 35 70 133 152 304 33 64 128 256), losses := [] }

theorem u2136 : Upper (D 8) (R 8) [34,68,129,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2136 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2137 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 35 70 133 152 304 40 97 225 353), lower := (rows 35 70 133 152 304 40 64 128 256), losses := [] }

theorem u2137 : Upper (D 8) (R 8) [34,68,129,144,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2137 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2138 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 133 152 304 96 105 169 297), lower := (rows 35 70 133 152 304 96 64 128 256), losses := [] }

theorem u2138 : Upper (D 8) (R 8) [34,68,129,144,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2138 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2139 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 133 152 336 33 104 168 296), lower := (rows 35 70 133 152 336 33 64 128 256), losses := [] }

theorem u2139 : Upper (D 8) (R 8) [34,68,129,144,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2139 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2140 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 70 133 152 336 40 97 161 289), lower := (rows 35 70 133 152 336 40 64 128 256), losses := [] }

theorem u2140 : Upper (D 8) (R 8) [34,68,129,144,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2140 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2141 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 133 168 280 33 112 240 368), lower := (rows 35 70 133 168 280 33 64 128 256), losses := [] }

theorem u2141 : Upper (D 8) (R 8) [34,68,129,160,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2141 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2142 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 35 70 133 168 280 48 97 225 353), lower := (rows 35 70 133 168 280 48 64 128 256), losses := [] }

theorem u2142 : Upper (D 8) (R 8) [34,68,129,160,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2142 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2143 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 133 168 280 96 113 177 305), lower := (rows 35 70 133 168 280 96 64 128 256), losses := [] }

theorem u2143 : Upper (D 8) (R 8) [34,68,129,160,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2143 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2144 : PairBound 9 := { available := 88, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 133 168 304 33 88 216 344), lower := (rows 35 70 133 168 304 33 64 128 256), losses := [] }

theorem u2144 : Upper (D 8) (R 8) [34,68,129,160,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2144 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2145 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 35 70 133 168 304 40 81 209 337), lower := (rows 35 70 133 168 304 40 64 128 256), losses := [] }

theorem u2145 : Upper (D 8) (R 8) [34,68,129,160,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2145 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2146 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 35 70 133 168 304 48 73 201 329), lower := (rows 35 70 133 168 304 48 64 128 256), losses := [] }

theorem u2146 : Upper (D 8) (R 8) [34,68,129,160,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2146 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2147 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 133 168 304 96 89 153 281), lower := (rows 35 70 133 168 304 96 64 128 256), losses := [] }

theorem u2147 : Upper (D 8) (R 8) [34,68,129,160,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2147 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2148 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 133 168 336 33 120 184 312), lower := (rows 35 70 133 168 336 33 64 128 256), losses := [] }

theorem u2148 : Upper (D 8) (R 8) [34,68,129,160,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2148 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2149 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 35 70 133 168 336 40 113 177 305), lower := (rows 35 70 133 168 336 40 64 128 256), losses := [] }

theorem u2149 : Upper (D 8) (R 8) [34,68,129,160,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2149 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2150 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 35 70 133 168 336 48 105 169 297), lower := (rows 35 70 133 168 336 48 64 128 256), losses := [] }

theorem u2150 : Upper (D 8) (R 8) [34,68,129,160,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2150 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2151 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 133 200 280 33 112 176 304), lower := (rows 35 70 133 200 280 33 64 128 256), losses := [] }

theorem u2151 : Upper (D 8) (R 8) [34,68,129,192,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2151 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2152 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 70 133 200 280 48 97 161 289), lower := (rows 35 70 133 200 280 48 64 128 256), losses := [] }

theorem u2152 : Upper (D 8) (R 8) [34,68,129,192,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2152 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2153 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 133 200 304 33 120 184 312), lower := (rows 35 70 133 200 304 33 64 128 256), losses := [] }

theorem u2153 : Upper (D 8) (R 8) [34,68,129,192,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2153 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2154 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 35 70 133 200 304 40 113 177 305), lower := (rows 35 70 133 200 304 40 64 128 256), losses := [] }

theorem u2154 : Upper (D 8) (R 8) [34,68,129,192,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2154 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2155 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 35 70 133 200 304 48 105 169 297), lower := (rows 35 70 133 200 304 48 64 128 256), losses := [] }

theorem u2155 : Upper (D 8) (R 8) [34,68,129,192,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2155 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2156 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 140 25 304 33 224 224 480), lower := (rows 35 70 140 25 304 33 64 128 256), losses := [] }

theorem u2156 : Upper (D 8) (R 8) [34,68,136,17,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2156 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2157 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 140 25 304 96 225 161 417), lower := (rows 35 70 140 25 304 96 64 128 256), losses := [] }

theorem u2157 : Upper (D 8) (R 8) [34,68,136,17,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2157 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2158 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 344, targets := 128 }], pairs := [(3,7)], upper := (rows 35 70 140 25 304 160 97 225 353), lower := (rows 35 70 140 25 304 160 64 128 256), losses := [] }

theorem u2158 : Upper (D 8) (R 8) [34,68,136,17,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2158 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2159 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 140 56 273 33 224 224 480), lower := (rows 35 70 140 56 273 33 64 128 256), losses := [] }

theorem u2159 : Upper (D 8) (R 8) [34,68,136,48,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2159 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u2159
end Delivery.IrregularNine14.P08

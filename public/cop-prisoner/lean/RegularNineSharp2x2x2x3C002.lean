import RegularNineSharp2x2x2x3Base
import RegularNineSharp2x2x2x3C000
import RegularNineSharp2x2x2x3C001
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp2x2x2x3
open Bounds BoundTreeRows Extremal
def cert128 : Leaf := ⟨⟨248,232,178,0,200,328,56,120,184⟩,[(3,0)],[(2,0,3),(8,4,5)],⟨7,19,76,13,304,176,194,424,360⟩,⟨7,19,76,13,304,176,194,384,320⟩,[⟨0,1266886668797206108046336,⟨502,114,508,508,304,176,242,432,368⟩⟩,⟨1,1229116942362256167927809,⟨445,185,508,445,304,176,240,432,368⟩⟩]⟩
theorem node128 : UpperPrefix a [2,4,6,0,8,7,1] 30 :=
  Boolean.leaf_sound a [2,4,6,0,8,7,1] 30 cert128 (by decide +kernel)

def cert129 : Local := ⟨⟨240,224,0,0,195,323,51,115,179⟩,[(2,6),(3,0)],[(2,0,3),(8,4,5),(3,6,2)]⟩
theorem node129 : UpperPrefix a [2,4,6,0,8,7,3] 30 :=
  local_sound a [2,4,6,0,8,7,3] 30 cert129 (by decide +kernel)

def cert130 : Leaf := ⟨⟨88,72,19,0,75,331,0,91,27⟩,[(3,0),(6,5)],[(2,0,3),(8,4,5),(7,5,6)],⟨7,19,76,13,304,176,224,394,330⟩,⟨7,19,76,13,304,176,224,384,320⟩,[⟨5,1513076888824603307172945,⟨15,155,461,13,415,155,463,396,461⟩⟩]⟩
theorem node130 : UpperPrefix a [2,4,6,0,8,7,5] 30 :=
  Boolean.leaf_sound a [2,4,6,0,8,7,5] 30 cert130 (by decide +kernel)

theorem node131 : UpperPrefix a [2,4,6,0,8,7] 30 :=
  branch_upper a [2,4,6,0,8,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,6,0,8,7,0] 30 (by decide +kernel))
  node128
  (invalid_upper a [2,4,6,0,8,7,2] 30 (by decide +kernel))
  node129
  (invalid_upper a [2,4,6,0,8,7,4] 30 (by decide +kernel))
  node130
  (invalid_upper a [2,4,6,0,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,0,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,0,8,7,8] 30 (by decide +kernel)))

theorem node132 : UpperPrefix a [2,4,6,0,8] 30 :=
  branch_upper a [2,4,6,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,6,0,8,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut37 [2,4,6,0,8,1] [2,4,6,0,7,1] 30 (by decide +kernel) node118)
  (invalid_upper a [2,4,6,0,8,2] 30 (by decide +kernel))
  node127
  (invalid_upper a [2,4,6,0,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,0,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,0,8,6] 30 (by decide +kernel))
  node131
  (invalid_upper a [2,4,6,0,8,8] 30 (by decide +kernel)))

theorem node133 : UpperPrefix a [2,4,6,0] 30 :=
  branch_upper a [2,4,6,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,6,0,0] 30 (by decide +kernel))
  node112
  (invalid_upper a [2,4,6,0,2] 30 (by decide +kernel))
  node114
  (invalid_upper a [2,4,6,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,0,6] 30 (by decide +kernel))
  node124
  node132)

theorem node134 : UpperPrefix a [2,4,6,1,0] 30 :=
  branch_upper a [2,4,6,1,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,6,1,0,0] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,1,0,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,1,0,2] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut36 [2,4,6,1,0,3] [2,4,1,5,6,0] 30 (by decide +kernel) node64)
  (invalid_upper a [2,4,6,1,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,1,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,1,0,6] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut38 [2,4,6,1,0,7] [2,4,1,6,8,0] 30 (by decide +kernel) node79)
  (PrefixConjugacy.upper aut37 [2,4,6,1,0,8] [2,4,1,6,7,0] 30 (by decide +kernel) node72))

def cert135 : Leaf := ⟨⟨0,484,433,0,449,449,305,113,177⟩,[(0,3),(3,0)],[],⟨7,19,76,14,56,433,481,417,481⟩,⟨7,19,76,14,56,48,192,384,320⟩,[⟨1,1224302388962685216620545,⟨485,497,92,508,60,48,192,384,320⟩⟩,⟨2,1224302388962685213475841,⟨483,499,88,506,56,48,192,384,320⟩⟩,⟨3,1337860978388404565713929,⟨487,499,453,487,499,498,192,384,320⟩⟩]⟩
theorem node135 : UpperPrefix a [2,4,6,1,3] 30 :=
  Boolean.leaf_sound a [2,4,6,1,3] 30 cert135 (by decide +kernel)

def cert136 : Leaf := ⟨⟨0,0,434,0,334,0,318,126,190⟩,[(0,3),(1,5),(3,0),(5,1)],[],⟨7,19,76,14,176,49,488,424,360⟩,⟨7,19,76,14,176,49,192,384,320⟩,[⟨0,1361519017103811155067904,⟨14,26,76,14,500,508,192,384,320⟩⟩]⟩
theorem node136 : UpperPrefix a [2,4,6,1,7,0] 30 :=
  Boolean.leaf_sound a [2,4,6,1,7,0] 30 cert136 (by decide +kernel)

def cert137 : Leaf := ⟨⟨0,164,163,0,71,135,295,103,167⟩,[(0,3),(3,0)],[],⟨7,19,76,14,176,56,481,417,353⟩,⟨7,19,76,14,176,56,192,384,320⟩,[⟨3,1361519017103809938736137,⟨7,19,69,7,498,499,192,384,320⟩⟩,⟨4,1361519017100512620184585,⟨15,11,77,15,484,493,192,384,320⟩⟩,⟨8,1181762219132417469901,⟨47,59,127,47,187,59,255,191,127⟩⟩,⟨6,1210106412432715957683209,⟨47,59,13,47,178,59,128,384,256⟩⟩]⟩
theorem node137 : UpperPrefix a [2,4,6,1,7,3] 30 :=
  Boolean.leaf_sound a [2,4,6,1,7,3] 30 cert137 (by decide +kernel)

def cert138 : Leaf := ⟨⟨0,164,179,0,256,128,63,127,191⟩,[(0,3),(3,0)],[(8,5,4)],⟨7,19,76,14,176,304,233,425,361⟩,⟨7,19,76,14,176,304,192,384,320⟩,[⟨3,1210107578807843634023437,⟨7,19,87,7,176,304,240,432,368⟩⟩,⟨6,1210106425886340772006925,⟨15,27,31,15,176,304,176,432,304⟩⟩,⟨0,1210107578807844841980928,⟨14,26,92,14,176,304,240,432,368⟩⟩,⟨1,1210107578807844707762177,⟨5,17,92,12,176,304,240,432,368⟩⟩,⟨2,1210107578807844706714625,⟨3,19,88,10,176,304,240,432,368⟩⟩]⟩
theorem node138 : UpperPrefix a [2,4,6,1,7,8] 30 :=
  Boolean.leaf_sound a [2,4,6,1,7,8] 30 cert138 (by decide +kernel)

theorem node139 : UpperPrefix a [2,4,6,1,7] 30 :=
  branch_upper a [2,4,6,1,7] 30 (by decide) (fin9_cases _
  node136
  (invalid_upper a [2,4,6,1,7,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,1,7,2] 30 (by decide +kernel))
  node137
  (invalid_upper a [2,4,6,1,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,1,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,1,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,1,7,7] 30 (by decide +kernel))
  node138)

def cert140 : Leaf := ⟨⟨0,292,291,0,71,263,295,103,167⟩,[(0,3),(3,0)],[],⟨7,19,76,14,304,56,225,417,481⟩,⟨7,19,76,14,304,56,192,384,320⟩,[⟨3,1361519017103809938736137,⟨7,19,69,7,498,499,192,384,320⟩⟩,⟨4,1361519017100512620184585,⟨15,11,77,15,484,493,192,384,320⟩⟩,⟨7,1208926990085502979532253,⟨47,59,111,47,319,59,127,319,383⟩⟩,⟨6,1210106412432715957683209,⟨47,59,13,47,306,59,128,384,256⟩⟩]⟩
theorem node140 : UpperPrefix a [2,4,6,1,8,3] 30 :=
  Boolean.leaf_sound a [2,4,6,1,8,3] 30 cert140 (by decide +kernel)

def cert141 : Leaf := ⟨⟨0,232,178,0,202,330,58,122,186⟩,[(0,3),(3,0)],[(8,4,5)],⟨7,19,76,14,304,176,193,424,360⟩,⟨7,19,76,14,304,176,193,384,320⟩,[⟨2,1229107736934248943224321,⟨499,115,506,442,304,176,243,432,370⟩⟩,⟨0,1531938702087869485286400,⟨446,186,508,446,304,176,508,432,500⟩⟩]⟩
theorem node141 : UpperPrefix a [2,4,6,1,8,7,0] 30 :=
  Boolean.leaf_sound a [2,4,6,1,8,7,0] 30 cert141 (by decide +kernel)

def cert142 : Leaf := ⟨⟨0,164,0,0,135,263,55,119,183⟩,[(0,3),(2,6),(3,0)],[(8,4,5),(3,6,2)],⟨7,19,76,14,304,176,200,417,353⟩,⟨7,19,76,14,304,176,200,384,320⟩,[⟨6,1210106419144135470515213,⟨15,27,47,15,304,176,187,432,306⟩⟩]⟩
theorem node142 : UpperPrefix a [2,4,6,1,8,7,3] 30 :=
  Boolean.leaf_sound a [2,4,6,1,8,7,3] 30 cert142 (by decide +kernel)

def cert143 : Leaf := ⟨⟨0,76,19,0,79,335,0,95,31⟩,[(0,3),(3,0),(6,5)],[(8,4,5),(7,5,6)],⟨7,19,76,14,304,176,224,393,329⟩,⟨7,19,76,14,304,176,224,384,320⟩,[⟨5,1534447441833960926110809,⟨399,155,461,399,415,155,463,388,461⟩⟩]⟩
theorem node143 : UpperPrefix a [2,4,6,1,8,7,5] 30 :=
  Boolean.leaf_sound a [2,4,6,1,8,7,5] 30 cert143 (by decide +kernel)

theorem node144 : UpperPrefix a [2,4,6,1,8,7] 30 :=
  branch_upper a [2,4,6,1,8,7] 30 (by decide) (fin9_cases _
  node141
  (invalid_upper a [2,4,6,1,8,7,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,1,8,7,2] 30 (by decide +kernel))
  node142
  (invalid_upper a [2,4,6,1,8,7,4] 30 (by decide +kernel))
  node143
  (invalid_upper a [2,4,6,1,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,1,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,1,8,7,8] 30 (by decide +kernel)))

theorem node145 : UpperPrefix a [2,4,6,1,8] 30 :=
  branch_upper a [2,4,6,1,8] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut37 [2,4,6,1,8,0] [2,4,6,1,7,0] 30 (by decide +kernel) node136)
  (invalid_upper a [2,4,6,1,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,1,8,2] 30 (by decide +kernel))
  node140
  (invalid_upper a [2,4,6,1,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,1,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,1,8,6] 30 (by decide +kernel))
  node144
  (invalid_upper a [2,4,6,1,8,8] 30 (by decide +kernel)))

theorem node146 : UpperPrefix a [2,4,6,1] 30 :=
  branch_upper a [2,4,6,1] 30 (by decide) (fin9_cases _
  node134
  (invalid_upper a [2,4,6,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,1,2] 30 (by decide +kernel))
  node135
  (invalid_upper a [2,4,6,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,1,6] 30 (by decide +kernel))
  node139
  node145)

def cert147 : Local := ⟨⟨0,500,0,481,385,448,305,113,177⟩,[(0,2),(2,1)],[(2,0,1),(3,1,0),(3,1,2),(1,2,0)]⟩
theorem node147 : UpperPrefix a [2,3,1,4,6,0] 30 :=
  local_sound a [2,3,1,4,6,0] 30 cert147 (by decide +kernel)

theorem node148 : UpperPrefix a [2,4,6,5,0] 30 :=
  branch_upper a [2,4,6,5,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,6,5,0,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut87 [2,4,6,5,0,1] [2,3,1,4,6,0] 30 (by decide +kernel) node147)
  (invalid_upper a [2,4,6,5,0,2] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut117 [2,4,6,5,0,3] [2,4,0,6,3,1] 30 (by decide +kernel) node65)
  (invalid_upper a [2,4,6,5,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,0,6] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut38 [2,4,6,5,0,7] [2,4,1,6,8,3] 30 (by decide +kernel) node82)
  (PrefixConjugacy.upper aut37 [2,4,6,5,0,8] [2,4,1,6,7,3] 30 (by decide +kernel) node76))

def cert149 : Local := ⟨⟨504,0,0,482,386,448,306,114,178⟩,[(1,2),(2,1)],[(2,0,1),(2,0,2),(3,1,0),(0,2,0)]⟩
theorem node149 : UpperPrefix a [2,3,0,4,6,1] 30 :=
  local_sound a [2,3,0,4,6,1] 30 cert149 (by decide +kernel)

theorem node150 : UpperPrefix a [2,4,6,5,1] 30 :=
  branch_upper a [2,4,6,5,1] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut84 [2,4,6,5,1,0] [2,3,0,4,6,1] 30 (by decide +kernel) node149)
  (invalid_upper a [2,4,6,5,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,1,2] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut90 [2,4,6,5,1,3] [2,4,0,5,1,6] 30 (by decide +kernel) node42)
  (invalid_upper a [2,4,6,5,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,1,6] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut38 [2,4,6,5,1,7] [2,4,0,6,8,3] 30 (by decide +kernel) node54)
  (PrefixConjugacy.upper aut37 [2,4,6,5,1,8] [2,4,0,6,7,3] 30 (by decide +kernel) node50))

def cert151 : Leaf := ⟨⟨24,12,403,467,0,451,259,67,131⟩,[(4,3)],[(5,3,4)],⟨7,19,76,44,56,435,451,387,451⟩,⟨7,19,76,44,56,48,192,384,320⟩,[⟨2,1224302388962685213475841,⟨483,499,88,56,56,48,192,384,320⟩⟩,⟨3,1224302388962134384968705,⟨487,499,68,36,48,48,192,384,320⟩⟩,⟨4,1224302388890667202905089,⟨455,451,76,44,40,32,192,384,320⟩⟩,⟨6,1210106412362896835099661,⟨7,19,31,63,59,50,128,384,256⟩⟩,⟨7,1208926973663684030643213,⟨7,19,95,63,59,50,64,256,320⟩⟩,⟨8,1181745669772267240461,⟨7,19,95,63,59,50,192,128,64⟩⟩]⟩
theorem node151 : UpperPrefix a [2,4,6,5,3] 30 :=
  Boolean.leaf_sound a [2,4,6,5,3] 30 cert151 (by decide +kernel)

def cert152 : Leaf := ⟨⟨144,132,144,144,68,132,279,87,151⟩,[],[(5,3,5),(3,5,3)],⟨7,19,76,44,176,56,451,387,323⟩,⟨7,19,76,44,176,56,192,384,320⟩,[⟨8,1181762219132417469901,⟨47,59,127,47,187,59,255,191,127⟩⟩,⟨0,1210107581833761591919616,⟨46,58,124,44,184,56,252,444,380⟩⟩,⟨1,1210107581833761591918593,⟨45,57,124,44,184,56,252,444,380⟩⟩,⟨6,1210106412432715957683209,⟨47,59,13,47,178,59,128,384,256⟩⟩]⟩
theorem node152 : UpperPrefix a [2,4,6,5,7,3] 30 :=
  Boolean.leaf_sound a [2,4,6,5,7,3] 30 cert152 (by decide +kernel)

def cert153 : Leaf := ⟨⟨176,160,176,208,256,128,58,123,187⟩,[],[(8,5,4)],⟨7,19,76,44,176,304,193,394,330⟩,⟨7,19,76,44,176,304,193,384,320⟩,[⟨2,1229033956700159406540289,⟨499,115,506,440,176,304,243,432,370⟩⟩,⟨0,1210107578807909216158720,⟨6,18,92,44,184,316,252,444,380⟩⟩,⟨1,1210107578807909216157697,⟨5,17,92,44,184,316,253,444,380⟩⟩,⟨3,1210107578807843634056205,⟨7,19,87,39,176,304,243,432,370⟩⟩,⟨6,1210106425886340100951053,⟨7,19,31,47,176,304,179,432,306⟩⟩]⟩
theorem node153 : UpperPrefix a [2,4,6,5,7,8,0] 30 :=
  Boolean.leaf_sound a [2,4,6,5,7,8,0] 30 cert153 (by decide +kernel)

def cert154 : Leaf := ⟨⟨240,224,176,208,320,192,49,120,184⟩,[],[(8,5,4),(0,7,6)],⟨7,19,76,44,176,304,194,385,328⟩,⟨7,19,76,44,176,304,194,385,320⟩,[⟨1,1531237725443010449113089,⟨445,185,380,300,184,316,508,445,380⟩⟩,⟨2,1229008916404069055137281,⟨499,243,376,296,242,368,242,499,368⟩⟩,⟨3,1210110172881228999494669,⟨7,83,87,39,242,368,242,499,368⟩⟩]⟩
theorem node154 : UpperPrefix a [2,4,6,5,7,8,1,0] 30 :=
  Boolean.leaf_sound a [2,4,6,5,7,8,1,0] 30 cert154 (by decide +kernel)

def cert155 : Leaf := ⟨⟨208,196,144,208,324,196,21,84,151⟩,[],[(8,5,4)],⟨7,19,76,44,176,304,194,392,321⟩,⟨7,19,76,44,176,304,194,392,320⟩,[⟨3,1842907284611617457769485,⟨295,371,375,295,498,368,498,499,368⟩⟩,⟨5,2414422148114116338803801,⟨455,339,461,463,471,339,455,461,321⟩⟩,⟨0,1212763909974864356705280,⟨6,18,92,188,184,444,254,444,508⟩⟩,⟨1,1212763909974864356704257,⟨5,17,92,188,184,444,252,444,508⟩⟩]⟩
theorem node155 : UpperPrefix a [2,4,6,5,7,8,1,3] 30 :=
  Boolean.leaf_sound a [2,4,6,5,7,8,1,3] 30 cert155 (by decide +kernel)

theorem node156 : UpperPrefix a [2,4,6,5,7,8,1] 30 :=
  branch_upper a [2,4,6,5,7,8,1] 30 (by decide) (fin9_cases _
  node154
  (invalid_upper a [2,4,6,5,7,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,7,8,1,2] 30 (by decide +kernel))
  node155
  (invalid_upper a [2,4,6,5,7,8,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,7,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,7,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,7,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,7,8,1,8] 30 (by decide +kernel)))

def cert157 : Leaf := ⟨⟨224,228,0,192,324,196,36,103,167⟩,[(2,6)],[(8,5,4),(3,6,2)],⟨7,19,76,44,176,304,200,387,323⟩,⟨7,19,76,44,176,304,200,384,320⟩,[⟨4,1224302659106651317470211,⟨455,463,76,44,236,364,204,384,324⟩⟩,⟨0,1210110172881296775709696,⟨6,94,92,44,252,380,252,508,380⟩⟩,⟨1,1210110172881296775708673,⟨5,93,92,44,252,380,252,508,380⟩⟩]⟩
theorem node157 : UpperPrefix a [2,4,6,5,7,8,3] 30 :=
  Boolean.leaf_sound a [2,4,6,5,7,8,3] 30 cert157 (by decide +kernel)

theorem node158 : UpperPrefix a [2,4,6,5,7,8] 30 :=
  branch_upper a [2,4,6,5,7,8] 30 (by decide) (fin9_cases _
  node153
  node156
  (invalid_upper a [2,4,6,5,7,8,2] 30 (by decide +kernel))
  node157
  (invalid_upper a [2,4,6,5,7,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,7,8,8] 30 (by decide +kernel)))

theorem node159 : UpperPrefix a [2,4,6,5,7] 30 :=
  branch_upper a [2,4,6,5,7] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut38 [2,4,6,5,7,0] [2,4,6,1,8,3] 30 (by decide +kernel) node140)
  (PrefixConjugacy.upper aut38 [2,4,6,5,7,1] [2,4,6,0,8,3] 30 (by decide +kernel) node127)
  (invalid_upper a [2,4,6,5,7,2] 30 (by decide +kernel))
  node152
  (invalid_upper a [2,4,6,5,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,7,7] 30 (by decide +kernel))
  node158)

def cert160 : Leaf := ⟨⟨176,160,176,144,128,256,58,123,187⟩,[],[(8,4,5)],⟨7,19,76,44,304,176,193,394,330⟩,⟨7,19,76,44,304,176,193,384,320⟩,[⟨2,1229033949957954105017857,⟨499,115,506,440,304,176,243,432,370⟩⟩,⟨6,1210106419144135336297477,⟨15,19,47,45,304,176,179,432,306⟩⟩,⟨0,1210107572065702304023552,⟨14,26,108,44,316,184,252,444,380⟩⟩,⟨1,1210107572065702304022529,⟨13,25,108,44,316,184,253,444,380⟩⟩,⟨3,1210107572065638332531717,⟨7,19,103,37,304,176,243,432,370⟩⟩]⟩
theorem node160 : UpperPrefix a [2,4,6,5,8,7,0] 30 :=
  Boolean.leaf_sound a [2,4,6,5,8,7,0] 30 cert160 (by decide +kernel)

def cert161 : Leaf := ⟨⟨248,224,176,208,192,320,49,120,184⟩,[],[(8,4,5),(0,7,6)],⟨7,19,76,44,304,176,194,385,328⟩,⟨7,19,76,44,304,176,194,385,320⟩,[⟨1,1531237716383719683522561,⟨445,185,380,316,316,184,508,445,380⟩⟩,⟨2,1266788129685515517625857,⟨499,243,376,376,368,242,242,499,368⟩⟩,⟨3,1210110454369399849681921,⟨7,19,100,100,368,242,242,499,368⟩⟩]⟩
theorem node161 : UpperPrefix a [2,4,6,5,8,7,1,0] 30 :=
  Boolean.leaf_sound a [2,4,6,5,8,7,1,0] 30 cert161 (by decide +kernel)

def cert162 : Leaf := ⟨⟨208,196,144,208,196,324,20,84,151⟩,[],[(8,4,5)],⟨7,19,76,44,304,176,194,392,321⟩,⟨7,19,76,44,304,176,194,392,320⟩,[⟨0,1212616374929042177786880,⟨110,254,108,44,444,184,254,444,508⟩⟩,⟨3,1871241761978571883093517,⟨279,19,375,375,368,498,498,499,368⟩⟩,⟨5,2414422436344492490515561,⟨455,339,461,463,339,471,455,461,321⟩⟩,⟨1,1212616338900244889600001,⟨45,185,108,44,444,184,252,444,508⟩⟩]⟩
theorem node162 : UpperPrefix a [2,4,6,5,8,7,1,3] 30 :=
  Boolean.leaf_sound a [2,4,6,5,8,7,1,3] 30 cert162 (by decide +kernel)

theorem node163 : UpperPrefix a [2,4,6,5,8,7,1] 30 :=
  branch_upper a [2,4,6,5,8,7,1] 30 (by decide) (fin9_cases _
  node161
  (invalid_upper a [2,4,6,5,8,7,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,8,7,1,2] 30 (by decide +kernel))
  node162
  (invalid_upper a [2,4,6,5,8,7,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,8,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,8,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,8,7,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,8,7,1,8] 30 (by decide +kernel)))

def cert164 : Leaf := ⟨⟨224,228,0,192,196,324,36,103,167⟩,[(2,6)],[(8,4,5),(3,6,2)],⟨7,19,76,44,304,176,200,387,323⟩,⟨7,19,76,44,304,176,200,384,320⟩,[⟨4,1224302947337027471279107,⟨455,463,76,108,364,236,204,384,324⟩⟩,⟨0,1210110454369468164342784,⟨14,30,108,108,380,252,252,508,380⟩⟩,⟨1,1210110454369468164341761,⟨13,29,108,108,380,252,252,508,380⟩⟩]⟩
theorem node164 : UpperPrefix a [2,4,6,5,8,7,3] 30 :=
  Boolean.leaf_sound a [2,4,6,5,8,7,3] 30 cert164 (by decide +kernel)

theorem node165 : UpperPrefix a [2,4,6,5,8,7] 30 :=
  branch_upper a [2,4,6,5,8,7] 30 (by decide) (fin9_cases _
  node160
  node163
  (invalid_upper a [2,4,6,5,8,7,2] 30 (by decide +kernel))
  node164
  (invalid_upper a [2,4,6,5,8,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,8,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,8,7,8] 30 (by decide +kernel)))

theorem node166 : UpperPrefix a [2,4,6,5,8] 30 :=
  branch_upper a [2,4,6,5,8] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut37 [2,4,6,5,8,0] [2,4,6,1,7,3] 30 (by decide +kernel) node137)
  (PrefixConjugacy.upper aut37 [2,4,6,5,8,1] [2,4,6,0,7,3] 30 (by decide +kernel) node122)
  (invalid_upper a [2,4,6,5,8,2] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut37 [2,4,6,5,8,3] [2,4,6,5,7,3] 30 (by decide +kernel) node152)
  (invalid_upper a [2,4,6,5,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,8,6] 30 (by decide +kernel))
  node165
  (invalid_upper a [2,4,6,5,8,8] 30 (by decide +kernel)))

theorem node167 : UpperPrefix a [2,4,6,5] 30 :=
  branch_upper a [2,4,6,5] 30 (by decide) (fin9_cases _
  node148
  node150
  (invalid_upper a [2,4,6,5,2] 30 (by decide +kernel))
  node151
  (invalid_upper a [2,4,6,5,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,6] 30 (by decide +kernel))
  node159
  node166)

def cert168 : Local := ⟨⟨0,372,0,353,385,321,305,113,49⟩,[(0,2),(2,1)],[(2,0,1),(3,1,0),(3,1,2),(1,2,0),(7,5,4)]⟩
theorem node168 : UpperPrefix a [2,3,1,4,6,7] 30 :=
  local_sound a [2,3,1,4,6,7] 30 cert168 (by decide +kernel)

theorem node169 : UpperPrefix a [2,4,6,7,0] 30 :=
  branch_upper a [2,4,6,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,6,7,0,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut87 [2,4,6,7,0,1] [2,3,1,4,6,7] 30 (by decide +kernel) node168)
  (invalid_upper a [2,4,6,7,0,2] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut36 [2,4,6,7,0,3] [2,4,1,5,6,7] 30 (by decide +kernel) node66)
  (invalid_upper a [2,4,6,7,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,0,7] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut37 [2,4,6,7,0,8] [2,4,1,6,7,8] 30 (by decide +kernel) node77))

def cert170 : Local := ⟨⟨376,0,0,354,386,322,306,114,50⟩,[(1,2),(2,1)],[(2,0,1),(2,0,2),(3,1,0),(0,2,0),(7,5,4)]⟩
theorem node170 : UpperPrefix a [2,3,0,4,6,7] 30 :=
  local_sound a [2,3,0,4,6,7] 30 cert170 (by decide +kernel)

theorem node171 : UpperPrefix a [2,4,6,7,1] 30 :=
  branch_upper a [2,4,6,7,1] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut84 [2,4,6,7,1,0] [2,3,0,4,6,7] 30 (by decide +kernel) node170)
  (invalid_upper a [2,4,6,7,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,1,2] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut36 [2,4,6,7,1,3] [2,4,0,5,6,7] 30 (by decide +kernel) node43)
  (invalid_upper a [2,4,6,7,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,1,7] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut37 [2,4,6,7,1,8] [2,4,0,6,7,8] 30 (by decide +kernel) node51))

theorem node172 : UpperPrefix a [2,4,6,7,3] 30 :=
  branch_upper a [2,4,6,7,3] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut36 [2,4,6,7,3,0] [2,4,5,1,6,7] 30 (by decide +kernel) node94)
  (PrefixConjugacy.upper aut95 [2,4,6,7,3,1] [2,4,1,5,6,8] 30 (by decide +kernel) node67)
  (invalid_upper a [2,4,6,7,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,3,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,3,7] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut37 [2,4,6,7,3,8] [2,4,5,6,7,8] 30 (by decide +kernel) node103))

theorem node173 : UpperPrefix a [2,4,6,7,8] 30 :=
  branch_upper a [2,4,6,7,8] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut37 [2,4,6,7,8,0] [2,4,6,1,7,8] 30 (by decide +kernel) node138)
  (PrefixConjugacy.upper aut37 [2,4,6,7,8,1] [2,4,6,0,7,8] 30 (by decide +kernel) node123)
  (invalid_upper a [2,4,6,7,8,2] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut37 [2,4,6,7,8,3] [2,4,6,5,7,8] 30 (by decide +kernel) node158)
  (invalid_upper a [2,4,6,7,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,8,8] 30 (by decide +kernel)))

theorem node174 : UpperPrefix a [2,4,6,7] 30 :=
  branch_upper a [2,4,6,7] 30 (by decide) (fin9_cases _
  node169
  node171
  (invalid_upper a [2,4,6,7,2] 30 (by decide +kernel))
  node172
  (invalid_upper a [2,4,6,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,7] 30 (by decide +kernel))
  node173)

def cert175 : Local := ⟨⟨0,436,0,417,385,193,305,49,177⟩,[(0,2),(2,1)],[(2,0,1),(3,1,0),(3,1,2),(1,2,0),(6,4,5)]⟩
theorem node175 : UpperPrefix a [2,3,1,4,6,8] 30 :=
  local_sound a [2,3,1,4,6,8] 30 cert175 (by decide +kernel)

theorem node176 : UpperPrefix a [2,4,6,8,0] 30 :=
  branch_upper a [2,4,6,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,6,8,0,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut87 [2,4,6,8,0,1] [2,3,1,4,6,8] 30 (by decide +kernel) node175)
  (invalid_upper a [2,4,6,8,0,2] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut36 [2,4,6,8,0,3] [2,4,1,5,6,8] 30 (by decide +kernel) node67)
  (invalid_upper a [2,4,6,8,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,0,6] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut38 [2,4,6,8,0,7] [2,4,1,6,8,7] 30 (by decide +kernel) node86)
  (invalid_upper a [2,4,6,8,0,8] 30 (by decide +kernel)))

def cert177 : Local := ⟨⟨440,0,0,418,386,194,306,50,178⟩,[(1,2),(2,1)],[(2,0,1),(2,0,2),(3,1,0),(0,2,0),(6,4,5)]⟩
theorem node177 : UpperPrefix a [2,3,0,4,6,8] 30 :=
  local_sound a [2,3,0,4,6,8] 30 cert177 (by decide +kernel)

theorem node178 : UpperPrefix a [2,4,6,8,1] 30 :=
  branch_upper a [2,4,6,8,1] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut84 [2,4,6,8,1,0] [2,3,0,4,6,8] 30 (by decide +kernel) node177)
  (invalid_upper a [2,4,6,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,1,2] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut91 [2,4,6,8,1,3] [2,4,0,5,6,7] 30 (by decide +kernel) node43)
  (invalid_upper a [2,4,6,8,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,1,6] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut38 [2,4,6,8,1,7] [2,4,0,6,8,7] 30 (by decide +kernel) node58)
  (invalid_upper a [2,4,6,8,1,8] 30 (by decide +kernel)))

theorem node179 : UpperPrefix a [2,4,6,8,3] 30 :=
  branch_upper a [2,4,6,8,3] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut70 [2,4,6,8,3,0] [2,4,5,1,6,7] 30 (by decide +kernel) node94)
  (PrefixConjugacy.upper aut94 [2,4,6,8,3,1] [2,4,1,5,6,7] 30 (by decide +kernel) node66)
  (invalid_upper a [2,4,6,8,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,3,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,3,6] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut38 [2,4,6,8,3,7] [2,4,5,6,8,7] 30 (by decide +kernel) node108)
  (invalid_upper a [2,4,6,8,3,8] 30 (by decide +kernel)))

theorem node180 : UpperPrefix a [2,4,6,8,7] 30 :=
  branch_upper a [2,4,6,8,7] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut38 [2,4,6,8,7,0] [2,4,6,1,8,7] 30 (by decide +kernel) node144)
  (PrefixConjugacy.upper aut38 [2,4,6,8,7,1] [2,4,6,0,8,7] 30 (by decide +kernel) node131)
  (invalid_upper a [2,4,6,8,7,2] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut38 [2,4,6,8,7,3] [2,4,6,5,8,7] 30 (by decide +kernel) node165)
  (invalid_upper a [2,4,6,8,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,7,8] 30 (by decide +kernel)))

theorem node181 : UpperPrefix a [2,4,6,8] 30 :=
  branch_upper a [2,4,6,8] 30 (by decide) (fin9_cases _
  node176
  node178
  (invalid_upper a [2,4,6,8,2] 30 (by decide +kernel))
  node179
  (invalid_upper a [2,4,6,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,6] 30 (by decide +kernel))
  node180
  (invalid_upper a [2,4,6,8,8] 30 (by decide +kernel)))

theorem node182 : UpperPrefix a [2,4,6] 30 :=
  branch_upper a [2,4,6] 30 (by decide) (fin9_cases _
  node133
  node146
  (invalid_upper a [2,4,6,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,4] 30 (by decide +kernel))
  node167
  (invalid_upper a [2,4,6,6] 30 (by decide +kernel))
  node174
  node181)

theorem node183 : UpperPrefix a [2,4] 30 :=
  branch_upper a [2,4] 30 (by decide) (fin9_cases _
  node61
  node89
  (invalid_upper a [2,4,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,4] 30 (by decide +kernel))
  node111
  node182
  (PrefixConjugacy.upper aut2 [2,4,7] [2,4,6] 30 (by decide +kernel) node182)
  (PrefixConjugacy.upper aut1 [2,4,8] [2,4,6] 30 (by decide +kernel) node182))

def cert184 : Leaf := ⟨⟨136,136,130,2,200,202,314,58,186⟩,[],[(2,0,2),(0,2,0)],⟨7,67,13,140,50,304,248,440,376⟩,⟨7,67,13,140,50,304,192,384,320⟩,[⟨8,1181745671447424697843,⟨7,79,13,141,55,55,207,143,79⟩⟩,⟨4,1210107565282778064520691,⟨7,79,13,141,39,295,207,399,335⟩⟩,⟨5,1210107564157977669305843,⟨7,79,13,141,23,279,207,399,335⟩⟩,⟨6,1210401560267532887131153,⟨7,3,13,140,191,445,128,384,256⟩⟩]⟩
theorem node184 : UpperPrefix a [2,6,0,7,1,8] 30 :=
  Boolean.leaf_sound a [2,6,0,7,1,8] 30 cert184 (by decide +kernel)

theorem node185 : UpperPrefix a [2,6,0,7,1] 30 :=
  branch_upper a [2,6,0,7,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,6,0,7,1,0] 30 (by decide +kernel))
  (invalid_upper a [2,6,0,7,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,6,0,7,1,2] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut90 [2,6,0,7,1,3] [2,4,6,5,7,3] 30 (by decide +kernel) node152)
  (invalid_upper a [2,6,0,7,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,6,0,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,6,0,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,6,0,7,1,7] 30 (by decide +kernel))
  node184)

def cert186 : Leaf := ⟨⟨432,432,432,304,384,128,304,48,176⟩,[],[(2,0,2),(0,2,0),(1,6,1)],⟨7,67,13,140,56,304,194,432,368⟩,⟨7,67,13,140,56,304,194,384,320⟩,[⟨3,1437224887688629096299533,⟨7,67,71,199,499,498,194,384,320⟩⟩,⟨6,1212762757053359750382659,⟨7,31,29,188,184,444,191,444,445⟩⟩]⟩
theorem node186 : UpperPrefix a [2,6,0,7,3,8,1] 30 :=
  Boolean.leaf_sound a [2,6,0,7,3,8,1] 30 cert186 (by decide +kernel)

def cert187 : Leaf := ⟨⟨328,264,322,322,322,74,298,106,58⟩,[],[(2,0,2),(0,2,0)],⟨7,67,13,140,56,304,208,418,354⟩,⟨7,67,13,140,56,304,208,384,320⟩,[⟨7,1520603163819789926958177,⟨311,355,61,28,61,311,375,258,355⟩⟩,⟨4,1210402713187963872380387,⟨7,79,13,141,173,431,207,399,335⟩⟩,⟨5,1210107564157977673500131,⟨7,79,13,141,29,279,223,399,335⟩⟩]⟩
theorem node187 : UpperPrefix a [2,6,0,7,3,8,4] 30 :=
  Boolean.leaf_sound a [2,6,0,7,3,8,4] 30 cert187 (by decide +kernel)

def cert188 : Leaf := ⟨⟨200,136,194,66,194,202,282,90,186⟩,[],[(2,0,2),(0,2,0),(8,5,6)],⟨7,67,13,140,56,304,224,402,338⟩,⟨7,67,13,140,56,304,224,384,320⟩,[⟨5,1210402712063163477165539,⟨7,79,13,141,157,415,207,399,335⟩⟩,⟨4,1210107565282778068714979,⟨7,79,13,141,45,295,239,399,335⟩⟩]⟩
theorem node188 : UpperPrefix a [2,6,0,7,3,8,5] 30 :=
  Boolean.leaf_sound a [2,6,0,7,3,8,5] 30 cert188 (by decide +kernel)

theorem node189 : UpperPrefix a [2,6,0,7,3,8] 30 :=
  branch_upper a [2,6,0,7,3,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,6,0,7,3,8,0] 30 (by decide +kernel))
  node186
  (invalid_upper a [2,6,0,7,3,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,6,0,7,3,8,3] 30 (by decide +kernel))
  node187
  node188
  (invalid_upper a [2,6,0,7,3,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,6,0,7,3,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,6,0,7,3,8,8] 30 (by decide +kernel)))

theorem node190 : UpperPrefix a [2,6,0,7,3] 30 :=
  branch_upper a [2,6,0,7,3] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,6,0,7,3,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut93 [2,6,0,7,3,1] [2,4,6,5,7,3] 30 (by decide +kernel) node152)
  (invalid_upper a [2,6,0,7,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,6,0,7,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,6,0,7,3,4] 30 (by decide +kernel))
  (invalid_upper a [2,6,0,7,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,6,0,7,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,6,0,7,3,7] 30 (by decide +kernel))
  node189)

theorem node191 : UpperPrefix a [2,6,0,7,8] 30 :=
  branch_upper a [2,6,0,7,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,6,0,7,8,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut3 [2,6,0,7,8,1] [2,6,0,7,1,8] 30 (by decide +kernel) node184)
  (invalid_upper a [2,6,0,7,8,2] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut3 [2,6,0,7,8,3] [2,6,0,7,3,8] 30 (by decide +kernel) node189)
  (invalid_upper a [2,6,0,7,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,6,0,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,6,0,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,6,0,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,6,0,7,8,8] 30 (by decide +kernel)))

#print axioms node191
end Delivery.FiniteExclusion.Sharp2x2x2x3

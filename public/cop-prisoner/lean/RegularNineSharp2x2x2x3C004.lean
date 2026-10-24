import RegularNineSharp2x2x2x3Base
import RegularNineSharp2x2x2x3C000
import RegularNineSharp2x2x2x3C001
import RegularNineSharp2x2x2x3C002
import RegularNineSharp2x2x2x3C003
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp2x2x2x3
open Bounds BoundTreeRows Extremal
def cert256 : Leaf := ⟨⟨232,0,226,226,78,204,46,0,174⟩,[(1,6),(7,3)],[(8,3,7),(0,6,1)],⟨7,67,28,268,176,50,193,392,352⟩,⟨7,67,28,268,176,50,193,392,320⟩,[⟨4,1285778649503299129155085,⟨207,67,463,463,482,290,195,459,322⟩⟩]⟩
theorem node256 : UpperPrefix a [2,6,4,8,7,1,0,3] 30 :=
  Boolean.leaf_sound a [2,6,4,8,7,1,0,3] 30 cert256 (by decide +kernel)

def cert257 : Leaf := ⟨⟨472,0,448,208,0,460,286,92,156⟩,[(1,6),(4,7)],[(0,6,1),(5,7,4)],⟨7,67,28,268,176,50,193,416,328⟩,⟨7,67,28,268,176,50,193,416,320⟩,[⟨1,1522078901069487629402113,⟨269,333,28,268,188,444,477,444,332⟩⟩]⟩
theorem node257 : UpperPrefix a [2,6,4,8,7,1,0,5] 30 :=
  Boolean.leaf_sound a [2,6,4,8,7,1,0,5] 30 cert257 (by decide +kernel)

theorem node258 : UpperPrefix a [2,6,4,8,7,1,0] 30 :=
  branch_upper a [2,6,4,8,7,1,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,6,4,8,7,1,0,0] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,8,7,1,0,1] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,8,7,1,0,2] 30 (by decide +kernel))
  node256
  (invalid_upper a [2,6,4,8,7,1,0,4] 30 (by decide +kernel))
  node257
  (invalid_upper a [2,6,4,8,7,1,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,8,7,1,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,8,7,1,0,8] 30 (by decide +kernel)))

def cert259 : Leaf := ⟨⟨232,172,224,240,67,193,292,98,176⟩,[],[(8,3,6)],⟨7,67,28,268,176,50,200,385,352⟩,⟨7,67,28,268,176,50,200,385,320⟩,[⟨0,1436781444691977799992320,⟨14,66,348,268,508,382,200,384,320⟩⟩,⟨1,1436781444691977799991297,⟨13,65,348,268,508,380,200,385,320⟩⟩,⟨2,1219579968482455930799105,⟨435,499,24,264,176,434,216,433,320⟩⟩,⟨3,1219579968482454858105857,⟨439,499,20,260,176,434,208,433,320⟩⟩,⟨4,1210181568431829126520333,⟨71,67,207,463,160,34,203,387,322⟩⟩]⟩
theorem node259 : UpperPrefix a [2,6,4,8,7,1,3,0] 30 :=
  Boolean.leaf_sound a [2,6,4,8,7,1,3,0] 30 cert259 (by decide +kernel)

def cert260 : Leaf := ⟨⟨88,156,65,81,0,205,277,93,29⟩,[(4,7)],[(8,3,6),(5,7,4)],⟨7,67,28,268,176,50,200,416,321⟩,⟨7,67,28,268,176,50,200,416,320⟩,[⟨1,1219850616699959414620161,⟨269,333,92,268,252,508,220,508,332⟩⟩,⟨7,1218371706628895186879521,⟨271,331,28,268,61,319,72,301,320⟩⟩]⟩
theorem node260 : UpperPrefix a [2,6,4,8,7,1,3,5] 30 :=
  Boolean.leaf_sound a [2,6,4,8,7,1,3,5] 30 cert260 (by decide +kernel)

theorem node261 : UpperPrefix a [2,6,4,8,7,1,3] 30 :=
  branch_upper a [2,6,4,8,7,1,3] 30 (by decide) (fin9_cases _
  node259
  (invalid_upper a [2,6,4,8,7,1,3,1] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,8,7,1,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,8,7,1,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,8,7,1,3,4] 30 (by decide +kernel))
  node260
  (invalid_upper a [2,6,4,8,7,1,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,8,7,1,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,8,7,1,3,8] 30 (by decide +kernel)))

def cert262 : Leaf := ⟨⟨328,268,323,67,0,461,0,79,15⟩,[(4,6),(6,4)],[],⟨7,67,28,268,176,50,224,393,329⟩,⟨7,67,28,268,176,50,224,384,320⟩,[⟨5,1525131836076739678864489,⟨399,459,157,399,157,415,463,386,459⟩⟩,⟨4,1238580979451651993635853,⟨399,459,463,399,224,482,224,384,320⟩⟩,⟨7,1520603161532543890785385,⟨271,331,29,271,61,319,367,258,331⟩⟩]⟩
theorem node262 : UpperPrefix a [2,6,4,8,7,1,5] 30 :=
  Boolean.leaf_sound a [2,6,4,8,7,1,5] 30 cert262 (by decide +kernel)

theorem node263 : UpperPrefix a [2,6,4,8,7,1] 30 :=
  branch_upper a [2,6,4,8,7,1] 30 (by decide) (fin9_cases _
  node258
  (invalid_upper a [2,6,4,8,7,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,8,7,1,2] 30 (by decide +kernel))
  node261
  (invalid_upper a [2,6,4,8,7,1,4] 30 (by decide +kernel))
  node262
  (invalid_upper a [2,6,4,8,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,8,7,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,8,7,1,8] 30 (by decide +kernel)))

def cert264 : Leaf := ⟨⟨184,184,0,176,264,0,59,123,187⟩,[(2,5),(5,2)],[],⟨7,67,28,268,176,56,227,419,355⟩,⟨7,67,28,268,176,56,192,384,320⟩,[⟨2,1214839173293962902373889,⟨499,467,56,296,176,56,192,384,320⟩⟩,⟨6,1210106428841879026009091,⟨39,55,60,300,188,60,188,444,316⟩⟩,⟨8,1182034040336159894589,⟨39,67,127,47,247,127,192,128,64⟩⟩,⟨0,1210107581763383632856064,⟨38,118,60,300,188,60,252,444,380⟩⟩,⟨1,1210107581763383632855041,⟨37,117,60,300,188,60,252,444,380⟩⟩]⟩
theorem node264 : UpperPrefix a [2,6,4,8,7,3] 30 :=
  Boolean.leaf_sound a [2,6,4,8,7,3] 30 cert264 (by decide +kernel)

theorem node265 : UpperPrefix a [2,6,4,8,7] 30 :=
  branch_upper a [2,6,4,8,7] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut65 [2,6,4,8,7,0] [2,6,4,8,1,7] 30 (by decide +kernel) node253)
  node263
  (invalid_upper a [2,6,4,8,7,2] 30 (by decide +kernel))
  node264
  (invalid_upper a [2,6,4,8,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,8,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,8,7,8] 30 (by decide +kernel)))

theorem node266 : UpperPrefix a [2,6,4,8] 30 :=
  branch_upper a [2,6,4,8] 30 (by decide) (fin9_cases _
  node247
  node254
  (invalid_upper a [2,6,4,8,2] 30 (by decide +kernel))
  node255
  (invalid_upper a [2,6,4,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,8,6] 30 (by decide +kernel))
  node265
  (invalid_upper a [2,6,4,8,8] 30 (by decide +kernel)))

theorem node267 : UpperPrefix a [2,6,4] 30 :=
  branch_upper a [2,6,4] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut54 [2,6,4,0] [2,4,1,6] 30 (by decide +kernel) node88)
  (PrefixConjugacy.upper aut78 [2,6,4,1] [2,4,6,1] 30 (by decide +kernel) node146)
  (invalid_upper a [2,6,4,2] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,3] 30 (by decide +kernel))
  (invalid_upper a [2,6,4,4] 30 (by decide +kernel))
  node222
  (invalid_upper a [2,6,4,6] 30 (by decide +kernel))
  node240
  node266)

def cert268 : Leaf := ⟨⟨488,488,0,387,0,323,259,67,131⟩,[(2,4),(4,2)],[],⟨7,19,44,76,56,176,451,387,323⟩,⟨7,19,44,76,56,176,192,384,320⟩,[⟨2,1224302388997594707658241,⟨499,499,56,88,56,176,192,384,320⟩⟩,⟨4,1224302388890667609752579,⟨463,463,44,76,44,164,192,384,320⟩⟩,⟨3,1224302388962134384968705,⟨487,499,36,68,48,176,192,384,320⟩⟩,⟨5,1224302387765866941907969,⟨463,475,12,76,24,144,192,384,320⟩⟩]⟩
theorem node268 : UpperPrefix a [2,4,5,6,3,7] 30 :=
  Boolean.leaf_sound a [2,4,5,6,3,7] 30 cert268 (by decide +kernel)

theorem node269 : UpperPrefix a [2,6,7,1,0] 30 :=
  branch_upper a [2,6,7,1,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,6,7,1,0,0] 30 (by decide +kernel))
  (invalid_upper a [2,6,7,1,0,1] 30 (by decide +kernel))
  (invalid_upper a [2,6,7,1,0,2] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut66 [2,6,7,1,0,3] [2,4,5,6,3,7] 30 (by decide +kernel) node268)
  (invalid_upper a [2,6,7,1,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,6,7,1,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,6,7,1,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,6,7,1,0,7] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut61 [2,6,7,1,0,8] [2,6,4,7,8,3] 30 (by decide +kernel) node238))

theorem node270 : UpperPrefix a [2,6,7,1,3] 30 :=
  branch_upper a [2,6,7,1,3] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut69 [2,6,7,1,3,0] [2,4,5,6,3,7] 30 (by decide +kernel) node268)
  (invalid_upper a [2,6,7,1,3,1] 30 (by decide +kernel))
  (invalid_upper a [2,6,7,1,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,6,7,1,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,6,7,1,3,4] 30 (by decide +kernel))
  (invalid_upper a [2,6,7,1,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,6,7,1,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,6,7,1,3,7] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut139 [2,6,7,1,3,8] [2,6,4,8,7,3] 30 (by decide +kernel) node264))

theorem node271 : UpperPrefix a [2,6,7,1,8] 30 :=
  branch_upper a [2,6,7,1,8] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut64 [2,6,7,1,8,0] [2,6,4,7,8,3] 30 (by decide +kernel) node238)
  (invalid_upper a [2,6,7,1,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,6,7,1,8,2] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut142 [2,6,7,1,8,3] [2,6,4,8,7,3] 30 (by decide +kernel) node264)
  (invalid_upper a [2,6,7,1,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,6,7,1,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,6,7,1,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,6,7,1,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,6,7,1,8,8] 30 (by decide +kernel)))

theorem node272 : UpperPrefix a [2,6,7,1] 30 :=
  branch_upper a [2,6,7,1] 30 (by decide) (fin9_cases _
  node269
  (invalid_upper a [2,6,7,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,6,7,1,2] 30 (by decide +kernel))
  node270
  (invalid_upper a [2,6,7,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,6,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,6,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,6,7,1,7] 30 (by decide +kernel))
  node271)

def cert273 : Leaf := ⟨⟨0,360,369,305,321,65,305,113,177⟩,[(0,2)],[(1,2,0)],⟨7,19,14,76,56,304,225,417,481⟩,⟨7,19,14,76,56,304,192,384,320⟩,[⟨2,1224302389138881951827457,⟨499,499,506,120,56,304,192,384,320⟩⟩,⟨7,1208926987206961587811839,⟨7,23,15,95,63,319,127,319,383⟩⟩,⟨3,1243228820439354422854661,⟨487,499,487,453,48,304,192,384,320⟩⟩]⟩
theorem node273 : UpperPrefix a [2,4,1,6,3,8] 30 :=
  Boolean.leaf_sound a [2,4,1,6,3,8] 30 cert273 (by decide +kernel)

theorem node274 : UpperPrefix a [2,6,7,4,0] 30 :=
  branch_upper a [2,6,7,4,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,6,7,4,0,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut60 [2,6,7,4,0,1] [2,3,4,6,7,0] 30 (by decide +kernel) node22)
  (invalid_upper a [2,6,7,4,0,2] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut119 [2,6,7,4,0,3] [2,4,1,6,3,8] 30 (by decide +kernel) node273)
  (invalid_upper a [2,6,7,4,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,6,7,4,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,6,7,4,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,6,7,4,0,7] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut104 [2,6,7,4,0,8] [2,6,4,7,1,8] 30 (by decide +kernel) node231))

theorem node275 : UpperPrefix a [2,6,7,4,1] 30 :=
  branch_upper a [2,6,7,4,1] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut63 [2,6,7,4,1,0] [2,3,4,6,7,1] 30 (by decide +kernel) node23)
  (invalid_upper a [2,6,7,4,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,6,7,4,1,2] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut143 [2,6,7,4,1,3] [2,4,1,6,8,3] 30 (by decide +kernel) node82)
  (invalid_upper a [2,6,7,4,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,6,7,4,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,6,7,4,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,6,7,4,1,7] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut128 [2,6,7,4,1,8] [2,6,4,7,8,1] 30 (by decide +kernel) node237))

def cert276 : Leaf := ⟨⟨280,264,274,306,322,66,306,50,178⟩,[],[(2,0,2),(0,2,0)],⟨7,19,13,76,56,304,226,418,482⟩,⟨7,19,13,76,56,304,192,384,320⟩,[⟨7,1208926987206961587811839,⟨7,23,15,95,63,319,127,319,383⟩⟩,⟨3,1224302388962134384968705,⟨487,499,453,68,48,304,192,384,320⟩⟩,⟨6,1210401560267526436316211,⟨7,23,13,12,191,439,128,384,256⟩⟩,⟨5,1210107564157951783494707,⟨7,23,13,76,31,279,192,384,320⟩⟩]⟩
theorem node276 : UpperPrefix a [2,4,0,6,3,8] 30 :=
  Boolean.leaf_sound a [2,4,0,6,3,8] 30 cert276 (by decide +kernel)

theorem node277 : UpperPrefix a [2,6,7,4,3] 30 :=
  branch_upper a [2,6,7,4,3] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut116 [2,6,7,4,3,0] [2,4,0,6,3,8] 30 (by decide +kernel) node276)
  (PrefixConjugacy.upper aut140 [2,6,7,4,3,1] [2,4,0,6,8,3] 30 (by decide +kernel) node54)
  (invalid_upper a [2,6,7,4,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,6,7,4,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,6,7,4,3,4] 30 (by decide +kernel))
  (invalid_upper a [2,6,7,4,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,6,7,4,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,6,7,4,3,7] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut104 [2,6,7,4,3,8] [2,6,0,7,1,8] 30 (by decide +kernel) node184))

def cert278 : Leaf := ⟨⟨432,0,304,288,70,324,310,60,62⟩,[(1,6)],[(0,6,1)],⟨7,67,140,28,304,50,193,424,360⟩,⟨7,67,140,28,304,50,193,384,320⟩,[⟨3,1210107649049044462902797,⟨103,99,247,119,304,50,243,432,370⟩⟩,⟨6,1210253986314943212815393,⟨7,3,140,156,445,191,129,384,256⟩⟩,⟨7,1520603172930275221996545,⟨319,379,28,28,304,306,379,304,370⟩⟩,⟨1,1210255139236447819661313,⟨5,65,140,156,444,188,193,384,320⟩⟩]⟩
theorem node278 : UpperPrefix a [2,6,7,4,8,1,0] 30 :=
  Boolean.leaf_sound a [2,6,7,4,8,1,0] 30 cert278 (by decide +kernel)

def cert279 : Leaf := ⟨⟨488,424,0,355,67,321,0,99,51⟩,[(2,6),(6,2)],[],⟨7,67,140,28,304,50,200,417,353⟩,⟨7,67,140,28,304,50,200,384,320⟩,[⟨2,1224302407014123520919041,⟨499,499,200,88,304,434,200,384,320⟩⟩,⟨3,1219579968473658765083649,⟨439,499,132,20,304,434,192,384,320⟩⟩,⟨7,1218371706736831997412353,⟨319,379,12,28,304,306,72,256,320⟩⟩,⟨4,1210255355408123983732559,⟨71,71,207,207,419,163,207,387,327⟩⟩]⟩
theorem node279 : UpperPrefix a [2,6,7,4,8,1,3] 30 :=
  Boolean.leaf_sound a [2,6,7,4,8,1,3] 30 cert279 (by decide +kernel)

def cert280 : Leaf := ⟨⟨144,148,273,257,77,69,21,29,29⟩,[],[],⟨7,67,140,28,304,50,224,393,329⟩,⟨7,67,140,28,304,50,224,384,320⟩,[⟨1,1219571321456631070851073,⟨389,461,140,28,380,508,252,384,332⟩⟩,⟨5,1513076888824563929089395,⟨7,455,140,157,415,159,463,387,455⟩⟩,⟨3,1210107637622919627021837,⟨71,67,231,119,304,50,224,384,320⟩⟩,⟨6,1210253986314943229592611,⟨7,7,140,156,445,191,173,384,260⟩⟩,⟨7,1218371706736831997412353,⟨319,379,12,28,304,306,112,256,320⟩⟩,⟨8,1181818008291526057485,⟨71,67,239,127,48,50,224,128,64⟩⟩]⟩
theorem node280 : UpperPrefix a [2,6,7,4,8,1,5] 30 :=
  Boolean.leaf_sound a [2,6,7,4,8,1,5] 30 cert280 (by decide +kernel)

theorem node281 : UpperPrefix a [2,6,7,4,8,1] 30 :=
  branch_upper a [2,6,7,4,8,1] 30 (by decide) (fin9_cases _
  node278
  (invalid_upper a [2,6,7,4,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,6,7,4,8,1,2] 30 (by decide +kernel))
  node279
  (invalid_upper a [2,6,7,4,8,1,4] 30 (by decide +kernel))
  node280
  (invalid_upper a [2,6,7,4,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,6,7,4,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,6,7,4,8,1,8] 30 (by decide +kernel)))

theorem node282 : UpperPrefix a [2,6,7,4,8] 30 :=
  branch_upper a [2,6,7,4,8] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut64 [2,6,7,4,8,0] [2,6,4,7,8,1] 30 (by decide +kernel) node237)
  node281
  (invalid_upper a [2,6,7,4,8,2] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut118 [2,6,7,4,8,3] [2,6,1,8,3,7] 30 (by decide +kernel) node207)
  (invalid_upper a [2,6,7,4,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,6,7,4,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,6,7,4,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,6,7,4,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,6,7,4,8,8] 30 (by decide +kernel)))

theorem node283 : UpperPrefix a [2,6,7,4] 30 :=
  branch_upper a [2,6,7,4] 30 (by decide) (fin9_cases _
  node274
  node275
  (invalid_upper a [2,6,7,4,2] 30 (by decide +kernel))
  node277
  (invalid_upper a [2,6,7,4,4] 30 (by decide +kernel))
  (invalid_upper a [2,6,7,4,5] 30 (by decide +kernel))
  (invalid_upper a [2,6,7,4,6] 30 (by decide +kernel))
  (invalid_upper a [2,6,7,4,7] 30 (by decide +kernel))
  node282)

theorem node284 : UpperPrefix a [2,6,7,8,0] 30 :=
  branch_upper a [2,6,7,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,6,7,8,0,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut60 [2,6,7,8,0,1] [2,3,4,6,7,8] 30 (by decide +kernel) node24)
  (invalid_upper a [2,6,7,8,0,2] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut66 [2,6,7,8,0,3] [2,4,5,6,8,7] 30 (by decide +kernel) node108)
  (invalid_upper a [2,6,7,8,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,6,7,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,6,7,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,6,7,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,6,7,8,0,8] 30 (by decide +kernel)))

theorem node285 : UpperPrefix a [2,6,7,8,1] 30 :=
  branch_upper a [2,6,7,8,1] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut63 [2,6,7,8,1,0] [2,3,4,6,7,8] 30 (by decide +kernel) node24)
  (invalid_upper a [2,6,7,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,6,7,8,1,2] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut90 [2,6,7,8,1,3] [2,4,6,5,8,7] 30 (by decide +kernel) node165)
  (invalid_upper a [2,6,7,8,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,6,7,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,6,7,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,6,7,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,6,7,8,1,8] 30 (by decide +kernel)))

theorem node286 : UpperPrefix a [2,6,7,8,3] 30 :=
  branch_upper a [2,6,7,8,3] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut69 [2,6,7,8,3,0] [2,4,5,6,8,7] 30 (by decide +kernel) node108)
  (PrefixConjugacy.upper aut93 [2,6,7,8,3,1] [2,4,6,5,8,7] 30 (by decide +kernel) node165)
  (invalid_upper a [2,6,7,8,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,6,7,8,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,6,7,8,3,4] 30 (by decide +kernel))
  (invalid_upper a [2,6,7,8,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,6,7,8,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,6,7,8,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,6,7,8,3,8] 30 (by decide +kernel)))

theorem node287 : UpperPrefix a [2,6,7,8] 30 :=
  branch_upper a [2,6,7,8] 30 (by decide) (fin9_cases _
  node284
  node285
  (invalid_upper a [2,6,7,8,2] 30 (by decide +kernel))
  node286
  (invalid_upper a [2,6,7,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,6,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,6,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,6,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,6,7,8,8] 30 (by decide +kernel)))

theorem node288 : UpperPrefix a [2,6,7] 30 :=
  branch_upper a [2,6,7] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut56 [2,6,7,0] [2,6,1,8] 30 (by decide +kernel) node210)
  node272
  (invalid_upper a [2,6,7,2] 30 (by decide +kernel))
  (invalid_upper a [2,6,7,3] 30 (by decide +kernel))
  node283
  (PrefixConjugacy.upper aut3 [2,6,7,5] [2,6,7,4] 30 (by decide +kernel) node283)
  (invalid_upper a [2,6,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,6,7,7] 30 (by decide +kernel))
  node287)

def cert289 : Leaf := ⟨⟨0,232,241,177,193,65,305,113,177⟩,[(0,2)],[(1,2,0)],⟨7,19,14,76,56,176,481,417,353⟩,⟨7,19,14,76,56,176,192,384,320⟩,[⟨2,1224302389138881951827457,⟨499,499,506,120,56,176,192,384,320⟩⟩,⟨8,1181752456001107525119,⟨7,23,31,127,63,183,255,191,127⟩⟩,⟨3,1243228820439354422854661,⟨487,499,487,453,48,176,192,384,320⟩⟩]⟩
theorem node289 : UpperPrefix a [2,4,1,6,3,7] 30 :=
  Boolean.leaf_sound a [2,4,1,6,3,7] 30 cert289 (by decide +kernel)

theorem node290 : UpperPrefix a [2,6,8,4,0] 30 :=
  branch_upper a [2,6,8,4,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,6,8,4,0,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut60 [2,6,8,4,0,1] [2,3,4,6,8,0] 30 (by decide +kernel) node28)
  (invalid_upper a [2,6,8,4,0,2] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut118 [2,6,8,4,0,3] [2,4,1,6,3,7] 30 (by decide +kernel) node289)
  (invalid_upper a [2,6,8,4,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,6,8,4,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,6,8,4,0,6] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut103 [2,6,8,4,0,7] [2,6,4,8,1,7] 30 (by decide +kernel) node253)
  (invalid_upper a [2,6,8,4,0,8] 30 (by decide +kernel)))

theorem node291 : UpperPrefix a [2,6,8,4,1] 30 :=
  branch_upper a [2,6,8,4,1] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut63 [2,6,8,4,1,0] [2,3,4,6,8,1] 30 (by decide +kernel) node31)
  (invalid_upper a [2,6,8,4,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,6,8,4,1,2] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut142 [2,6,8,4,1,3] [2,4,1,6,7,3] 30 (by decide +kernel) node76)
  (invalid_upper a [2,6,8,4,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,6,8,4,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,6,8,4,1,6] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut127 [2,6,8,4,1,7] [2,6,4,8,7,1] 30 (by decide +kernel) node263)
  (invalid_upper a [2,6,8,4,1,8] 30 (by decide +kernel)))

def cert292 : Leaf := ⟨⟨152,136,146,178,194,66,306,114,178⟩,[],[(2,0,2),(0,2,0)],⟨7,19,13,76,56,176,482,418,354⟩,⟨7,19,13,76,56,176,192,384,320⟩,[⟨8,1181752456001107525119,⟨7,23,31,127,63,183,255,191,127⟩⟩,⟨3,1224302388962134384968705,⟨487,499,453,68,48,176,192,384,320⟩⟩,⟨5,1210107564157951783494707,⟨7,23,13,76,31,151,192,384,320⟩⟩,⟨6,1210106412362347083490355,⟨7,23,13,12,63,183,128,384,256⟩⟩]⟩
theorem node292 : UpperPrefix a [2,4,0,6,3,7] 30 :=
  Boolean.leaf_sound a [2,4,0,6,3,7] 30 cert292 (by decide +kernel)

theorem node293 : UpperPrefix a [2,6,8,4,3] 30 :=
  branch_upper a [2,6,8,4,3] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut115 [2,6,8,4,3,0] [2,4,0,6,3,7] 30 (by decide +kernel) node292)
  (PrefixConjugacy.upper aut139 [2,6,8,4,3,1] [2,4,0,6,7,3] 30 (by decide +kernel) node50)
  (invalid_upper a [2,6,8,4,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,6,8,4,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,6,8,4,3,4] 30 (by decide +kernel))
  (invalid_upper a [2,6,8,4,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,6,8,4,3,6] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut116 [2,6,8,4,3,7] [2,6,0,7,3,8] 30 (by decide +kernel) node189)
  (invalid_upper a [2,6,8,4,3,8] 30 (by decide +kernel)))

def cert294 : Leaf := ⟨⟨504,0,0,482,330,456,314,0,186⟩,[(1,6),(2,7),(7,2)],[(0,6,1)],⟨7,67,268,28,176,50,193,392,352⟩,⟨7,67,268,28,176,50,193,392,320⟩,[⟨2,1526543042516753764615681,⟨499,371,440,152,176,306,499,440,370⟩⟩]⟩
theorem node294 : UpperPrefix a [2,6,8,4,7,1,0,3] 30 :=
  Boolean.leaf_sound a [2,6,8,4,7,1,0,3] 30 cert294 (by decide +kernel)

def cert295 : Leaf := ⟨⟨472,0,208,448,0,460,286,92,156⟩,[(1,6),(4,7)],[(0,6,1),(5,7,4)],⟨7,67,268,28,176,50,193,416,328⟩,⟨7,67,268,28,176,50,193,416,320⟩,[⟨1,1522078901069455077933057,⟨261,333,268,28,188,444,477,444,332⟩⟩]⟩
theorem node295 : UpperPrefix a [2,6,8,4,7,1,0,5] 30 :=
  Boolean.leaf_sound a [2,6,8,4,7,1,0,5] 30 cert295 (by decide +kernel)

theorem node296 : UpperPrefix a [2,6,8,4,7,1,0] 30 :=
  branch_upper a [2,6,8,4,7,1,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,6,8,4,7,1,0,0] 30 (by decide +kernel))
  (invalid_upper a [2,6,8,4,7,1,0,1] 30 (by decide +kernel))
  (invalid_upper a [2,6,8,4,7,1,0,2] 30 (by decide +kernel))
  node294
  (invalid_upper a [2,6,8,4,7,1,0,4] 30 (by decide +kernel))
  node295
  (invalid_upper a [2,6,8,4,7,1,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,6,8,4,7,1,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,6,8,4,7,1,0,8] 30 (by decide +kernel)))

def cert297 : Leaf := ⟨⟨456,396,240,480,323,449,260,66,144⟩,[],[],⟨7,67,268,28,176,50,200,385,352⟩,⟨7,67,268,28,176,50,200,385,352⟩,[⟨0,1436781444691977332327424,⟨6,66,268,348,508,382,204,388,364⟩⟩,⟨1,1436781444691977332326401,⟨5,65,268,348,508,380,204,389,364⟩⟩,⟨2,1219579968482455930799105,⟨435,499,264,24,176,434,216,433,368⟩⟩,⟨3,1219579968482454858105857,⟨439,499,260,20,176,434,208,433,368⟩⟩,⟨4,1210144674943681707417101,⟨199,67,463,207,160,34,203,387,354⟩⟩,⟨5,1210144673818881312202253,⟨199,67,463,223,144,18,203,387,322⟩⟩]⟩
theorem node297 : UpperPrefix a [2,6,8,4,7,1,3,0,5] 30 :=
  Boolean.leaf_sound a [2,6,8,4,7,1,3,0,5] 30 cert297 (by decide +kernel)

theorem node298 : UpperPrefix a [2,6,8,4,7,1,3,0] 30 :=
  branch_upper a [2,6,8,4,7,1,3,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,6,8,4,7,1,3,0,0] 30 (by decide +kernel))
  (invalid_upper a [2,6,8,4,7,1,3,0,1] 30 (by decide +kernel))
  (invalid_upper a [2,6,8,4,7,1,3,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,6,8,4,7,1,3,0,3] 30 (by decide +kernel))
  (invalid_upper a [2,6,8,4,7,1,3,0,4] 30 (by decide +kernel))
  node297
  (invalid_upper a [2,6,8,4,7,1,3,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,6,8,4,7,1,3,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,6,8,4,7,1,3,0,8] 30 (by decide +kernel)))

def cert299 : Leaf := ⟨⟨328,268,65,321,0,461,277,77,13⟩,[(4,7)],[(5,7,4)],⟨7,67,268,28,176,50,200,416,321⟩,⟨7,67,268,28,176,50,200,416,320⟩,[⟨1,1219850616699935436308481,⟨261,333,268,92,252,508,220,508,332⟩⟩,⟨4,1522078901057328128361799,⟨263,327,271,13,160,419,463,419,327⟩⟩,⟨7,1520603161532537360254439,⟨263,327,271,29,61,319,335,303,327⟩⟩]⟩
theorem node299 : UpperPrefix a [2,6,8,4,7,1,3,5] 30 :=
  Boolean.leaf_sound a [2,6,8,4,7,1,3,5] 30 cert299 (by decide +kernel)

theorem node300 : UpperPrefix a [2,6,8,4,7,1,3] 30 :=
  branch_upper a [2,6,8,4,7,1,3] 30 (by decide) (fin9_cases _
  node298
  (invalid_upper a [2,6,8,4,7,1,3,1] 30 (by decide +kernel))
  (invalid_upper a [2,6,8,4,7,1,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,6,8,4,7,1,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,6,8,4,7,1,3,4] 30 (by decide +kernel))
  node299
  (invalid_upper a [2,6,8,4,7,1,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,6,8,4,7,1,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,6,8,4,7,1,3,8] 30 (by decide +kernel)))

def cert301 : Leaf := ⟨⟨480,420,224,480,0,452,0,109,173⟩,[(4,6),(6,4)],[],⟨7,67,268,28,176,50,224,393,329⟩,⟨7,67,268,28,176,50,224,384,320⟩,[⟨4,1247997465840527747322893,⟨135,67,399,463,224,98,224,384,320⟩⟩,⟨1,1219580833063476836171777,⟨397,477,268,92,252,508,252,396,348⟩⟩,⟨0,1210107853589039826338816,⟨38,122,268,92,252,122,252,396,348⟩⟩,⟨3,1210107853870468531491853,⟨39,115,295,119,240,114,240,384,336⟩⟩]⟩
theorem node301 : UpperPrefix a [2,6,8,4,7,1,5] 30 :=
  Boolean.leaf_sound a [2,6,8,4,7,1,5] 30 cert301 (by decide +kernel)

theorem node302 : UpperPrefix a [2,6,8,4,7,1] 30 :=
  branch_upper a [2,6,8,4,7,1] 30 (by decide) (fin9_cases _
  node296
  (invalid_upper a [2,6,8,4,7,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,6,8,4,7,1,2] 30 (by decide +kernel))
  node300
  (invalid_upper a [2,6,8,4,7,1,4] 30 (by decide +kernel))
  node301
  (invalid_upper a [2,6,8,4,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,6,8,4,7,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,6,8,4,7,1,8] 30 (by decide +kernel)))

theorem node303 : UpperPrefix a [2,6,8,4,7] 30 :=
  branch_upper a [2,6,8,4,7] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut65 [2,6,8,4,7,0] [2,6,4,8,7,1] 30 (by decide +kernel) node263)
  node302
  (invalid_upper a [2,6,8,4,7,2] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut119 [2,6,8,4,7,3] [2,6,1,7,3,8] 30 (by decide +kernel) node201)
  (invalid_upper a [2,6,8,4,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,6,8,4,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,6,8,4,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,6,8,4,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,6,8,4,7,8] 30 (by decide +kernel)))

theorem node304 : UpperPrefix a [2,6,8,4] 30 :=
  branch_upper a [2,6,8,4] 30 (by decide) (fin9_cases _
  node290
  node291
  (invalid_upper a [2,6,8,4,2] 30 (by decide +kernel))
  node293
  (invalid_upper a [2,6,8,4,4] 30 (by decide +kernel))
  (invalid_upper a [2,6,8,4,5] 30 (by decide +kernel))
  (invalid_upper a [2,6,8,4,6] 30 (by decide +kernel))
  node303
  (invalid_upper a [2,6,8,4,8] 30 (by decide +kernel)))

theorem node305 : UpperPrefix a [2,6,8,7,0] 30 :=
  branch_upper a [2,6,8,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,6,8,7,0,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut60 [2,6,8,7,0,1] [2,3,4,6,8,7] 30 (by decide +kernel) node32)
  (invalid_upper a [2,6,8,7,0,2] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut66 [2,6,8,7,0,3] [2,4,5,6,7,8] 30 (by decide +kernel) node103)
  (invalid_upper a [2,6,8,7,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,6,8,7,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,6,8,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,6,8,7,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,6,8,7,0,8] 30 (by decide +kernel)))

theorem node306 : UpperPrefix a [2,6,8,7,1] 30 :=
  branch_upper a [2,6,8,7,1] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut63 [2,6,8,7,1,0] [2,3,4,6,8,7] 30 (by decide +kernel) node32)
  (invalid_upper a [2,6,8,7,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,6,8,7,1,2] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut90 [2,6,8,7,1,3] [2,4,6,5,7,8] 30 (by decide +kernel) node158)
  (invalid_upper a [2,6,8,7,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,6,8,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,6,8,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,6,8,7,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,6,8,7,1,8] 30 (by decide +kernel)))

theorem node307 : UpperPrefix a [2,6,8,7,3] 30 :=
  branch_upper a [2,6,8,7,3] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut69 [2,6,8,7,3,0] [2,4,5,6,7,8] 30 (by decide +kernel) node103)
  (PrefixConjugacy.upper aut93 [2,6,8,7,3,1] [2,4,6,5,7,8] 30 (by decide +kernel) node158)
  (invalid_upper a [2,6,8,7,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,6,8,7,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,6,8,7,3,4] 30 (by decide +kernel))
  (invalid_upper a [2,6,8,7,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,6,8,7,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,6,8,7,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,6,8,7,3,8] 30 (by decide +kernel)))

theorem node308 : UpperPrefix a [2,6,8,7] 30 :=
  branch_upper a [2,6,8,7] 30 (by decide) (fin9_cases _
  node305
  node306
  (invalid_upper a [2,6,8,7,2] 30 (by decide +kernel))
  node307
  (invalid_upper a [2,6,8,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,6,8,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,6,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,6,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,6,8,7,8] 30 (by decide +kernel)))

theorem node309 : UpperPrefix a [2,6,8] 30 :=
  branch_upper a [2,6,8] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut55 [2,6,8,0] [2,6,1,7] 30 (by decide +kernel) node204)
  (PrefixConjugacy.upper aut79 [2,6,8,1] [2,6,7,1] 30 (by decide +kernel) node272)
  (invalid_upper a [2,6,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,6,8,3] 30 (by decide +kernel))
  node304
  (PrefixConjugacy.upper aut3 [2,6,8,5] [2,6,8,4] 30 (by decide +kernel) node304)
  (invalid_upper a [2,6,8,6] 30 (by decide +kernel))
  node308
  (invalid_upper a [2,6,8,8] 30 (by decide +kernel)))

theorem node310 : UpperPrefix a [2,6] 30 :=
  branch_upper a [2,6] 30 (by decide) (fin9_cases _
  node193
  node211
  (invalid_upper a [2,6,2] 30 (by decide +kernel))
  (invalid_upper a [2,6,3] 30 (by decide +kernel))
  node267
  (PrefixConjugacy.upper aut3 [2,6,5] [2,6,4] 30 (by decide +kernel) node267)
  (invalid_upper a [2,6,6] 30 (by decide +kernel))
  node288
  node309)

theorem node311 : UpperPrefix a [2] 30 :=
  branch_upper a [2] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,0] 30 (by decide +kernel))
  (invalid_upper a [2,1] 30 (by decide +kernel))
  (invalid_upper a [2,2] 30 (by decide +kernel))
  node38
  node183
  (PrefixConjugacy.upper aut3 [2,5] [2,4] 30 (by decide +kernel) node183)
  node310
  (PrefixConjugacy.upper aut2 [2,7] [2,6] 30 (by decide +kernel) node310)
  (PrefixConjugacy.upper aut1 [2,8] [2,6] 30 (by decide +kernel) node310))

theorem node312 : UpperPrefix a [6,7,0] 30 :=
  branch_upper a [6,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [6,7,0,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut48 [6,7,0,1] [2,3,6,7] 30 (by decide +kernel) node36)
  (invalid_upper a [6,7,0,2] 30 (by decide +kernel))
  (invalid_upper a [6,7,0,3] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut48 [6,7,0,4] [2,4,6,7] 30 (by decide +kernel) node174)
  (PrefixConjugacy.upper aut51 [6,7,0,5] [2,4,6,7] 30 (by decide +kernel) node174)
  (invalid_upper a [6,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [6,7,0,7] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut49 [6,7,0,8] [2,6,7,8] 30 (by decide +kernel) node287))

theorem node313 : UpperPrefix a [6,7,1] 30 :=
  branch_upper a [6,7,1] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut54 [6,7,1,0] [2,3,6,7] 30 (by decide +kernel) node36)
  (invalid_upper a [6,7,1,1] 30 (by decide +kernel))
  (invalid_upper a [6,7,1,2] 30 (by decide +kernel))
  (invalid_upper a [6,7,1,3] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut74 [6,7,1,4] [2,4,6,8] 30 (by decide +kernel) node181)
  (PrefixConjugacy.upper aut77 [6,7,1,5] [2,4,6,8] 30 (by decide +kernel) node181)
  (invalid_upper a [6,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [6,7,1,7] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut73 [6,7,1,8] [2,6,8,7] 30 (by decide +kernel) node308))

def cert314 : Leaf := ⟨⟨32,16,128,64,335,335,271,79,15⟩,[],[(4,0,1),(5,1,0),(7,3,2)],⟨19,35,76,140,319,319,463,399,335⟩,⟨19,35,76,140,48,48,192,384,320⟩,[⟨8,1181745669248365126705,⟨19,35,76,140,51,51,204,140,76⟩⟩,⟨0,1210107565283877539808256,⟨18,34,76,140,48,48,204,396,332⟩⟩,⟨1,1210107565283877539807233,⟨17,33,76,140,48,48,204,396,332⟩⟩,⟨2,1210107565283851685094449,⟨19,35,72,136,51,51,192,384,320⟩⟩,⟨3,1210107565283850612401201,⟨19,35,68,132,51,51,192,384,320⟩⟩,⟨6,1210106412362347079296049,⟨19,35,12,140,51,51,128,384,256⟩⟩]⟩
theorem node314 : UpperPrefix a [4,5,6,7] 30 :=
  Boolean.leaf_sound a [4,5,6,7] 30 cert314 (by decide +kernel)

def cert315 : Local := ⟨⟨248,0,0,178,322,194,50,114,178⟩,[(1,2),(2,1)],[(2,0,1),(2,0,2),(3,1,0),(0,2,0),(8,5,4)]⟩
theorem node315 : UpperPrefix a [2,3,0,6,7,8] 30 :=
  local_sound a [2,3,0,6,7,8] 30 cert315 (by decide +kernel)

theorem node316 : UpperPrefix a [4,6,7,8,0] 30 :=
  branch_upper a [4,6,7,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [4,6,7,8,0,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut60 [4,6,7,8,0,1] [2,3,0,6,7,8] 30 (by decide +kernel) node315)
  (PrefixConjugacy.upper aut60 [4,6,7,8,0,2] [2,4,0,6,7,8] 30 (by decide +kernel) node51)
  (PrefixConjugacy.upper aut66 [4,6,7,8,0,3] [2,4,0,6,8,7] 30 (by decide +kernel) node58)
  (invalid_upper a [4,6,7,8,0,4] 30 (by decide +kernel))
  (invalid_upper a [4,6,7,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [4,6,7,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [4,6,7,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [4,6,7,8,0,8] 30 (by decide +kernel)))

def cert317 : Local := ⟨⟨0,244,0,177,321,193,49,113,177⟩,[(0,2),(2,1)],[(2,0,1),(3,1,0),(3,1,2),(1,2,0),(8,5,4)]⟩
theorem node317 : UpperPrefix a [2,3,1,6,7,8] 30 :=
  local_sound a [2,3,1,6,7,8] 30 cert317 (by decide +kernel)

theorem node318 : UpperPrefix a [4,6,7,8,1] 30 :=
  branch_upper a [4,6,7,8,1] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut63 [4,6,7,8,1,0] [2,3,1,6,7,8] 30 (by decide +kernel) node317)
  (invalid_upper a [4,6,7,8,1,1] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut84 [4,6,7,8,1,2] [2,4,6,0,7,8] 30 (by decide +kernel) node123)
  (PrefixConjugacy.upper aut90 [4,6,7,8,1,3] [2,4,6,0,8,7] 30 (by decide +kernel) node131)
  (invalid_upper a [4,6,7,8,1,4] 30 (by decide +kernel))
  (invalid_upper a [4,6,7,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [4,6,7,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [4,6,7,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [4,6,7,8,1,8] 30 (by decide +kernel)))

theorem node319 : UpperPrefix a [4,6,7,8,2] 30 :=
  branch_upper a [4,6,7,8,2] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut63 [4,6,7,8,2,0] [2,4,1,6,7,8] 30 (by decide +kernel) node77)
  (PrefixConjugacy.upper aut87 [4,6,7,8,2,1] [2,4,6,1,7,8] 30 (by decide +kernel) node138)
  (invalid_upper a [4,6,7,8,2,2] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut110 [4,6,7,8,2,3] [2,3,6,7,0,8] 30 (by decide +kernel) node217)
  (invalid_upper a [4,6,7,8,2,4] 30 (by decide +kernel))
  (invalid_upper a [4,6,7,8,2,5] 30 (by decide +kernel))
  (invalid_upper a [4,6,7,8,2,6] 30 (by decide +kernel))
  (invalid_upper a [4,6,7,8,2,7] 30 (by decide +kernel))
  (invalid_upper a [4,6,7,8,2,8] 30 (by decide +kernel)))

#print axioms node319
end Delivery.FiniteExclusion.Sharp2x2x2x3

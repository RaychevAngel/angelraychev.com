import RegularNineSharp3x3x3Base
import RegularNineSharp3x3x3C000
import RegularNineSharp3x3x3C003
import RegularNineSharp3x3x3C004
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp3x3x3
open Bounds BoundTreeRows Extremal
def cert320 : Leaf := ⟨⟨68,73,106,0,139,67,267,75,11⟩,[(3,2)],[(4,2,3),(2,3,0),(7,5,4)],⟨11,38,21,28,112,168,451,387,323⟩,⟨11,38,21,28,112,168,192,384,320⟩,[⟨8,1181752446675122906623,⟨15,47,31,31,127,175,255,191,127⟩⟩,⟨5,1224302387765867344561155,⟨459,463,477,28,80,136,192,384,320⟩⟩]⟩
theorem node320 : UpperPrefix a [3,5,4,2,6,7] 30 :=
  Boolean.leaf_sound a [3,5,4,2,6,7] 30 cert320 (by decide +kernel)

def cert321 : Leaf := ⟨⟨372,320,0,0,390,326,294,102,38⟩,[(2,3),(3,2)],[(7,5,4)],⟨11,38,21,25,112,168,454,390,326⟩,⟨11,38,21,25,112,168,192,384,320⟩,[⟨0,1238497212535347151375360,⟨506,502,502,56,112,168,192,384,320⟩⟩,⟨3,1375713840711862408463361,⟨471,502,469,469,498,502,192,384,320⟩⟩,⟨4,1238497212533766603410433,⟨491,486,487,41,96,168,192,384,320⟩⟩]⟩
theorem node321 : UpperPrefix a [3,5,4,0,6,7] 30 :=
  Boolean.leaf_sound a [3,5,4,0,6,7] 30 cert321 (by decide +kernel)

def cert322 : Leaf := ⟨⟨0,89,64,101,133,85,277,85,21⟩,[(0,3)],[(5,1,3),(1,3,0),(7,5,4)],⟨11,38,21,26,112,168,453,389,325⟩,⟨11,38,21,26,112,168,192,384,320⟩,[⟨3,1233765604630513098949633,⟨471,502,469,18,112,160,192,384,320⟩⟩,⟨8,1181752446675122906623,⟨15,47,31,31,127,175,255,191,127⟩⟩]⟩
theorem node322 : UpperPrefix a [3,5,4,1,6,7] 30 :=
  Boolean.leaf_sound a [3,5,4,1,6,7] 30 cert322 (by decide +kernel)

def cert323 : Leaf := ⟨⟨20,9,34,135,263,71,6,7,7⟩,[],[(6,3,5),(7,4,3),(8,5,4)],⟨11,38,21,88,176,296,193,390,326⟩,⟨11,38,21,88,176,296,193,384,320⟩,[⟨3,1224302424920700098970625,⟨471,502,469,80,176,288,453,384,320⟩⟩,⟨4,1238497194519368093928449,⟨491,486,487,72,160,296,225,384,320⟩⟩,⟨5,1219570797910960844571651,⟨459,463,93,88,144,264,193,384,320⟩⟩]⟩
theorem node323 : UpperPrefix a [3,5,4,6,7,8,0] 30 :=
  Boolean.leaf_sound a [3,5,4,6,7,8,0] 30 cert323 (by decide +kernel)

def cert324 : Leaf := ⟨⟨16,25,34,131,259,83,21,23,23⟩,[],[(6,3,5),(7,4,3),(8,5,4)],⟨11,38,21,88,176,296,194,389,325⟩,⟨11,38,21,88,176,296,194,384,320⟩,[⟨3,1233765568601716079985665,⟨471,502,469,80,176,288,210,384,320⟩⟩,⟨5,1238497157330586844529667,⟨459,463,477,88,144,264,451,384,320⟩⟩,⟨2,1210107578807887656387649,⟨11,34,17,89,176,296,251,440,377⟩⟩]⟩
theorem node324 : UpperPrefix a [3,5,4,6,7,8,1] 30 :=
  Boolean.leaf_sound a [3,5,4,6,7,8,1] 30 cert324 (by decide +kernel)

def cert325 : Leaf := ⟨⟨20,8,42,134,270,70,11,15,15⟩,[],[(6,3,5),(7,4,3),(8,5,4)],⟨11,38,21,88,176,296,196,387,323⟩,⟨11,38,21,88,176,296,196,384,320⟩,[⟨4,1233765622678860103420929,⟨491,486,487,72,160,296,454,384,320⟩⟩,⟨5,1224302441809062873007107,⟨459,463,477,88,144,264,204,384,320⟩⟩,⟨0,1210107578807887657468928,⟨10,38,20,90,176,296,254,440,378⟩⟩]⟩
theorem node325 : UpperPrefix a [3,5,4,6,7,8,2] 30 :=
  Boolean.leaf_sound a [3,5,4,6,7,8,2] 30 cert325 (by decide +kernel)

theorem node326 : UpperPrefix a [3,5,4,6,7,8] 30 :=
  branch_upper a [3,5,4,6,7,8] 30 (by decide) (fin9_cases _
  node323
  node324
  node325
  (invalid_upper a [3,5,4,6,7,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,7,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,7,8,8] 30 (by decide +kernel)))

theorem node327 : UpperPrefix a [3,5,4,6,7] 30 :=
  branch_upper a [3,5,4,6,7] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut39 [3,5,4,6,7,0] [3,5,4,2,6,7] 30 (by decide +kernel) node320)
  (PrefixConjugacy.upper aut39 [3,5,4,6,7,1] [3,5,4,0,6,7] 30 (by decide +kernel) node321)
  (PrefixConjugacy.upper aut39 [3,5,4,6,7,2] [3,5,4,1,6,7] 30 (by decide +kernel) node322)
  (invalid_upper a [3,5,4,6,7,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,7,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,7,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,7,7] 30 (by decide +kernel))
  node326)

def cert328 : Leaf := ⟨⟨260,265,298,0,267,67,267,11,139⟩,[(3,2)],[(4,2,3),(2,3,0)],⟨11,38,21,28,112,296,195,387,451⟩,⟨11,38,21,28,112,296,192,384,320⟩,[⟨7,1208926987195990630721023,⟨15,47,31,31,127,319,127,319,383⟩⟩,⟨5,1224302387765867344561155,⟨459,463,477,28,80,264,192,384,320⟩⟩,⟨6,1210401560267529122767935,⟨15,175,31,31,191,431,128,384,256⟩⟩]⟩
theorem node328 : UpperPrefix a [3,5,4,2,6,8] 30 :=
  Boolean.leaf_sound a [3,5,4,2,6,8] 30 cert328 (by decide +kernel)

def cert329 : Leaf := ⟨⟨500,448,0,0,390,198,294,102,166⟩,[(2,3),(3,2)],[],⟨11,38,21,25,112,296,198,390,454⟩,⟨11,38,21,25,112,296,192,384,320⟩,[⟨0,1238497212535347151375360,⟨506,502,502,56,112,296,192,384,320⟩⟩,⟨3,1375713840711862408463361,⟨471,502,469,469,498,502,192,384,320⟩⟩,⟨4,1238497212533766603410433,⟨491,486,487,41,96,296,192,384,320⟩⟩]⟩
theorem node329 : UpperPrefix a [3,5,4,0,6,8] 30 :=
  Boolean.leaf_sound a [3,5,4,0,6,8] 30 cert329 (by decide +kernel)

def cert330 : Leaf := ⟨⟨0,281,256,293,261,85,277,21,149⟩,[(0,3)],[(5,1,3),(1,3,0)],⟨11,38,21,26,112,296,197,389,453⟩,⟨11,38,21,26,112,296,192,384,320⟩,[⟨3,1233765604630513098949633,⟨471,502,469,18,112,288,192,384,320⟩⟩,⟨7,1208926987195990630721023,⟨15,47,31,31,127,319,127,319,383⟩⟩,⟨6,1210401560267529122767935,⟨15,175,31,31,191,431,128,384,256⟩⟩]⟩
theorem node330 : UpperPrefix a [3,5,4,1,6,8] 30 :=
  Boolean.leaf_sound a [3,5,4,1,6,8] 30 cert330 (by decide +kernel)

def cert331 : Leaf := ⟨⟨20,9,34,135,71,263,6,7,7⟩,[],[],⟨11,38,21,88,304,168,193,390,326⟩,⟨11,38,21,88,304,168,193,384,320⟩,[⟨3,1224302424920700098970625,⟨471,502,469,80,304,160,453,384,320⟩⟩,⟨4,1238497194519368093928449,⟨491,486,487,72,288,168,225,384,320⟩⟩,⟨5,1219570797910960844571651,⟨459,463,93,88,272,136,193,384,320⟩⟩,⟨6,1210253986596411738715689,⟨47,39,151,191,439,175,131,384,256⟩⟩,⟨7,1246705905528290475009065,⟨271,55,23,351,311,319,65,256,320⟩⟩,⟨8,1182322129976968635453,⟨15,103,31,95,127,239,193,128,64⟩⟩]⟩
theorem node331 : UpperPrefix a [3,5,4,6,8,7,0] 30 :=
  Boolean.leaf_sound a [3,5,4,6,8,7,0] 30 cert331 (by decide +kernel)

def cert332 : Leaf := ⟨⟨16,25,34,131,67,275,21,23,23⟩,[],[],⟨11,38,21,88,304,168,194,389,325⟩,⟨11,38,21,88,304,168,194,384,320⟩,[⟨3,1233765568601716079985665,⟨471,502,469,80,304,160,210,384,320⟩⟩,⟨5,1238497157330586844529667,⟨459,463,477,88,272,136,451,384,320⟩⟩,⟨6,1210253986596411738715689,⟨47,39,151,191,439,175,130,384,256⟩⟩,⟨7,1246705905528290475009065,⟨271,55,23,351,311,319,70,256,320⟩⟩,⟨8,1182322129976968635453,⟨15,103,31,95,127,239,194,128,64⟩⟩,⟨2,1210107572065682354865217,⟨11,34,17,121,312,184,251,440,377⟩⟩]⟩
theorem node332 : UpperPrefix a [3,5,4,6,8,7,1] 30 :=
  Boolean.leaf_sound a [3,5,4,6,8,7,1] 30 cert332 (by decide +kernel)

def cert333 : Leaf := ⟨⟨20,8,42,134,78,262,11,15,15⟩,[],[],⟨11,38,21,88,304,168,196,387,323⟩,⟨11,38,21,88,304,168,196,384,320⟩,[⟨4,1233765622678860103420929,⟨491,486,487,72,288,168,454,384,320⟩⟩,⟨5,1224302441809062873007107,⟨459,463,477,88,272,136,204,384,320⟩⟩,⟨6,1210253986596411738715689,⟨47,39,151,191,439,175,132,384,256⟩⟩,⟨7,1246705905528290475009065,⟨271,55,23,351,311,319,68,256,320⟩⟩,⟨8,1182322129976968635453,⟨15,103,31,95,127,239,197,128,64⟩⟩,⟨0,1210107572065682355946496,⟨10,38,20,122,312,184,254,440,378⟩⟩]⟩
theorem node333 : UpperPrefix a [3,5,4,6,8,7,2] 30 :=
  Boolean.leaf_sound a [3,5,4,6,8,7,2] 30 cert333 (by decide +kernel)

theorem node334 : UpperPrefix a [3,5,4,6,8,7] 30 :=
  branch_upper a [3,5,4,6,8,7] 30 (by decide) (fin9_cases _
  node331
  node332
  node333
  (invalid_upper a [3,5,4,6,8,7,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,8,7,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,8,7,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,8,7,8] 30 (by decide +kernel)))

theorem node335 : UpperPrefix a [3,5,4,6,8] 30 :=
  branch_upper a [3,5,4,6,8] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut39 [3,5,4,6,8,0] [3,5,4,2,6,8] 30 (by decide +kernel) node328)
  (PrefixConjugacy.upper aut39 [3,5,4,6,8,1] [3,5,4,0,6,8] 30 (by decide +kernel) node329)
  (PrefixConjugacy.upper aut39 [3,5,4,6,8,2] [3,5,4,1,6,8] 30 (by decide +kernel) node330)
  (invalid_upper a [3,5,4,6,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,8,6] 30 (by decide +kernel))
  node334
  (invalid_upper a [3,5,4,6,8,8] 30 (by decide +kernel)))

theorem node336 : UpperPrefix a [3,5,4,6] 30 :=
  branch_upper a [3,5,4,6] 30 (by decide) (fin9_cases _
  node317
  node318
  node319
  (invalid_upper a [3,5,4,6,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,6] 30 (by decide +kernel))
  node327
  node335)

theorem node337 : UpperPrefix a [3,5,4] 30 :=
  branch_upper a [3,5,4] 30 (by decide) (fin9_cases _
  node314
  node315
  node316
  (invalid_upper a [3,5,4,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,5] 30 (by decide +kernel))
  node336
  (PrefixConjugacy.upper aut2 [3,5,4,7] [3,5,4,6] 30 (by decide +kernel) node336)
  (PrefixConjugacy.upper aut1 [3,5,4,8] [3,5,4,6] 30 (by decide +kernel) node336))

def cert338 : Leaf := ⟨⟨400,465,400,386,0,469,276,84,148⟩,[(4,1)],[(5,1,4),(1,4,3)],⟨11,38,69,25,50,444,468,404,468⟩,⟨11,38,69,25,50,40,192,384,320⟩,[⟨3,1413566703666302484235265,⟨471,502,453,469,498,502,192,384,320⟩⟩,⟨0,1219570781022599144014848,⟨474,502,68,24,498,40,192,384,320⟩⟩,⟨2,1210107565283991674160147,⟨27,59,73,25,59,40,192,384,320⟩⟩,⟨6,1210106412362487068361747,⟨27,63,13,25,59,40,128,384,256⟩⟩]⟩
theorem node338 : UpperPrefix a [3,5,6,0,1] 30 :=
  Boolean.leaf_sound a [3,5,6,0,1] 30 cert338 (by decide +kernel)

def cert339 : Leaf := ⟨⟨36,0,434,36,0,470,310,118,182⟩,[(1,4),(4,1)],[],⟨11,38,69,25,52,442,466,402,466⟩,⟨11,38,69,25,52,40,192,384,320⟩,[⟨0,1356787409549378645404672,⟨506,502,502,506,502,488,192,384,320⟩⟩,⟨3,1489272429575182635787265,⟨471,502,453,471,502,502,192,384,320⟩⟩,⟨6,1210106412362487068369947,⟨27,63,13,27,63,41,128,384,256⟩⟩,⟨7,1208926973663274263913499,⟨27,63,77,27,63,41,64,256,320⟩⟩,⟨8,1181745669362500510747,⟨27,63,77,27,63,41,192,128,64⟩⟩,⟨1,1210107565283989259288577,⟨25,52,77,25,52,40,192,384,320⟩⟩,⟨4,1210107565282752174498825,⟨11,38,69,11,38,41,192,384,320⟩⟩]⟩
theorem node339 : UpperPrefix a [3,5,6,0,2] 30 :=
  Boolean.leaf_sound a [3,5,6,0,2] 30 cert339 (by decide +kernel)

def cert340 : Leaf := ⟨⟨0,464,432,484,324,0,308,116,180⟩,[(0,5),(5,0)],[],⟨11,38,69,25,176,42,468,404,340⟩,⟨11,38,69,25,176,42,192,384,320⟩,[⟨1,1413566703666303692177409,⟨477,500,461,477,496,508,192,384,320⟩⟩,⟨3,1413566703666302484235265,⟨471,502,453,469,498,502,192,384,320⟩⟩,⟨0,1238497212537546174630912,⟨506,502,502,56,176,506,192,384,320⟩⟩]⟩
theorem node340 : UpperPrefix a [3,5,6,0,7,1] 30 :=
  Boolean.leaf_sound a [3,5,6,0,7,1] 30 cert340 (by decide +kernel)

def cert341 : Leaf := ⟨⟨240,208,178,224,320,208,52,116,180⟩,[],[(8,5,4),(1,6,2)],⟨11,38,69,25,176,296,194,404,340⟩,⟨11,38,69,25,176,296,194,384,320⟩,[⟨0,1238497230549745660857344,⟨506,502,502,120,176,296,466,384,320⟩⟩,⟨3,1413566847781490560091137,⟨471,502,453,469,498,502,466,384,320⟩⟩,⟨2,1210107578807888193258563,⟨11,43,89,25,176,296,251,440,377⟩⟩]⟩
theorem node341 : UpperPrefix a [3,5,6,0,7,8,1] 30 :=
  Boolean.leaf_sound a [3,5,6,0,7,8,1] 30 cert341 (by decide +kernel)

def cert342 : Leaf := ⟨⟨164,128,162,166,262,150,34,54,182⟩,[],[(8,5,4)],⟨11,38,69,25,176,296,196,402,338⟩,⟨11,38,69,25,176,296,196,384,320⟩,[⟨0,1546050553386294383217664,⟨506,502,502,440,176,312,470,384,448⟩⟩,⟨3,1451419494563148522079233,⟨471,502,453,469,498,502,196,384,320⟩⟩,⟨6,1212467609147631362671943,⟨11,63,31,25,184,441,191,441,443⟩⟩,⟨4,1210107853513128332518441,⟨15,39,69,79,231,303,196,384,320⟩⟩]⟩
theorem node342 : UpperPrefix a [3,5,6,0,7,8,2] 30 :=
  Boolean.leaf_sound a [3,5,6,0,7,8,2] 30 cert342 (by decide +kernel)

def cert343 : Leaf := ⟨⟨116,80,50,102,326,86,0,118,54⟩,[(6,4)],[(7,4,6),(8,5,4)],⟨11,38,69,25,176,296,208,390,326⟩,⟨11,38,69,25,176,296,208,384,320⟩,[⟨0,1238497518780121812569088,⟨506,502,502,120,240,296,208,384,320⟩⟩,⟨3,1375714273057426636030977,⟨471,502,453,469,498,502,208,384,320⟩⟩]⟩
theorem node343 : UpperPrefix a [3,5,6,0,7,8,4] 30 :=
  Boolean.leaf_sound a [3,5,6,0,7,8,4] 30 cert343 (by decide +kernel)

theorem node344 : UpperPrefix a [3,5,6,0,7,8] 30 :=
  branch_upper a [3,5,6,0,7,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,6,0,7,8,0] 30 (by decide +kernel))
  node341
  node342
  (invalid_upper a [3,5,6,0,7,8,3] 30 (by decide +kernel))
  node343
  (invalid_upper a [3,5,6,0,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,0,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,0,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,0,7,8,8] 30 (by decide +kernel)))

theorem node345 : UpperPrefix a [3,5,6,0,7] 30 :=
  branch_upper a [3,5,6,0,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,6,0,7,0] 30 (by decide +kernel))
  node340
  (PrefixConjugacy.upper aut77 [3,5,6,0,7,2] [3,4,6,8,1,0] 30 (by decide +kernel) node287)
  (invalid_upper a [3,5,6,0,7,3] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut59 [3,5,6,0,7,4] [2,3,6,1,0,8] 30 (by decide +kernel) node57)
  (invalid_upper a [3,5,6,0,7,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,0,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,0,7,7] 30 (by decide +kernel))
  node344)

def cert346 : Leaf := ⟨⟨180,144,178,164,132,276,52,116,180⟩,[],[(1,6,2)],⟨11,38,69,25,304,168,194,404,340⟩,⟨11,38,69,25,304,168,194,384,320⟩,[⟨0,1238497230549745660857344,⟨506,502,502,120,304,168,466,384,320⟩⟩,⟨3,1413566847781490560091137,⟨471,502,453,469,498,502,466,384,320⟩⟩,⟨6,1210106419144177749068869,⟨11,39,47,25,312,184,187,440,313⟩⟩,⟨8,1182322129976975451193,⟨15,103,69,31,127,239,198,128,64⟩⟩]⟩
theorem node346 : UpperPrefix a [3,5,6,0,8,7,1] 30 :=
  Boolean.leaf_sound a [3,5,6,0,8,7,1] 30 cert346 (by decide +kernel)

def cert347 : Leaf := ⟨⟨164,128,162,166,134,278,34,54,182⟩,[],[],⟨11,38,69,25,304,168,196,402,338⟩,⟨11,38,69,25,304,168,196,384,320⟩,[⟨0,1546050553386294383217664,⟨506,502,502,440,304,184,470,384,448⟩⟩,⟨3,1451419494563148522079233,⟨471,502,453,469,498,502,196,384,320⟩⟩,⟨6,1212467611955781107223877,⟨11,39,47,57,441,184,191,441,443⟩⟩,⟨8,1182322129976975451193,⟨15,103,69,31,127,239,196,128,64⟩⟩,⟨4,1210108141743504491045929,⟨15,103,69,15,359,239,196,384,320⟩⟩]⟩
theorem node347 : UpperPrefix a [3,5,6,0,8,7,2] 30 :=
  Boolean.leaf_sound a [3,5,6,0,8,7,2] 30 cert347 (by decide +kernel)

def cert348 : Leaf := ⟨⟨116,64,50,102,198,70,294,102,38⟩,[],[(8,4,6)],⟨11,38,69,25,304,168,208,390,326⟩,⟨11,38,69,25,304,168,208,384,320⟩,[⟨0,1238497230549745660857344,⟨506,502,502,120,304,168,208,384,320⟩⟩,⟨3,1375714273057426636030977,⟨471,502,453,469,498,502,208,384,320⟩⟩,⟨7,1511158428566802389804121,⟨11,38,333,27,319,41,351,260,333⟩⟩,⟨4,1229052371481636256091137,⟨171,422,487,41,288,168,192,384,320⟩⟩]⟩
theorem node348 : UpperPrefix a [3,5,6,0,8,7,4] 30 :=
  Boolean.leaf_sound a [3,5,6,0,8,7,4] 30 cert348 (by decide +kernel)

theorem node349 : UpperPrefix a [3,5,6,0,8,7] 30 :=
  branch_upper a [3,5,6,0,8,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,6,0,8,7,0] 30 (by decide +kernel))
  node346
  node347
  (invalid_upper a [3,5,6,0,8,7,3] 30 (by decide +kernel))
  node348
  (invalid_upper a [3,5,6,0,8,7,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,0,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,0,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,0,8,7,8] 30 (by decide +kernel)))

theorem node350 : UpperPrefix a [3,5,6,0,8] 30 :=
  branch_upper a [3,5,6,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,6,0,8,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut94 [3,5,6,0,8,1] [3,5,6,0,7,1] 30 (by decide +kernel) node340)
  (PrefixConjugacy.upper aut76 [3,5,6,0,8,2] [3,4,6,7,1,0] 30 (by decide +kernel) node247)
  (invalid_upper a [3,5,6,0,8,3] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut58 [3,5,6,0,8,4] [2,3,6,1,0,7] 30 (by decide +kernel) node56)
  (invalid_upper a [3,5,6,0,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,0,8,6] 30 (by decide +kernel))
  node349
  (invalid_upper a [3,5,6,0,8,8] 30 (by decide +kernel)))

theorem node351 : UpperPrefix a [3,5,6,0] 30 :=
  branch_upper a [3,5,6,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,6,0,0] 30 (by decide +kernel))
  node338
  node339
  (invalid_upper a [3,5,6,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,0,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,0,6] 30 (by decide +kernel))
  node345
  node350)

def cert352 : Leaf := ⟨⟨0,465,400,33,8,469,277,85,149⟩,[(0,3)],[(3,0,4),(5,1,3),(1,3,0)],⟨11,38,69,26,49,444,468,404,468⟩,⟨11,38,69,26,49,40,192,384,320⟩,[⟨2,1210107565286188549932043,⟨27,59,73,27,57,57,192,384,320⟩⟩,⟨6,1210106412364683944133643,⟨27,63,13,27,57,57,128,384,256⟩⟩,⟨7,1208926973665471139677195,⟨27,63,77,27,57,57,64,256,320⟩⟩,⟨8,1181745671559376274443,⟨27,63,77,27,57,57,192,128,64⟩⟩]⟩
theorem node352 : UpperPrefix a [3,5,6,1,0] 30 :=
  Boolean.leaf_sound a [3,5,6,1,0] 30 cert352 (by decide +kernel)

def cert353 : Local := ⟨⟨0,0,408,485,0,465,281,89,153⟩,[(0,3),(1,4),(4,1)],[(5,1,3),(1,3,0),(2,4,3)]⟩
theorem node353 : UpperPrefix a [3,5,6,1,2] 30 :=
  local_sound a [3,5,6,1,2] 30 cert353 (by decide +kernel)

def cert354 : Local := ⟨⟨0,481,416,0,460,196,292,100,164⟩,[(0,3),(3,1)],[(3,0,4),(4,1,0),(4,1,3),(1,3,0),(0,4,1)]⟩
theorem node354 : UpperPrefix a [3,4,6,1,0,8] 30 :=
  local_sound a [3,4,6,1,0,8] 30 cert354 (by decide +kernel)

def cert355 : Local := ⟨⟨0,0,408,481,329,465,281,89,153⟩,[(0,3),(1,5)],[(5,1,3),(1,3,0),(2,5,1)]⟩
theorem node355 : UpperPrefix a [3,5,6,1,7,2] 30 :=
  local_sound a [3,5,6,1,7,2] 30 cert355 (by decide +kernel)

def cert356 : Local := ⟨⟨0,216,0,228,332,212,28,92,156⟩,[(0,3),(2,6)],[(5,1,3),(1,3,0),(8,5,4),(0,6,2)]⟩
theorem node356 : UpperPrefix a [3,5,6,1,7,8,0] 30 :=
  local_sound a [3,5,6,1,7,8,0] 30 cert356 (by decide +kernel)

def cert357 : Leaf := ⟨⟨0,153,152,161,265,145,25,25,153⟩,[(0,3)],[(5,1,3),(1,3,0),(8,5,4)],⟨11,38,69,26,176,296,196,401,337⟩,⟨11,38,69,26,176,296,196,384,320⟩,[⟨2,1229347519571465244509195,⟨187,443,505,187,176,441,496,384,336⟩⟩,⟨6,1212762757052926813832527,⟨27,191,31,27,176,441,191,441,443⟩⟩]⟩
theorem node357 : UpperPrefix a [3,5,6,1,7,8,2] 30 :=
  Boolean.leaf_sound a [3,5,6,1,7,8,2] 30 cert357 (by decide +kernel)

def cert358 : Local := ⟨⟨0,89,24,101,333,85,0,93,29⟩,[(0,3),(6,4)],[(5,1,3),(1,3,0),(7,4,6),(8,5,4)]⟩
theorem node358 : UpperPrefix a [3,5,6,1,7,8,4] 30 :=
  local_sound a [3,5,6,1,7,8,4] 30 cert358 (by decide +kernel)

theorem node359 : UpperPrefix a [3,5,6,1,7,8] 30 :=
  branch_upper a [3,5,6,1,7,8] 30 (by decide) (fin9_cases _
  node356
  (invalid_upper a [3,5,6,1,7,8,1] 30 (by decide +kernel))
  node357
  (invalid_upper a [3,5,6,1,7,8,3] 30 (by decide +kernel))
  node358
  (invalid_upper a [3,5,6,1,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,1,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,1,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,1,7,8,8] 30 (by decide +kernel)))

theorem node360 : UpperPrefix a [3,5,6,1,7] 30 :=
  branch_upper a [3,5,6,1,7] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut59 [3,5,6,1,7,0] [3,4,6,1,0,8] 30 (by decide +kernel) node354)
  (invalid_upper a [3,5,6,1,7,1] 30 (by decide +kernel))
  node355
  (invalid_upper a [3,5,6,1,7,3] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut95 [3,5,6,1,7,4] [2,3,6,0,8,1] 30 (by decide +kernel) node47)
  (invalid_upper a [3,5,6,1,7,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,1,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,1,7,7] 30 (by decide +kernel))
  node359)

def cert361 : Local := ⟨⟨0,481,416,0,460,324,292,100,164⟩,[(0,3),(3,1)],[(3,0,4),(4,1,0),(4,1,3),(1,3,0),(0,4,1)]⟩
theorem node361 : UpperPrefix a [3,4,6,1,0,7] 30 :=
  local_sound a [3,4,6,1,0,7] 30 cert361 (by decide +kernel)

def cert362 : Local := ⟨⟨0,0,408,481,201,465,281,89,153⟩,[(0,3),(1,5)],[(5,1,3),(1,3,0),(2,5,1)]⟩
theorem node362 : UpperPrefix a [3,5,6,1,8,2] 30 :=
  local_sound a [3,5,6,1,8,2] 30 cert362 (by decide +kernel)

def cert363 : Local := ⟨⟨0,472,0,484,204,340,284,92,156⟩,[(0,3),(2,6)],[(5,1,3),(1,3,0),(0,6,2)]⟩
theorem node363 : UpperPrefix a [3,5,6,1,8,7,0] 30 :=
  local_sound a [3,5,6,1,8,7,0] 30 cert363 (by decide +kernel)

def cert364 : Leaf := ⟨⟨0,409,408,417,137,273,281,25,153⟩,[(0,3)],[(5,1,3),(1,3,0)],⟨11,38,69,26,304,168,196,401,337⟩,⟨11,38,69,26,304,168,196,384,320⟩,[⟨2,1229052371980127741936651,⟨187,443,505,187,304,169,496,384,336⟩⟩,⟨6,1212615186189826432994637,⟨43,39,47,187,441,185,191,441,443⟩⟩]⟩
theorem node364 : UpperPrefix a [3,5,6,1,8,7,2] 30 :=
  Boolean.leaf_sound a [3,5,6,1,8,7,2] 30 cert364 (by decide +kernel)

def cert365 : Leaf := ⟨⟨0,89,16,101,69,85,261,85,21⟩,[(0,3)],[(5,1,3),(1,3,0),(8,4,6)],⟨11,38,69,26,304,168,208,389,325⟩,⟨11,38,69,26,304,168,208,384,320⟩,[⟨3,1233765568601716079985665,⟨471,502,453,82,304,160,208,384,320⟩⟩,⟨7,1530047894498418812265563,⟨27,319,333,27,319,41,351,260,333⟩⟩]⟩
theorem node365 : UpperPrefix a [3,5,6,1,8,7,4] 30 :=
  Boolean.leaf_sound a [3,5,6,1,8,7,4] 30 cert365 (by decide +kernel)

theorem node366 : UpperPrefix a [3,5,6,1,8,7] 30 :=
  branch_upper a [3,5,6,1,8,7] 30 (by decide) (fin9_cases _
  node363
  (invalid_upper a [3,5,6,1,8,7,1] 30 (by decide +kernel))
  node364
  (invalid_upper a [3,5,6,1,8,7,3] 30 (by decide +kernel))
  node365
  (invalid_upper a [3,5,6,1,8,7,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,1,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,1,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,1,8,7,8] 30 (by decide +kernel)))

theorem node367 : UpperPrefix a [3,5,6,1,8] 30 :=
  branch_upper a [3,5,6,1,8] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut58 [3,5,6,1,8,0] [3,4,6,1,0,7] 30 (by decide +kernel) node361)
  (invalid_upper a [3,5,6,1,8,1] 30 (by decide +kernel))
  node362
  (invalid_upper a [3,5,6,1,8,3] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut94 [3,5,6,1,8,4] [2,3,6,0,7,1] 30 (by decide +kernel) node40)
  (invalid_upper a [3,5,6,1,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,1,8,6] 30 (by decide +kernel))
  node366
  (invalid_upper a [3,5,6,1,8,8] 30 (by decide +kernel)))

theorem node368 : UpperPrefix a [3,5,6,1] 30 :=
  branch_upper a [3,5,6,1] 30 (by decide) (fin9_cases _
  node352
  (invalid_upper a [3,5,6,1,1] 30 (by decide +kernel))
  node353
  (invalid_upper a [3,5,6,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,1,6] 30 (by decide +kernel))
  node360
  node367)

def cert369 : Local := ⟨⟨0,481,458,452,389,0,261,69,133⟩,[(0,5),(5,0)],[(3,0,2),(4,1,0),(4,1,5),(5,2,1),(1,5,2)]⟩
theorem node369 : UpperPrefix a [3,4,5,0,6,1] 30 :=
  local_sound a [3,4,5,0,6,1] 30 cert369 (by decide +kernel)

def cert370 : Leaf := ⟨⟨0,496,482,416,456,448,288,96,160⟩,[(0,1)],[(2,0,0),(3,1,4),(4,2,1),(1,4,2)],⟨7,14,21,88,50,41,480,416,480⟩,⟨7,14,21,88,50,41,192,384,320⟩,[⟨0,1437224743012698143329792,⟨14,14,478,472,506,506,192,384,320⟩⟩]⟩
theorem node370 : UpperPrefix a [2,3,4,6,1,0] 30 :=
  Boolean.leaf_sound a [2,3,4,6,1,0] 30 cert370 (by decide +kernel)

theorem node371 : UpperPrefix a [3,5,6,2,0] 30 :=
  branch_upper a [3,5,6,2,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,6,2,0,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut93 [3,5,6,2,0,1] [3,4,5,0,6,1] 30 (by decide +kernel) node369)
  (invalid_upper a [3,5,6,2,0,2] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,2,0,3] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut75 [3,5,6,2,0,4] [2,3,4,6,1,0] 30 (by decide +kernel) node370)
  (invalid_upper a [3,5,6,2,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,2,0,6] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut74 [3,5,6,2,0,7] [3,4,6,8,0,2] 30 (by decide +kernel) node281)
  (PrefixConjugacy.upper aut73 [3,5,6,2,0,8] [3,4,6,7,0,2] 30 (by decide +kernel) node239))

def cert372 : Local := ⟨⟨0,464,0,484,460,404,276,84,148⟩,[(0,3),(2,4)],[(3,0,4),(5,1,3),(1,3,0),(0,4,2)]⟩
theorem node372 : UpperPrefix a [3,5,4,1,0,6] 30 :=
  local_sound a [3,5,4,1,0,6] 30 cert372 (by decide +kernel)

def cert373 : Local := ⟨⟨0,496,0,418,456,466,306,114,178⟩,[(0,1),(2,5)],[(2,0,0),(3,1,4),(0,5,2)]⟩
theorem node373 : UpperPrefix a [2,3,5,6,1,0] 30 :=
  local_sound a [2,3,5,6,1,0] 30 cert373 (by decide +kernel)

def cert374 : Leaf := ⟨⟨148,217,146,131,0,83,275,83,147⟩,[(4,1)],[(5,1,4),(2,3,0)],⟨11,38,69,28,50,168,465,401,337⟩,⟨11,38,69,28,50,168,192,384,320⟩,[⟨8,1181752458080637128191,⟨27,63,127,31,59,187,255,191,127⟩⟩,⟨3,1214839173153293061063681,⟨471,54,453,20,50,160,192,384,320⟩⟩,⟨6,1210106412362484786660371,⟨27,63,5,29,59,168,128,384,256⟩⟩]⟩
theorem node374 : UpperPrefix a [3,5,6,2,1,7] 30 :=
  Boolean.leaf_sound a [3,5,6,2,1,7] 30 cert374 (by decide +kernel)

def cert375 : Leaf := ⟨⟨276,345,274,259,0,83,275,83,147⟩,[(4,1)],[(5,1,4),(2,3,0)],⟨11,38,69,28,50,296,209,401,465⟩,⟨11,38,69,28,50,296,192,384,320⟩,[⟨7,1208926987207121258661367,⟨27,63,95,29,59,319,127,319,383⟩⟩,⟨3,1214839173153293061063681,⟨471,54,453,20,50,288,192,384,320⟩⟩,⟨6,1210106412362484786660371,⟨27,63,5,29,59,296,128,384,256⟩⟩]⟩
theorem node375 : UpperPrefix a [3,5,6,2,1,8] 30 :=
  Boolean.leaf_sound a [3,5,6,2,1,8] 30 cert375 (by decide +kernel)

theorem node376 : UpperPrefix a [3,5,6,2,1] 30 :=
  branch_upper a [3,5,6,2,1] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut57 [3,5,6,2,1,0] [3,5,4,1,0,6] 30 (by decide +kernel) node372)
  (invalid_upper a [3,5,6,2,1,1] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,2,1,2] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,2,1,3] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut75 [3,5,6,2,1,4] [2,3,5,6,1,0] 30 (by decide +kernel) node373)
  (invalid_upper a [3,5,6,2,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,2,1,6] 30 (by decide +kernel))
  node374
  node375)

def cert377 : Leaf := ⟨⟨0,337,272,353,328,85,277,85,149⟩,[(0,3)],[(3,0,4),(5,1,3),(1,3,0)],⟨11,38,69,26,49,296,212,404,468⟩,⟨11,38,69,26,49,296,192,384,320⟩,[⟨7,1208926987207123540362751,⟨27,63,95,27,59,319,127,319,383⟩⟩,⟨2,1210107565286188549932043,⟨27,59,73,27,57,313,192,384,320⟩⟩]⟩
theorem node377 : UpperPrefix a [3,5,6,1,0,8] 30 :=
  Boolean.leaf_sound a [3,5,6,1,0,8] 30 cert377 (by decide +kernel)

def cert378 : Leaf := ⟨⟨244,216,0,224,320,208,50,114,178⟩,[(2,6)],[(2,3,0),(8,5,4),(0,6,2)],⟨11,38,69,28,176,296,193,402,338⟩,⟨11,38,69,28,176,296,193,384,320⟩,[⟨3,1224302424920700115747841,⟨471,502,453,84,176,288,453,384,324⟩⟩,⟨1,1210107578807888211083265,⟨9,44,93,28,176,296,253,440,380⟩⟩]⟩
theorem node378 : UpperPrefix a [3,5,6,2,7,8,0] 30 :=
  Boolean.leaf_sound a [3,5,6,2,7,8,0] 30 cert378 (by decide +kernel)

def cert379 : Leaf := ⟨⟨244,208,178,224,320,208,49,112,176⟩,[],[(2,3,0),(8,5,4),(1,6,2)],⟨11,38,69,28,176,296,194,385,336⟩,⟨11,38,69,28,176,296,194,385,320⟩,[⟨3,1639889518474069829493761,⟨471,502,453,470,502,352,470,453,320⟩⟩,⟨0,1531228486615967353281536,⟨42,302,382,318,176,298,498,384,336⟩⟩]⟩
theorem node379 : UpperPrefix a [3,5,6,2,7,8,1,0] 30 :=
  Boolean.leaf_sound a [3,5,6,2,7,8,1,0] 30 cert379 (by decide +kernel)

def cert380 : Leaf := ⟨⟨196,201,138,193,329,193,9,73,137⟩,[],[(2,3,0),(8,5,4),(1,6,2)],⟨11,38,69,28,176,296,194,400,321⟩,⟨11,38,69,28,176,296,194,400,320⟩,[⟨4,1342336421193146961002025,⟨303,295,359,367,487,303,194,454,320⟩⟩,⟨5,1536024656466667910726721,⟨463,262,325,412,152,396,463,412,325⟩⟩]⟩
theorem node380 : UpperPrefix a [3,5,6,2,7,8,1,4] 30 :=
  Boolean.leaf_sound a [3,5,6,2,7,8,1,4] 30 cert380 (by decide +kernel)

theorem node381 : UpperPrefix a [3,5,6,2,7,8,1] 30 :=
  branch_upper a [3,5,6,2,7,8,1] 30 (by decide) (fin9_cases _
  node379
  (invalid_upper a [3,5,6,2,7,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,2,7,8,1,2] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,2,7,8,1,3] 30 (by decide +kernel))
  node380
  (invalid_upper a [3,5,6,2,7,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,2,7,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,2,7,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,2,7,8,1,8] 30 (by decide +kernel)))

def cert382 : Leaf := ⟨⟨116,81,50,99,323,83,0,114,51⟩,[(6,4)],[(2,3,0),(7,4,6),(8,5,4)],⟨11,38,69,28,176,296,208,385,322⟩,⟨11,38,69,28,176,296,208,385,320⟩,[⟨3,1639889518474069829493761,⟨471,502,453,470,502,352,470,453,320⟩⟩]⟩
theorem node382 : UpperPrefix a [3,5,6,2,7,8,4,0] 30 :=
  Boolean.leaf_sound a [3,5,6,2,7,8,4,0] 30 cert382 (by decide +kernel)

def cert383 : Leaf := ⟨⟨100,73,58,99,331,67,0,105,43⟩,[(6,4)],[(2,3,0),(7,4,6),(8,5,4)],⟨11,38,69,28,176,296,208,386,321⟩,⟨11,38,69,28,176,296,208,386,320⟩,[⟨4,1229384413121253632644137,⟨171,423,325,431,161,427,192,386,320⟩⟩]⟩
theorem node383 : UpperPrefix a [3,5,6,2,7,8,4,1] 30 :=
  Boolean.leaf_sound a [3,5,6,2,7,8,4,1] 30 cert383 (by decide +kernel)

#print axioms node383
end Delivery.FiniteExclusion.Sharp3x3x3

import RegularNineSharp3x3x3Base
import RegularNineSharp3x3x3C001
import RegularNineSharp3x3x3C002
import RegularNineSharp3x3x3C003
import RegularNineSharp3x3x3C004
import RegularNineSharp3x3x3C005
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp3x3x3
open Bounds BoundTreeRows Extremal
theorem node384 : UpperPrefix a [3,5,6,2,7,8,4] 30 :=
  branch_upper a [3,5,6,2,7,8,4] 30 (by decide) (fin9_cases _
  node382
  node383
  (invalid_upper a [3,5,6,2,7,8,4,2] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,2,7,8,4,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,2,7,8,4,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,2,7,8,4,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,2,7,8,4,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,2,7,8,4,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,2,7,8,4,8] 30 (by decide +kernel)))

theorem node385 : UpperPrefix a [3,5,6,2,7,8] 30 :=
  branch_upper a [3,5,6,2,7,8] 30 (by decide) (fin9_cases _
  node378
  node381
  (invalid_upper a [3,5,6,2,7,8,2] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,2,7,8,3] 30 (by decide +kernel))
  node384
  (invalid_upper a [3,5,6,2,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,2,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,2,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,2,7,8,8] 30 (by decide +kernel)))

theorem node386 : UpperPrefix a [3,5,6,2,7] 30 :=
  branch_upper a [3,5,6,2,7] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut59 [3,5,6,2,7,0] [3,5,6,1,0,8] 30 (by decide +kernel) node377)
  (PrefixConjugacy.upper aut95 [3,5,6,2,7,1] [3,4,6,0,8,1] 30 (by decide +kernel) node189)
  (invalid_upper a [3,5,6,2,7,2] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,2,7,3] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut77 [3,5,6,2,7,4] [2,3,6,8,1,0] 30 (by decide +kernel) node133)
  (invalid_upper a [3,5,6,2,7,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,2,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,2,7,7] 30 (by decide +kernel))
  node385)

def cert387 : Leaf := ⟨⟨0,209,144,225,200,85,277,85,149⟩,[(0,3)],[(3,0,4),(5,1,3),(1,3,0)],⟨11,38,69,26,49,168,468,404,340⟩,⟨11,38,69,26,49,168,192,384,320⟩,[⟨8,1181752458085066313199,⟨27,63,127,27,57,187,255,191,127⟩⟩,⟨2,1210107565286188549932043,⟨27,59,73,27,57,185,192,384,320⟩⟩]⟩
theorem node387 : UpperPrefix a [3,5,6,1,0,7] 30 :=
  Boolean.leaf_sound a [3,5,6,1,0,7] 30 cert387 (by decide +kernel)

def cert388 : Leaf := ⟨⟨244,216,0,224,192,336,50,114,178⟩,[(2,6)],[(2,3,0),(0,6,2)],⟨11,38,69,28,304,168,193,402,338⟩,⟨11,38,69,28,304,168,193,384,320⟩,[⟨3,1224302424920700115747841,⟨471,502,453,84,304,160,453,384,324⟩⟩,⟨8,1182322129976992228409,⟨15,103,69,31,127,239,197,128,68⟩⟩,⟨1,1210107572065682372689921,⟨9,36,109,28,312,184,253,440,380⟩⟩]⟩
theorem node388 : UpperPrefix a [3,5,6,2,8,7,0] 30 :=
  Boolean.leaf_sound a [3,5,6,2,8,7,0] 30 cert388 (by decide +kernel)

def cert389 : Leaf := ⟨⟨484,448,418,480,192,320,289,96,176⟩,[],[(2,3,0),(1,6,2)],⟨11,38,69,28,304,168,194,385,336⟩,⟨11,38,69,28,304,168,194,385,320⟩,[⟨3,1753226458180328413742081,⟨471,502,453,404,370,502,470,453,320⟩⟩,⟨4,1210258454166142621349417,⟨111,103,71,239,487,239,198,455,320⟩⟩,⟨0,1531228488393190729059328,⟨26,318,382,286,304,168,506,400,368⟩⟩]⟩
theorem node389 : UpperPrefix a [3,5,6,2,8,7,1,0] 30 :=
  Boolean.leaf_sound a [3,5,6,2,8,7,1,0] 30 cert389 (by decide +kernel)

def cert390 : Local := ⟨⟨228,201,170,225,201,81,41,0,169⟩,[(7,4)],[(2,3,0),(8,4,7),(1,6,2),(4,7,5)]⟩
theorem node390 : UpperPrefix a [3,5,6,2,8,7,1,4] 30 :=
  local_sound a [3,5,6,2,8,7,1,4] 30 cert390 (by decide +kernel)

theorem node391 : UpperPrefix a [3,5,6,2,8,7,1] 30 :=
  branch_upper a [3,5,6,2,8,7,1] 30 (by decide) (fin9_cases _
  node389
  (invalid_upper a [3,5,6,2,8,7,1,1] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,2,8,7,1,2] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,2,8,7,1,3] 30 (by decide +kernel))
  node390
  (invalid_upper a [3,5,6,2,8,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,2,8,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,2,8,7,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,2,8,7,1,8] 30 (by decide +kernel)))

def cert392 : Leaf := ⟨⟨228,193,176,225,193,65,289,98,163⟩,[],[(2,3,0),(8,4,6)],⟨11,38,69,28,304,168,208,385,322⟩,⟨11,38,69,28,304,168,208,385,320⟩,[⟨3,1450995147391859195921409,⟨471,502,453,468,370,502,468,453,320⟩⟩,⟨1,1210110454369431021682689,⟨9,108,109,28,376,252,252,509,376⟩⟩,⟨4,1229273732691995747425321,⟨171,423,487,431,417,171,192,417,320⟩⟩]⟩
theorem node392 : UpperPrefix a [3,5,6,2,8,7,4,0] 30 :=
  Boolean.leaf_sound a [3,5,6,2,8,7,4,0] 30 cert392 (by decide +kernel)

def cert393 : Leaf := ⟨⟨116,89,50,97,65,81,289,113,49⟩,[],[(2,3,0),(8,4,6)],⟨11,38,69,28,304,168,208,386,321⟩,⟨11,38,69,28,304,168,208,386,320⟩,[⟨7,1530047894498435857917147,⟨27,319,333,287,319,41,351,287,333⟩⟩,⟨1,1228999918031625211871233,⟨25,380,325,284,368,248,240,504,320⟩⟩,⟨3,1233749427700651584128001,⟨471,502,453,276,304,224,208,466,320⟩⟩]⟩
theorem node393 : UpperPrefix a [3,5,6,2,8,7,4,1] 30 :=
  Boolean.leaf_sound a [3,5,6,2,8,7,4,1] 30 cert393 (by decide +kernel)

theorem node394 : UpperPrefix a [3,5,6,2,8,7,4] 30 :=
  branch_upper a [3,5,6,2,8,7,4] 30 (by decide) (fin9_cases _
  node392
  node393
  (invalid_upper a [3,5,6,2,8,7,4,2] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,2,8,7,4,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,2,8,7,4,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,2,8,7,4,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,2,8,7,4,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,2,8,7,4,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,2,8,7,4,8] 30 (by decide +kernel)))

theorem node395 : UpperPrefix a [3,5,6,2,8,7] 30 :=
  branch_upper a [3,5,6,2,8,7] 30 (by decide) (fin9_cases _
  node388
  node391
  (invalid_upper a [3,5,6,2,8,7,2] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,2,8,7,3] 30 (by decide +kernel))
  node394
  (invalid_upper a [3,5,6,2,8,7,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,2,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,2,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,2,8,7,8] 30 (by decide +kernel)))

theorem node396 : UpperPrefix a [3,5,6,2,8] 30 :=
  branch_upper a [3,5,6,2,8] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut58 [3,5,6,2,8,0] [3,5,6,1,0,7] 30 (by decide +kernel) node387)
  (PrefixConjugacy.upper aut94 [3,5,6,2,8,1] [3,4,6,0,7,1] 30 (by decide +kernel) node182)
  (invalid_upper a [3,5,6,2,8,2] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,2,8,3] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut76 [3,5,6,2,8,4] [2,3,6,7,1,0] 30 (by decide +kernel) node106)
  (invalid_upper a [3,5,6,2,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,2,8,6] 30 (by decide +kernel))
  node395
  (invalid_upper a [3,5,6,2,8,8] 30 (by decide +kernel)))

theorem node397 : UpperPrefix a [3,5,6,2] 30 :=
  branch_upper a [3,5,6,2] 30 (by decide) (fin9_cases _
  node371
  node376
  (invalid_upper a [3,5,6,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,2,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,2,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,2,6] 30 (by decide +kernel))
  node386
  node396)

def cert398 : Leaf := ⟨⟨500,0,424,0,457,193,297,105,169⟩,[(1,3),(3,1)],[(4,1,0),(2,3,0)],⟨11,22,69,28,50,296,225,417,481⟩,⟨11,22,69,28,50,296,192,384,320⟩,[⟨1,1233765605017405095149569,⟨493,508,485,508,56,296,192,384,320⟩⟩]⟩
theorem node398 : UpperPrefix a [3,4,6,2,1,8] 30 :=
  Boolean.leaf_sound a [3,4,6,2,1,8] 30 cert398 (by decide +kernel)

def cert399 : Leaf := ⟨⟨0,312,370,353,328,80,312,120,184⟩,[(0,1)],[(2,0,0),(1,3,2)],⟨7,70,13,26,49,296,240,432,496⟩,⟨7,70,13,26,49,296,192,384,320⟩,[⟨0,1323666154569384378502144,⟨38,102,494,506,496,488,192,384,320⟩⟩,⟨7,1208926987206983331775979,⟨15,95,13,31,61,319,127,319,383⟩⟩]⟩
theorem node399 : UpperPrefix a [2,6,3,1,0,8] 30 :=
  Boolean.leaf_sound a [2,6,3,1,0,8] 30 cert399 (by decide +kernel)

def cert400 : Leaf := ⟨⟨224,193,130,65,200,209,5,85,149⟩,[],[(3,0,4),(1,6,2)],⟨11,38,69,152,49,296,194,404,340⟩,⟨11,38,69,152,49,296,194,384,320⟩,[⟨8,1181889786755734070377,⟨95,55,77,223,55,127,223,132,77⟩⟩,⟨5,1285886806827151278736385,⟨207,6,69,412,477,392,194,384,320⟩⟩,⟨2,1210107578816666569540673,⟨11,34,89,184,49,312,251,440,377⟩⟩,⟨4,1210107709397940261119017,⟨79,39,69,207,39,367,194,384,320⟩⟩]⟩
theorem node400 : UpperPrefix a [3,5,6,7,0,8,1] 30 :=
  Boolean.leaf_sound a [3,5,6,7,0,8,1] 30 cert400 (by decide +kernel)

def cert401 : Leaf := ⟨⟨160,129,162,35,138,147,35,33,179⟩,[],[(3,0,4)],⟨11,38,69,152,49,296,196,386,336⟩,⟨11,38,69,152,49,296,196,386,320⟩,[⟨2,1531246948851017301623939,⟨187,443,377,185,57,312,505,443,376⟩⟩,⟨6,1212467609148317752133063,⟨27,63,31,185,57,441,191,443,443⟩⟩,⟨8,1184195629773504144553,⟨95,55,69,223,55,127,205,223,68⟩⟩,⟨4,1210406063866054306456617,⟨79,231,69,207,231,495,196,454,320⟩⟩]⟩
theorem node401 : UpperPrefix a [3,5,6,7,0,8,2,1] 30 :=
  Boolean.leaf_sound a [3,5,6,7,0,8,2,1] 30 cert401 (by decide +kernel)

def cert402 : Leaf := ⟨⟨164,129,162,0,142,135,35,39,167⟩,[(3,7)],[(3,0,4),(4,7,3)],⟨11,38,69,152,49,296,196,400,322⟩,⟨11,38,69,152,49,296,196,400,320⟩,[⟨6,1212762757052949765064007,⟨27,191,31,184,185,441,191,441,443⟩⟩,⟨8,1184195629773504144553,⟨95,55,69,223,55,127,205,223,68⟩⟩]⟩
theorem node402 : UpperPrefix a [3,5,6,7,0,8,2,4] 30 :=
  Boolean.leaf_sound a [3,5,6,7,0,8,2,4] 30 cert402 (by decide +kernel)

theorem node403 : UpperPrefix a [3,5,6,7,0,8,2] 30 :=
  branch_upper a [3,5,6,7,0,8,2] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,6,7,0,8,2,0] 30 (by decide +kernel))
  node401
  (invalid_upper a [3,5,6,7,0,8,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,7,0,8,2,3] 30 (by decide +kernel))
  node402
  (invalid_upper a [3,5,6,7,0,8,2,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,7,0,8,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,7,0,8,2,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,7,0,8,2,8] 30 (by decide +kernel)))

def cert404 : Leaf := ⟨⟨244,208,146,0,206,214,0,86,150⟩,[(3,6),(6,3)],[(3,0,4)],⟨11,38,69,152,49,296,208,390,326⟩,⟨11,38,69,152,49,296,208,384,320⟩,[⟨0,1229052524710684804516864,⟨202,422,494,216,48,360,216,416,360⟩⟩,⟨8,1181889786755734070377,⟨95,55,77,223,55,127,223,132,77⟩⟩,⟨5,1214839586358433248707585,⟨463,6,461,220,477,328,220,384,328⟩⟩]⟩
theorem node404 : UpperPrefix a [3,5,6,7,0,8,4] 30 :=
  Boolean.leaf_sound a [3,5,6,7,0,8,4] 30 cert404 (by decide +kernel)

theorem node405 : UpperPrefix a [3,5,6,7,0,8] 30 :=
  branch_upper a [3,5,6,7,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,6,7,0,8,0] 30 (by decide +kernel))
  node400
  node403
  (invalid_upper a [3,5,6,7,0,8,3] 30 (by decide +kernel))
  node404
  (invalid_upper a [3,5,6,7,0,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,7,0,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,7,0,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,7,0,8,8] 30 (by decide +kernel)))

theorem node406 : UpperPrefix a [3,5,6,7,0] 30 :=
  branch_upper a [3,5,6,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,6,7,0,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut62 [3,5,6,7,0,1] [3,4,6,2,1,8] 30 (by decide +kernel) node398)
  (PrefixConjugacy.upper aut62 [3,5,6,7,0,2] [3,5,6,2,1,8] 30 (by decide +kernel) node375)
  (invalid_upper a [3,5,6,7,0,3] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut59 [3,5,6,7,0,4] [2,6,3,1,0,8] 30 (by decide +kernel) node399)
  (invalid_upper a [3,5,6,7,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,7,0,7] 30 (by decide +kernel))
  node405)

def cert407 : Leaf := ⟨⟨0,440,0,482,200,464,312,120,184⟩,[(0,1),(2,3)],[(2,0,0),(0,3,2)],⟨7,70,13,25,304,42,240,432,496⟩,⟨7,70,13,25,304,42,192,384,320⟩,[⟨1,1437224743012691166101505,⟨5,68,13,477,496,508,192,384,320⟩⟩]⟩
theorem node407 : UpperPrefix a [2,6,3,0,8,1] 30 :=
  Boolean.leaf_sound a [2,6,3,0,8,1] 30 cert407 (by decide +kernel)

def cert408 : Leaf := ⟨⟨452,456,0,326,0,214,262,86,150⟩,[(2,6),(4,1)],[(5,1,4),(0,6,2)],⟨11,38,69,152,50,296,193,404,340⟩,⟨11,38,69,152,50,296,193,384,320⟩,[⟨3,1224302424920700115747841,⟨471,502,453,144,434,288,453,384,324⟩⟩,⟨4,1210107709397940277896233,⟨79,39,69,207,39,367,197,384,324⟩⟩]⟩
theorem node408 : UpperPrefix a [3,5,6,7,1,8,0] 30 :=
  Boolean.leaf_sound a [3,5,6,7,1,8,0] 30 cert408 (by decide +kernel)

def cert409 : Leaf := ⟨⟨400,409,402,259,0,147,275,19,147⟩,[(4,1)],[(5,1,4)],⟨11,38,69,152,50,296,196,401,337⟩,⟨11,38,69,152,50,296,196,384,320⟩,[⟨2,1229052373910666686235667,⟨187,443,505,153,187,296,488,384,352⟩⟩,⟨6,1212762757041954648786263,⟨27,191,31,185,187,441,191,441,443⟩⟩,⟨3,1214839245210887098991617,⟨471,118,453,144,50,288,196,384,320⟩⟩]⟩
theorem node409 : UpperPrefix a [3,5,6,7,1,8,2] 30 :=
  Boolean.leaf_sound a [3,5,6,7,1,8,2] 30 cert409 (by decide +kernel)

def cert410 : Leaf := ⟨⟨468,473,408,0,0,213,0,93,157⟩,[(3,6),(4,1),(6,3)],[(5,1,4)],⟨11,38,69,152,50,296,208,389,325⟩,⟨11,38,69,152,50,296,208,384,320⟩,[⟨1,1233765667856701967302657,⟨493,420,493,216,48,360,216,416,360⟩⟩]⟩
theorem node410 : UpperPrefix a [3,5,6,7,1,8,4] 30 :=
  Boolean.leaf_sound a [3,5,6,7,1,8,4] 30 cert410 (by decide +kernel)

theorem node411 : UpperPrefix a [3,5,6,7,1,8] 30 :=
  branch_upper a [3,5,6,7,1,8] 30 (by decide) (fin9_cases _
  node408
  (invalid_upper a [3,5,6,7,1,8,1] 30 (by decide +kernel))
  node409
  (invalid_upper a [3,5,6,7,1,8,3] 30 (by decide +kernel))
  node410
  (invalid_upper a [3,5,6,7,1,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,7,1,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,7,1,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,7,1,8,8] 30 (by decide +kernel)))

theorem node412 : UpperPrefix a [3,5,6,7,1] 30 :=
  branch_upper a [3,5,6,7,1] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut98 [3,5,6,7,1,0] [3,5,6,1,8,2] 30 (by decide +kernel) node362)
  (invalid_upper a [3,5,6,7,1,1] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut98 [3,5,6,7,1,2] [3,4,6,1,8,2] 30 (by decide +kernel) node207)
  (invalid_upper a [3,5,6,7,1,3] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut95 [3,5,6,7,1,4] [2,6,3,0,8,1] 30 (by decide +kernel) node407)
  (invalid_upper a [3,5,6,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,7,1,7] 30 (by decide +kernel))
  node411)

def cert413 : Leaf := ⟨⟨0,0,440,357,0,0,317,125,189⟩,[(0,5),(1,4),(4,1),(5,0)],[],⟨11,38,69,152,52,42,465,401,337⟩,⟨11,38,69,152,52,42,192,384,320⟩,[⟨1,1214839173153294269022209,⟨477,52,461,152,52,56,192,384,320⟩⟩]⟩
theorem node413 : UpperPrefix a [3,5,6,7,2,1] 30 :=
  Boolean.leaf_sound a [3,5,6,7,2,1] 30 cert413 (by decide +kernel)

def cert414 : Leaf := ⟨⟨0,441,0,226,457,0,314,122,186⟩,[(0,1),(2,5),(5,2)],[(2,0,0)],⟨7,70,13,280,50,41,240,432,496⟩,⟨7,70,13,280,50,41,192,384,320⟩,[⟨0,1285813291192733985145856,⟨6,70,12,472,506,40,192,384,320⟩⟩]⟩
theorem node414 : UpperPrefix a [2,6,3,8,1,0] 30 :=
  Boolean.leaf_sound a [2,6,3,8,1,0] 30 cert414 (by decide +kernel)

def cert415 : Leaf := ⟨⟨500,0,0,356,0,212,310,118,182⟩,[(1,4),(2,6),(4,1)],[(0,6,2)],⟨11,38,69,152,52,296,193,402,338⟩,⟨11,38,69,152,52,296,193,384,320⟩,[⟨3,1300081649575498953794561,⟨471,502,453,402,502,416,453,384,324⟩⟩,⟨1,1210107578816804026318849,⟨25,52,93,184,52,312,253,440,380⟩⟩]⟩
theorem node415 : UpperPrefix a [3,5,6,7,2,8,0] 30 :=
  Boolean.leaf_sound a [3,5,6,7,2,8,0] 30 cert415 (by decide +kernel)

def cert416 : Leaf := ⟨⟨244,0,178,100,0,212,52,117,181⟩,[(1,4),(4,1)],[(1,6,2)],⟨11,38,69,152,52,296,194,401,337⟩,⟨11,38,69,152,52,296,194,384,320⟩,[⟨3,1214839317268481136927745,⟨471,54,453,210,54,352,210,384,320⟩⟩,⟨8,1181889786755734070377,⟨95,55,77,223,55,127,223,132,77⟩⟩,⟨0,1210107718406385045611520,⟨90,54,76,218,54,360,218,416,360⟩⟩]⟩
theorem node416 : UpperPrefix a [3,5,6,7,2,8,1] 30 :=
  Boolean.leaf_sound a [3,5,6,7,2,8,1] 30 cert416 (by decide +kernel)

def cert417 : Leaf := ⟨⟨500,0,442,0,0,211,0,123,187⟩,[(1,4),(3,6),(4,1),(6,3)],[],⟨11,38,69,152,52,296,208,387,323⟩,⟨11,38,69,152,52,296,208,384,320⟩,[⟨2,1214839308437075966034945,⟨491,34,489,216,48,360,216,416,360⟩⟩]⟩
theorem node417 : UpperPrefix a [3,5,6,7,2,8,4] 30 :=
  Boolean.leaf_sound a [3,5,6,7,2,8,4] 30 cert417 (by decide +kernel)

theorem node418 : UpperPrefix a [3,5,6,7,2,8] 30 :=
  branch_upper a [3,5,6,7,2,8] 30 (by decide) (fin9_cases _
  node415
  node416
  (invalid_upper a [3,5,6,7,2,8,2] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,7,2,8,3] 30 (by decide +kernel))
  node417
  (invalid_upper a [3,5,6,7,2,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,7,2,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,7,2,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,7,2,8,8] 30 (by decide +kernel)))

theorem node419 : UpperPrefix a [3,5,6,7,2] 30 :=
  branch_upper a [3,5,6,7,2] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut80 [3,5,6,7,2,0] [3,4,6,8,2,1] 30 (by decide +kernel) node293)
  node413
  (invalid_upper a [3,5,6,7,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,7,2,3] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut77 [3,5,6,7,2,4] [2,6,3,8,1,0] 30 (by decide +kernel) node414)
  (invalid_upper a [3,5,6,7,2,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,7,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,7,2,7] 30 (by decide +kernel))
  node418)

def cert420 : Leaf := ⟨⟨228,193,162,356,196,0,36,116,180⟩,[(5,0)],[(3,0,5),(8,4,3),(0,5,1),(1,6,2)],⟨11,38,69,152,304,41,194,404,340⟩,⟨11,38,69,152,304,41,194,384,320⟩,[⟨4,1210107709714599609925161,⟨111,39,103,239,295,111,194,384,320⟩⟩]⟩
theorem node420 : UpperPrefix a [3,5,6,7,8,0,1] 30 :=
  Boolean.leaf_sound a [3,5,6,7,8,0,1] 30 cert420 (by decide +kernel)

def cert421 : Leaf := ⟨⟨180,145,178,294,134,0,50,54,182⟩,[(5,0)],[(3,0,5),(8,4,3),(0,5,1)],⟨11,38,69,152,304,41,196,402,338⟩,⟨11,38,69,152,304,41,196,384,320⟩,[⟨6,1212467612131702967668037,⟨43,39,47,184,441,41,191,441,443⟩⟩]⟩
theorem node421 : UpperPrefix a [3,5,6,7,8,0,2] 30 :=
  Boolean.leaf_sound a [3,5,6,7,8,0,2] 30 cert421 (by decide +kernel)

def cert422 : Local := ⟨⟨244,209,178,0,198,0,0,118,182⟩,[(3,6),(5,0),(6,3)],[(3,0,5),(8,4,3),(8,4,6),(0,5,1)]⟩
theorem node422 : UpperPrefix a [3,5,6,7,8,0,4] 30 :=
  local_sound a [3,5,6,7,8,0,4] 30 cert422 (by decide +kernel)

theorem node423 : UpperPrefix a [3,5,6,7,8,0] 30 :=
  branch_upper a [3,5,6,7,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,6,7,8,0,0] 30 (by decide +kernel))
  node420
  node421
  (invalid_upper a [3,5,6,7,8,0,3] 30 (by decide +kernel))
  node422
  (invalid_upper a [3,5,6,7,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,7,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,7,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,7,8,0,8] 30 (by decide +kernel)))

def cert424 : Leaf := ⟨⟨0,216,0,356,204,0,60,124,188⟩,[(0,5),(2,6),(5,0)],[(8,4,3),(0,6,2)],⟨11,38,69,152,304,42,193,404,340⟩,⟨11,38,69,152,304,42,193,384,320⟩,[⟨1,1224302424922904910364673,⟨477,508,461,152,312,440,461,384,324⟩⟩]⟩
theorem node424 : UpperPrefix a [3,5,6,7,8,1,0] 30 :=
  Boolean.leaf_sound a [3,5,6,7,8,1,0] 30 cert424 (by decide +kernel)

def cert425 : Leaf := ⟨⟨0,153,154,259,139,0,27,27,155⟩,[(0,5),(5,0)],[(8,4,3)],⟨11,38,69,152,304,42,196,401,337⟩,⟨11,38,69,152,304,42,196,384,320⟩,[⟨5,1285813434182022167004193,⟨79,7,69,476,477,79,196,384,320⟩⟩,⟨2,1229199945506122476028963,⟨187,443,505,152,441,187,472,384,328⟩⟩,⟨6,1212615181017743063289189,⟨43,39,47,152,441,43,191,441,443⟩⟩]⟩
theorem node425 : UpperPrefix a [3,5,6,7,8,1,2] 30 :=
  Boolean.leaf_sound a [3,5,6,7,8,1,2] 30 cert425 (by decide +kernel)

def cert426 : Local := ⟨⟨0,217,186,0,207,0,0,127,191⟩,[(0,5),(3,6),(5,0),(6,3)],[(8,4,3),(8,4,6)]⟩
theorem node426 : UpperPrefix a [3,5,6,7,8,1,4] 30 :=
  local_sound a [3,5,6,7,8,1,4] 30 cert426 (by decide +kernel)

theorem node427 : UpperPrefix a [3,5,6,7,8,1] 30 :=
  branch_upper a [3,5,6,7,8,1] 30 (by decide) (fin9_cases _
  node424
  (invalid_upper a [3,5,6,7,8,1,1] 30 (by decide +kernel))
  node425
  (invalid_upper a [3,5,6,7,8,1,3] 30 (by decide +kernel))
  node426
  (invalid_upper a [3,5,6,7,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,7,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,7,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,7,8,1,8] 30 (by decide +kernel)))

def cert428 : Local := ⟨⟨240,0,0,354,202,210,58,122,186⟩,[(1,5),(2,6)],[(8,4,3),(2,5,1),(0,6,2)]⟩
theorem node428 : UpperPrefix a [3,5,6,7,8,2,0] 30 :=
  local_sound a [3,5,6,7,8,2,0] 30 cert428 (by decide +kernel)

def cert429 : Leaf := ⟨⟨160,0,170,289,201,193,41,57,185⟩,[(1,5)],[(8,4,3),(2,5,1),(1,6,2)],⟨11,38,69,152,304,44,194,401,337⟩,⟨11,38,69,152,304,44,194,384,320⟩,[⟨4,1210107709714599609925161,⟨111,39,103,239,295,111,194,384,320⟩⟩,⟨6,1210253986314938903184433,⟨11,39,5,153,443,47,130,384,256⟩⟩]⟩
theorem node429 : UpperPrefix a [3,5,6,7,8,2,1] 30 :=
  Boolean.leaf_sound a [3,5,6,7,8,2,1] 30 cert429 (by decide +kernel)

def cert430 : Leaf := ⟨⟨240,0,178,0,203,211,0,115,179⟩,[(1,5),(3,6),(6,3)],[(8,4,3),(8,4,6),(2,5,1)],⟨11,38,69,152,304,44,208,387,323⟩,⟨11,38,69,152,304,44,208,384,320⟩,[⟨3,1214839299253945188500481,⟨455,38,453,208,306,102,208,384,320⟩⟩]⟩
theorem node430 : UpperPrefix a [3,5,6,7,8,2,4] 30 :=
  Boolean.leaf_sound a [3,5,6,7,8,2,4] 30 cert430 (by decide +kernel)

theorem node431 : UpperPrefix a [3,5,6,7,8,2] 30 :=
  branch_upper a [3,5,6,7,8,2] 30 (by decide) (fin9_cases _
  node428
  node429
  (invalid_upper a [3,5,6,7,8,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,7,8,2,3] 30 (by decide +kernel))
  node430
  (invalid_upper a [3,5,6,7,8,2,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,7,8,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,7,8,2,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,7,8,2,8] 30 (by decide +kernel)))

def cert432 : Leaf := ⟨⟨0,185,122,98,72,81,312,120,56⟩,[(0,1)],[(2,0,0),(7,2,1)],⟨7,70,133,25,304,42,248,440,376⟩,⟨7,70,133,25,304,42,192,384,320⟩,[⟨0,1361519017103811012461568,⟨6,70,132,24,496,506,192,384,320⟩⟩,⟨1,1361519017103811012460545,⟨5,68,133,25,496,504,192,384,320⟩⟩,⟨8,1181746232174662813123,⟨7,71,133,57,59,43,199,135,71⟩⟩]⟩
theorem node432 : UpperPrefix a [2,6,7,0,8,1] 30 :=
  Boolean.leaf_sound a [2,6,7,0,8,1] 30 cert432 (by decide +kernel)

theorem node433 : UpperPrefix a [3,5,6,7,8] 30 :=
  branch_upper a [3,5,6,7,8] 30 (by decide) (fin9_cases _
  node423
  node427
  node431
  (invalid_upper a [3,5,6,7,8,3] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut95 [3,5,6,7,8,4] [2,6,7,0,8,1] 30 (by decide +kernel) node432)
  (invalid_upper a [3,5,6,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,7,8,8] 30 (by decide +kernel)))

theorem node434 : UpperPrefix a [3,5,6,7] 30 :=
  branch_upper a [3,5,6,7] 30 (by decide) (fin9_cases _
  node406
  node412
  node419
  (invalid_upper a [3,5,6,7,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,7,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,7,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,7,7] 30 (by decide +kernel))
  node433)

def cert435 : Leaf := ⟨⟨500,0,424,0,457,321,297,105,169⟩,[(1,3),(3,1)],[(4,1,0),(2,3,0)],⟨11,22,69,28,50,168,481,417,353⟩,⟨11,22,69,28,50,168,192,384,320⟩,[⟨1,1233765605017405095149569,⟨493,508,485,508,56,168,192,384,320⟩⟩]⟩
theorem node435 : UpperPrefix a [3,4,6,2,1,7] 30 :=
  Boolean.leaf_sound a [3,4,6,2,1,7] 30 cert435 (by decide +kernel)

def cert436 : Leaf := ⟨⟨0,184,242,225,200,80,312,120,184⟩,[(0,1)],[(2,0,0),(1,3,2)],⟨7,70,13,26,49,168,496,432,368⟩,⟨7,70,13,26,49,168,192,384,320⟩,[⟨0,1323666154569384378502144,⟨38,102,494,506,496,488,192,384,320⟩⟩,⟨8,1181752457805405521355,⟨31,127,13,31,61,189,255,191,127⟩⟩]⟩
theorem node436 : UpperPrefix a [2,6,3,1,0,7] 30 :=
  Boolean.leaf_sound a [2,6,3,1,0,7] 30 cert436 (by decide +kernel)

def cert437 : Leaf := ⟨⟨176,145,146,129,136,273,21,85,149⟩,[],[(3,0,4),(8,3,5),(1,6,2)],⟨11,38,69,280,49,168,194,404,340⟩,⟨11,38,69,280,49,168,194,384,320⟩,[⟨5,1285886806827151278736385,⟨207,6,69,412,477,136,194,384,320⟩⟩,⟨6,1210106419140063170399297,⟨11,54,55,280,49,168,187,440,313⟩⟩,⟨2,1210107572061567776195649,⟨11,50,113,280,49,168,251,440,377⟩⟩]⟩
theorem node437 : UpperPrefix a [3,5,6,8,0,7,1] 30 :=
  Boolean.leaf_sound a [3,5,6,8,0,7,1] 30 cert437 (by decide +kernel)

def cert438 : Leaf := ⟨⟨160,129,162,163,138,259,35,33,179⟩,[],[(3,0,4),(8,3,5)],⟨11,38,69,280,49,168,196,386,336⟩,⟨11,38,69,280,49,168,196,386,320⟩,[⟨2,1531246939739948960449667,⟨187,443,377,280,49,185,505,443,376⟩⟩,⟨4,1210184397009054479449641,⟨239,103,103,495,103,239,198,454,320⟩⟩,⟨6,1212467611681785816059329,⟨59,54,55,441,49,185,191,443,443⟩⟩]⟩
theorem node438 : UpperPrefix a [3,5,6,8,0,7,2,1] 30 :=
  Boolean.leaf_sound a [3,5,6,8,0,7,2,1] 30 cert438 (by decide +kernel)

def cert439 : Local := ⟨⟨228,193,162,0,206,343,35,0,167⟩,[(3,7),(7,3)],[(3,0,4),(8,3,5),(4,7,5)]⟩
theorem node439 : UpperPrefix a [3,5,6,8,0,7,2,4] 30 :=
  local_sound a [3,5,6,8,0,7,2,4] 30 cert439 (by decide +kernel)

theorem node440 : UpperPrefix a [3,5,6,8,0,7,2] 30 :=
  branch_upper a [3,5,6,8,0,7,2] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,6,8,0,7,2,0] 30 (by decide +kernel))
  node438
  (invalid_upper a [3,5,6,8,0,7,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,8,0,7,2,3] 30 (by decide +kernel))
  node439
  (invalid_upper a [3,5,6,8,0,7,2,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,8,0,7,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,8,0,7,2,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,8,0,7,2,8] 30 (by decide +kernel)))

def cert441 : Leaf := ⟨⟨176,145,146,131,138,275,3,85,151⟩,[],[(3,0,4),(8,3,5)],⟨11,38,69,280,49,168,208,386,324⟩,⟨11,38,69,280,49,168,208,386,320⟩,[⟨2,1210110454358732223546497,⟨11,114,113,280,113,249,249,507,376⟩⟩,⟨5,1644593238928456596587521,⟨395,390,461,348,477,392,476,386,328⟩⟩,⟨6,1210106419133466100632705,⟨11,54,55,280,49,185,185,443,312⟩⟩]⟩
theorem node441 : UpperPrefix a [3,5,6,8,0,7,4,1] 30 :=
  Boolean.leaf_sound a [3,5,6,8,0,7,4,1] 30 cert441 (by decide +kernel)

def cert442 : Leaf := ⟨⟨180,144,176,164,140,276,37,112,182⟩,[],[(3,0,4),(6,2,7),(8,3,5)],⟨11,38,69,280,49,168,208,388,322⟩,⟨11,38,69,280,49,168,208,388,320⟩,[⟨1,1210183827305161894920193,⟨253,52,117,508,117,232,252,508,352⟩⟩,⟨0,1531283828778938953436160,⟨170,422,494,280,48,170,506,422,360⟩⟩]⟩
theorem node442 : UpperPrefix a [3,5,6,8,0,7,4,2] 30 :=
  Boolean.leaf_sound a [3,5,6,8,0,7,4,2] 30 cert442 (by decide +kernel)

theorem node443 : UpperPrefix a [3,5,6,8,0,7,4] 30 :=
  branch_upper a [3,5,6,8,0,7,4] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,6,8,0,7,4,0] 30 (by decide +kernel))
  node441
  node442
  (invalid_upper a [3,5,6,8,0,7,4,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,8,0,7,4,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,8,0,7,4,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,8,0,7,4,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,8,0,7,4,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,8,0,7,4,8] 30 (by decide +kernel)))

theorem node444 : UpperPrefix a [3,5,6,8,0,7] 30 :=
  branch_upper a [3,5,6,8,0,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,6,8,0,7,0] 30 (by decide +kernel))
  node437
  node440
  (invalid_upper a [3,5,6,8,0,7,3] 30 (by decide +kernel))
  node443
  (invalid_upper a [3,5,6,8,0,7,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,8,0,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,8,0,7,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,8,0,7,8] 30 (by decide +kernel)))

theorem node445 : UpperPrefix a [3,5,6,8,0] 30 :=
  branch_upper a [3,5,6,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,6,8,0,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut61 [3,5,6,8,0,1] [3,4,6,2,1,7] 30 (by decide +kernel) node435)
  (PrefixConjugacy.upper aut61 [3,5,6,8,0,2] [3,5,6,2,1,7] 30 (by decide +kernel) node374)
  (invalid_upper a [3,5,6,8,0,3] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut58 [3,5,6,8,0,4] [2,6,3,1,0,7] 30 (by decide +kernel) node436)
  (invalid_upper a [3,5,6,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,8,0,6] 30 (by decide +kernel))
  node444
  (invalid_upper a [3,5,6,8,0,8] 30 (by decide +kernel)))

def cert446 : Leaf := ⟨⟨0,440,0,482,328,464,312,120,184⟩,[(0,1),(2,3)],[(2,0,0),(0,3,2)],⟨7,70,13,25,176,42,496,432,368⟩,⟨7,70,13,25,176,42,192,384,320⟩,[⟨1,1437224743012691166101505,⟨5,68,13,477,496,508,192,384,320⟩⟩]⟩
theorem node446 : UpperPrefix a [2,6,3,0,7,1] 30 :=
  Boolean.leaf_sound a [2,6,3,0,7,1] 30 cert446 (by decide +kernel)

def cert447 : Leaf := ⟨⟨212,216,0,198,0,342,22,86,150⟩,[(2,6),(4,1)],[(5,1,4),(8,3,5),(0,6,2)],⟨11,38,69,280,50,168,193,404,340⟩,⟨11,38,69,280,50,168,193,384,320⟩,[⟨3,1224302424920700115747841,⟨471,502,453,272,434,160,453,384,324⟩⟩]⟩
theorem node447 : UpperPrefix a [3,5,6,8,1,7,0] 30 :=
  Boolean.leaf_sound a [3,5,6,8,1,7,0] 30 cert447 (by decide +kernel)

#print axioms node447
end Delivery.FiniteExclusion.Sharp3x3x3

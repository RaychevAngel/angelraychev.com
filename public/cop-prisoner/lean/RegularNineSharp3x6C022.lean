import RegularNineSharp3x6Base
import RegularNineSharp3x6C003
import RegularNineSharp3x6C009
import RegularNineSharp3x6C011
import RegularNineSharp3x6C019
import RegularNineSharp3x6C020
import RegularNineSharp3x6C021
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp3x6
open Bounds BoundTreeRows Extremal
theorem node1408 : UpperPrefix a [3,6,5,8,7,4] 30 :=
  branch_upper a [3,6,5,8,7,4] 30 (by decide) (fin9_cases _
  node1405
  node1406
  node1407
  (invalid_upper a [3,6,5,8,7,4,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,8,7,4,4] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,8,7,4,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,8,7,4,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,8,7,4,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,8,7,4,8] 30 (by decide +kernel)))

theorem node1409 : UpperPrefix a [3,6,5,8,7] 30 :=
  branch_upper a [3,6,5,8,7] 30 (by decide) (fin9_cases _
  node1394
  node1398
  node1402
  (invalid_upper a [3,6,5,8,7,3] 30 (by decide +kernel))
  node1408
  (invalid_upper a [3,6,5,8,7,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,8,7,8] 30 (by decide +kernel)))

theorem node1410 : UpperPrefix a [3,6,5,8] 30 :=
  branch_upper a [3,6,5,8] 30 (by decide) (fin9_cases _
  node1374
  node1385
  node1390
  (invalid_upper a [3,6,5,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,8,6] 30 (by decide +kernel))
  node1409
  (invalid_upper a [3,6,5,8,8] 30 (by decide +kernel)))

theorem node1411 : UpperPrefix a [3,6,5] 30 :=
  branch_upper a [3,6,5] 30 (by decide) (fin9_cases _
  node1269
  node1292
  node1319
  (invalid_upper a [3,6,5,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,4] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,6] 30 (by decide +kernel))
  node1369
  node1410)

theorem node1412 : UpperPrefix a [3,6] 30 :=
  branch_upper a [3,6] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,6,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut6 [3,6,1] [2,3,6] 30 (by decide +kernel) node231)
  (invalid_upper a [3,6,2] 30 (by decide +kernel))
  (invalid_upper a [3,6,3] 30 (by decide +kernel))
  node1230
  node1411
  (invalid_upper a [3,6,6] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut15 [3,6,7] [3,4,6] 30 (by decide +kernel) node606)
  (PrefixConjugacy.upper aut7 [3,6,8] [3,4,7] 30 (by decide +kernel) node738))

def cert1413 : Leaf := ⟨⟨208,120,216,194,204,152,280,88,208⟩,[],[(1,4,3),(2,5,4)],⟨11,134,37,25,50,100,464,464,344⟩,⟨11,134,37,25,50,100,192,384,264⟩,[⟨0,1252729001867124520537088,⟨506,246,502,472,50,246,192,384,456⟩⟩,⟨8,1181747927634993513587,⟨11,143,61,29,63,127,255,128,8⟩⟩,⟨5,1323666153021274154075153,⟨459,134,5,473,475,68,192,384,456⟩⟩]⟩
theorem node1413 : UpperPrefix a [3,7,5,0,1,2] 30 :=
  Boolean.leaf_sound a [3,7,5,0,1,2] 30 cert1413 (by decide +kernel)

def cert1414 : Leaf := ⟨⟨240,0,216,226,204,140,0,120,240⟩,[(1,6),(6,1)],[(1,4,3)],⟨11,134,37,25,50,112,196,448,328⟩,⟨11,134,37,25,50,112,196,384,264⟩,[⟨8,1184094980563793708275,⟨127,255,61,61,127,127,255,255,12⟩⟩,⟨0,1214876159781415139970048,⟨506,246,502,440,114,114,246,384,264⟩⟩,⟨2,1361518440640866127184913,⟨11,130,425,25,443,505,192,384,264⟩⟩]⟩
theorem node1414 : UpperPrefix a [3,7,5,0,1,4,2] 30 :=
  Boolean.leaf_sound a [3,7,5,0,1,4,2] 30 cert1414 (by decide +kernel)

def cert1415 : Leaf := ⟨⟨80,89,88,66,201,137,0,93,85⟩,[(6,7)],[(1,4,3),(8,6,6)],⟨11,134,37,25,50,112,448,452,332⟩,⟨11,134,37,25,50,112,448,384,264⟩,[⟨5,1229054784251058201824277,⟨203,455,463,25,219,89,448,448,264⟩⟩,⟨2,1210109871197443183346707,⟨59,251,57,25,59,121,448,448,264⟩⟩,⟨7,1360042701114969376687121,⟨11,6,301,29,319,381,320,256,264⟩⟩]⟩
theorem node1415 : UpperPrefix a [3,7,5,0,1,4,8] 30 :=
  Boolean.leaf_sound a [3,7,5,0,1,4,8] 30 cert1415 (by decide +kernel)

theorem node1416 : UpperPrefix a [3,7,5,0,1,4] 30 :=
  branch_upper a [3,7,5,0,1,4] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,7,5,0,1,4,0] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,0,1,4,1] 30 (by decide +kernel))
  node1414
  (invalid_upper a [3,7,5,0,1,4,3] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,0,1,4,4] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,0,1,4,5] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,0,1,4,6] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,0,1,4,7] 30 (by decide +kernel))
  node1415)

def cert1417 : Leaf := ⟨⟨404,0,408,390,396,156,0,92,212⟩,[(1,6),(6,1)],[(1,4,3)],⟨11,134,37,25,50,352,196,464,344⟩,⟨11,134,37,25,50,352,196,384,264⟩,[⟨0,1215171304801475981511680,⟨506,246,502,440,242,498,246,384,264⟩⟩,⟨5,1285813037865254945588241,⟨75,198,5,409,475,322,198,384,264⟩⟩,⟨6,1210106412364553094464627,⟨11,143,61,29,63,319,143,384,264⟩⟩]⟩
theorem node1417 : UpperPrefix a [3,7,5,0,1,8,2] 30 :=
  Boolean.leaf_sound a [3,7,5,0,1,8,2] 30 cert1417 (by decide +kernel)

def cert1418 : Leaf := ⟨⟨432,0,408,418,392,152,296,56,240⟩,[(1,7)],[(1,4,3),(2,7,1)],⟨11,134,37,25,50,352,208,388,328⟩,⟨11,134,37,25,50,352,208,388,264⟩,[⟨0,1214869243877465684773888,⟨378,246,502,312,114,368,242,502,264⟩⟩,⟨6,1210401560270033363528959,⟨11,159,191,31,191,447,159,415,265⟩⟩]⟩
theorem node1418 : UpperPrefix a [3,7,5,0,1,8,4,2] 30 :=
  Boolean.leaf_sound a [3,7,5,0,1,8,4,2] 30 cert1418 (by decide +kernel)

def cert1419 : Leaf := ⟨⟨308,313,280,294,269,0,301,0,53⟩,[(5,7),(7,5)],[(1,4,3)],⟨11,134,37,25,50,352,208,448,268⟩,⟨11,134,37,25,50,352,208,448,264⟩,[⟨6,1805124589206136981325043,⟨267,399,317,285,319,319,415,395,264⟩⟩,⟨7,2413130433550441845883923,⟨287,319,301,285,319,364,381,364,264⟩⟩]⟩
theorem node1419 : UpperPrefix a [3,7,5,0,1,8,4,6] 30 :=
  Boolean.leaf_sound a [3,7,5,0,1,8,4,6] 30 cert1419 (by decide +kernel)

theorem node1420 : UpperPrefix a [3,7,5,0,1,8,4] 30 :=
  branch_upper a [3,7,5,0,1,8,4] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,7,5,0,1,8,4,0] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,0,1,8,4,1] 30 (by decide +kernel))
  node1418
  (invalid_upper a [3,7,5,0,1,8,4,3] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,0,1,8,4,4] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,0,1,8,4,5] 30 (by decide +kernel))
  node1419
  (invalid_upper a [3,7,5,0,1,8,4,7] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,0,1,8,4,8] 30 (by decide +kernel)))

theorem node1421 : UpperPrefix a [3,7,5,0,1,8] 30 :=
  branch_upper a [3,7,5,0,1,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,7,5,0,1,8,0] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,0,1,8,1] 30 (by decide +kernel))
  node1417
  (invalid_upper a [3,7,5,0,1,8,3] 30 (by decide +kernel))
  node1420
  (invalid_upper a [3,7,5,0,1,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,0,1,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,0,1,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,0,1,8,8] 30 (by decide +kernel)))

theorem node1422 : UpperPrefix a [3,7,5,0,1] 30 :=
  branch_upper a [3,7,5,0,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,7,5,0,1,0] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,0,1,1] 30 (by decide +kernel))
  node1413
  (invalid_upper a [3,7,5,0,1,3] 30 (by decide +kernel))
  node1416
  (invalid_upper a [3,7,5,0,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,0,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,0,1,7] 30 (by decide +kernel))
  node1421)

def cert1423 : Leaf := ⟨⟨84,88,90,68,0,156,284,92,84⟩,[(4,2)],[(7,1,5),(5,2,4),(1,5,2)],⟨11,134,37,25,52,98,464,464,344⟩,⟨11,134,37,25,52,98,192,384,264⟩,[⟨0,1252729002744466080017408,⟨506,246,502,506,246,114,192,384,488⟩⟩,⟨8,1181747927910139855971,⟨11,159,61,29,61,127,255,128,8⟩⟩]⟩
theorem node1423 : UpperPrefix a [3,7,5,0,2,1] 30 :=
  Boolean.leaf_sound a [3,7,5,0,2,1] 30 cert1423 (by decide +kernel)

def cert1424 : Leaf := ⟨⟨196,72,218,198,0,142,270,78,198⟩,[(4,2)],[(5,2,4)],⟨11,134,37,25,52,112,450,450,330⟩,⟨11,134,37,25,52,112,192,384,264⟩,[⟨0,1252729002744466080017408,⟨506,246,502,506,246,114,192,384,488⟩⟩,⟨4,1252729001652238716775433,⟨459,198,487,459,230,98,192,384,457⟩⟩,⟨8,1181747927910139855971,⟨11,159,61,29,61,127,255,128,8⟩⟩]⟩
theorem node1424 : UpperPrefix a [3,7,5,0,2,4] 30 :=
  Boolean.leaf_sound a [3,7,5,0,2,4] 30 cert1424 (by decide +kernel)

def cert1425 : Leaf := ⟨⟨340,344,346,326,0,30,0,94,86⟩,[(4,2),(6,1)],[(7,1,6),(5,2,4)],⟨11,134,37,25,52,352,194,464,344⟩,⟨11,134,37,25,52,352,194,384,264⟩,[⟨0,1252729335377519807835136,⟨506,246,502,506,246,352,210,416,488⟩⟩]⟩
theorem node1425 : UpperPrefix a [3,7,5,0,2,8,1] 30 :=
  Boolean.leaf_sound a [3,7,5,0,2,8,1] 30 cert1425 (by decide +kernel)

def cert1426 : Leaf := ⟨⟨212,88,218,198,0,154,10,90,210⟩,[(4,2)],[(5,2,4)],⟨11,134,37,25,52,352,208,450,330⟩,⟨11,134,37,25,52,352,208,384,264⟩,[⟨0,1252729335377519807835136,⟨506,246,502,506,246,352,210,416,488⟩⟩,⟨8,1181781700509281846371,⟨75,223,61,29,61,127,223,128,8⟩⟩,⟨2,1214839308577804864455681,⟨491,130,417,505,48,352,208,416,360⟩⟩]⟩
theorem node1426 : UpperPrefix a [3,7,5,0,2,8,4] 30 :=
  Boolean.leaf_sound a [3,7,5,0,2,8,4] 30 cert1426 (by decide +kernel)

theorem node1427 : UpperPrefix a [3,7,5,0,2,8] 30 :=
  branch_upper a [3,7,5,0,2,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,7,5,0,2,8,0] 30 (by decide +kernel))
  node1425
  (invalid_upper a [3,7,5,0,2,8,2] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,0,2,8,3] 30 (by decide +kernel))
  node1426
  (invalid_upper a [3,7,5,0,2,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,0,2,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,0,2,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,0,2,8,8] 30 (by decide +kernel)))

theorem node1428 : UpperPrefix a [3,7,5,0,2] 30 :=
  branch_upper a [3,7,5,0,2] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,7,5,0,2,0] 30 (by decide +kernel))
  node1423
  (invalid_upper a [3,7,5,0,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,0,2,3] 30 (by decide +kernel))
  node1424
  (invalid_upper a [3,7,5,0,2,5] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,0,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,0,2,7] 30 (by decide +kernel))
  node1427)

def cert1429 : Leaf := ⟨⟨48,57,26,32,0,157,317,61,53⟩,[(4,5)],[(7,1,5),(6,4,4),(1,5,2)],⟨11,134,37,25,112,98,468,404,284⟩,⟨11,134,37,25,112,98,192,384,264⟩,[⟨8,1181748490584949032051,⟨15,143,61,61,127,127,255,128,12⟩⟩,⟨2,1210107565286057687647267,⟨11,139,57,25,121,123,192,384,264⟩⟩]⟩
theorem node1429 : UpperPrefix a [3,7,5,0,6,1] 30 :=
  Boolean.leaf_sound a [3,7,5,0,6,1] 30 cert1429 (by decide +kernel)

def cert1430 : Leaf := ⟨⟨48,56,154,32,0,154,318,62,182⟩,[(4,5)],[(6,4,4)],⟨11,134,37,25,112,100,466,402,282⟩,⟨11,134,37,25,112,100,192,384,264⟩,[⟨0,1214876138912684444765184,⟨506,246,502,472,114,246,192,384,264⟩⟩,⟨8,1181748490584949032051,⟨15,143,61,61,127,127,255,128,12⟩⟩,⟨2,1210107565286051245196291,⟨11,139,57,25,112,120,192,384,264⟩⟩,⟨7,1208926973665333834941443,⟨11,15,61,25,112,124,64,256,264⟩⟩,⟨1,1210107565286051246243841,⟨9,140,61,25,112,124,192,384,264⟩⟩]⟩
theorem node1430 : UpperPrefix a [3,7,5,0,6,2] 30 :=
  Boolean.leaf_sound a [3,7,5,0,6,2] 30 cert1430 (by decide +kernel)

def cert1431 : Leaf := ⟨⟨52,49,18,38,0,0,311,55,55⟩,[(4,5),(5,4)],[(6,4,4),(6,4,5)],⟨11,134,37,25,112,112,454,390,270⟩,⟨11,134,37,25,112,112,192,384,264⟩,[⟨3,1212473376569837862650881,⟨7,182,53,53,112,112,240,498,502⟩⟩,⟨7,1223094075933090586297347,⟨271,271,317,317,112,112,112,256,268⟩⟩,⟨8,1181748490584949032051,⟨15,143,61,61,127,127,255,128,12⟩⟩]⟩
theorem node1431 : UpperPrefix a [3,7,5,0,6,4] 30 :=
  Boolean.leaf_sound a [3,7,5,0,6,4] 30 cert1431 (by decide +kernel)

def cert1432 : Leaf := ⟨⟨308,313,282,292,0,31,0,61,53⟩,[(4,5),(6,1)],[(7,1,6),(6,4,4)],⟨11,134,37,25,112,352,194,404,284⟩,⟨11,134,37,25,112,352,194,384,264⟩,[⟨1,1229033924705677246201857,⟨9,396,445,25,112,368,192,384,264⟩⟩]⟩
theorem node1432 : UpperPrefix a [3,7,5,0,6,8,1] 30 :=
  Boolean.leaf_sound a [3,7,5,0,6,8,1] 30 cert1432 (by decide +kernel)

def cert1433 : Leaf := ⟨⟨404,0,410,390,0,159,0,31,151⟩,[(1,6),(4,5),(6,1)],[(6,4,4)],⟨11,134,37,25,112,352,196,402,282⟩,⟨11,134,37,25,112,352,196,384,264⟩,[⟨5,1285813037865254945588241,⟨75,198,5,409,475,322,198,384,264⟩⟩]⟩
theorem node1433 : UpperPrefix a [3,7,5,0,6,8,2] 30 :=
  Boolean.leaf_sound a [3,7,5,0,6,8,2] 30 cert1433 (by decide +kernel)

def cert1434 : Leaf := ⟨⟨48,57,154,32,0,153,297,63,55⟩,[(4,5)],[(6,4,4)],⟨11,134,37,25,112,352,208,390,270⟩,⟨11,134,37,25,112,352,208,384,264⟩,[⟨2,1210109911674789086364675,⟨91,251,57,25,112,368,240,496,264⟩⟩,⟨8,1181745671437116540019,⟨11,143,61,29,127,127,223,128,8⟩⟩,⟨1,1210109911674788818976769,⟨89,252,61,25,112,368,240,496,264⟩⟩,⟨7,1218371706631073125368835,⟨267,271,61,25,112,368,80,256,264⟩⟩]⟩
theorem node1434 : UpperPrefix a [3,7,5,0,6,8,4] 30 :=
  Boolean.leaf_sound a [3,7,5,0,6,8,4] 30 cert1434 (by decide +kernel)

theorem node1435 : UpperPrefix a [3,7,5,0,6,8] 30 :=
  branch_upper a [3,7,5,0,6,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,7,5,0,6,8,0] 30 (by decide +kernel))
  node1432
  node1433
  (invalid_upper a [3,7,5,0,6,8,3] 30 (by decide +kernel))
  node1434
  (invalid_upper a [3,7,5,0,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,0,6,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,0,6,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,0,6,8,8] 30 (by decide +kernel)))

theorem node1436 : UpperPrefix a [3,7,5,0,6] 30 :=
  branch_upper a [3,7,5,0,6] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,7,5,0,6,0] 30 (by decide +kernel))
  node1429
  node1430
  (invalid_upper a [3,7,5,0,6,3] 30 (by decide +kernel))
  node1431
  (invalid_upper a [3,7,5,0,6,5] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,0,6,6] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,0,6,7] 30 (by decide +kernel))
  node1435)

def cert1437 : Local := ⟨⟨368,0,346,352,73,413,0,121,113⟩,[(1,6),(6,1)],[(7,1,5),(1,5,2),(2,6,5)]⟩
theorem node1437 : UpperPrefix a [3,7,5,0,8,1,2] 30 :=
  local_sound a [3,7,5,0,8,1,2] 30 cert1437 (by decide +kernel)

def cert1438 : Local := ⟨⟨112,0,90,96,73,153,297,121,113⟩,[(1,7)],[(7,1,5),(8,4,6),(1,5,2),(2,7,1)]⟩
theorem node1438 : UpperPrefix a [3,7,5,0,8,1,4,2] 30 :=
  local_sound a [3,7,5,0,8,1,4,2] 30 cert1438 (by decide +kernel)

def cert1439 : Leaf := ⟨⟨52,49,18,36,5,149,293,53,53⟩,[],[(7,1,5),(8,4,6),(1,5,2)],⟨11,134,37,25,304,98,208,448,268⟩,⟨11,134,37,25,304,98,208,448,264⟩,[⟨3,1212623722868429209080833,⟨103,246,37,247,498,98,240,498,502⟩⟩,⟨6,1805124589206412127667427,⟨267,415,317,285,317,319,415,395,264⟩⟩]⟩
theorem node1439 : UpperPrefix a [3,7,5,0,8,1,4,6] 30 :=
  Boolean.leaf_sound a [3,7,5,0,8,1,4,6] 30 cert1439 (by decide +kernel)

theorem node1440 : UpperPrefix a [3,7,5,0,8,1,4] 30 :=
  branch_upper a [3,7,5,0,8,1,4] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,7,5,0,8,1,4,0] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,0,8,1,4,1] 30 (by decide +kernel))
  node1438
  (invalid_upper a [3,7,5,0,8,1,4,3] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,0,8,1,4,4] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,0,8,1,4,5] 30 (by decide +kernel))
  node1439
  (invalid_upper a [3,7,5,0,8,1,4,7] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,0,8,1,4,8] 30 (by decide +kernel)))

theorem node1441 : UpperPrefix a [3,7,5,0,8,1] 30 :=
  branch_upper a [3,7,5,0,8,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,7,5,0,8,1,0] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,0,8,1,1] 30 (by decide +kernel))
  node1437
  (invalid_upper a [3,7,5,0,8,1,3] 30 (by decide +kernel))
  node1440
  (invalid_upper a [3,7,5,0,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,0,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,0,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,0,8,1,8] 30 (by decide +kernel)))

def cert1442 : Leaf := ⟨⟨368,368,338,354,66,274,0,114,114⟩,[(6,1)],[(7,1,6)],⟨11,134,37,25,304,100,194,464,344⟩,⟨11,134,37,25,304,100,194,384,264⟩,[⟨0,1252877332422115132984320,⟨506,246,502,472,498,246,226,384,392⟩⟩,⟨2,1427760752655225214469187,⟨459,475,505,473,440,505,459,384,392⟩⟩,⟨3,1212623717801879628289025,⟨103,246,37,247,498,100,242,498,502⟩⟩]⟩
theorem node1442 : UpperPrefix a [3,7,5,0,8,2,1] 30 :=
  Boolean.leaf_sound a [3,7,5,0,8,2,1] 30 cert1442 (by decide +kernel)

def cert1443 : Leaf := ⟨⟨208,80,210,194,194,146,258,82,210⟩,[],[(8,4,6)],⟨11,134,37,25,304,100,208,450,330⟩,⟨11,134,37,25,304,100,208,384,264⟩,[⟨0,1215024757698051208924160,⟨506,246,502,472,498,246,208,384,328⟩⟩,⟨2,1224302587050426000999427,⟨459,475,505,473,304,120,208,384,328⟩⟩,⟨3,1212623717801879628289025,⟨103,246,37,247,498,100,208,498,502⟩⟩,⟨5,1441955899393945243765809,⟨459,134,391,473,475,463,473,384,328⟩⟩]⟩
theorem node1443 : UpperPrefix a [3,7,5,0,8,2,4] 30 :=
  Boolean.leaf_sound a [3,7,5,0,8,2,4] 30 cert1443 (by decide +kernel)

theorem node1444 : UpperPrefix a [3,7,5,0,8,2] 30 :=
  branch_upper a [3,7,5,0,8,2] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,7,5,0,8,2,0] 30 (by decide +kernel))
  node1442
  (invalid_upper a [3,7,5,0,8,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,0,8,2,3] 30 (by decide +kernel))
  node1443
  (invalid_upper a [3,7,5,0,8,2,5] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,0,8,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,0,8,2,7] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,0,8,2,8] 30 (by decide +kernel)))

def cert1445 : Leaf := ⟨⟨368,0,346,354,74,266,0,122,114⟩,[(1,7),(6,1)],[(7,1,6),(2,7,1),(2,7,6)],⟨11,134,37,25,304,112,194,388,328⟩,⟨11,134,37,25,304,112,194,388,264⟩,[⟨0,1214869246195648512986112,⟨378,246,502,312,304,112,242,502,280⟩⟩]⟩
theorem node1445 : UpperPrefix a [3,7,5,0,8,4,1,2] 30 :=
  Boolean.leaf_sound a [3,7,5,0,8,4,1,2] 30 cert1445 (by decide +kernel)

def cert1446 : Leaf := ⟨⟨356,353,322,356,69,261,0,37,101⟩,[(6,1)],[(7,1,6)],⟨11,134,37,25,304,112,194,448,268⟩,⟨11,134,37,25,304,112,194,448,264⟩,[⟨1,1239032066760434831589377,⟨281,444,317,25,304,240,496,496,264⟩⟩,⟨3,1212623725085044650677249,⟨103,246,37,247,498,240,242,498,502⟩⟩,⟨4,1250484011281190057180425,⟨459,198,231,463,487,230,194,449,459⟩⟩]⟩
theorem node1446 : UpperPrefix a [3,7,5,0,8,4,1,6] 30 :=
  Boolean.leaf_sound a [3,7,5,0,8,4,1,6] 30 cert1446 (by decide +kernel)

theorem node1447 : UpperPrefix a [3,7,5,0,8,4,1] 30 :=
  branch_upper a [3,7,5,0,8,4,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,7,5,0,8,4,1,0] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,0,8,4,1,1] 30 (by decide +kernel))
  node1445
  (invalid_upper a [3,7,5,0,8,4,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,0,8,4,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,0,8,4,1,5] 30 (by decide +kernel))
  node1446
  (invalid_upper a [3,7,5,0,8,4,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,0,8,4,1,8] 30 (by decide +kernel)))

def cert1448 : Leaf := ⟨⟨452,0,450,454,198,390,0,70,198⟩,[(1,6),(6,1)],[],⟨11,134,37,25,304,112,196,450,330⟩,⟨11,134,37,25,304,112,196,384,264⟩,[⟨0,1214876159212280433642496,⟨506,246,502,440,304,114,246,384,280⟩⟩,⟨3,1212621131011659285304321,⟨103,246,37,247,498,242,246,498,502⟩⟩,⟨4,1255238641551790184660233,⟨459,198,487,463,487,230,198,385,459⟩⟩,⟨5,1385785239430322193468453,⟨459,455,463,409,409,475,455,384,264⟩⟩]⟩
theorem node1448 : UpperPrefix a [3,7,5,0,8,4,2] 30 :=
  Boolean.leaf_sound a [3,7,5,0,8,4,2] 30 cert1448 (by decide +kernel)

theorem node1449 : UpperPrefix a [3,7,5,0,8,4] 30 :=
  branch_upper a [3,7,5,0,8,4] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,7,5,0,8,4,0] 30 (by decide +kernel))
  node1447
  node1448
  (invalid_upper a [3,7,5,0,8,4,3] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,0,8,4,4] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,0,8,4,5] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,0,8,4,6] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,0,8,4,7] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,0,8,4,8] 30 (by decide +kernel)))

theorem node1450 : UpperPrefix a [3,7,5,0,8] 30 :=
  branch_upper a [3,7,5,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,7,5,0,8,0] 30 (by decide +kernel))
  node1441
  node1444
  (invalid_upper a [3,7,5,0,8,3] 30 (by decide +kernel))
  node1449
  (invalid_upper a [3,7,5,0,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,0,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,0,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,0,8,8] 30 (by decide +kernel)))

theorem node1451 : UpperPrefix a [3,7,5,0] 30 :=
  branch_upper a [3,7,5,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,7,5,0,0] 30 (by decide +kernel))
  node1422
  node1428
  (invalid_upper a [3,7,5,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,0,4] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,0,5] 30 (by decide +kernel))
  node1436
  (invalid_upper a [3,7,5,0,7] 30 (by decide +kernel))
  node1450)

def cert1452 : Leaf := ⟨⟨0,377,0,481,0,409,312,120,240⟩,[(0,3),(2,4),(4,2)],[(1,3,0)],⟨11,134,37,26,49,100,464,464,344⟩,⟨11,134,37,26,49,100,192,384,264⟩,[⟨2,1257423643977176926127115,⟨459,475,49,475,49,112,192,384,457⟩⟩,⟨0,1247960428238291761890304,⟨458,134,36,474,48,100,192,384,456⟩⟩]⟩
theorem node1452 : UpperPrefix a [3,7,5,1,0,2] 30 :=
  Boolean.leaf_sound a [3,7,5,1,0,2] 30 cert1452 (by decide +kernel)

def cert1453 : Leaf := ⟨⟨0,105,0,229,0,141,301,109,229⟩,[(0,3),(2,4),(4,2)],[(1,3,0)],⟨11,134,37,26,49,112,452,452,332⟩,⟨11,134,37,26,49,112,192,384,264⟩,[⟨4,1247960428237192254461193,⟨459,134,37,463,37,100,192,385,459⟩⟩,⟨8,1181747927907455501419,⟨11,159,61,31,61,127,255,128,9⟩⟩]⟩
theorem node1453 : UpperPrefix a [3,7,5,1,0,4] 30 :=
  Boolean.leaf_sound a [3,7,5,1,0,4] 30 cert1453 (by decide +kernel)

def cert1454 : Leaf := ⟨⟨0,377,0,161,0,157,53,125,245⟩,[(0,3),(2,4),(4,2)],[(1,3,0)],⟨11,134,37,26,49,352,212,468,348⟩,⟨11,134,37,26,49,352,192,384,264⟩,[⟨8,1181781698294680912907,⟨75,223,53,95,53,96,192,128,9⟩⟩,⟨2,1210107565284126831412235,⟨11,155,49,27,49,352,192,384,265⟩⟩,⟨3,1210107601312922513441793,⟨67,214,53,86,53,352,192,384,256⟩⟩,⟨6,1210106412362622229808139,⟨11,159,53,31,53,288,128,384,265⟩⟩]⟩
theorem node1454 : UpperPrefix a [3,7,5,1,0,8] 30 :=
  Boolean.leaf_sound a [3,7,5,1,0,8] 30 cert1454 (by decide +kernel)

theorem node1455 : UpperPrefix a [3,7,5,1,0] 30 :=
  branch_upper a [3,7,5,1,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,7,5,1,0,0] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,1,0,1] 30 (by decide +kernel))
  node1452
  (invalid_upper a [3,7,5,1,0,3] 30 (by decide +kernel))
  node1453
  (invalid_upper a [3,7,5,1,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,1,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,1,0,7] 30 (by decide +kernel))
  node1454)

def cert1456 : Leaf := ⟨⟨0,345,472,388,0,409,281,89,209⟩,[(0,3),(4,2)],[(5,2,4),(1,3,0),(2,4,3)],⟨11,134,37,26,52,369,465,465,345⟩,⟨11,134,37,26,52,96,192,384,264⟩,[⟨0,1210107565284126832460800,⟨10,158,52,26,52,96,192,384,264⟩⟩,⟨6,1210106412362622225613835,⟨11,159,53,27,52,32,128,384,265⟩⟩]⟩
theorem node1456 : UpperPrefix a [3,7,5,1,2] 30 :=
  Boolean.leaf_sound a [3,7,5,1,2] 30 cert1456 (by decide +kernel)

def cert1457 : Local := ⟨⟨0,312,0,420,0,412,316,60,180⟩,[(0,3),(2,5),(4,5)],[(1,3,0),(6,4,4),(0,5,2)]⟩
theorem node1457 : UpperPrefix a [3,7,5,1,6,0] 30 :=
  local_sound a [3,7,5,1,6,0] 30 cert1457 (by decide +kernel)

def cert1458 : Leaf := ⟨⟨0,57,152,165,0,153,313,57,177⟩,[(0,3),(4,5)],[(1,3,0),(6,4,4)],⟨11,134,37,26,112,100,465,401,281⟩,⟨11,134,37,26,112,100,192,384,264⟩,[⟨8,1181748490584412161145,⟨15,134,61,63,127,127,255,128,13⟩⟩,⟨2,1247960428240490784097289,⟨459,130,49,475,112,112,192,384,457⟩⟩]⟩
theorem node1458 : UpperPrefix a [3,7,5,1,6,2] 30 :=
  Boolean.leaf_sound a [3,7,5,1,6,2] 30 cert1458 (by decide +kernel)

def cert1459 : Local := ⟨⟨0,313,408,421,0,0,317,61,181⟩,[(0,3),(4,5),(5,4)],[(1,3,0),(6,4,4),(6,4,5)]⟩
theorem node1459 : UpperPrefix a [3,7,5,1,6,4] 30 :=
  local_sound a [3,7,5,1,6,4] 30 cert1459 (by decide +kernel)

def cert1460 : Leaf := ⟨⟨0,312,408,420,0,157,316,60,180⟩,[(0,3),(4,5)],[(1,3,0),(6,4,4)],⟨11,134,37,26,112,352,193,404,284⟩,⟨11,134,37,26,112,352,193,384,264⟩,[⟨0,1229033924705677246204928,⟨10,398,446,26,112,368,192,384,264⟩⟩]⟩
theorem node1460 : UpperPrefix a [3,7,5,1,6,8,0] 30 :=
  Boolean.leaf_sound a [3,7,5,1,6,8,0] 30 cert1460 (by decide +kernel)

def cert1461 : Local := ⟨⟨0,0,408,421,0,157,0,61,181⟩,[(0,3),(1,6),(4,5),(6,1)],[(1,3,0),(6,4,4)]⟩
theorem node1461 : UpperPrefix a [3,7,5,1,6,8,2] 30 :=
  local_sound a [3,7,5,1,6,8,2] 30 cert1461 (by decide +kernel)

def cert1462 : Leaf := ⟨⟨0,313,408,416,0,152,296,61,181⟩,[(0,3),(4,5)],[(1,3,0),(6,4,4)],⟨11,134,37,26,112,352,208,389,269⟩,⟨11,134,37,26,112,352,208,384,264⟩,[⟨0,1210109911674788550542336,⟨90,254,60,90,112,368,240,496,264⟩⟩,⟨2,1210109911674788549493771,⟨91,251,57,91,112,368,240,496,265⟩⟩]⟩
theorem node1462 : UpperPrefix a [3,7,5,1,6,8,4] 30 :=
  Boolean.leaf_sound a [3,7,5,1,6,8,4] 30 cert1462 (by decide +kernel)

theorem node1463 : UpperPrefix a [3,7,5,1,6,8] 30 :=
  branch_upper a [3,7,5,1,6,8] 30 (by decide) (fin9_cases _
  node1460
  (invalid_upper a [3,7,5,1,6,8,1] 30 (by decide +kernel))
  node1461
  (invalid_upper a [3,7,5,1,6,8,3] 30 (by decide +kernel))
  node1462
  (invalid_upper a [3,7,5,1,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,1,6,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,1,6,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,1,6,8,8] 30 (by decide +kernel)))

theorem node1464 : UpperPrefix a [3,7,5,1,6] 30 :=
  branch_upper a [3,7,5,1,6] 30 (by decide) (fin9_cases _
  node1457
  (invalid_upper a [3,7,5,1,6,1] 30 (by decide +kernel))
  node1458
  (invalid_upper a [3,7,5,1,6,3] 30 (by decide +kernel))
  node1459
  (invalid_upper a [3,7,5,1,6,5] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,1,6,6] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,1,6,7] 30 (by decide +kernel))
  node1463)

def cert1465 : Local := ⟨⟨0,0,0,484,204,412,0,124,244⟩,[(0,3),(1,6),(2,5),(6,1)],[(1,3,0),(0,5,2)]⟩
theorem node1465 : UpperPrefix a [3,7,5,1,8,0,2] 30 :=
  local_sound a [3,7,5,1,8,0,2] 30 cert1465 (by decide +kernel)

def cert1466 : Local := ⟨⟨0,120,0,228,204,156,300,124,244⟩,[(0,3),(2,5)],[(1,3,0),(8,4,6),(0,5,2)]⟩
theorem node1466 : UpperPrefix a [3,7,5,1,8,0,4] 30 :=
  local_sound a [3,7,5,1,8,0,4] 30 cert1466 (by decide +kernel)

theorem node1467 : UpperPrefix a [3,7,5,1,8,0] 30 :=
  branch_upper a [3,7,5,1,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,7,5,1,8,0,0] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,1,8,0,1] 30 (by decide +kernel))
  node1465
  (invalid_upper a [3,7,5,1,8,0,3] 30 (by decide +kernel))
  node1466
  (invalid_upper a [3,7,5,1,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,1,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,1,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,1,8,0,8] 30 (by decide +kernel)))

def cert1468 : Leaf := ⟨⟨0,352,448,484,204,385,312,120,240⟩,[(0,3)],[(1,3,0),(0,6,5)],⟨11,134,37,26,304,100,193,464,344⟩,⟨11,134,37,26,304,100,193,384,264⟩,[⟨2,1248112631891298374124553,⟨459,130,97,475,496,96,193,448,457⟩⟩,⟨3,1210107567535650442871809,⟨3,134,37,18,304,102,231,384,256⟩⟩,⟨4,1210107567534552004985865,⟨11,134,37,11,288,102,231,384,265⟩⟩]⟩
theorem node1468 : UpperPrefix a [3,7,5,1,8,2,0] 30 :=
  Boolean.leaf_sound a [3,7,5,1,8,2,0] 30 cert1468 (by decide +kernel)

def cert1469 : Leaf := ⟨⟨0,89,216,193,201,153,265,89,209⟩,[(0,3)],[(1,3,0),(8,4,6)],⟨11,134,37,26,304,100,208,449,329⟩,⟨11,134,37,26,304,100,208,384,264⟩,[⟨2,1264554247310388160889867,⟨459,475,497,475,496,240,208,384,457⟩⟩,⟨5,1633580676831631476018201,⟨459,134,391,475,475,454,473,384,457⟩⟩]⟩
theorem node1469 : UpperPrefix a [3,7,5,1,8,2,4] 30 :=
  Boolean.leaf_sound a [3,7,5,1,8,2,4] 30 cert1469 (by decide +kernel)

theorem node1470 : UpperPrefix a [3,7,5,1,8,2] 30 :=
  branch_upper a [3,7,5,1,8,2] 30 (by decide) (fin9_cases _
  node1468
  (invalid_upper a [3,7,5,1,8,2,1] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,1,8,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,1,8,2,3] 30 (by decide +kernel))
  node1469
  (invalid_upper a [3,7,5,1,8,2,5] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,1,8,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,1,8,2,7] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,1,8,2,8] 30 (by decide +kernel)))

def cert1471 : Leaf := ⟨⟨0,0,472,480,200,392,312,120,240⟩,[(0,3),(1,7)],[(1,3,0),(2,7,1)],⟨11,134,37,26,304,112,193,388,328⟩,⟨11,134,37,26,304,112,193,388,264⟩,[⟨0,1663491643386183382273024,⟨10,158,446,26,304,376,506,414,264⟩⟩]⟩
theorem node1471 : UpperPrefix a [3,7,5,1,8,4,0,2] 30 :=
  Boolean.leaf_sound a [3,7,5,1,8,4,0,2] 30 cert1471 (by decide +kernel)

#print axioms node1471
end Delivery.FiniteExclusion.Sharp3x6

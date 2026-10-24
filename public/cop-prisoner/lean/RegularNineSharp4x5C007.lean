import RegularNineSharp4x5Base
import RegularNineSharp4x5C000
import RegularNineSharp4x5C001
import RegularNineSharp4x5C002
import RegularNineSharp4x5C004
import RegularNineSharp4x5C005
import RegularNineSharp4x5C006
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp4x5
open Bounds BoundTreeRows Extremal
def cert448 : Local := ⟨⟨0,425,179,0,0,409,0,59,171⟩,[(0,1),(3,6),(4,5),(6,3)],[(2,0,0),(6,4,4)]⟩
theorem node448 : UpperPrefix a [2,4,8,7,6,1,0] 30 :=
  local_sound a [2,4,8,7,6,1,0] 30 cert448 (by decide +kernel)

def cert449 : Local := ⟨⟨0,297,51,306,0,281,0,59,43⟩,[(0,1),(4,5),(6,3)],[(2,0,0),(7,3,6),(6,4,4)]⟩
theorem node449 : UpperPrefix a [2,4,8,7,6,1,3] 30 :=
  local_sound a [2,4,8,7,6,1,3] 30 cert449 (by decide +kernel)

def cert450 : Local := ⟨⟨0,393,147,274,0,409,283,27,139⟩,[(0,1),(4,5)],[(2,0,0),(6,4,4),(5,6,4)]⟩
theorem node450 : UpperPrefix a [2,4,8,7,6,1,5] 30 :=
  local_sound a [2,4,8,7,6,1,5] 30 cert450 (by decide +kernel)

theorem node451 : UpperPrefix a [2,4,8,7,6,1] 30 :=
  branch_upper a [2,4,8,7,6,1] 30 (by decide) (fin9_cases _
  node448
  (invalid_upper a [2,4,8,7,6,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,6,1,2] 30 (by decide +kernel))
  node449
  (invalid_upper a [2,4,8,7,6,1,4] 30 (by decide +kernel))
  node450
  (invalid_upper a [2,4,8,7,6,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,6,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,6,1,8] 30 (by decide +kernel)))

def cert452 : Leaf := ⟨⟨0,41,51,306,0,147,59,59,43⟩,[(0,1),(4,5)],[(2,0,0),(7,3,5),(6,4,4)],⟨7,22,268,137,112,104,227,419,307⟩,⟨7,22,268,137,112,104,192,384,272⟩,[⟨8,1181890209646709313031,⟨55,55,127,251,112,120,192,128,16⟩⟩]⟩
theorem node452 : UpperPrefix a [2,4,8,7,6,3] 30 :=
  Boolean.leaf_sound a [2,4,8,7,6,3] 30 cert452 (by decide +kernel)

theorem node453 : UpperPrefix a [2,4,8,7,6] 30 :=
  branch_upper a [2,4,8,7,6] 30 (by decide) (fin9_cases _
  node447
  node451
  (invalid_upper a [2,4,8,7,6,2] 30 (by decide +kernel))
  node452
  (invalid_upper a [2,4,8,7,6,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,6,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,6,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,6,8] 30 (by decide +kernel)))

theorem node454 : UpperPrefix a [2,4,8,7] 30 :=
  branch_upper a [2,4,8,7] 30 (by decide) (fin9_cases _
  node429
  node434
  (invalid_upper a [2,4,8,7,2] 30 (by decide +kernel))
  node443
  (invalid_upper a [2,4,8,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,5] 30 (by decide +kernel))
  node453
  (invalid_upper a [2,4,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,8] 30 (by decide +kernel)))

theorem node455 : UpperPrefix a [2,4,8] 30 :=
  branch_upper a [2,4,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,8,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut5 [2,4,8,1] [2,3,4,8] 30 (by decide +kernel) node81)
  (invalid_upper a [2,4,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,4] 30 (by decide +kernel))
  node391
  node420
  node454
  (invalid_upper a [2,4,8,8] 30 (by decide +kernel)))

theorem node456 : UpperPrefix a [2,4] 30 :=
  branch_upper a [2,4] 30 (by decide) (fin9_cases _
  node96
  node138
  (invalid_upper a [2,4,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,4] 30 (by decide +kernel))
  node186
  node271
  node371
  node455)

theorem node457 : UpperPrefix a [2] 30 :=
  branch_upper a [2] 30 (by decide) (fin9_cases _
  node46
  (invalid_upper a [2,1] 30 (by decide +kernel))
  (invalid_upper a [2,2] 30 (by decide +kernel))
  node83
  node456
  (PrefixConjugacy.upper aut4 [2,5] [2,4] 30 (by decide +kernel) node456)
  (PrefixConjugacy.upper aut3 [2,6] [2,4] 30 (by decide +kernel) node456)
  (PrefixConjugacy.upper aut2 [2,7] [2,4] 30 (by decide +kernel) node456)
  (PrefixConjugacy.upper aut1 [2,8] [2,4] 30 (by decide +kernel) node456))

def cert458 : Local := ⟨⟨0,0,0,0,448,400,304,112,224⟩,[(0,2),(1,3),(2,0),(3,1)],[(3,0,1),(3,0,3),(0,1,0),(0,1,2),(1,2,1),(1,2,3),(2,3,0),(2,3,2)]⟩
theorem node458 : UpperPrefix a [3,0,1,2] 30 :=
  local_sound a [3,0,1,2] 30 cert458 (by decide +kernel)

def cert459 : Leaf := ⟨⟨0,472,0,452,452,404,308,116,228⟩,[(0,2),(2,0)],[(3,0,1),(0,1,0),(0,1,2),(1,2,1)],⟨11,7,14,25,500,484,484,484,500⟩,⟨11,7,14,25,48,96,192,384,272⟩,[⟨5,1210107564157988393959325,⟨15,7,15,31,31,66,199,399,287⟩⟩]⟩
theorem node459 : UpperPrefix a [3,0,1,4] 30 :=
  Boolean.leaf_sound a [3,0,1,4] 30 cert459 (by decide +kernel)

theorem node460 : UpperPrefix a [3,0,1] 30 :=
  branch_upper a [3,0,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,0,1,0] 30 (by decide +kernel))
  (invalid_upper a [3,0,1,1] 30 (by decide +kernel))
  node458
  (invalid_upper a [3,0,1,3] 30 (by decide +kernel))
  node459
  (PrefixConjugacy.upper aut4 [3,0,1,5] [3,0,1,4] 30 (by decide +kernel) node459)
  (PrefixConjugacy.upper aut3 [3,0,1,6] [3,0,1,4] 30 (by decide +kernel) node459)
  (PrefixConjugacy.upper aut2 [3,0,1,7] [3,0,1,4] 30 (by decide +kernel) node459)
  (PrefixConjugacy.upper aut1 [3,0,1,8] [3,0,1,4] 30 (by decide +kernel) node459))

def cert461 : Leaf := ⟨⟨4,8,34,22,454,406,278,86,198⟩,[],[(3,0,1),(0,1,0),(5,3,2)],⟨11,7,28,41,502,486,454,454,470⟩,⟨11,7,28,41,48,96,192,384,272⟩,[⟨6,1210106412362349298265365,⟨11,7,31,41,63,32,130,391,287⟩⟩,⟨7,1208926973663136493808917,⟨11,7,31,41,63,96,66,263,287⟩⟩,⟨8,1181745669224730406165,⟨11,7,31,41,63,96,194,135,31⟩⟩,⟨4,1210107565282752174492677,⟨11,7,15,41,32,96,192,384,256⟩⟩]⟩
theorem node461 : UpperPrefix a [3,0,4,5] 30 :=
  Boolean.leaf_sound a [3,0,4,5] 30 cert461 (by decide +kernel)

def cert462 : Leaf := ⟨⟨100,104,96,52,68,404,308,116,228⟩,[],[(3,0,1),(0,1,0)],⟨11,7,28,73,50,484,484,420,436⟩,⟨11,7,28,73,50,96,192,384,272⟩,[⟨1,1307124010151531701600257,⟨233,493,508,73,508,96,192,480,500⟩⟩,⟨7,1208926973665337605778485,⟨11,7,31,73,63,127,64,258,279⟩⟩,⟨8,1181745671425842375733,⟨11,7,31,73,63,127,192,130,23⟩⟩,⟨4,1210107565282752174492677,⟨11,7,15,73,34,96,192,384,256⟩⟩]⟩
theorem node462 : UpperPrefix a [3,0,4,6,1] 30 :=
  Boolean.leaf_sound a [3,0,4,6,1] 30 cert462 (by decide +kernel)

def cert463 : Leaf := ⟨⟨36,40,98,38,66,390,294,38,166⟩,[],[(3,0,1),(0,1,0)],⟨11,7,28,73,52,482,482,418,434⟩,⟨11,7,28,73,52,96,192,384,272⟩,[⟨4,1212473369217456218844421,⟨11,7,15,73,39,96,200,489,491⟩⟩,⟨7,1208926973665337605778485,⟨11,7,31,73,63,127,64,258,279⟩⟩,⟨8,1181745671425842375733,⟨11,7,31,73,63,127,192,130,23⟩⟩,⟨6,1285811850040851079113733,⟨11,7,415,9,439,32,128,384,402⟩⟩]⟩
theorem node463 : UpperPrefix a [3,0,4,6,2] 30 :=
  Boolean.leaf_sound a [3,0,4,6,2] 30 cert463 (by decide +kernel)

def cert464 : Leaf := ⟨⟨68,72,66,6,70,148,310,118,102⟩,[],[(3,0,1),(0,1,0)],⟨11,7,28,73,176,98,484,420,308⟩,⟨11,7,28,73,176,98,192,384,272⟩,[⟨8,1181748206908264873597,⟨47,7,63,127,191,127,255,130,23⟩⟩,⟨7,1284484837389052897537077,⟨11,7,287,73,319,107,64,258,279⟩⟩,⟨5,1210107564157956078578741,⟨11,7,31,73,159,75,192,386,279⟩⟩,⟨4,1210107565282756469460005,⟨11,7,15,73,169,107,192,384,256⟩⟩]⟩
theorem node464 : UpperPrefix a [3,0,4,6,7,1] 30 :=
  Boolean.leaf_sound a [3,0,4,6,7,1] 30 cert464 (by decide +kernel)

def cert465 : Leaf := ⟨⟨52,56,98,54,6,146,310,54,38⟩,[],[(3,0,1),(0,1,0)],⟨11,7,28,73,176,100,482,418,306⟩,⟨11,7,28,73,176,100,192,384,272⟩,[⟨8,1181748206908264873597,⟨47,7,63,127,191,127,255,130,23⟩⟩,⟨6,1437222725400058102041605,⟨11,7,415,9,434,439,128,384,400⟩⟩,⟨7,1284484837389052897553461,⟨11,7,287,73,319,111,64,258,279⟩⟩]⟩
theorem node465 : UpperPrefix a [3,0,4,6,7,2] 30 :=
  Boolean.leaf_sound a [3,0,4,6,7,2] 30 cert465 (by decide +kernel)

def cert466 : Leaf := ⟨⟨68,72,66,22,326,150,54,118,102⟩,[],[(3,0,1),(0,1,0),(8,5,4)],⟨11,7,28,73,176,352,230,422,310⟩,⟨11,7,28,73,176,352,192,384,272⟩,[⟨7,1284484837389052897537077,⟨11,7,287,73,319,363,64,258,279⟩⟩,⟨5,1210107564157956078578741,⟨11,7,31,73,159,331,192,386,279⟩⟩,⟨4,1210107565282752174492677,⟨11,7,15,73,160,352,192,384,256⟩⟩]⟩
theorem node466 : UpperPrefix a [3,0,4,6,7,8] 30 :=
  Boolean.leaf_sound a [3,0,4,6,7,8] 30 cert466 (by decide +kernel)

theorem node467 : UpperPrefix a [3,0,4,6,7] 30 :=
  branch_upper a [3,0,4,6,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,0,4,6,7,0] 30 (by decide +kernel))
  node464
  node465
  (invalid_upper a [3,0,4,6,7,3] 30 (by decide +kernel))
  (invalid_upper a [3,0,4,6,7,4] 30 (by decide +kernel))
  (invalid_upper a [3,0,4,6,7,5] 30 (by decide +kernel))
  (invalid_upper a [3,0,4,6,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,0,4,6,7,7] 30 (by decide +kernel))
  node466)

def cert468 : Leaf := ⟨⟨64,72,66,2,198,404,310,118,230⟩,[],[(3,0,1),(0,1,0)],⟨11,7,28,73,304,98,228,420,436⟩,⟨11,7,28,73,304,98,192,384,272⟩,[⟨5,1210107564157956078578741,⟨11,7,31,73,287,75,192,386,279⟩⟩,⟨7,1208926973663138574117941,⟨11,7,31,73,319,107,64,258,279⟩⟩,⟨8,1181745669226810715189,⟨11,7,31,73,63,107,192,130,23⟩⟩,⟨4,1210107565282756469460005,⟨11,7,15,73,297,107,192,384,256⟩⟩,⟨2,1210107565283855980037153,⟨11,3,24,73,313,107,192,384,272⟩⟩]⟩
theorem node468 : UpperPrefix a [3,0,4,6,8,1] 30 :=
  Boolean.leaf_sound a [3,0,4,6,8,1] 30 cert468 (by decide +kernel)

def cert469 : Leaf := ⟨⟨260,264,322,262,134,386,294,38,166⟩,[],[(3,0,1),(0,1,0)],⟨11,7,28,73,304,100,226,418,434⟩,⟨11,7,28,73,304,100,192,384,272⟩,[⟨4,1210255499734459880590391,⟨43,111,239,73,491,111,192,392,457⟩⟩,⟨6,1437222725400058102041605,⟨11,7,415,9,434,439,128,384,400⟩⟩,⟨5,1210107564157956078595125,⟨11,7,31,73,287,79,192,386,279⟩⟩,⟨7,1208926973663138574134325,⟨11,7,31,73,319,111,64,258,279⟩⟩]⟩
theorem node469 : UpperPrefix a [3,0,4,6,8,2] 30 :=
  Boolean.leaf_sound a [3,0,4,6,8,2] 30 cert469 (by decide +kernel)

def cert470 : Leaf := ⟨⟨260,264,354,310,70,0,310,118,102⟩,[(5,6)],[(3,0,1),(0,1,0),(7,5,5)],⟨11,7,28,73,304,224,230,422,310⟩,⟨11,7,28,73,304,224,192,384,272⟩,[⟨4,1210107567534551988177925,⟨11,7,15,105,288,224,224,384,256⟩⟩,⟨5,1210107564157951779277829,⟨11,7,31,73,272,192,192,384,272⟩⟩,⟨6,1210106412362347079273477,⟨11,7,31,9,304,160,128,384,272⟩⟩]⟩
theorem node470 : UpperPrefix a [3,0,4,6,8,7] 30 :=
  Boolean.leaf_sound a [3,0,4,6,8,7] 30 cert470 (by decide +kernel)

theorem node471 : UpperPrefix a [3,0,4,6,8] 30 :=
  branch_upper a [3,0,4,6,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,0,4,6,8,0] 30 (by decide +kernel))
  node468
  node469
  (invalid_upper a [3,0,4,6,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,0,4,6,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,0,4,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,0,4,6,8,6] 30 (by decide +kernel))
  node470
  (invalid_upper a [3,0,4,6,8,8] 30 (by decide +kernel)))

theorem node472 : UpperPrefix a [3,0,4,6] 30 :=
  branch_upper a [3,0,4,6] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,0,4,6,0] 30 (by decide +kernel))
  node462
  node463
  (invalid_upper a [3,0,4,6,3] 30 (by decide +kernel))
  (invalid_upper a [3,0,4,6,4] 30 (by decide +kernel))
  (invalid_upper a [3,0,4,6,5] 30 (by decide +kernel))
  (invalid_upper a [3,0,4,6,6] 30 (by decide +kernel))
  node467
  node471)

def cert473 : Leaf := ⟨⟨240,248,224,112,196,144,304,112,224⟩,[],[(3,0,1),(0,1,0),(2,5,4)],⟨11,7,28,137,50,100,480,480,368⟩,⟨11,7,28,137,50,100,192,384,272⟩,[⟨1,1307422040360472571543553,⟨233,493,508,201,508,484,192,480,500⟩⟩,⟨8,1181747927628010024037,⟨11,7,31,137,55,127,255,128,18⟩⟩]⟩
theorem node473 : UpperPrefix a [3,0,4,7,1,2] 30 :=
  Boolean.leaf_sound a [3,0,4,7,1,2] 30 cert473 (by decide +kernel)

def cert474 : Leaf := ⟨⟨4,8,480,372,452,148,308,116,228⟩,[],[(3,0,1),(0,1,0)],⟨11,7,28,137,50,352,228,484,372⟩,⟨11,7,28,137,50,352,192,384,272⟩,[⟨1,1307124014655131328970753,⟨233,493,508,169,508,480,224,480,500⟩⟩,⟨4,1210107565282752174492677,⟨11,7,15,137,34,352,192,384,256⟩⟩,⟨5,1210107564157951779277829,⟨11,7,31,137,18,320,192,384,272⟩⟩,⟨6,1210106412362347079273477,⟨11,7,31,137,50,288,128,384,272⟩⟩,⟨7,1208926973663134274817029,⟨11,7,31,9,50,352,64,256,272⟩⟩,⟨8,1181745669222511414277,⟨11,7,31,137,50,96,192,128,16⟩⟩]⟩
theorem node474 : UpperPrefix a [3,0,4,7,1,8] 30 :=
  Boolean.leaf_sound a [3,0,4,7,1,8] 30 cert474 (by decide +kernel)

theorem node475 : UpperPrefix a [3,0,4,7,1] 30 :=
  branch_upper a [3,0,4,7,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,0,4,7,1,0] 30 (by decide +kernel))
  (invalid_upper a [3,0,4,7,1,1] 30 (by decide +kernel))
  node473
  (invalid_upper a [3,0,4,7,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,0,4,7,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,0,4,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,0,4,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,0,4,7,1,7] 30 (by decide +kernel))
  node474)

def cert476 : Leaf := ⟨⟨228,232,226,102,194,132,288,96,224⟩,[],[(3,0,1),(0,1,0)],⟨11,7,28,137,52,98,480,480,368⟩,⟨11,7,28,137,52,98,192,384,272⟩,[⟨4,1212475675060465432538373,⟨11,7,15,201,39,98,200,489,491⟩⟩,⟨8,1181747927628010024037,⟨11,7,31,137,55,127,255,128,18⟩⟩,⟨1,1285813291192731837661185,⟨9,5,476,137,500,96,192,384,464⟩⟩,⟨2,1285813291192731836613633,⟨11,3,472,137,496,98,192,384,464⟩⟩]⟩
theorem node476 : UpperPrefix a [3,0,4,7,2,1] 30 :=
  Boolean.leaf_sound a [3,0,4,7,2,1] 30 cert476 (by decide +kernel)

def cert477 : Leaf := ⟨⟨164,168,162,38,130,134,292,102,230⟩,[],[(3,0,1),(0,1,0)],⟨11,7,28,137,52,352,194,480,368⟩,⟨11,7,28,137,52,352,194,384,272⟩,[⟨4,1212768809856626383138133,⟨11,7,79,169,239,489,235,489,491⟩⟩,⟨6,1210106412364554700876901,⟨11,7,31,137,55,319,139,384,274⟩⟩,⟨8,1181745671430133017701,⟨11,7,31,137,55,127,203,128,18⟩⟩]⟩
theorem node477 : UpperPrefix a [3,0,4,7,2,8,1] 30 :=
  Boolean.leaf_sound a [3,0,4,7,2,8,1] 30 cert477 (by decide +kernel)

def cert478 : Leaf := ⟨⟨196,200,194,70,194,134,262,70,230⟩,[],[(3,0,1),(0,1,0),(8,5,6)],⟨11,7,28,137,52,352,224,450,338⟩,⟨11,7,28,137,52,352,224,384,272⟩,[⟨4,1212476400140009734155541,⟨75,7,79,233,111,489,232,489,491⟩⟩,⟨5,1210402712063163415883261,⟨11,7,31,139,159,463,203,399,287⟩⟩]⟩
theorem node478 : UpperPrefix a [3,0,4,7,2,8,5] 30 :=
  Boolean.leaf_sound a [3,0,4,7,2,8,5] 30 cert478 (by decide +kernel)

theorem node479 : UpperPrefix a [3,0,4,7,2,8] 30 :=
  branch_upper a [3,0,4,7,2,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,0,4,7,2,8,0] 30 (by decide +kernel))
  node477
  (invalid_upper a [3,0,4,7,2,8,2] 30 (by decide +kernel))
  (invalid_upper a [3,0,4,7,2,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,0,4,7,2,8,4] 30 (by decide +kernel))
  node478
  (invalid_upper a [3,0,4,7,2,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,0,4,7,2,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,0,4,7,2,8,8] 30 (by decide +kernel)))

theorem node480 : UpperPrefix a [3,0,4,7,2] 30 :=
  branch_upper a [3,0,4,7,2] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,0,4,7,2,0] 30 (by decide +kernel))
  node476
  (invalid_upper a [3,0,4,7,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,0,4,7,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,0,4,7,2,4] 30 (by decide +kernel))
  (invalid_upper a [3,0,4,7,2,5] 30 (by decide +kernel))
  (invalid_upper a [3,0,4,7,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,0,4,7,2,7] 30 (by decide +kernel))
  node479)

def cert481 : Leaf := ⟨⟨148,152,130,22,0,406,310,54,166⟩,[(4,5)],[(3,0,1),(0,1,0),(6,4,4)],⟨11,7,28,137,112,358,486,422,310⟩,⟨11,7,28,137,112,96,192,384,272⟩,[⟨5,1210107564157977553415317,⟨11,7,31,137,95,72,201,395,279⟩⟩,⟨8,1181745671447317212341,⟨11,7,31,137,127,127,201,139,23⟩⟩]⟩
theorem node481 : UpperPrefix a [3,0,4,7,6] 30 :=
  Boolean.leaf_sound a [3,0,4,7,6] 30 cert481 (by decide +kernel)

def cert482 : Leaf := ⟨⟨96,104,482,98,66,4,306,114,98⟩,[],[(3,0,1),(0,1,0),(2,6,5)],⟨11,7,28,137,304,98,196,480,368⟩,⟨11,7,28,137,304,98,196,384,272⟩,[⟨7,1662274158277017098816517,⟨11,7,31,9,304,370,375,256,272⟩⟩,⟨4,1210107567534560578145381,⟨11,7,15,137,289,107,239,384,256⟩⟩,⟨8,1181747921030915066981,⟨11,7,31,137,49,107,239,128,16⟩⟩]⟩
theorem node482 : UpperPrefix a [3,0,4,7,8,1,2] 30 :=
  Boolean.leaf_sound a [3,0,4,7,8,1,2] 30 cert482 (by decide +kernel)

def cert483 : Leaf := ⟨⟨228,232,480,100,196,132,4,116,228⟩,[],[(3,0,1),(0,1,0)],⟨11,7,28,137,304,98,224,452,340⟩,⟨11,7,28,137,304,98,224,384,272⟩,[⟨1,1758972853150731486625793,⟨9,397,476,137,500,508,500,384,464⟩⟩,⟨4,1210107709573870700727333,⟨107,39,111,233,289,107,233,384,256⟩⟩,⟨8,1181889960341037648933,⟨107,39,127,233,49,107,233,128,16⟩⟩]⟩
theorem node483 : UpperPrefix a [3,0,4,7,8,1,5] 30 :=
  Boolean.leaf_sound a [3,0,4,7,8,1,5] 30 cert483 (by decide +kernel)

theorem node484 : UpperPrefix a [3,0,4,7,8,1] 30 :=
  branch_upper a [3,0,4,7,8,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,0,4,7,8,1,0] 30 (by decide +kernel))
  (invalid_upper a [3,0,4,7,8,1,1] 30 (by decide +kernel))
  node482
  (invalid_upper a [3,0,4,7,8,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,0,4,7,8,1,4] 30 (by decide +kernel))
  node483
  (invalid_upper a [3,0,4,7,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,0,4,7,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,0,4,7,8,1,8] 30 (by decide +kernel)))

def cert485 : Leaf := ⟨⟨4,8,482,358,70,386,294,102,102⟩,[],[(3,0,1),(0,1,0)],⟨11,7,28,137,304,100,226,482,370⟩,⟨11,7,28,137,304,100,192,384,272⟩,[⟨4,1210255499734455317187639,⟨43,111,239,137,491,111,192,392,457⟩⟩,⟨7,1360042701117161944927237,⟨11,7,31,9,306,375,64,256,272⟩⟩,⟨5,1210107564157951779294213,⟨11,7,31,137,274,71,192,384,272⟩⟩,⟨6,1210106412362347079289861,⟨11,7,31,137,306,39,128,384,272⟩⟩,⟨8,1181745669222511430661,⟨11,7,31,137,50,103,192,128,16⟩⟩]⟩
theorem node485 : UpperPrefix a [3,0,4,7,8,2] 30 :=
  Boolean.leaf_sound a [3,0,4,7,8,2] 30 cert485 (by decide +kernel)

theorem node486 : UpperPrefix a [3,0,4,7,8] 30 :=
  branch_upper a [3,0,4,7,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,0,4,7,8,0] 30 (by decide +kernel))
  node484
  node485
  (invalid_upper a [3,0,4,7,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,0,4,7,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,0,4,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,0,4,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,0,4,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,0,4,7,8,8] 30 (by decide +kernel)))

theorem node487 : UpperPrefix a [3,0,4,7] 30 :=
  branch_upper a [3,0,4,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,0,4,7,0] 30 (by decide +kernel))
  node475
  node480
  (invalid_upper a [3,0,4,7,3] 30 (by decide +kernel))
  (invalid_upper a [3,0,4,7,4] 30 (by decide +kernel))
  (invalid_upper a [3,0,4,7,5] 30 (by decide +kernel))
  node481
  (invalid_upper a [3,0,4,7,7] 30 (by decide +kernel))
  node486)

def cert488 : Leaf := ⟨⟨276,280,256,20,452,404,308,116,228⟩,[],[(3,0,1),(0,1,0)],⟨11,7,28,265,50,228,228,484,500⟩,⟨11,7,28,265,50,96,192,384,272⟩,[⟨1,1307124010151531567382529,⟨233,493,508,489,508,96,192,480,500⟩⟩,⟨5,1210107564158003386195405,⟨11,7,31,271,18,65,203,399,287⟩⟩,⟨6,1210106412362398686191053,⟨11,7,31,271,50,33,139,399,287⟩⟩,⟨7,1208926973663185881734605,⟨11,7,31,271,50,97,75,271,287⟩⟩]⟩
theorem node488 : UpperPrefix a [3,0,4,8,1] 30 :=
  Boolean.leaf_sound a [3,0,4,8,1] 30 cert488 (by decide +kernel)

def cert489 : Leaf := ⟨⟨260,264,258,6,450,390,294,102,230⟩,[],[(3,0,1),(0,1,0)],⟨11,7,28,265,52,226,226,482,498⟩,⟨11,7,28,265,52,96,192,384,272⟩,[⟨4,1212473369217456218844421,⟨11,7,15,489,39,96,200,489,491⟩⟩,⟨5,1210107564158003386203597,⟨11,7,31,271,23,65,203,399,287⟩⟩,⟨6,1210106412362398686199245,⟨11,7,31,271,55,33,139,399,287⟩⟩,⟨7,1208926973663185881742797,⟨11,7,31,271,55,97,75,271,287⟩⟩]⟩
theorem node489 : UpperPrefix a [3,0,4,8,2] 30 :=
  Boolean.leaf_sound a [3,0,4,8,2] 30 cert489 (by decide +kernel)

def cert490 : Leaf := ⟨⟨276,280,258,22,0,406,310,54,166⟩,[(4,5)],[(3,0,1),(0,1,0),(6,4,4)],⟨11,7,28,265,112,230,230,422,438⟩,⟨11,7,28,265,112,96,192,384,272⟩,[⟨5,1210107564158003386195405,⟨11,7,31,271,81,65,203,399,287⟩⟩,⟨7,1208926973665384904990157,⟨11,7,31,271,113,113,75,271,287⟩⟩]⟩
theorem node490 : UpperPrefix a [3,0,4,8,6] 30 :=
  Boolean.leaf_sound a [3,0,4,8,6] 30 cert490 (by decide +kernel)

def cert491 : Leaf := ⟨⟨4,8,258,22,326,276,310,118,230⟩,[],[(3,0,1),(0,1,0)],⟨11,7,28,265,176,98,228,484,372⟩,⟨11,7,28,265,176,98,192,384,272⟩,[⟨7,1208926975914985699622365,⟨11,7,31,271,63,99,107,271,287⟩⟩,⟨5,1210107564158003390397917,⟨11,7,31,271,159,67,203,399,287⟩⟩,⟨6,1210106412362398690393565,⟨11,7,31,271,191,35,139,399,287⟩⟩,⟨4,1210107565282752174492677,⟨11,7,15,265,160,98,192,384,256⟩⟩,⟨8,1181745669222511414277,⟨11,7,31,9,176,98,192,128,16⟩⟩]⟩
theorem node491 : UpperPrefix a [3,0,4,8,7,1] 30 :=
  Boolean.leaf_sound a [3,0,4,8,7,1] 30 cert491 (by decide +kernel)

def cert492 : Leaf := ⟨⟨260,264,258,22,326,386,294,118,230⟩,[],[(3,0,1),(0,1,0)],⟨11,7,28,265,176,100,226,482,370⟩,⟨11,7,28,265,176,100,192,384,272⟩,[⟨4,1210107853653865814576133,⟨11,39,111,265,226,103,192,384,320⟩⟩,⟨5,1210107564158003390414301,⟨11,7,31,271,159,71,203,399,287⟩⟩,⟨6,1210106412362398690409949,⟨11,7,31,271,191,39,139,399,287⟩⟩,⟨7,1208926973663185885953501,⟨11,7,31,271,63,103,75,271,287⟩⟩]⟩
theorem node492 : UpperPrefix a [3,0,4,8,7,2] 30 :=
  Boolean.leaf_sound a [3,0,4,8,7,2] 30 cert492 (by decide +kernel)

theorem node493 : UpperPrefix a [3,0,4,8,7] 30 :=
  branch_upper a [3,0,4,8,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,0,4,8,7,0] 30 (by decide +kernel))
  node491
  node492
  (invalid_upper a [3,0,4,8,7,3] 30 (by decide +kernel))
  (invalid_upper a [3,0,4,8,7,4] 30 (by decide +kernel))
  (invalid_upper a [3,0,4,8,7,5] 30 (by decide +kernel))
  (invalid_upper a [3,0,4,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,0,4,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [3,0,4,8,7,8] 30 (by decide +kernel)))

theorem node494 : UpperPrefix a [3,0,4,8] 30 :=
  branch_upper a [3,0,4,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,0,4,8,0] 30 (by decide +kernel))
  node488
  node489
  (invalid_upper a [3,0,4,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,0,4,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,0,4,8,5] 30 (by decide +kernel))
  node490
  node493
  (invalid_upper a [3,0,4,8,8] 30 (by decide +kernel)))

theorem node495 : UpperPrefix a [3,0,4] 30 :=
  branch_upper a [3,0,4] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,0,4,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut5 [3,0,4,1] [2,0,1,4] 30 (by decide +kernel) node0)
  (PrefixConjugacy.upper aut5 [3,0,4,2] [3,0,1,4] 30 (by decide +kernel) node459)
  (invalid_upper a [3,0,4,3] 30 (by decide +kernel))
  (invalid_upper a [3,0,4,4] 30 (by decide +kernel))
  node461
  node472
  node487
  node494)

theorem node496 : UpperPrefix a [3,0] 30 :=
  branch_upper a [3,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,0,0] 30 (by decide +kernel))
  node460
  (invalid_upper a [3,0,2] 30 (by decide +kernel))
  (invalid_upper a [3,0,3] 30 (by decide +kernel))
  node495
  (PrefixConjugacy.upper aut4 [3,0,5] [3,0,4] 30 (by decide +kernel) node495)
  (PrefixConjugacy.upper aut3 [3,0,6] [3,0,4] 30 (by decide +kernel) node495)
  (PrefixConjugacy.upper aut2 [3,0,7] [3,0,4] 30 (by decide +kernel) node495)
  (PrefixConjugacy.upper aut1 [3,0,8] [3,0,4] 30 (by decide +kernel) node495))

theorem node497 : UpperPrefix a [3,4,0] 30 :=
  branch_upper a [3,4,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,0,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut5 [3,4,0,1] [2,0,4,1] 30 (by decide +kernel) node2)
  (PrefixConjugacy.upper aut10 [3,4,0,2] [2,0,1,4] 30 (by decide +kernel) node0)
  (invalid_upper a [3,4,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,0,4] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut14 [3,4,0,5] [2,4,1,8] 30 (by decide +kernel) node137)
  (PrefixConjugacy.upper aut13 [3,4,0,6] [2,4,1,7] 30 (by decide +kernel) node136)
  (PrefixConjugacy.upper aut12 [3,4,0,7] [2,4,1,6] 30 (by decide +kernel) node119)
  (PrefixConjugacy.upper aut11 [3,4,0,8] [2,4,1,5] 30 (by decide +kernel) node105))

def cert498 : Leaf := ⟨⟨0,488,0,0,0,414,318,126,238⟩,[(0,2),(2,0),(3,4),(4,3)],[],⟨11,22,14,41,49,484,452,452,468⟩,⟨11,22,14,41,49,96,192,384,272⟩,[⟨0,1295322714672759236207616,⟨494,502,494,236,502,96,192,384,498⟩⟩]⟩
theorem node498 : UpperPrefix a [3,4,1,5,0] 30 :=
  Boolean.leaf_sound a [3,4,1,5,0] 30 cert498 (by decide +kernel)

def cert499 : Leaf := ⟨⟨0,0,0,402,395,411,283,91,203⟩,[(0,2),(1,4),(2,0)],[(2,4,1)],⟨11,22,14,41,52,481,449,449,465⟩,⟨11,22,14,41,52,96,192,384,272⟩,[⟨5,1295322712737618771321861,⟨463,471,463,205,471,64,192,384,466⟩⟩,⟨6,1210106412365102383529791,⟨31,31,31,63,63,63,128,391,287⟩⟩]⟩
theorem node499 : UpperPrefix a [3,4,1,5,2] 30 :=
  Boolean.leaf_sound a [3,4,1,5,2] 30 cert499 (by decide +kernel)

def cert500 : Leaf := ⟨⟨0,41,0,22,0,415,287,31,143⟩,[(0,2),(2,0),(4,5)],[(6,4,4)],⟨11,22,14,41,112,485,453,389,405⟩,⟨11,22,14,41,112,96,192,384,272⟩,[⟨5,1219616986828738619769861,⟨463,471,463,205,80,64,192,384,272⟩⟩,⟨7,1208926973665339823256895,⟨15,31,15,63,127,127,64,263,287⟩⟩,⟨8,1181745671428059854143,⟨15,31,15,63,127,127,192,135,31⟩⟩]⟩
theorem node500 : UpperPrefix a [3,4,1,5,6] 30 :=
  Boolean.leaf_sound a [3,4,1,5,6] 30 cert500 (by decide +kernel)

def cert501 : Leaf := ⟨⟨0,488,0,0,332,412,316,124,236⟩,[(0,2),(2,0),(3,5)],[(0,5,3)],⟨11,22,14,41,176,97,452,452,340⟩,⟨11,22,14,41,176,97,192,384,272⟩,[⟨1,1219607746603460682842113,⟨505,468,460,57,184,121,192,384,272⟩⟩]⟩
theorem node501 : UpperPrefix a [3,4,1,5,7,0] 30 :=
  Boolean.leaf_sound a [3,4,1,5,7,0] 30 cert501 (by decide +kernel)

def cert502 : Leaf := ⟨⟨0,481,0,466,321,401,305,113,225⟩,[(0,2),(2,0)],[],⟨11,22,14,41,176,100,449,449,337⟩,⟨11,22,14,41,176,100,192,384,272⟩,[⟨3,1252692036249157819714561,⟨467,54,502,499,178,118,192,384,272⟩⟩,⟨1,1252692036249158893436929,⟨473,52,508,505,176,116,192,384,272⟩⟩,⟨2,1432493135143940204266501,⟨475,467,475,505,504,505,192,384,272⟩⟩]⟩
theorem node502 : UpperPrefix a [3,4,1,5,7,2] 30 :=
  Boolean.leaf_sound a [3,4,1,5,7,2] 30 cert502 (by decide +kernel)

def cert503 : Leaf := ⟨⟨0,40,0,22,334,158,30,94,206⟩,[(0,2),(2,0)],[(8,5,4)],⟨11,22,14,41,176,352,193,452,340⟩,⟨11,22,14,41,176,352,193,384,272⟩,[⟨0,1512929318256264571294720,⟨14,22,14,62,176,498,502,384,272⟩⟩,⟨5,1219617130943926695625733,⟨463,471,463,205,144,320,197,384,272⟩⟩,⟨6,1210106412362353602340151,⟨15,31,15,45,191,303,133,391,287⟩⟩,⟨7,1208926973663140797883703,⟨15,31,15,45,63,367,69,263,287⟩⟩]⟩
theorem node503 : UpperPrefix a [3,4,1,5,7,8,0] 30 :=
  Boolean.leaf_sound a [3,4,1,5,7,8,0] 30 cert503 (by decide +kernel)

def cert504 : Leaf := ⟨⟨0,41,0,18,331,155,27,91,203⟩,[(0,2),(2,0)],[(8,5,4)],⟨11,22,14,41,176,352,196,449,337⟩,⟨11,22,14,41,176,352,196,384,272⟩,[⟨2,1512929318256273157784581,⟨11,19,11,57,176,504,505,384,272⟩⟩,⟨5,1219617130943926695625733,⟨463,471,463,205,144,320,197,384,272⟩⟩,⟨6,1210106412362353602340151,⟨15,31,15,45,191,303,133,391,287⟩⟩,⟨7,1208926973663140797883703,⟨15,31,15,45,63,367,69,263,287⟩⟩]⟩
theorem node504 : UpperPrefix a [3,4,1,5,7,8,2] 30 :=
  Boolean.leaf_sound a [3,4,1,5,7,8,2] 30 cert504 (by decide +kernel)

theorem node505 : UpperPrefix a [3,4,1,5,7,8] 30 :=
  branch_upper a [3,4,1,5,7,8] 30 (by decide) (fin9_cases _
  node503
  (invalid_upper a [3,4,1,5,7,8,1] 30 (by decide +kernel))
  node504
  (invalid_upper a [3,4,1,5,7,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,1,5,7,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,1,5,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,1,5,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,1,5,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,1,5,7,8,8] 30 (by decide +kernel)))

theorem node506 : UpperPrefix a [3,4,1,5,7] 30 :=
  branch_upper a [3,4,1,5,7] 30 (by decide) (fin9_cases _
  node501
  (invalid_upper a [3,4,1,5,7,1] 30 (by decide +kernel))
  node502
  (invalid_upper a [3,4,1,5,7,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,1,5,7,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,1,5,7,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,1,5,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,1,5,7,7] 30 (by decide +kernel))
  node505)

def cert507 : Leaf := ⟨⟨0,488,0,0,204,412,316,124,236⟩,[(0,2),(2,0),(3,5)],[(0,5,3)],⟨11,22,14,41,304,97,196,452,468⟩,⟨11,22,14,41,304,97,192,384,272⟩,[⟨1,1219607746603460682842113,⟨505,468,460,57,312,121,192,384,272⟩⟩]⟩
theorem node507 : UpperPrefix a [3,4,1,5,8,0] 30 :=
  Boolean.leaf_sound a [3,4,1,5,8,0] 30 cert507 (by decide +kernel)

def cert508 : Leaf := ⟨⟨0,481,0,466,193,401,305,113,225⟩,[(0,2),(2,0)],[],⟨11,22,14,41,304,100,193,449,465⟩,⟨11,22,14,41,304,100,192,384,272⟩,[⟨3,1252692036249157819714561,⟨467,54,502,499,306,118,192,384,272⟩⟩,⟨1,1252692036249158893436929,⟨473,52,508,505,304,116,192,384,272⟩⟩,⟨2,1432493135143940204266501,⟨475,467,475,505,504,505,192,384,272⟩⟩]⟩
theorem node508 : UpperPrefix a [3,4,1,5,8,2] 30 :=
  Boolean.leaf_sound a [3,4,1,5,8,2] 30 cert508 (by decide +kernel)

def cert509 : Leaf := ⟨⟨0,105,0,86,79,0,31,95,79⟩,[(0,2),(2,0),(5,6)],[(7,5,5)],⟨11,22,14,41,304,224,197,453,341⟩,⟨11,22,14,41,304,224,192,384,272⟩,[⟨5,1219617130943926695625733,⟨463,471,463,205,272,192,192,384,272⟩⟩,⟨8,1184634728415787623831,⟨15,31,15,109,127,237,237,239,31⟩⟩]⟩
theorem node509 : UpperPrefix a [3,4,1,5,8,7] 30 :=
  Boolean.leaf_sound a [3,4,1,5,8,7] 30 cert509 (by decide +kernel)

theorem node510 : UpperPrefix a [3,4,1,5,8] 30 :=
  branch_upper a [3,4,1,5,8] 30 (by decide) (fin9_cases _
  node507
  (invalid_upper a [3,4,1,5,8,1] 30 (by decide +kernel))
  node508
  (invalid_upper a [3,4,1,5,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,1,5,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,1,5,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,1,5,8,6] 30 (by decide +kernel))
  node509
  (invalid_upper a [3,4,1,5,8,8] 30 (by decide +kernel)))

theorem node511 : UpperPrefix a [3,4,1,5] 30 :=
  branch_upper a [3,4,1,5] 30 (by decide) (fin9_cases _
  node498
  (invalid_upper a [3,4,1,5,1] 30 (by decide +kernel))
  node499
  (invalid_upper a [3,4,1,5,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,1,5,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,1,5,5] 30 (by decide +kernel))
  node500
  node506
  node510)

#print axioms node511
end Delivery.FiniteExclusion.Sharp4x5

import RegularNineSharp3x3x3Base
import RegularNineSharp3x3x3C000
import RegularNineSharp3x3x3C002
import RegularNineSharp3x3x3C003
import RegularNineSharp3x3x3C004
import RegularNineSharp3x3x3C005
import RegularNineSharp3x3x3C006
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp3x3x3
open Bounds BoundTreeRows Extremal
def cert448 : Leaf := ⟨⟨144,153,154,131,0,275,27,27,155⟩,[(4,1)],[(5,1,4),(8,3,5)],⟨11,38,69,280,50,168,196,401,337⟩,⟨11,38,69,280,50,168,196,384,320⟩,[⟨2,1229126161766568544961555,⟨187,443,505,441,187,168,488,384,352⟩⟩,⟨6,1212541398681857593216321,⟨187,54,55,441,50,168,191,441,443⟩⟩]⟩
theorem node448 : UpperPrefix a [3,5,6,8,1,7,2] 30 :=
  Boolean.leaf_sound a [3,5,6,8,1,7,2] 30 cert448 (by decide +kernel)

def cert449 : Leaf := ⟨⟨84,217,18,71,0,343,7,85,21⟩,[(4,1)],[(5,1,4),(8,3,5)],⟨11,38,69,280,50,168,208,389,325⟩,⟨11,38,69,280,50,168,208,384,320⟩,[⟨3,1233765568601716079985665,⟨471,502,453,272,114,160,208,384,320⟩⟩,⟨7,1530047894498416463447059,⟨27,319,333,281,59,40,349,256,332⟩⟩,⟨1,1229033924703477686075393,⟨9,420,453,280,48,168,208,384,320⟩⟩]⟩
theorem node449 : UpperPrefix a [3,5,6,8,1,7,4] 30 :=
  Boolean.leaf_sound a [3,5,6,8,1,7,4] 30 cert449 (by decide +kernel)

theorem node450 : UpperPrefix a [3,5,6,8,1,7] 30 :=
  branch_upper a [3,5,6,8,1,7] 30 (by decide) (fin9_cases _
  node447
  (invalid_upper a [3,5,6,8,1,7,1] 30 (by decide +kernel))
  node448
  (invalid_upper a [3,5,6,8,1,7,3] 30 (by decide +kernel))
  node449
  (invalid_upper a [3,5,6,8,1,7,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,8,1,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,8,1,7,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,8,1,7,8] 30 (by decide +kernel)))

theorem node451 : UpperPrefix a [3,5,6,8,1] 30 :=
  branch_upper a [3,5,6,8,1] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut97 [3,5,6,8,1,0] [3,5,6,1,7,2] 30 (by decide +kernel) node355)
  (invalid_upper a [3,5,6,8,1,1] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut97 [3,5,6,8,1,2] [3,4,6,1,7,2] 30 (by decide +kernel) node200)
  (invalid_upper a [3,5,6,8,1,3] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut94 [3,5,6,8,1,4] [2,6,3,0,7,1] 30 (by decide +kernel) node446)
  (invalid_upper a [3,5,6,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,8,1,6] 30 (by decide +kernel))
  node450
  (invalid_upper a [3,5,6,8,1,8] 30 (by decide +kernel)))

def cert452 : Leaf := ⟨⟨0,441,0,354,457,0,314,122,186⟩,[(0,1),(2,5),(5,2)],[(2,0,0)],⟨7,70,13,152,50,41,496,432,368⟩,⟨7,70,13,152,50,41,192,384,320⟩,[⟨0,1285813291192733985145856,⟨6,70,12,472,506,40,192,384,320⟩⟩]⟩
theorem node452 : UpperPrefix a [2,6,3,7,1,0] 30 :=
  Boolean.leaf_sound a [2,6,3,7,1,0] 30 cert452 (by decide +kernel)

def cert453 : Leaf := ⟨⟨244,0,0,230,0,342,54,118,182⟩,[(1,4),(2,6),(4,1)],[(8,3,5),(0,6,2)],⟨11,38,69,280,52,168,193,402,338⟩,⟨11,38,69,280,52,168,193,384,320⟩,[⟨3,1300081649575498953794561,⟨471,502,453,402,502,160,453,384,324⟩⟩]⟩
theorem node453 : UpperPrefix a [3,5,6,8,2,7,0] 30 :=
  Boolean.leaf_sound a [3,5,6,8,2,7,0] 30 cert453 (by decide +kernel)

def cert454 : Leaf := ⟨⟨116,0,50,101,0,341,53,117,53⟩,[(1,4),(4,1)],[(8,3,5),(1,6,2)],⟨11,38,69,280,52,168,194,401,337⟩,⟨11,38,69,280,52,168,194,384,320⟩,[⟨3,1214839173153293061071873,⟨471,54,453,274,54,160,210,384,320⟩⟩,⟨7,1511158428566937681273929,⟨27,54,333,287,54,41,351,260,333⟩⟩]⟩
theorem node454 : UpperPrefix a [3,5,6,8,2,7,1] 30 :=
  Boolean.leaf_sound a [3,5,6,8,2,7,1] 30 cert454 (by decide +kernel)

def cert455 : Leaf := ⟨⟨100,0,50,103,0,327,39,103,39⟩,[(1,4),(4,1)],[(8,3,5)],⟨11,38,69,280,52,168,208,387,323⟩,⟨11,38,69,280,52,168,208,384,320⟩,[⟨3,1214839173153293061071873,⟨471,54,453,274,54,160,210,384,320⟩⟩,⟨4,1229107711995332361464841,⟨171,422,487,427,422,169,194,384,320⟩⟩,⟨7,1511158428566937681273929,⟨27,54,333,287,54,41,351,260,333⟩⟩]⟩
theorem node455 : UpperPrefix a [3,5,6,8,2,7,4] 30 :=
  Boolean.leaf_sound a [3,5,6,8,2,7,4] 30 cert455 (by decide +kernel)

theorem node456 : UpperPrefix a [3,5,6,8,2,7] 30 :=
  branch_upper a [3,5,6,8,2,7] 30 (by decide) (fin9_cases _
  node453
  node454
  (invalid_upper a [3,5,6,8,2,7,2] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,8,2,7,3] 30 (by decide +kernel))
  node455
  (invalid_upper a [3,5,6,8,2,7,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,8,2,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,8,2,7,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,8,2,7,8] 30 (by decide +kernel)))

theorem node457 : UpperPrefix a [3,5,6,8,2] 30 :=
  branch_upper a [3,5,6,8,2] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut79 [3,5,6,8,2,0] [3,4,6,7,2,1] 30 (by decide +kernel) node254)
  (PrefixConjugacy.upper aut79 [3,5,6,8,2,1] [3,5,6,7,2,1] 30 (by decide +kernel) node413)
  (invalid_upper a [3,5,6,8,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,8,2,3] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut76 [3,5,6,8,2,4] [2,6,3,7,1,0] 30 (by decide +kernel) node452)
  (invalid_upper a [3,5,6,8,2,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,8,2,6] 30 (by decide +kernel))
  node456
  (invalid_upper a [3,5,6,8,2,8] 30 (by decide +kernel)))

def cert458 : Leaf := ⟨⟨420,385,418,164,260,0,292,116,180⟩,[(5,0)],[(3,0,5),(0,5,1),(1,6,2)],⟨11,38,69,280,176,41,194,404,340⟩,⟨11,38,69,280,176,41,194,384,320⟩,[⟨4,1210107853829787681324585,⟨47,39,103,367,231,47,194,384,320⟩⟩,⟨6,1210106423669776198929473,⟨43,38,55,312,184,41,187,440,313⟩⟩]⟩
theorem node458 : UpperPrefix a [3,5,6,8,7,0,1] 30 :=
  Boolean.leaf_sound a [3,5,6,8,7,0,1] 30 cert458 (by decide +kernel)

def cert459 : Leaf := ⟨⟨420,385,418,166,262,0,290,54,182⟩,[(5,0)],[(3,0,5),(0,5,1)],⟨11,38,69,280,176,41,196,402,338⟩,⟨11,38,69,280,176,41,196,384,320⟩,[⟨6,1212467611714427567508801,⟨59,38,55,441,184,57,191,441,443⟩⟩,⟨4,1210107853829787681324585,⟨47,39,103,367,231,47,198,384,320⟩⟩]⟩
theorem node459 : UpperPrefix a [3,5,6,8,7,0,2] 30 :=
  Boolean.leaf_sound a [3,5,6,8,7,0,2] 30 cert459 (by decide +kernel)

def cert460 : Local := ⟨⟨372,337,306,102,326,0,0,118,54⟩,[(5,0),(6,4)],[(3,0,5),(7,4,6),(0,5,1)]⟩
theorem node460 : UpperPrefix a [3,5,6,8,7,0,4] 30 :=
  local_sound a [3,5,6,8,7,0,4] 30 cert460 (by decide +kernel)

theorem node461 : UpperPrefix a [3,5,6,8,7,0] 30 :=
  branch_upper a [3,5,6,8,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,6,8,7,0,0] 30 (by decide +kernel))
  node458
  node459
  (invalid_upper a [3,5,6,8,7,0,3] 30 (by decide +kernel))
  node460
  (invalid_upper a [3,5,6,8,7,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,8,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,8,7,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,8,7,0,8] 30 (by decide +kernel)))

def cert462 : Leaf := ⟨⟨0,472,0,228,332,0,316,124,188⟩,[(0,5),(2,6),(5,0)],[(0,6,2)],⟨11,38,69,280,176,42,193,404,340⟩,⟨11,38,69,280,176,42,193,384,320⟩,[⟨1,1224302424922904910364673,⟨477,508,461,280,184,440,461,384,324⟩⟩]⟩
theorem node462 : UpperPrefix a [3,5,6,8,7,1,0] 30 :=
  Boolean.leaf_sound a [3,5,6,8,7,1,0] 30 cert462 (by decide +kernel)

def cert463 : Leaf := ⟨⟨0,408,410,130,266,0,283,27,155⟩,[(0,5),(5,0)],[],⟨11,38,69,280,176,42,196,401,337⟩,⟨11,38,69,280,176,42,196,384,320⟩,[⟨5,1285813434182022167004193,⟨79,7,69,476,477,79,196,384,320⟩⟩,⟨2,1229052371555793965679651,⟨187,443,505,280,177,187,472,384,328⟩⟩,⟨6,1212541393907915544366433,⟨187,55,55,441,185,187,191,441,443⟩⟩,⟨0,1210107576591280805809152,⟨42,38,118,312,184,42,254,440,378⟩⟩]⟩
theorem node463 : UpperPrefix a [3,5,6,8,7,1,2] 30 :=
  Boolean.leaf_sound a [3,5,6,8,7,1,2] 30 cert463 (by decide +kernel)

def cert464 : Leaf := ⟨⟨0,345,312,101,333,0,0,125,61⟩,[(0,5),(5,0),(6,4)],[(7,4,6)],⟨11,38,69,280,176,42,208,389,325⟩,⟨11,38,69,280,176,42,208,384,320⟩,[⟨1,1233765856832093708091393,⟨477,508,461,344,240,120,208,384,320⟩⟩]⟩
theorem node464 : UpperPrefix a [3,5,6,8,7,1,4] 30 :=
  Boolean.leaf_sound a [3,5,6,8,7,1,4] 30 cert464 (by decide +kernel)

theorem node465 : UpperPrefix a [3,5,6,8,7,1] 30 :=
  branch_upper a [3,5,6,8,7,1] 30 (by decide) (fin9_cases _
  node462
  (invalid_upper a [3,5,6,8,7,1,1] 30 (by decide +kernel))
  node463
  (invalid_upper a [3,5,6,8,7,1,3] 30 (by decide +kernel))
  node464
  (invalid_upper a [3,5,6,8,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,8,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,8,7,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,8,7,1,8] 30 (by decide +kernel)))

def cert466 : Leaf := ⟨⟨496,0,0,226,322,466,306,114,178⟩,[(1,5),(2,6)],[(2,5,1),(0,6,2)],⟨11,38,69,280,176,44,193,402,338⟩,⟨11,38,69,280,176,44,193,384,320⟩,[⟨3,1375860874232496815096833,⟨471,502,453,400,434,502,453,384,324⟩⟩]⟩
theorem node466 : UpperPrefix a [3,5,6,8,7,2,0] 30 :=
  Boolean.leaf_sound a [3,5,6,8,7,2,0] 30 cert466 (by decide +kernel)

def cert467 : Leaf := ⟨⟨224,0,170,225,329,193,40,121,185⟩,[(1,5)],[(2,5,1),(1,6,2)],⟨11,38,69,280,176,44,194,401,337⟩,⟨11,38,69,280,176,44,194,384,320⟩,[⟨4,1210107853829787681324585,⟨47,39,103,367,231,47,194,384,320⟩⟩,⟨8,1182034216258018246185,⟨47,39,103,127,247,47,194,128,64⟩⟩,⟨0,1210107853514227837846528,⟨10,38,68,344,242,46,194,384,320⟩⟩]⟩
theorem node467 : UpperPrefix a [3,5,6,8,7,2,1] 30 :=
  Boolean.leaf_sound a [3,5,6,8,7,2,1] 30 cert467 (by decide +kernel)

def cert468 : Leaf := ⟨⟨96,0,58,99,331,83,0,123,59⟩,[(1,5),(6,4)],[(7,4,6),(2,5,1)],⟨11,38,69,280,176,44,208,387,323⟩,⟨11,38,69,280,176,44,208,384,320⟩,[⟨8,1182034216258018246185,⟨47,39,103,127,247,47,214,128,64⟩⟩,⟨4,1210107565282752174507041,⟨11,39,69,264,163,47,192,384,320⟩⟩]⟩
theorem node468 : UpperPrefix a [3,5,6,8,7,2,4] 30 :=
  Boolean.leaf_sound a [3,5,6,8,7,2,4] 30 cert468 (by decide +kernel)

theorem node469 : UpperPrefix a [3,5,6,8,7,2] 30 :=
  branch_upper a [3,5,6,8,7,2] 30 (by decide) (fin9_cases _
  node466
  node467
  (invalid_upper a [3,5,6,8,7,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,8,7,2,3] 30 (by decide +kernel))
  node468
  (invalid_upper a [3,5,6,8,7,2,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,8,7,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,8,7,2,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,8,7,2,8] 30 (by decide +kernel)))

def cert470 : Leaf := ⟨⟨0,409,218,386,264,401,312,56,184⟩,[(0,1)],[(2,0,0)],⟨7,70,261,25,176,42,248,440,376⟩,⟨7,70,261,25,176,42,192,384,320⟩,[⟨0,1361519017103811012461568,⟨6,70,260,24,496,506,192,384,320⟩⟩,⟨1,1361519017103811012460545,⟨5,68,261,25,496,504,192,384,320⟩⟩,⟨6,1210143305956533885469699,⟨191,191,445,57,184,59,128,384,256⟩⟩,⟨5,1210107564157954027587015,⟨7,71,263,25,157,11,199,391,327⟩⟩]⟩
theorem node470 : UpperPrefix a [2,6,8,0,7,1] 30 :=
  Boolean.leaf_sound a [2,6,8,0,7,1] 30 cert470 (by decide +kernel)

theorem node471 : UpperPrefix a [3,5,6,8,7] 30 :=
  branch_upper a [3,5,6,8,7] 30 (by decide) (fin9_cases _
  node461
  node465
  node469
  (invalid_upper a [3,5,6,8,7,3] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut94 [3,5,6,8,7,4] [2,6,8,0,7,1] 30 (by decide +kernel) node470)
  (invalid_upper a [3,5,6,8,7,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,8,7,8] 30 (by decide +kernel)))

theorem node472 : UpperPrefix a [3,5,6,8] 30 :=
  branch_upper a [3,5,6,8] 30 (by decide) (fin9_cases _
  node445
  node451
  node457
  (invalid_upper a [3,5,6,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,8,6] 30 (by decide +kernel))
  node471
  (invalid_upper a [3,5,6,8,8] 30 (by decide +kernel)))

theorem node473 : UpperPrefix a [3,5,6] 30 :=
  branch_upper a [3,5,6] 30 (by decide) (fin9_cases _
  node351
  node368
  node397
  (invalid_upper a [3,5,6,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,6,6] 30 (by decide +kernel))
  node434
  node472)

theorem node474 : UpperPrefix a [3,5] 30 :=
  branch_upper a [3,5] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut18 [3,5,1] [2,3,5] 30 (by decide +kernel) node38)
  (invalid_upper a [3,5,2] 30 (by decide +kernel))
  (invalid_upper a [3,5,3] 30 (by decide +kernel))
  node337
  (invalid_upper a [3,5,5] 30 (by decide +kernel))
  node473
  (PrefixConjugacy.upper aut2 [3,5,7] [3,5,6] 30 (by decide +kernel) node473)
  (PrefixConjugacy.upper aut1 [3,5,8] [3,5,6] 30 (by decide +kernel) node473))

theorem node475 : UpperPrefix a [3,6] 30 :=
  branch_upper a [3,6] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,6,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut18 [3,6,1] [2,3,6] 30 (by decide +kernel) node153)
  (invalid_upper a [3,6,2] 30 (by decide +kernel))
  (invalid_upper a [3,6,3] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut24 [3,6,4] [3,5,6] 30 (by decide +kernel) node473)
  (PrefixConjugacy.upper aut21 [3,6,5] [3,4,6] 30 (by decide +kernel) node312)
  (invalid_upper a [3,6,6] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut45 [3,6,7] [3,4,6] 30 (by decide +kernel) node312)
  (PrefixConjugacy.upper aut45 [3,6,8] [3,5,6] 30 (by decide +kernel) node473))

theorem node476 : UpperPrefix a [3] 30 :=
  branch_upper a [3] 30 (by decide) (fin9_cases _
  node156
  (invalid_upper a [3,1] 30 (by decide +kernel))
  (invalid_upper a [3,2] 30 (by decide +kernel))
  (invalid_upper a [3,3] 30 (by decide +kernel))
  node313
  node474
  node475
  (PrefixConjugacy.upper aut2 [3,7] [3,6] 30 (by decide +kernel) node475)
  (PrefixConjugacy.upper aut1 [3,8] [3,6] 30 (by decide +kernel) node475))

theorem node477 : UpperPrefix a [] 30 :=
  branch_upper a [] 30 (by decide) (fin9_cases _
  (invalid_upper a [0] 30 (by decide +kernel))
  (invalid_upper a [1] 30 (by decide +kernel))
  node155
  node476
  (PrefixConjugacy.upper aut6 [4] [3] 30 (by decide +kernel) node476)
  (PrefixConjugacy.upper aut3 [5] [3] 30 (by decide +kernel) node476)
  (PrefixConjugacy.upper aut9 [6] [3] 30 (by decide +kernel) node476)
  (PrefixConjugacy.upper aut11 [7] [3] 30 (by decide +kernel) node476)
  (PrefixConjugacy.upper aut10 [8] [3] 30 (by decide +kernel) node476))

#print axioms node477
end Delivery.FiniteExclusion.Sharp3x3x3

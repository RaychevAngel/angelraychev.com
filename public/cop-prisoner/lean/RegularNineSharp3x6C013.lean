import RegularNineSharp3x6Base
import RegularNineSharp3x6C011
import RegularNineSharp3x6C012
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp3x6
open Bounds BoundTreeRows Extremal
def cert832 : Leaf := ⟨⟨400,393,426,259,0,143,267,11,131⟩,[(4,5)],[(6,4,4)],⟨11,38,21,152,112,352,196,387,267⟩,⟨11,38,21,152,112,352,196,384,264⟩,[⟨4,1214876156888119010954241,⟨491,230,487,136,98,354,230,384,264⟩⟩,⟨5,1224302441809062873007107,⟨459,463,477,152,80,320,204,384,264⟩⟩,⟨2,1224302334850771013600259,⟨395,443,409,152,112,368,200,384,264⟩⟩]⟩
theorem node832 : UpperPrefix a [3,5,4,7,6,8,2] 30 :=
  Boolean.leaf_sound a [3,5,4,7,6,8,2] 30 cert832 (by decide +kernel)

theorem node833 : UpperPrefix a [3,5,4,7,6,8] 30 :=
  branch_upper a [3,5,4,7,6,8] 30 (by decide) (fin9_cases _
  node828
  node831
  node832
  (invalid_upper a [3,5,4,7,6,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,6,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,6,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,6,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,6,8,8] 30 (by decide +kernel)))

theorem node834 : UpperPrefix a [3,5,4,7,6] 30 :=
  branch_upper a [3,5,4,7,6] 30 (by decide) (fin9_cases _
  node823
  node824
  node825
  (invalid_upper a [3,5,4,7,6,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,6,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,6,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,6,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,6,7] 30 (by decide +kernel))
  node833)

def cert835 : Leaf := ⟨⟨224,201,232,352,200,138,44,104,224⟩,[],[(8,4,3),(0,5,1),(1,6,5),(2,7,6)],⟨11,38,21,152,304,97,194,388,328⟩,⟨11,38,21,152,304,97,194,388,264⟩,[⟨4,1252648324625910838922249,⟨363,230,487,491,288,353,194,486,361⟩⟩]⟩
theorem node835 : UpperPrefix a [3,5,4,7,8,0,1,2] 30 :=
  Boolean.leaf_sound a [3,5,4,7,8,0,1,2] 30 cert835 (by decide +kernel)

def cert836 : Leaf := ⟨⟨52,25,40,292,12,30,60,60,52⟩,[],[(8,4,3),(0,5,1),(1,6,5)],⟨11,38,21,152,304,97,194,448,268⟩,⟨11,38,21,152,304,97,194,448,264⟩,[⟨6,2310417802873319498474601,⟨287,311,279,415,311,319,415,397,269⟩⟩,⟨7,1251428276524105696933129,⟨287,54,279,319,311,375,118,375,287⟩⟩]⟩
theorem node836 : UpperPrefix a [3,5,4,7,8,0,1,6] 30 :=
  Boolean.leaf_sound a [3,5,4,7,8,0,1,6] 30 cert836 (by decide +kernel)

theorem node837 : UpperPrefix a [3,5,4,7,8,0,1] 30 :=
  branch_upper a [3,5,4,7,8,0,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,4,7,8,0,1,0] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,8,0,1,1] 30 (by decide +kernel))
  node835
  (invalid_upper a [3,5,4,7,8,0,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,8,0,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,8,0,1,5] 30 (by decide +kernel))
  node836
  (invalid_upper a [3,5,4,7,8,0,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,8,0,1,8] 30 (by decide +kernel)))

def cert838 : Leaf := ⟨⟨208,201,234,322,202,138,10,72,194⟩,[],[(8,4,3),(0,5,1)],⟨11,38,21,152,304,97,196,386,328⟩,⟨11,38,21,152,304,97,196,386,264⟩,[⟨2,1663473196641971829998723,⟨155,443,25,153,304,377,505,411,264⟩⟩,⟨4,1215171304793298363780097,⟨491,230,487,136,416,483,230,450,264⟩⟩,⟨5,1545423362644198747538435,⟨459,463,477,152,272,449,460,451,264⟩⟩]⟩
theorem node838 : UpperPrefix a [3,5,4,7,8,0,2,1] 30 :=
  Boolean.leaf_sound a [3,5,4,7,8,0,2,1] 30 cert838 (by decide +kernel)

def cert839 : Leaf := ⟨⟨112,73,106,354,74,14,42,42,98⟩,[],[(8,4,3),(0,5,1)],⟨11,38,21,152,304,97,196,448,266⟩,⟨11,38,21,152,304,97,196,448,264⟩,[⟨7,1251428276524105696933129,⟨287,54,279,319,311,375,118,375,287⟩⟩,⟨2,1224569812639983146632195,⟨283,443,281,152,440,505,192,448,264⟩⟩,⟨4,1215171304793298363780097,⟨491,230,487,136,416,483,230,450,264⟩⟩]⟩
theorem node839 : UpperPrefix a [3,5,4,7,8,0,2,6] 30 :=
  Boolean.leaf_sound a [3,5,4,7,8,0,2,6] 30 cert839 (by decide +kernel)

theorem node840 : UpperPrefix a [3,5,4,7,8,0,2] 30 :=
  branch_upper a [3,5,4,7,8,0,2] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,4,7,8,0,2,0] 30 (by decide +kernel))
  node838
  (invalid_upper a [3,5,4,7,8,0,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,8,0,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,8,0,2,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,8,0,2,5] 30 (by decide +kernel))
  node839
  (invalid_upper a [3,5,4,7,8,0,2,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,8,0,2,8] 30 (by decide +kernel)))

theorem node841 : UpperPrefix a [3,5,4,7,8,0] 30 :=
  branch_upper a [3,5,4,7,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,4,7,8,0,0] 30 (by decide +kernel))
  node837
  node840
  (invalid_upper a [3,5,4,7,8,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,8,0,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,8,0,8] 30 (by decide +kernel)))

def cert842 : Leaf := ⟨⟨132,137,168,261,205,141,12,9,197⟩,[],[(8,4,3)],⟨11,38,21,152,304,98,193,388,328⟩,⟨11,38,21,152,304,98,193,388,264⟩,[⟨1,2301629172315690663936001,⟨477,508,477,408,312,504,461,460,264⟩⟩,⟨4,1252645980572673536756745,⟨363,230,487,491,288,98,483,486,361⟩⟩,⟨5,1847683082139117418447875,⟨459,463,477,408,336,451,449,460,264⟩⟩,⟨6,1212615169556374268945439,⟨15,47,159,159,447,35,129,397,397⟩⟩]⟩
theorem node842 : UpperPrefix a [3,5,4,7,8,1,0,2] 30 :=
  Boolean.leaf_sound a [3,5,4,7,8,1,0,2] 30 cert842 (by decide +kernel)

def cert843 : Leaf := ⟨⟨84,89,104,324,76,29,28,28,84⟩,[],[(8,4,3)],⟨11,38,21,152,304,98,193,448,268⟩,⟨11,38,21,152,304,98,193,448,264⟩,[⟨1,1546345682961728930054145,⟨477,508,477,152,440,504,461,448,264⟩⟩,⟨7,1251428278778104542262537,⟨287,38,279,319,311,118,375,375,287⟩⟩,⟨5,1238949751078741217379331,⟨459,463,477,152,472,451,193,448,264⟩⟩,⟨0,1238736912088592083321856,⟨282,446,284,152,440,506,192,448,264⟩⟩]⟩
theorem node843 : UpperPrefix a [3,5,4,7,8,1,0,6] 30 :=
  Boolean.leaf_sound a [3,5,4,7,8,1,0,6] 30 cert843 (by decide +kernel)

theorem node844 : UpperPrefix a [3,5,4,7,8,1,0] 30 :=
  branch_upper a [3,5,4,7,8,1,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,4,7,8,1,0,0] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,8,1,0,1] 30 (by decide +kernel))
  node842
  (invalid_upper a [3,5,4,7,8,1,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,8,1,0,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,8,1,0,5] 30 (by decide +kernel))
  node843
  (invalid_upper a [3,5,4,7,8,1,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,8,1,0,8] 30 (by decide +kernel)))

def cert845 : Leaf := ⟨⟨208,201,232,321,201,141,9,73,193⟩,[],[(8,4,3),(2,6,5)],⟨11,38,21,152,304,98,196,449,329⟩,⟨11,38,21,152,304,98,196,384,264⟩,[⟨1,1233765640659312131178497,⟨477,508,477,152,304,120,460,384,264⟩⟩,⟨4,1214876159210287568817153,⟨491,230,487,136,288,98,230,384,264⟩⟩,⟨5,1243523949133870373274627,⟨459,463,477,152,408,451,460,384,264⟩⟩]⟩
theorem node845 : UpperPrefix a [3,5,4,7,8,1,2] 30 :=
  Boolean.leaf_sound a [3,5,4,7,8,1,2] 30 cert845 (by decide +kernel)

theorem node846 : UpperPrefix a [3,5,4,7,8,1] 30 :=
  branch_upper a [3,5,4,7,8,1] 30 (by decide) (fin9_cases _
  node844
  (invalid_upper a [3,5,4,7,8,1,1] 30 (by decide +kernel))
  node845
  (invalid_upper a [3,5,4,7,8,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,8,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,8,1,8] 30 (by decide +kernel)))

def cert847 : Leaf := ⟨⟨208,0,234,322,202,139,10,74,194⟩,[(1,5)],[(8,4,3),(2,5,1),(0,6,5)],⟨11,38,21,152,304,100,193,450,330⟩,⟨11,38,21,152,304,100,193,384,264⟩,[⟨5,1224302459823461382489091,⟨459,463,477,152,272,76,449,384,264⟩⟩,⟨4,1214876138908904873544705,⟨491,230,487,136,290,230,449,384,264⟩⟩]⟩
theorem node847 : UpperPrefix a [3,5,4,7,8,2,0] 30 :=
  Boolean.leaf_sound a [3,5,4,7,8,2,0] 30 cert847 (by decide +kernel)

def cert848 : Leaf := ⟨⟨208,0,226,323,195,147,17,90,211⟩,[(1,5)],[(3,0,7),(8,4,3),(2,5,1)],⟨11,38,21,152,304,100,194,385,328⟩,⟨11,38,21,152,304,100,194,385,264⟩,[⟨5,1394934770447680697009155,⟨459,463,477,152,272,460,451,449,264⟩⟩]⟩
theorem node848 : UpperPrefix a [3,5,4,7,8,2,1,0] 30 :=
  Boolean.leaf_sound a [3,5,4,7,8,2,1,0] 30 cert848 (by decide +kernel)

def cert849 : Leaf := ⟨⟨208,0,232,321,201,155,25,25,209⟩,[(1,5)],[(8,4,3),(2,5,1)],⟨11,38,21,152,304,100,194,448,265⟩,⟨11,38,21,152,304,100,194,448,264⟩,[⟨1,1234014545605731028303873,⟨285,444,285,152,440,508,216,456,264⟩⟩,⟨5,1244114190901033550480387,⟨459,463,477,152,408,460,451,448,264⟩⟩]⟩
theorem node849 : UpperPrefix a [3,5,4,7,8,2,1,6] 30 :=
  Boolean.leaf_sound a [3,5,4,7,8,2,1,6] 30 cert849 (by decide +kernel)

theorem node850 : UpperPrefix a [3,5,4,7,8,2,1] 30 :=
  branch_upper a [3,5,4,7,8,2,1] 30 (by decide) (fin9_cases _
  node848
  (invalid_upper a [3,5,4,7,8,2,1,1] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,8,2,1,2] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,8,2,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,8,2,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,8,2,1,5] 30 (by decide +kernel))
  node849
  (invalid_upper a [3,5,4,7,8,2,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,8,2,1,8] 30 (by decide +kernel)))

theorem node851 : UpperPrefix a [3,5,4,7,8,2] 30 :=
  branch_upper a [3,5,4,7,8,2] 30 (by decide) (fin9_cases _
  node847
  node850
  (invalid_upper a [3,5,4,7,8,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,8,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,8,2,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,8,2,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,8,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,8,2,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,8,2,8] 30 (by decide +kernel)))

theorem node852 : UpperPrefix a [3,5,4,7,8] 30 :=
  branch_upper a [3,5,4,7,8] 30 (by decide) (fin9_cases _
  node841
  node846
  node851
  (invalid_upper a [3,5,4,7,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,8,8] 30 (by decide +kernel)))

theorem node853 : UpperPrefix a [3,5,4,7] 30 :=
  branch_upper a [3,5,4,7] 30 (by decide) (fin9_cases _
  node813
  node821
  node822
  (invalid_upper a [3,5,4,7,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,5] 30 (by decide +kernel))
  node834
  (invalid_upper a [3,5,4,7,7] 30 (by decide +kernel))
  node852)

def cert854 : Leaf := ⟨⟨404,400,0,196,454,404,276,84,212⟩,[(2,4)],[(0,4,2),(1,5,4)],⟨11,38,21,280,49,98,196,452,460⟩,⟨11,38,21,280,49,98,192,384,264⟩,[⟨3,1210181524417621683092993,⟨247,54,119,502,119,98,192,416,482⟩⟩,⟨5,1352055800237104751969283,⟨459,463,477,476,477,451,192,384,456⟩⟩,⟨6,1210106412362347085571081,⟨15,38,23,287,55,34,128,384,269⟩⟩]⟩
theorem node854 : UpperPrefix a [3,5,4,8,0,1] 30 :=
  Boolean.leaf_sound a [3,5,4,8,0,1] 30 cert854 (by decide +kernel)

def cert855 : Leaf := ⟨⟨464,0,0,194,458,410,282,90,210⟩,[(1,5),(2,4)],[(0,4,2),(2,5,1)],⟨11,38,21,280,49,100,194,450,458⟩,⟨11,38,21,280,49,100,192,384,264⟩,[⟨5,1224302387765869496239107,⟨459,463,477,284,477,76,192,384,264⟩⟩]⟩
theorem node855 : UpperPrefix a [3,5,4,8,0,2] 30 :=
  Boolean.leaf_sound a [3,5,4,8,0,2] 30 cert855 (by decide +kernel)

def cert856 : Leaf := ⟨⟨308,272,0,102,326,0,310,118,118⟩,[(2,4),(5,6)],[(0,4,2),(7,5,5)],⟨11,38,21,280,49,224,198,454,334⟩,⟨11,38,21,280,49,224,192,384,264⟩,[⟨3,1210181525965734055001601,⟨247,54,119,502,119,224,224,416,482⟩⟩,⟨6,1210106412362347085571081,⟨15,38,23,287,55,160,128,384,269⟩⟩]⟩
theorem node856 : UpperPrefix a [3,5,4,8,0,7] 30 :=
  Boolean.leaf_sound a [3,5,4,8,0,7] 30 cert856 (by decide +kernel)

theorem node857 : UpperPrefix a [3,5,4,8,0] 30 :=
  branch_upper a [3,5,4,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,4,8,0,0] 30 (by decide +kernel))
  node854
  node855
  (invalid_upper a [3,5,4,8,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,8,0,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,8,0,6] 30 (by decide +kernel))
  node856
  (invalid_upper a [3,5,4,8,0,8] 30 (by decide +kernel)))

def cert858 : Leaf := ⟨⟨276,281,266,196,0,412,284,92,212⟩,[(4,1)],[(5,1,4),(1,4,2),(0,5,1)],⟨11,38,21,280,50,97,196,452,460⟩,⟨11,38,21,280,50,97,192,384,264⟩,[⟨6,1210106412364683552252937,⟨31,54,23,287,54,55,128,384,269⟩⟩,⟨7,1208926973665470747796489,⟨31,54,23,287,54,119,64,256,269⟩⟩]⟩
theorem node858 : UpperPrefix a [3,5,4,8,1,0] 30 :=
  Boolean.leaf_sound a [3,5,4,8,1,0] 30 cert858 (by decide +kernel)

def cert859 : Local := ⟨⟨464,0,458,193,0,409,281,89,209⟩,[(1,5),(4,1)],[(5,1,4),(1,4,2),(2,5,1),(2,5,4)]⟩
theorem node859 : UpperPrefix a [3,5,4,8,1,2] 30 :=
  local_sound a [3,5,4,8,1,2] 30 cert859 (by decide +kernel)

def cert860 : Local := ⟨⟨340,345,330,69,0,0,285,93,85⟩,[(4,1),(5,6)],[(5,1,4),(1,4,2),(7,5,5)]⟩
theorem node860 : UpperPrefix a [3,5,4,8,1,7] 30 :=
  local_sound a [3,5,4,8,1,7] 30 cert860 (by decide +kernel)

theorem node861 : UpperPrefix a [3,5,4,8,1] 30 :=
  branch_upper a [3,5,4,8,1] 30 (by decide) (fin9_cases _
  node858
  (invalid_upper a [3,5,4,8,1,1] 30 (by decide +kernel))
  node859
  (invalid_upper a [3,5,4,8,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,8,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,8,1,6] 30 (by decide +kernel))
  node860
  (invalid_upper a [3,5,4,8,1,8] 30 (by decide +kernel)))

def cert862 : Leaf := ⟨⟨448,0,490,195,0,395,267,75,195⟩,[(1,4),(4,1)],[],⟨11,38,21,280,52,227,195,451,459⟩,⟨11,38,21,280,52,96,192,384,264⟩,[⟨2,1224302388997320366621699,⟨491,491,505,280,56,96,192,384,264⟩⟩,⟨4,1252729002109635553930249,⟨491,230,487,491,230,96,192,384,489⟩⟩,⟨5,1224302387765867344561155,⟨459,463,477,280,28,64,192,384,264⟩⟩]⟩
theorem node862 : UpperPrefix a [3,5,4,8,2] 30 :=
  Boolean.leaf_sound a [3,5,4,8,2] 30 cert862 (by decide +kernel)

def cert863 : Leaf := ⟨⟨276,281,296,132,0,414,284,28,148⟩,[(4,5)],[(6,4,4),(0,5,1),(1,6,5)],⟨11,38,21,280,112,97,194,388,396⟩,⟨11,38,21,280,112,97,194,384,264⟩,[⟨5,1238497157330586844529667,⟨459,463,477,280,80,65,451,384,264⟩⟩,⟨7,1208926973665333308580873,⟨15,54,23,287,118,119,66,256,269⟩⟩]⟩
theorem node863 : UpperPrefix a [3,5,4,8,6,0,1] 30 :=
  Boolean.leaf_sound a [3,5,4,8,6,0,1] 30 cert863 (by decide +kernel)

def cert864 : Leaf := ⟨⟨436,385,418,166,0,390,290,38,166⟩,[(4,5)],[(6,4,4),(0,5,1)],⟨11,38,21,280,112,97,196,386,394⟩,⟨11,38,21,280,112,97,196,384,264⟩,[⟨3,1210181370457406496370177,⟨247,54,119,402,118,119,246,384,384⟩⟩,⟨4,1215171304793298363780097,⟨491,230,487,264,226,483,230,384,264⟩⟩]⟩
theorem node864 : UpperPrefix a [3,5,4,8,6,0,2] 30 :=
  Boolean.leaf_sound a [3,5,4,8,6,0,2] 30 cert864 (by decide +kernel)

theorem node865 : UpperPrefix a [3,5,4,8,6,0] 30 :=
  branch_upper a [3,5,4,8,6,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,4,8,6,0,0] 30 (by decide +kernel))
  node863
  node864
  (invalid_upper a [3,5,4,8,6,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,8,6,0,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,8,6,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,8,6,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,8,6,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,8,6,0,8] 30 (by decide +kernel)))

def cert866 : Leaf := ⟨⟨148,153,168,133,0,157,29,29,149⟩,[(4,5)],[(6,4,4)],⟨11,38,21,280,112,98,197,389,397⟩,⟨11,38,21,280,112,98,192,384,264⟩,[⟨1,1233765604632714135470081,⟨477,508,477,280,112,120,192,384,264⟩⟩,⟨5,1238497211373782372975619,⟨459,463,477,280,80,451,192,384,264⟩⟩,⟨8,1184058845974318128393,⟨15,54,55,63,114,114,246,247,15⟩⟩]⟩
theorem node866 : UpperPrefix a [3,5,4,8,6,1] 30 :=
  Boolean.leaf_sound a [3,5,4,8,6,1] 30 cert866 (by decide +kernel)

def cert867 : Leaf := ⟨⟨400,0,426,131,0,411,283,27,147⟩,[(1,5),(4,5)],[(6,4,4),(2,5,1)],⟨11,38,21,280,112,100,195,387,395⟩,⟨11,38,21,280,112,100,192,384,264⟩,[⟨5,1224302387765867344561155,⟨459,463,477,280,80,76,192,384,264⟩⟩]⟩
theorem node867 : UpperPrefix a [3,5,4,8,6,2] 30 :=
  Boolean.leaf_sound a [3,5,4,8,6,2] 30 cert867 (by decide +kernel)

def cert868 : Leaf := ⟨⟨308,281,298,38,0,0,318,62,54⟩,[(4,5),(5,6)],[(6,4,4),(7,5,4),(7,5,5)],⟨11,38,21,280,112,224,193,390,270⟩,⟨11,38,21,280,112,224,193,384,264⟩,[⟨0,1219570747252061837984768,⟨394,446,20,280,112,240,240,384,264⟩⟩]⟩
theorem node868 : UpperPrefix a [3,5,4,8,6,7,0] 30 :=
  Boolean.leaf_sound a [3,5,4,8,6,7,0] 30 cert868 (by decide +kernel)

def cert869 : Leaf := ⟨⟨276,281,298,7,0,0,285,31,23⟩,[(4,5),(5,6)],[(6,4,4),(7,5,4),(7,5,5)],⟨11,38,21,280,112,224,194,389,269⟩,⟨11,38,21,280,112,224,194,384,264⟩,[⟨5,1238497157330586844529667,⟨459,463,477,280,80,192,451,384,264⟩⟩]⟩
theorem node869 : UpperPrefix a [3,5,4,8,6,7,1] 30 :=
  Boolean.leaf_sound a [3,5,4,8,6,7,1] 30 cert869 (by decide +kernel)

def cert870 : Leaf := ⟨⟨276,281,298,7,0,0,283,31,23⟩,[(4,5),(5,6)],[(6,4,4),(7,5,4),(7,5,5)],⟨11,38,21,280,112,224,196,387,267⟩,⟨11,38,21,280,112,224,196,384,264⟩,[⟨5,1224302441809062873007107,⟨459,463,477,280,80,192,204,384,264⟩⟩]⟩
theorem node870 : UpperPrefix a [3,5,4,8,6,7,2] 30 :=
  Boolean.leaf_sound a [3,5,4,8,6,7,2] 30 cert870 (by decide +kernel)

theorem node871 : UpperPrefix a [3,5,4,8,6,7] 30 :=
  branch_upper a [3,5,4,8,6,7] 30 (by decide) (fin9_cases _
  node868
  node869
  node870
  (invalid_upper a [3,5,4,8,6,7,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,8,6,7,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,8,6,7,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,8,6,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,8,6,7,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,8,6,7,8] 30 (by decide +kernel)))

theorem node872 : UpperPrefix a [3,5,4,8,6] 30 :=
  branch_upper a [3,5,4,8,6] 30 (by decide) (fin9_cases _
  node865
  node866
  node867
  (invalid_upper a [3,5,4,8,6,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,8,6,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,8,6,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,8,6,6] 30 (by decide +kernel))
  node871
  (invalid_upper a [3,5,4,8,6,8] 30 (by decide +kernel)))

def cert873 : Leaf := ⟨⟨240,201,232,224,72,138,44,104,224⟩,[],[(0,5,1),(1,6,5),(2,7,6)],⟨11,38,21,280,176,97,194,388,328⟩,⟨11,38,21,280,176,97,194,388,264⟩,[⟨8,1184344681614153088777,⟨47,38,119,127,246,119,246,247,47⟩⟩,⟨4,1252648459452424683326465,⟨363,230,487,328,226,353,194,486,264⟩⟩]⟩
theorem node873 : UpperPrefix a [3,5,4,8,7,0,1,2] 30 :=
  Boolean.leaf_sound a [3,5,4,8,7,0,1,2] 30 cert873 (by decide +kernel)

def cert874 : Leaf := ⟨⟨308,273,288,36,324,278,308,52,52⟩,[],[(0,5,1),(1,6,5),(6,7,4)],⟨11,38,21,280,176,97,194,448,268⟩,⟨11,38,21,280,176,97,194,448,264⟩,[⟨3,1212542986037533598838273,⟨247,38,119,466,246,119,194,448,448⟩⟩,⟨7,1355320336883895780779039,⟨271,303,287,287,319,353,355,352,269⟩⟩]⟩
theorem node874 : UpperPrefix a [3,5,4,8,7,0,1,6] 30 :=
  Boolean.leaf_sound a [3,5,4,8,7,0,1,6] 30 cert874 (by decide +kernel)

theorem node875 : UpperPrefix a [3,5,4,8,7,0,1] 30 :=
  branch_upper a [3,5,4,8,7,0,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,4,8,7,0,1,0] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,8,7,0,1,1] 30 (by decide +kernel))
  node873
  (invalid_upper a [3,5,4,8,7,0,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,8,7,0,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,8,7,0,1,5] 30 (by decide +kernel))
  node874
  (invalid_upper a [3,5,4,8,7,0,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,8,7,0,1,8] 30 (by decide +kernel)))

def cert876 : Leaf := ⟨⟨212,193,226,198,70,134,2,70,198⟩,[],[(0,5,1)],⟨11,38,21,280,176,97,196,450,330⟩,⟨11,38,21,280,176,97,196,384,264⟩,[⟨3,1210181658685308746919425,⟨247,38,119,466,246,119,246,384,384⟩⟩,⟨8,1184344681614153088777,⟨47,38,119,127,246,119,246,247,47⟩⟩,⟨4,1215171304793298363780097,⟨491,230,487,264,160,483,230,384,264⟩⟩,⟨5,1224302441809062873007107,⟨459,463,477,280,144,449,204,384,264⟩⟩]⟩
theorem node876 : UpperPrefix a [3,5,4,8,7,0,2] 30 :=
  Boolean.leaf_sound a [3,5,4,8,7,0,2] 30 cert876 (by decide +kernel)

theorem node877 : UpperPrefix a [3,5,4,8,7,0] 30 :=
  branch_upper a [3,5,4,8,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,4,8,7,0,0] 30 (by decide +kernel))
  node875
  node876
  (invalid_upper a [3,5,4,8,7,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,8,7,0,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,8,7,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,8,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,8,7,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,8,7,0,8] 30 (by decide +kernel)))

def cert878 : Leaf := ⟨⟨212,209,224,196,68,149,28,88,212⟩,[],[],⟨11,38,21,280,176,98,193,388,328⟩,⟨11,38,21,280,176,98,193,388,264⟩,[⟨1,2301629172315692811419649,⟨477,508,477,280,440,504,461,460,264⟩⟩,⟨8,1184058843775311674633,⟨15,38,55,63,246,118,247,247,15⟩⟩,⟨5,1923240945865033889350659,⟨459,463,477,280,472,451,449,460,264⟩⟩,⟨0,1361241739482097215603712,⟨154,446,28,280,440,506,192,388,264⟩⟩,⟨3,1210107567540048489399297,⟨3,38,21,272,178,118,247,388,256⟩⟩]⟩
theorem node878 : UpperPrefix a [3,5,4,8,7,1,0,2] 30 :=
  Boolean.leaf_sound a [3,5,4,8,7,1,0,2] 30 cert878 (by decide +kernel)

def cert879 : Leaf := ⟨⟨20,25,40,5,77,157,28,29,21⟩,[],[(6,7,4)],⟨11,38,21,280,176,98,193,448,268⟩,⟨11,38,21,280,176,98,193,448,264⟩,[⟨1,1546345682961726782570497,⟨477,508,477,280,184,504,461,448,264⟩⟩,⟨8,1184058843775311674633,⟨15,38,55,63,246,118,247,247,15⟩⟩,⟨5,1238802177126149393482755,⟨459,463,477,280,208,451,193,448,264⟩⟩,⟨7,1355320334632095967093791,⟨271,303,287,287,319,355,321,320,269⟩⟩]⟩
theorem node879 : UpperPrefix a [3,5,4,8,7,1,0,6] 30 :=
  Boolean.leaf_sound a [3,5,4,8,7,1,0,6] 30 cert879 (by decide +kernel)

theorem node880 : UpperPrefix a [3,5,4,8,7,1,0] 30 :=
  branch_upper a [3,5,4,8,7,1,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,4,8,7,1,0,0] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,8,7,1,0,1] 30 (by decide +kernel))
  node878
  (invalid_upper a [3,5,4,8,7,1,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,8,7,1,0,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,8,7,1,0,5] 30 (by decide +kernel))
  node879
  (invalid_upper a [3,5,4,8,7,1,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,8,7,1,0,8] 30 (by decide +kernel)))

def cert881 : Leaf := ⟨⟨208,201,232,193,73,141,9,73,193⟩,[],[(2,6,5)],⟨11,38,21,280,176,98,196,449,329⟩,⟨11,38,21,280,176,98,196,384,264⟩,[⟨1,1233765640659312131178497,⟨477,508,477,280,176,120,460,384,264⟩⟩,⟨8,1184347496363911790345,⟨47,38,119,127,246,114,246,247,47⟩⟩,⟨4,1214876159210287568817153,⟨491,230,487,264,160,98,230,384,264⟩⟩,⟨5,1243523949133868225790979,⟨459,463,477,280,144,451,460,384,264⟩⟩]⟩
theorem node881 : UpperPrefix a [3,5,4,8,7,1,2] 30 :=
  Boolean.leaf_sound a [3,5,4,8,7,1,2] 30 cert881 (by decide +kernel)

theorem node882 : UpperPrefix a [3,5,4,8,7,1] 30 :=
  branch_upper a [3,5,4,8,7,1] 30 (by decide) (fin9_cases _
  node880
  (invalid_upper a [3,5,4,8,7,1,1] 30 (by decide +kernel))
  node881
  (invalid_upper a [3,5,4,8,7,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,8,7,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,8,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,8,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,8,7,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,8,7,1,8] 30 (by decide +kernel)))

def cert883 : Leaf := ⟨⟨208,0,234,194,74,155,26,90,210⟩,[(1,5)],[(2,5,1),(0,6,5)],⟨11,38,21,280,176,100,193,450,330⟩,⟨11,38,21,280,176,100,193,384,264⟩,[⟨5,1224302459823461382489091,⟨459,463,477,280,144,76,449,384,264⟩⟩,⟨8,1184058843775311674633,⟨15,38,55,63,246,118,247,247,15⟩⟩]⟩
theorem node883 : UpperPrefix a [3,5,4,8,7,2,0] 30 :=
  Boolean.leaf_sound a [3,5,4,8,7,2,0] 30 cert883 (by decide +kernel)

def cert884 : Leaf := ⟨⟨208,0,234,195,75,139,9,75,195⟩,[(1,5)],[(2,5,1)],⟨11,38,21,280,176,100,194,449,329⟩,⟨11,38,21,280,176,100,194,384,264⟩,[⟨5,1243819042995852050170883,⟨459,463,477,280,144,460,451,384,264⟩⟩,⟨8,1184347496363911806729,⟨47,38,119,127,246,118,246,247,47⟩⟩,⟨4,1214877039628830347643905,⟨491,230,487,328,226,230,226,384,264⟩⟩]⟩
theorem node884 : UpperPrefix a [3,5,4,8,7,2,1] 30 :=
  Boolean.leaf_sound a [3,5,4,8,7,2,1] 30 cert884 (by decide +kernel)

theorem node885 : UpperPrefix a [3,5,4,8,7,2] 30 :=
  branch_upper a [3,5,4,8,7,2] 30 (by decide) (fin9_cases _
  node883
  node884
  (invalid_upper a [3,5,4,8,7,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,8,7,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,8,7,2,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,8,7,2,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,8,7,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,8,7,2,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,8,7,2,8] 30 (by decide +kernel)))

theorem node886 : UpperPrefix a [3,5,4,8,7] 30 :=
  branch_upper a [3,5,4,8,7] 30 (by decide) (fin9_cases _
  node877
  node882
  node885
  (invalid_upper a [3,5,4,8,7,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,8,7,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,8,7,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,8,7,8] 30 (by decide +kernel)))

theorem node887 : UpperPrefix a [3,5,4,8] 30 :=
  branch_upper a [3,5,4,8] 30 (by decide) (fin9_cases _
  node857
  node861
  node862
  (invalid_upper a [3,5,4,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,8,5] 30 (by decide +kernel))
  node872
  node886
  (invalid_upper a [3,5,4,8,8] 30 (by decide +kernel)))

theorem node888 : UpperPrefix a [3,5,4] 30 :=
  branch_upper a [3,5,4] 30 (by decide) (fin9_cases _
  node745
  node759
  node760
  (invalid_upper a [3,5,4,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,5] 30 (by decide +kernel))
  node807
  node853
  node887)

def cert889 : Local := ⟨⟨336,0,344,322,0,409,281,89,81⟩,[(1,5),(4,1)],[(5,1,4),(7,2,5),(1,4,3),(2,5,1),(2,5,4)]⟩
theorem node889 : UpperPrefix a [3,5,7,0,1,2] 30 :=
  local_sound a [3,5,7,0,1,2] 30 cert889 (by decide +kernel)

def cert890 : Leaf := ⟨⟨208,217,72,194,0,141,269,77,197⟩,[(4,1)],[(5,1,4),(1,4,3)],⟨11,38,133,25,50,112,452,452,332⟩,⟨11,38,133,25,50,112,192,384,264⟩,[⟨8,1181747927772285682803,⟨27,63,141,25,59,127,255,128,8⟩⟩,⟨4,1255094796579691969119233,⟨463,230,453,461,34,96,192,448,460⟩⟩,⟨2,1210107565283995969127443,⟨27,59,137,25,59,121,192,384,264⟩⟩]⟩
theorem node890 : UpperPrefix a [3,5,7,0,1,4] 30 :=
  Boolean.leaf_sound a [3,5,7,0,1,4] 30 cert890 (by decide +kernel)

def cert891 : Local := ⟨⟨340,345,344,326,0,29,0,93,85⟩,[(4,1),(6,2)],[(5,1,4),(7,2,6),(1,4,3)]⟩
theorem node891 : UpperPrefix a [3,5,7,0,1,8,2] 30 :=
  local_sound a [3,5,7,0,1,8,2] 30 cert891 (by decide +kernel)

def cert892 : Leaf := ⟨⟨144,153,24,130,0,157,269,93,213⟩,[(4,1)],[(5,1,4),(1,4,3)],⟨11,38,133,25,50,352,208,452,332⟩,⟨11,38,133,25,50,352,208,384,264⟩,[⟨6,1210106412364698993312819,⟨27,63,141,25,59,319,157,384,264⟩⟩,⟨8,1181745671574425453619,⟨27,63,141,25,59,127,221,128,8⟩⟩,⟨2,1210107565284000264094739,⟨27,59,137,25,59,360,217,384,264⟩⟩]⟩
theorem node892 : UpperPrefix a [3,5,7,0,1,8,4] 30 :=
  Boolean.leaf_sound a [3,5,7,0,1,8,4] 30 cert892 (by decide +kernel)

theorem node893 : UpperPrefix a [3,5,7,0,1,8] 30 :=
  branch_upper a [3,5,7,0,1,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,7,0,1,8,0] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,0,1,8,1] 30 (by decide +kernel))
  node891
  (invalid_upper a [3,5,7,0,1,8,3] 30 (by decide +kernel))
  node892
  (invalid_upper a [3,5,7,0,1,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,0,1,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,0,1,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,0,1,8,8] 30 (by decide +kernel)))

theorem node894 : UpperPrefix a [3,5,7,0,1] 30 :=
  branch_upper a [3,5,7,0,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,7,0,1,0] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,0,1,1] 30 (by decide +kernel))
  node889
  (invalid_upper a [3,5,7,0,1,3] 30 (by decide +kernel))
  node890
  (invalid_upper a [3,5,7,0,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,0,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,0,1,7] 30 (by decide +kernel))
  node893)

def cert895 : Leaf := ⟨⟨500,0,344,484,0,408,280,88,208⟩,[(1,4),(4,1)],[],⟨11,38,133,25,52,98,464,464,344⟩,⟨11,38,133,25,52,98,192,384,264⟩,[⟨1,1252692036107734346891265,⟨477,52,461,477,52,112,192,384,460⟩⟩,⟨0,1252729002744466080017408,⟨506,246,502,506,246,114,192,384,488⟩⟩,⟨2,1247960428273476132930561,⟨491,34,161,505,48,98,192,384,456⟩⟩,⟨5,1247960427112391857406977,⟨463,6,133,477,20,66,192,384,460⟩⟩]⟩
theorem node895 : UpperPrefix a [3,5,7,0,2,1] 30 :=
  Boolean.leaf_sound a [3,5,7,0,2,1] 30 cert895 (by decide +kernel)

#print axioms node895
end Delivery.FiniteExclusion.Sharp3x6

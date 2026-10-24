import RegularNineSharp3x6Base
import RegularNineSharp3x6C011
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp3x6
open Bounds BoundTreeRows Extremal
def cert768 : Leaf := ⟨⟨84,89,10,5,0,413,285,29,149⟩,[(4,1)],[(5,1,4),(1,4,2)],⟨11,38,21,88,50,485,453,389,397⟩,⟨11,38,21,88,50,96,192,384,264⟩,[⟨7,1208926973665475047482427,⟨31,63,23,95,63,127,64,256,269⟩⟩,⟨8,1181745671563284079675,⟨31,63,23,95,63,127,192,128,13⟩⟩,⟨6,1214874895705538437579777,⟨415,182,405,24,50,32,128,384,264⟩⟩]⟩
theorem node768 : UpperPrefix a [3,5,4,6,1] 30 :=
  Boolean.leaf_sound a [3,5,4,6,1] 30 cert768 (by decide +kernel)

def cert769 : Leaf := ⟨⟨448,0,490,387,0,395,267,75,195⟩,[(1,4),(4,1)],[],⟨11,38,21,88,52,483,451,387,395⟩,⟨11,38,21,88,52,96,192,384,264⟩,[⟨2,1224302388997320366621699,⟨491,491,505,88,56,96,192,384,264⟩⟩,⟨4,1252729002109635553930249,⟨491,230,487,491,230,96,192,384,489⟩⟩,⟨5,1224302387765867344561155,⟨459,463,477,88,28,64,192,384,264⟩⟩]⟩
theorem node769 : UpperPrefix a [3,5,4,6,2] 30 :=
  Boolean.leaf_sound a [3,5,4,6,2] 30 cert769 (by decide +kernel)

def cert770 : Leaf := ⟨⟨52,25,40,164,12,30,60,60,52⟩,[],[(7,4,3),(0,5,1),(1,6,5)],⟨11,38,21,88,176,97,194,388,268⟩,⟨11,38,21,88,176,97,194,384,264⟩,[⟨8,1184347496396690292735,⟨47,47,127,127,255,127,255,255,47⟩⟩,⟨6,1255383945693603646694409,⟨415,182,407,415,182,439,146,384,397⟩⟩]⟩
theorem node770 : UpperPrefix a [3,5,4,6,7,0,1] 30 :=
  Boolean.leaf_sound a [3,5,4,6,7,0,1] 30 cert770 (by decide +kernel)

def cert771 : Leaf := ⟨⟨36,9,42,166,14,14,42,46,38⟩,[],[(7,4,3),(0,5,1)],⟨11,38,21,88,176,97,196,386,266⟩,⟨11,38,21,88,176,97,196,384,264⟩,[⟨8,1184347496396690292735,⟨47,47,127,127,255,127,255,255,47⟩⟩,⟨4,1253024023914025340406793,⟨491,230,487,491,160,483,230,384,425⟩⟩,⟨6,1253022762452168824087561,⟨415,182,407,415,182,439,132,384,397⟩⟩]⟩
theorem node771 : UpperPrefix a [3,5,4,6,7,0,2] 30 :=
  Boolean.leaf_sound a [3,5,4,6,7,0,2] 30 cert771 (by decide +kernel)

def cert772 : Leaf := ⟨⟨52,25,42,166,14,30,0,62,54⟩,[(6,7)],[(7,4,3),(0,5,1),(8,6,6)],⟨11,38,21,88,176,97,448,390,270⟩,⟨11,38,21,88,176,97,448,384,264⟩,[⟨6,1253022762452168824087561,⟨415,182,407,415,182,439,384,384,397⟩⟩]⟩
theorem node772 : UpperPrefix a [3,5,4,6,7,0,8] 30 :=
  Boolean.leaf_sound a [3,5,4,6,7,0,8] 30 cert772 (by decide +kernel)

theorem node773 : UpperPrefix a [3,5,4,6,7,0] 30 :=
  branch_upper a [3,5,4,6,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,4,6,7,0,0] 30 (by decide +kernel))
  node770
  node771
  (invalid_upper a [3,5,4,6,7,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,7,0,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,7,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,7,0,7] 30 (by decide +kernel))
  node772)

def cert774 : Leaf := ⟨⟨84,89,104,132,76,29,28,92,84⟩,[],[(7,4,3)],⟨11,38,21,88,176,98,193,388,268⟩,⟨11,38,21,88,176,98,193,384,264⟩,[⟨8,1184347496396690292735,⟨47,47,127,127,255,127,255,255,47⟩⟩,⟨1,1546050535056547429744641,⟨477,508,477,472,184,504,461,384,264⟩⟩,⟨5,1238497805848935333364739,⟨459,463,477,88,216,451,193,384,264⟩⟩,⟨0,1219570744996005443273728,⟨410,446,20,88,184,506,192,384,264⟩⟩]⟩
theorem node774 : UpperPrefix a [3,5,4,6,7,1,0] 30 :=
  Boolean.leaf_sound a [3,5,4,6,7,1,0] 30 cert774 (by decide +kernel)

def cert775 : Leaf := ⟨⟨96,73,104,161,73,13,41,105,97⟩,[],[(7,4,3),(2,6,5)],⟨11,38,21,88,176,98,196,385,265⟩,⟨11,38,21,88,176,98,196,384,264⟩,[⟨8,1184347496396690292735,⟨47,47,127,127,255,127,255,255,47⟩⟩,⟨1,1233765640659316426145793,⟨477,508,477,88,184,120,460,384,264⟩⟩,⟨4,1255090061572449368050697,⟨491,230,487,491,160,98,230,384,425⟩⟩]⟩
theorem node775 : UpperPrefix a [3,5,4,6,7,1,2] 30 :=
  Boolean.leaf_sound a [3,5,4,6,7,1,2] 30 cert775 (by decide +kernel)

def cert776 : Leaf := ⟨⟨84,89,104,133,77,29,0,93,85⟩,[(6,7)],[(7,4,3),(8,6,6)],⟨11,38,21,88,176,98,448,389,269⟩,⟨11,38,21,88,176,98,448,384,264⟩,[⟨1,1233767946502327787323393,⟨477,508,477,88,248,120,448,448,264⟩⟩,⟨5,1238500111691944547058691,⟨459,463,477,88,216,451,448,448,264⟩⟩]⟩
theorem node776 : UpperPrefix a [3,5,4,6,7,1,8] 30 :=
  Boolean.leaf_sound a [3,5,4,6,7,1,8] 30 cert776 (by decide +kernel)

theorem node777 : UpperPrefix a [3,5,4,6,7,1] 30 :=
  branch_upper a [3,5,4,6,7,1] 30 (by decide) (fin9_cases _
  node774
  (invalid_upper a [3,5,4,6,7,1,1] 30 (by decide +kernel))
  node775
  (invalid_upper a [3,5,4,6,7,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,7,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,7,1,7] 30 (by decide +kernel))
  node776)

def cert778 : Leaf := ⟨⟨80,0,106,131,75,11,267,75,67⟩,[(1,5)],[(7,4,3),(2,5,1)],⟨11,38,21,88,176,100,451,387,267⟩,⟨11,38,21,88,176,100,192,384,264⟩,[⟨5,1224302387765867344561155,⟨459,463,477,88,144,76,192,384,264⟩⟩,⟨8,1181748206908264871803,⟨47,47,23,127,191,127,255,131,47⟩⟩,⟨4,1214876138908904873544705,⟨491,230,487,72,162,230,192,384,264⟩⟩]⟩
theorem node778 : UpperPrefix a [3,5,4,6,7,2] 30 :=
  Boolean.leaf_sound a [3,5,4,6,7,2] 30 cert778 (by decide +kernel)

def cert779 : Leaf := ⟨⟨80,89,104,129,329,25,26,93,85⟩,[],[(7,4,3),(8,5,4),(1,7,6)],⟨11,38,21,88,176,352,193,386,268⟩,⟨11,38,21,88,176,352,193,386,264⟩,[⟨2,1210110163874063566505091,⟨11,43,89,88,249,376,249,507,264⟩⟩,⟨5,1238471865115081679307779,⟨459,463,477,88,216,320,193,451,264⟩⟩]⟩
theorem node779 : UpperPrefix a [3,5,4,6,7,8,0,1] 30 :=
  Boolean.leaf_sound a [3,5,4,6,7,8,0,1] 30 cert779 (by decide +kernel)

def cert780 : Leaf := ⟨⟨112,73,106,162,330,10,46,106,98⟩,[],[(7,4,3),(8,5,4)],⟨11,38,21,88,176,352,193,388,266⟩,⟨11,38,21,88,176,352,193,388,264⟩,[⟨0,1224330007221029934466048,⟨410,446,404,120,184,376,504,388,264⟩⟩,⟨2,1224274666988671365809155,⟨267,299,273,120,184,376,505,384,264⟩⟩,⟨4,1214866904207500206214145,⟨267,230,487,104,162,352,483,486,264⟩⟩]⟩
theorem node780 : UpperPrefix a [3,5,4,6,7,8,0,2] 30 :=
  Boolean.leaf_sound a [3,5,4,6,7,8,0,2] 30 cert780 (by decide +kernel)

theorem node781 : UpperPrefix a [3,5,4,6,7,8,0] 30 :=
  branch_upper a [3,5,4,6,7,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,4,6,7,8,0,0] 30 (by decide +kernel))
  node779
  node780
  (invalid_upper a [3,5,4,6,7,8,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,7,8,0,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,7,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,7,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,7,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,7,8,0,8] 30 (by decide +kernel)))

def cert782 : Leaf := ⟨⟨112,81,96,161,321,21,49,120,117⟩,[],[(3,0,7),(7,4,3),(8,5,4)],⟨11,38,21,88,176,352,194,385,268⟩,⟨11,38,21,88,176,352,194,385,264⟩,[⟨1,1602110102760108426788865,⟨445,444,405,376,444,376,508,405,296⟩⟩,⟨2,1210402749220177806623811,⟨91,251,25,89,184,505,219,393,264⟩⟩]⟩
theorem node782 : UpperPrefix a [3,5,4,6,7,8,1,0] 30 :=
  Boolean.leaf_sound a [3,5,4,6,7,8,1,0] 30 cert782 (by decide +kernel)

def cert783 : Leaf := ⟨⟨112,88,104,160,328,26,60,121,113⟩,[],[(7,4,3),(8,5,4),(2,7,6)],⟨11,38,21,88,176,352,194,388,265⟩,⟨11,38,21,88,176,352,194,388,264⟩,[⟨0,1210110163874063567619072,⟨10,46,92,88,250,376,250,510,264⟩⟩,⟨1,1214876048627051634360321,⟨413,180,405,88,176,360,216,388,264⟩⟩]⟩
theorem node783 : UpperPrefix a [3,5,4,6,7,8,1,2] 30 :=
  Boolean.leaf_sound a [3,5,4,6,7,8,1,2] 30 cert783 (by decide +kernel)

theorem node784 : UpperPrefix a [3,5,4,6,7,8,1] 30 :=
  branch_upper a [3,5,4,6,7,8,1] 30 (by decide) (fin9_cases _
  node782
  (invalid_upper a [3,5,4,6,7,8,1,1] 30 (by decide +kernel))
  node783
  (invalid_upper a [3,5,4,6,7,8,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,7,8,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,7,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,7,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,7,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,7,8,1,8] 30 (by decide +kernel)))

def cert785 : Leaf := ⟨⟨100,64,98,166,326,6,35,110,102⟩,[],[(3,0,7),(7,4,3),(8,5,4),(0,7,6)],⟨11,38,21,88,176,352,196,385,266⟩,⟨11,38,21,88,176,352,196,385,264⟩,[⟨4,1255090059250280810187785,⟨491,230,487,491,160,482,230,417,425⟩⟩]⟩
theorem node785 : UpperPrefix a [3,5,4,6,7,8,2,0] 30 :=
  Boolean.leaf_sound a [3,5,4,6,7,8,2,0] 30 cert785 (by decide +kernel)

def cert786 : Leaf := ⟨⟨100,64,98,166,326,6,34,100,103⟩,[],[(7,4,3),(8,5,4)],⟨11,38,21,88,176,352,196,386,265⟩,⟨11,38,21,88,176,352,196,386,264⟩,[⟨0,1210402753736988754478080,⟨90,254,28,90,184,506,254,506,264⟩⟩,⟨3,1210402753736957213574145,⟨87,246,21,82,176,498,246,498,256⟩⟩,⟨4,1253024028417624967777289,⟨491,230,487,491,160,482,230,482,425⟩⟩]⟩
theorem node786 : UpperPrefix a [3,5,4,6,7,8,2,1] 30 :=
  Boolean.leaf_sound a [3,5,4,6,7,8,2,1] 30 cert786 (by decide +kernel)

theorem node787 : UpperPrefix a [3,5,4,6,7,8,2] 30 :=
  branch_upper a [3,5,4,6,7,8,2] 30 (by decide) (fin9_cases _
  node785
  node786
  (invalid_upper a [3,5,4,6,7,8,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,7,8,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,7,8,2,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,7,8,2,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,7,8,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,7,8,2,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,7,8,2,8] 30 (by decide +kernel)))

theorem node788 : UpperPrefix a [3,5,4,6,7,8] 30 :=
  branch_upper a [3,5,4,6,7,8] 30 (by decide) (fin9_cases _
  node781
  node784
  node787
  (invalid_upper a [3,5,4,6,7,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,7,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,7,8,8] 30 (by decide +kernel)))

theorem node789 : UpperPrefix a [3,5,4,6,7] 30 :=
  branch_upper a [3,5,4,6,7] 30 (by decide) (fin9_cases _
  node773
  node777
  node778
  (invalid_upper a [3,5,4,6,7,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,7,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,7,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,7,7] 30 (by decide +kernel))
  node788)

def cert790 : Leaf := ⟨⟨276,281,296,388,12,286,284,28,148⟩,[],[(0,5,1),(1,6,5)],⟨11,38,21,88,304,97,194,388,396⟩,⟨11,38,21,88,304,97,194,384,264⟩,[⟨6,1255531519646055883891721,⟨399,182,407,415,438,439,130,384,397⟩⟩,⟨5,1238497157330586844529667,⟨459,463,477,88,272,65,451,384,264⟩⟩,⟨7,1208926973962201544668937,⟨47,38,23,127,311,99,70,279,319⟩⟩]⟩
theorem node790 : UpperPrefix a [3,5,4,6,8,0,1] 30 :=
  Boolean.leaf_sound a [3,5,4,6,8,0,1] 30 cert790 (by decide +kernel)

def cert791 : Leaf := ⟨⟨384,393,426,386,138,398,266,10,130⟩,[],[(0,5,1)],⟨11,38,21,88,304,97,196,386,394⟩,⟨11,38,21,88,304,97,196,384,264⟩,[⟨4,1253024023914025340406793,⟨491,230,487,491,416,483,230,384,425⟩⟩,⟨6,1253170336404621061284873,⟨399,182,407,415,438,439,132,384,397⟩⟩,⟨2,1224302334850911942214659,⟨411,443,401,88,312,505,192,384,264⟩⟩,⟨5,1224302441809062873007107,⟨459,463,477,88,272,449,204,384,264⟩⟩]⟩
theorem node791 : UpperPrefix a [3,5,4,6,8,0,2] 30 :=
  Boolean.leaf_sound a [3,5,4,6,8,0,2] 30 cert791 (by decide +kernel)

theorem node792 : UpperPrefix a [3,5,4,6,8,0] 30 :=
  branch_upper a [3,5,4,6,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,4,6,8,0,0] 30 (by decide +kernel))
  node790
  node791
  (invalid_upper a [3,5,4,6,8,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,8,0,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,8,0,8] 30 (by decide +kernel)))

def cert793 : Leaf := ⟨⟨84,89,104,388,76,29,28,88,212⟩,[],[],⟨11,38,21,88,304,98,193,388,392⟩,⟨11,38,21,88,304,98,193,388,264⟩,[⟨1,2339408104178647825645569,⟨477,508,477,472,312,504,461,460,264⟩⟩,⟨5,1847683082139119565931523,⟨459,463,477,88,344,451,449,460,264⟩⟩,⟨7,1208926976214001358386953,⟨47,38,23,127,311,98,103,279,319⟩⟩,⟨8,1184058549106149373705,⟨47,38,23,127,55,98,227,231,47⟩⟩,⟨0,1375445732418851154428928,⟨410,446,404,88,312,506,448,388,264⟩⟩]⟩
theorem node793 : UpperPrefix a [3,5,4,6,8,1,0,2] 30 :=
  Boolean.leaf_sound a [3,5,4,6,8,1,0,2] 30 cert793 (by decide +kernel)

theorem node794 : UpperPrefix a [3,5,4,6,8,1,0] 30 :=
  branch_upper a [3,5,4,6,8,1,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,4,6,8,1,0,0] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,8,1,0,1] 30 (by decide +kernel))
  node793
  (invalid_upper a [3,5,4,6,8,1,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,8,1,0,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,8,1,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,8,1,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,8,1,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,8,1,0,8] 30 (by decide +kernel)))

def cert795 : Leaf := ⟨⟨320,329,360,385,73,269,265,73,193⟩,[],[(2,6,5)],⟨11,38,21,88,304,98,196,385,393⟩,⟨11,38,21,88,304,98,196,384,264⟩,[⟨1,1233765640659316426145793,⟨477,508,477,88,312,120,460,384,264⟩⟩,⟨4,1255090061572449368050697,⟨491,230,487,491,416,98,230,384,425⟩⟩,⟨5,1243523949133868225790979,⟨459,463,477,88,400,451,460,384,264⟩⟩,⟨7,1208926976214001358386953,⟨47,38,23,127,311,98,102,279,319⟩⟩]⟩
theorem node795 : UpperPrefix a [3,5,4,6,8,1,2] 30 :=
  Boolean.leaf_sound a [3,5,4,6,8,1,2] 30 cert795 (by decide +kernel)

theorem node796 : UpperPrefix a [3,5,4,6,8,1] 30 :=
  branch_upper a [3,5,4,6,8,1] 30 (by decide) (fin9_cases _
  node794
  (invalid_upper a [3,5,4,6,8,1,1] 30 (by decide +kernel))
  node795
  (invalid_upper a [3,5,4,6,8,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,8,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,8,1,8] 30 (by decide +kernel)))

def cert797 : Leaf := ⟨⟨80,0,106,387,75,11,11,75,195⟩,[(1,5)],[(2,5,1)],⟨11,38,21,88,304,100,195,387,395⟩,⟨11,38,21,88,304,100,192,384,264⟩,[⟨5,1224302387765867344561155,⟨459,463,477,88,272,76,192,384,264⟩⟩,⟨4,1214876138908904873544705,⟨491,230,487,72,290,230,192,384,264⟩⟩,⟨7,1208926976214001358403337,⟨47,38,23,127,311,102,102,279,319⟩⟩,⟨8,1184051793706708268809,⟨47,38,23,127,55,102,192,195,47⟩⟩]⟩
theorem node797 : UpperPrefix a [3,5,4,6,8,2] 30 :=
  Boolean.leaf_sound a [3,5,4,6,8,2] 30 cert797 (by decide +kernel)

def cert798 : Leaf := ⟨⟨336,345,360,257,73,0,282,93,85⟩,[(5,6)],[(7,5,5),(1,7,6)],⟨11,38,21,88,304,224,193,386,268⟩,⟨11,38,21,88,304,224,193,386,264⟩,[⟨5,1238471865115079531824131,⟨459,463,477,88,272,192,193,451,264⟩⟩,⟨2,1210110454351840948520067,⟨11,107,25,120,376,249,249,507,264⟩⟩]⟩
theorem node798 : UpperPrefix a [3,5,4,6,8,7,0,1] 30 :=
  Boolean.leaf_sound a [3,5,4,6,8,7,0,1] 30 cert798 (by decide +kernel)

def cert799 : Leaf := ⟨⟨336,345,362,258,74,0,286,90,82⟩,[(5,6)],[(7,5,5)],⟨11,38,21,88,304,224,193,388,266⟩,⟨11,38,21,88,304,224,193,388,264⟩,[⟨5,1224330129939571946816515,⟨459,463,477,88,272,192,449,460,264⟩⟩,⟨0,1224330007221029934466048,⟨410,446,404,120,312,248,504,388,264⟩⟩,⟨2,1224274666988808804762627,⟨283,315,273,120,312,248,505,384,264⟩⟩]⟩
theorem node799 : UpperPrefix a [3,5,4,6,8,7,0,2] 30 :=
  Boolean.leaf_sound a [3,5,4,6,8,7,0,2] 30 cert799 (by decide +kernel)

theorem node800 : UpperPrefix a [3,5,4,6,8,7,0] 30 :=
  branch_upper a [3,5,4,6,8,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,4,6,8,7,0,0] 30 (by decide +kernel))
  node798
  node799
  (invalid_upper a [3,5,4,6,8,7,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,8,7,0,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,8,7,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,8,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,8,7,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,8,7,0,8] 30 (by decide +kernel)))

def cert801 : Leaf := ⟨⟨340,337,352,261,69,0,277,92,85⟩,[(5,6)],[(3,0,7),(7,5,5)],⟨11,38,21,88,304,224,194,385,268⟩,⟨11,38,21,88,304,224,194,385,264⟩,[⟨1,1224320783848993079951361,⟨413,444,405,120,312,248,504,389,264⟩⟩,⟨5,1239096676512982404957187,⟨459,463,477,216,272,192,451,449,264⟩⟩]⟩
theorem node801 : UpperPrefix a [3,5,4,6,8,7,1,0] 30 :=
  Boolean.leaf_sound a [3,5,4,6,8,7,1,0] 30 cert801 (by decide +kernel)

def cert802 : Leaf := ⟨⟨80,89,106,3,75,0,29,91,83⟩,[(5,6)],[(7,5,5),(2,7,6)],⟨11,38,21,88,304,224,194,388,265⟩,⟨11,38,21,88,304,224,194,388,264⟩,[⟨5,1243219523813456489743363,⟨459,463,477,88,272,192,451,396,264⟩⟩,⟨8,1184634728385623438621,⟨15,103,31,127,127,226,226,231,15⟩⟩]⟩
theorem node802 : UpperPrefix a [3,5,4,6,8,7,1,2] 30 :=
  Boolean.leaf_sound a [3,5,4,6,8,7,1,2] 30 cert802 (by decide +kernel)

theorem node803 : UpperPrefix a [3,5,4,6,8,7,1] 30 :=
  branch_upper a [3,5,4,6,8,7,1] 30 (by decide) (fin9_cases _
  node801
  (invalid_upper a [3,5,4,6,8,7,1,1] 30 (by decide +kernel))
  node802
  (invalid_upper a [3,5,4,6,8,7,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,8,7,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,8,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,8,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,8,7,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,8,7,1,8] 30 (by decide +kernel)))

def cert804 : Leaf := ⟨⟨68,73,106,263,79,0,267,75,67⟩,[(5,6)],[(7,5,5)],⟨11,38,21,88,304,224,196,387,267⟩,⟨11,38,21,88,304,224,196,384,264⟩,[⟨4,1252728878331014545443849,⟨491,230,487,491,288,226,230,384,425⟩⟩,⟨5,1224302441809062873007107,⟨459,463,477,88,272,192,204,384,264⟩⟩,⟨8,1181747921022331434249,⟨15,38,23,127,55,226,230,129,15⟩⟩,⟨2,1214839157390557998744577,⟨395,34,401,120,304,224,224,384,264⟩⟩]⟩
theorem node804 : UpperPrefix a [3,5,4,6,8,7,2] 30 :=
  Boolean.leaf_sound a [3,5,4,6,8,7,2] 30 cert804 (by decide +kernel)

theorem node805 : UpperPrefix a [3,5,4,6,8,7] 30 :=
  branch_upper a [3,5,4,6,8,7] 30 (by decide) (fin9_cases _
  node800
  node803
  node804
  (invalid_upper a [3,5,4,6,8,7,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,8,7,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,8,7,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,8,7,8] 30 (by decide +kernel)))

theorem node806 : UpperPrefix a [3,5,4,6,8] 30 :=
  branch_upper a [3,5,4,6,8] 30 (by decide) (fin9_cases _
  node792
  node796
  node797
  (invalid_upper a [3,5,4,6,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,8,6] 30 (by decide +kernel))
  node805
  (invalid_upper a [3,5,4,6,8,8] 30 (by decide +kernel)))

theorem node807 : UpperPrefix a [3,5,4,6] 30 :=
  branch_upper a [3,5,4,6] 30 (by decide) (fin9_cases _
  node767
  node768
  node769
  (invalid_upper a [3,5,4,6,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,6] 30 (by decide +kernel))
  node789
  node806)

def cert808 : Leaf := ⟨⟨148,152,0,68,206,156,284,92,212⟩,[(2,4)],[(0,4,2),(1,5,4)],⟨11,38,21,152,49,98,452,452,332⟩,⟨11,38,21,152,49,98,192,384,264⟩,[⟨5,1352055800237104751969283,⟨459,463,477,476,477,451,192,384,456⟩⟩,⟨8,1181747927765456053353,⟨31,55,23,159,55,127,255,128,13⟩⟩,⟨6,1210106412362347085571081,⟨15,38,23,159,55,34,128,384,269⟩⟩]⟩
theorem node808 : UpperPrefix a [3,5,4,7,0,1] 30 :=
  Boolean.leaf_sound a [3,5,4,7,0,1] 30 cert808 (by decide +kernel)

def cert809 : Leaf := ⟨⟨464,0,0,322,458,410,282,90,210⟩,[(1,5),(2,4)],[(0,4,2),(2,5,1)],⟨11,38,21,152,49,100,450,450,330⟩,⟨11,38,21,152,49,100,192,384,264⟩,[⟨5,1224302387765869496239107,⟨459,463,477,156,477,76,192,384,264⟩⟩]⟩
theorem node809 : UpperPrefix a [3,5,4,7,0,2] 30 :=
  Boolean.leaf_sound a [3,5,4,7,0,2] 30 cert809 (by decide +kernel)

def cert810 : Leaf := ⟨⟨148,152,0,6,142,158,28,94,214⟩,[(2,4)],[(0,4,2)],⟨11,38,21,152,49,352,194,452,332⟩,⟨11,38,21,152,49,352,194,384,264⟩,[⟨5,1314202595009092996039683,⟨459,463,477,412,477,320,451,384,264⟩⟩,⟨8,1181889786755671680105,⟨95,55,23,223,55,127,223,128,77⟩⟩,⟨6,1210106412364692163683433,⟨31,55,23,159,55,319,159,384,269⟩⟩]⟩
theorem node810 : UpperPrefix a [3,5,4,7,0,8,1] 30 :=
  Boolean.leaf_sound a [3,5,4,7,0,8,1] 30 cert810 (by decide +kernel)

def cert811 : Leaf := ⟨⟨212,192,0,326,462,134,2,78,198⟩,[(2,4)],[(0,4,2)],⟨11,38,21,152,49,352,196,450,330⟩,⟨11,38,21,152,49,352,196,384,264⟩,[⟨4,1215171304793298363780097,⟨491,230,487,136,417,482,230,384,264⟩⟩,⟨5,1224302874154629252252675,⟨459,463,477,220,477,320,204,384,328⟩⟩,⟨3,1210107718406237947175937,⟨67,38,23,214,55,352,196,416,352⟩⟩,⟨8,1181889784410593567753,⟨79,38,23,223,55,96,196,128,77⟩⟩]⟩
theorem node811 : UpperPrefix a [3,5,4,7,0,8,2] 30 :=
  Boolean.leaf_sound a [3,5,4,7,0,8,2] 30 cert811 (by decide +kernel)

theorem node812 : UpperPrefix a [3,5,4,7,0,8] 30 :=
  branch_upper a [3,5,4,7,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,4,7,0,8,0] 30 (by decide +kernel))
  node810
  node811
  (invalid_upper a [3,5,4,7,0,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,0,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,0,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,0,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,0,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,0,8,8] 30 (by decide +kernel)))

theorem node813 : UpperPrefix a [3,5,4,7,0] 30 :=
  branch_upper a [3,5,4,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,4,7,0,0] 30 (by decide +kernel))
  node808
  node809
  (invalid_upper a [3,5,4,7,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,0,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,0,7] 30 (by decide +kernel))
  node812)

def cert814 : Leaf := ⟨⟨148,153,138,68,0,156,284,92,212⟩,[(4,1)],[(5,1,4),(1,4,2),(0,5,1)],⟨11,38,21,152,50,97,452,452,332⟩,⟨11,38,21,152,50,97,192,384,264⟩,[⟨8,1181747927765456053353,⟨31,55,23,159,55,127,255,128,13⟩⟩,⟨6,1210106412364683552252937,⟨31,54,23,159,54,55,128,384,269⟩⟩]⟩
theorem node814 : UpperPrefix a [3,5,4,7,1,0] 30 :=
  Boolean.leaf_sound a [3,5,4,7,1,0] 30 cert814 (by decide +kernel)

def cert815 : Local := ⟨⟨464,0,458,321,0,409,281,89,209⟩,[(1,5),(4,1)],[(5,1,4),(1,4,2),(2,5,1),(2,5,4)]⟩
theorem node815 : UpperPrefix a [3,5,4,7,1,2] 30 :=
  local_sound a [3,5,4,7,1,2] 30 cert815 (by decide +kernel)

def cert816 : Leaf := ⟨⟨388,393,394,261,0,141,268,9,197⟩,[(4,1)],[(5,1,4),(1,4,2)],⟨11,38,21,152,50,352,193,388,328⟩,⟨11,38,21,152,50,352,193,388,264⟩,[⟨4,1252645989509504047320073,⟨363,230,487,491,34,352,483,486,361⟩⟩,⟨6,1212762743511304443290687,⟨31,191,31,159,191,447,133,389,397⟩⟩]⟩
theorem node816 : UpperPrefix a [3,5,4,7,1,8,0,2] 30 :=
  Boolean.leaf_sound a [3,5,4,7,1,8,0,2] 30 cert816 (by decide +kernel)

def cert817 : Local := ⟨⟨468,473,458,325,0,0,284,0,213⟩,[(4,1),(5,7),(7,5)],[(5,1,4),(1,4,2)]⟩
theorem node817 : UpperPrefix a [3,5,4,7,1,8,0,6] 30 :=
  local_sound a [3,5,4,7,1,8,0,6] 30 cert817 (by decide +kernel)

theorem node818 : UpperPrefix a [3,5,4,7,1,8,0] 30 :=
  branch_upper a [3,5,4,7,1,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,4,7,1,8,0,0] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,1,8,0,1] 30 (by decide +kernel))
  node816
  (invalid_upper a [3,5,4,7,1,8,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,1,8,0,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,1,8,0,5] 30 (by decide +kernel))
  node817
  (invalid_upper a [3,5,4,7,1,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,1,8,0,8] 30 (by decide +kernel)))

def cert819 : Leaf := ⟨⟨468,457,2,325,0,141,265,77,197⟩,[(4,1)],[(5,1,4),(1,4,2)],⟨11,38,21,152,50,352,196,449,329⟩,⟨11,38,21,152,50,352,196,384,264⟩,[⟨4,1214876156888119010954241,⟨491,230,487,136,98,354,230,384,264⟩⟩,⟨3,1210107565283988051592193,⟨23,54,21,144,50,352,196,384,256⟩⟩,⟨6,1210106412362484518487041,⟨31,54,21,152,50,288,132,384,264⟩⟩,⟨7,1208926973663271714030593,⟨31,54,21,24,50,352,68,256,264⟩⟩,⟨8,1181745669359950627841,⟨31,54,21,152,50,96,196,128,8⟩⟩]⟩
theorem node819 : UpperPrefix a [3,5,4,7,1,8,2] 30 :=
  Boolean.leaf_sound a [3,5,4,7,1,8,2] 30 cert819 (by decide +kernel)

theorem node820 : UpperPrefix a [3,5,4,7,1,8] 30 :=
  branch_upper a [3,5,4,7,1,8] 30 (by decide) (fin9_cases _
  node818
  (invalid_upper a [3,5,4,7,1,8,1] 30 (by decide +kernel))
  node819
  (invalid_upper a [3,5,4,7,1,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,1,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,1,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,1,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,1,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,1,8,8] 30 (by decide +kernel)))

theorem node821 : UpperPrefix a [3,5,4,7,1] 30 :=
  branch_upper a [3,5,4,7,1] 30 (by decide) (fin9_cases _
  node814
  (invalid_upper a [3,5,4,7,1,1] 30 (by decide +kernel))
  node815
  (invalid_upper a [3,5,4,7,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,1,7] 30 (by decide +kernel))
  node820)

def cert822 : Leaf := ⟨⟨448,0,490,323,0,395,267,75,195⟩,[(1,4),(4,1)],[],⟨11,38,21,152,52,355,451,451,331⟩,⟨11,38,21,152,52,96,192,384,264⟩,[⟨2,1224302388997320366621699,⟨491,491,505,152,56,96,192,384,264⟩⟩,⟨4,1252729002109635553930249,⟨491,230,487,491,230,96,192,384,489⟩⟩,⟨5,1224302387765867344561155,⟨459,463,477,152,28,64,192,384,264⟩⟩]⟩
theorem node822 : UpperPrefix a [3,5,4,7,2] 30 :=
  Boolean.leaf_sound a [3,5,4,7,2] 30 cert822 (by decide +kernel)

def cert823 : Leaf := ⟨⟨52,17,34,38,0,158,318,62,54⟩,[(4,5)],[(6,4,4),(0,5,1)],⟨11,38,21,152,112,97,454,390,270⟩,⟨11,38,21,152,112,97,192,384,264⟩,[⟨8,1181748490577970265465,⟨15,55,55,191,127,127,255,129,15⟩⟩,⟨7,1251428272011160115504137,⟨271,54,279,287,118,375,64,256,269⟩⟩,⟨3,1210107565286049644045313,⟨3,54,23,146,118,119,192,384,256⟩⟩]⟩
theorem node823 : UpperPrefix a [3,5,4,7,6,0] 30 :=
  Boolean.leaf_sound a [3,5,4,7,6,0] 30 cert823 (by decide +kernel)

def cert824 : Leaf := ⟨⟨148,153,168,5,0,157,285,29,149⟩,[(4,5)],[(6,4,4)],⟨11,38,21,152,112,98,453,389,269⟩,⟨11,38,21,152,112,98,192,384,264⟩,[⟨1,1233765604632714135470081,⟨477,508,477,152,112,120,192,384,264⟩⟩,⟨5,1238497211373782372975619,⟨459,463,477,152,80,451,192,384,264⟩⟩,⟨8,1181748490577970265465,⟨15,55,55,191,127,127,255,129,15⟩⟩]⟩
theorem node824 : UpperPrefix a [3,5,4,7,6,1] 30 :=
  Boolean.leaf_sound a [3,5,4,7,6,1] 30 cert824 (by decide +kernel)

def cert825 : Leaf := ⟨⟨400,0,426,259,0,411,283,27,147⟩,[(1,5),(4,5)],[(6,4,4),(2,5,1)],⟨11,38,21,152,112,100,451,387,267⟩,⟨11,38,21,152,112,100,192,384,264⟩,[⟨5,1224302387765867344561155,⟨459,463,477,152,80,76,192,384,264⟩⟩]⟩
theorem node825 : UpperPrefix a [3,5,4,7,6,2] 30 :=
  Boolean.leaf_sound a [3,5,4,7,6,2] 30 cert825 (by decide +kernel)

def cert826 : Leaf := ⟨⟨276,281,296,261,0,29,286,29,21⟩,[(4,5)],[(6,4,4),(1,7,6)],⟨11,38,21,152,112,352,193,386,268⟩,⟨11,38,21,152,112,352,193,386,264⟩,[⟨5,1238471865115079531824131,⟨459,463,477,216,80,320,193,451,264⟩⟩,⟨7,1251428274267357984121865,⟨271,54,279,287,118,374,375,258,269⟩⟩]⟩
theorem node826 : UpperPrefix a [3,5,4,7,6,8,0,1] 30 :=
  Boolean.leaf_sound a [3,5,4,7,6,8,0,1] 30 cert826 (by decide +kernel)

def cert827 : Leaf := ⟨⟨260,265,298,263,0,15,270,11,7⟩,[(4,5)],[(6,4,4)],⟨11,38,21,152,112,352,193,388,266⟩,⟨11,38,21,152,112,352,193,388,264⟩,[⟨4,1252645989509504047320073,⟨363,230,487,491,96,352,483,486,361⟩⟩,⟨5,1224330129939571946816515,⟨459,463,477,152,80,320,449,460,264⟩⟩,⟨7,1251428274267357984121865,⟨271,54,279,287,118,374,375,260,269⟩⟩]⟩
theorem node827 : UpperPrefix a [3,5,4,7,6,8,0,2] 30 :=
  Boolean.leaf_sound a [3,5,4,7,6,8,0,2] 30 cert827 (by decide +kernel)

theorem node828 : UpperPrefix a [3,5,4,7,6,8,0] 30 :=
  branch_upper a [3,5,4,7,6,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,4,7,6,8,0,0] 30 (by decide +kernel))
  node826
  node827
  (invalid_upper a [3,5,4,7,6,8,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,6,8,0,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,6,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,6,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,6,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,6,8,0,8] 30 (by decide +kernel)))

def cert829 : Leaf := ⟨⟨404,401,418,261,0,149,277,28,149⟩,[(4,5)],[(3,0,7),(6,4,4)],⟨11,38,21,152,112,352,194,385,268⟩,⟨11,38,21,152,112,352,194,385,264⟩,[⟨5,1239096676512984552440835,⟨459,463,477,152,216,448,451,449,264⟩⟩,⟨1,1238487883299660109971457,⟨393,444,413,152,120,376,504,385,264⟩⟩]⟩
theorem node829 : UpperPrefix a [3,5,4,7,6,8,1,0] 30 :=
  Boolean.leaf_sound a [3,5,4,7,6,8,1,0] 30 cert829 (by decide +kernel)

def cert830 : Leaf := ⟨⟨384,393,426,259,0,139,269,11,131⟩,[(4,5)],[(6,4,4),(2,7,6)],⟨11,38,21,152,112,352,194,388,265⟩,⟨11,38,21,152,112,352,194,388,264⟩,[⟨4,1252648329129510466292745,⟨363,230,487,491,96,352,226,486,361⟩⟩,⟨5,1243219523813456489743363,⟨459,463,477,152,80,320,451,396,264⟩⟩]⟩
theorem node830 : UpperPrefix a [3,5,4,7,6,8,1,2] 30 :=
  Boolean.leaf_sound a [3,5,4,7,6,8,1,2] 30 cert830 (by decide +kernel)

theorem node831 : UpperPrefix a [3,5,4,7,6,8,1] 30 :=
  branch_upper a [3,5,4,7,6,8,1] 30 (by decide) (fin9_cases _
  node829
  (invalid_upper a [3,5,4,7,6,8,1,1] 30 (by decide +kernel))
  node830
  (invalid_upper a [3,5,4,7,6,8,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,6,8,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,6,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,6,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,6,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,7,6,8,1,8] 30 (by decide +kernel)))

#print axioms node831
end Delivery.FiniteExclusion.Sharp3x6

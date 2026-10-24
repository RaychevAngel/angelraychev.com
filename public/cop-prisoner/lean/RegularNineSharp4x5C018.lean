import RegularNineSharp4x5Base
import RegularNineSharp4x5C000
import RegularNineSharp4x5C002
import RegularNineSharp4x5C004
import RegularNineSharp4x5C006
import RegularNineSharp4x5C007
import RegularNineSharp4x5C009
import RegularNineSharp4x5C011
import RegularNineSharp4x5C014
import RegularNineSharp4x5C015
import RegularNineSharp4x5C016
import RegularNineSharp4x5C017
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp4x5
open Bounds BoundTreeRows Extremal
def cert1152 : Leaf := ⟨⟨160,145,147,18,0,150,283,27,139⟩,[(4,5)],[(5,1,0),(8,2,6),(6,4,4)],⟨19,38,268,137,112,97,196,394,282⟩,⟨19,38,268,137,112,97,196,384,272⟩,[⟨2,1224302334850774905914371,⟨411,443,264,393,120,505,192,384,272⟩⟩,⟨3,1210107568105197449282675,⟨51,55,260,129,115,115,247,384,305⟩⟩]⟩
theorem node1152 : UpperPrefix a [4,5,8,7,6,0,2] 30 :=
  Boolean.leaf_sound a [4,5,8,7,6,0,2] 30 cert1152 (by decide +kernel)

def cert1153 : Local := ⟨⟨300,281,19,278,0,286,0,31,15⟩,[(4,5),(6,3)],[(5,1,0),(7,3,6),(6,4,4)]⟩
theorem node1153 : UpperPrefix a [4,5,8,7,6,0,3] 30 :=
  local_sound a [4,5,8,7,6,0,3] 30 cert1153 (by decide +kernel)

theorem node1154 : UpperPrefix a [4,5,8,7,6,0] 30 :=
  branch_upper a [4,5,8,7,6,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [4,5,8,7,6,0,0] 30 (by decide +kernel))
  node1151
  node1152
  node1153
  (invalid_upper a [4,5,8,7,6,0,4] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,7,6,0,5] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,7,6,0,6] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,7,6,0,7] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,7,6,0,8] 30 (by decide +kernel)))

def cert1155 : Local := ⟨⟨428,409,147,0,0,413,0,31,143⟩,[(3,6),(4,5),(6,3)],[(5,1,0),(6,4,4)]⟩
theorem node1155 : UpperPrefix a [4,5,8,7,6,1,0] 30 :=
  local_sound a [4,5,8,7,6,1,0] 30 cert1155 (by decide +kernel)

def cert1156 : Leaf := ⟨⟨168,153,145,16,0,157,281,25,137⟩,[(4,5)],[(5,1,0),(8,2,6),(6,4,4),(2,6,5)],⟨19,38,268,137,112,98,196,393,281⟩,⟨19,38,268,137,112,98,196,384,272⟩,[⟨1,1214913176304570246365185,⟨477,116,460,461,112,112,196,384,272⟩⟩]⟩
theorem node1156 : UpperPrefix a [4,5,8,7,6,1,2] 30 :=
  Boolean.leaf_sound a [4,5,8,7,6,1,2] 30 cert1156 (by decide +kernel)

def cert1157 : Local := ⟨⟨300,281,19,278,0,285,0,31,15⟩,[(4,5),(6,3)],[(5,1,0),(7,3,6),(6,4,4)]⟩
theorem node1157 : UpperPrefix a [4,5,8,7,6,1,3] 30 :=
  local_sound a [4,5,8,7,6,1,3] 30 cert1157 (by decide +kernel)

theorem node1158 : UpperPrefix a [4,5,8,7,6,1] 30 :=
  branch_upper a [4,5,8,7,6,1] 30 (by decide) (fin9_cases _
  node1155
  (invalid_upper a [4,5,8,7,6,1,1] 30 (by decide +kernel))
  node1156
  node1157
  (invalid_upper a [4,5,8,7,6,1,4] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,7,6,1,5] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,7,6,1,6] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,7,6,1,7] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,7,6,1,8] 30 (by decide +kernel)))

def cert1159 : Local := ⟨⟨424,0,147,274,0,411,283,27,139⟩,[(1,5),(4,5)],[(5,1,0),(6,4,4),(2,5,1)]⟩
theorem node1159 : UpperPrefix a [4,5,8,7,6,2] 30 :=
  local_sound a [4,5,8,7,6,2] 30 cert1159 (by decide +kernel)

def cert1160 : Leaf := ⟨⟨32,281,19,278,0,407,279,23,7⟩,[(4,5)],[(5,1,0),(7,3,5),(6,4,4),(3,5,1)],⟨19,38,268,137,112,104,199,391,279⟩,⟨19,38,268,137,112,104,192,384,272⟩,[⟨2,1210107565286050708325379,⟨19,51,264,137,112,120,192,384,272⟩⟩,⟨8,1181745671421534667779,⟨19,55,12,137,112,120,192,128,16⟩⟩]⟩
theorem node1160 : UpperPrefix a [4,5,8,7,6,3] 30 :=
  Boolean.leaf_sound a [4,5,8,7,6,3] 30 cert1160 (by decide +kernel)

theorem node1161 : UpperPrefix a [4,5,8,7,6] 30 :=
  branch_upper a [4,5,8,7,6] 30 (by decide) (fin9_cases _
  node1154
  node1158
  node1159
  node1160
  (invalid_upper a [4,5,8,7,6,4] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,7,6,5] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,7,6,6] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,7,6,7] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,7,6,8] 30 (by decide +kernel)))

theorem node1162 : UpperPrefix a [4,5,8,7] 30 :=
  branch_upper a [4,5,8,7] 30 (by decide) (fin9_cases _
  node1133
  node1137
  node1138
  node1150
  (invalid_upper a [4,5,8,7,4] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,7,5] 30 (by decide +kernel))
  node1161
  (invalid_upper a [4,5,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,7,8] 30 (by decide +kernel)))

theorem node1163 : UpperPrefix a [4,5,8] 30 :=
  branch_upper a [4,5,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [4,5,8,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut5 [4,5,8,1] [2,4,5,8] 30 (by decide +kernel) node185)
  (PrefixConjugacy.upper aut5 [4,5,8,2] [3,4,5,8] 30 (by decide +kernel) node625)
  (invalid_upper a [4,5,8,3] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,4] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,5] 30 (by decide +kernel))
  node1129
  node1162
  (invalid_upper a [4,5,8,8] 30 (by decide +kernel)))

theorem node1164 : UpperPrefix a [4,5] 30 :=
  branch_upper a [4,5] 30 (by decide) (fin9_cases _
  node1006
  node1007
  (invalid_upper a [4,5,2] 30 (by decide +kernel))
  (invalid_upper a [4,5,3] 30 (by decide +kernel))
  (invalid_upper a [4,5,4] 30 (by decide +kernel))
  (invalid_upper a [4,5,5] 30 (by decide +kernel))
  node1042
  node1084
  node1163)

theorem node1165 : UpperPrefix a [4,6,0] 30 :=
  branch_upper a [4,6,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [4,6,0,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut10 [4,6,0,1] [2,3,4,6] 30 (by decide +kernel) node61)
  (PrefixConjugacy.upper aut10 [4,6,0,2] [2,0,4,6] 30 (by decide +kernel) node25)
  (invalid_upper a [4,6,0,3] 30 (by decide +kernel))
  (invalid_upper a [4,6,0,4] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut14 [4,6,0,5] [2,4,8,5] 30 (by decide +kernel) node391)
  (invalid_upper a [4,6,0,6] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut12 [4,6,0,7] [2,4,6,8] 30 (by decide +kernel) node270)
  (PrefixConjugacy.upper aut11 [4,6,0,8] [2,4,5,7] 30 (by decide +kernel) node173))

theorem node1166 : UpperPrefix a [4,6,1] 30 :=
  branch_upper a [4,6,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [4,6,1,0] 30 (by decide +kernel))
  (invalid_upper a [4,6,1,1] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut10 [4,6,1,2] [3,0,4,6] 30 (by decide +kernel) node472)
  (invalid_upper a [4,6,1,3] 30 (by decide +kernel))
  (invalid_upper a [4,6,1,4] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut14 [4,6,1,5] [3,4,8,5] 30 (by decide +kernel) node908)
  (invalid_upper a [4,6,1,6] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut12 [4,6,1,7] [3,4,6,8] 30 (by decide +kernel) node747)
  (PrefixConjugacy.upper aut11 [4,6,1,8] [3,4,5,7] 30 (by decide +kernel) node596))

def cert1167 : Leaf := ⟨⟨40,185,145,52,10,0,317,61,45⟩,[(5,1)],[(6,1,5),(1,5,4)],⟨19,70,44,137,49,98,460,396,284⟩,⟨19,70,44,137,49,98,192,384,272⟩,[⟨8,1181747998477791052919,⟨55,127,63,153,55,127,255,128,17⟩⟩,⟨7,1227816439667661659440163,⟨51,375,317,25,49,115,64,256,272⟩⟩,⟨2,1210107565356900488840227,⟨51,115,57,153,49,115,192,384,272⟩⟩]⟩
theorem node1167 : UpperPrefix a [4,6,5,7,0,1] 30 :=
  Boolean.leaf_sound a [4,6,5,7,0,1] 30 cert1167 (by decide +kernel)

def cert1168 : Leaf := ⟨⟨204,0,147,18,206,0,283,27,139⟩,[(1,5),(5,1)],[],⟨19,70,44,137,49,100,458,394,282⟩,⟨19,70,44,137,49,100,192,384,272⟩,[⟨5,1290544897936173581747217,⟨475,70,14,457,475,70,192,392,473⟩⟩,⟨2,1214839173153158976242689,⟨475,66,40,457,505,96,192,384,280⟩⟩,⟨6,1214838002217255865156609,⟨415,6,44,393,445,36,128,384,284⟩⟩,⟨8,1181747998477791052919,⟨55,127,63,153,55,127,255,128,17⟩⟩]⟩
theorem node1168 : UpperPrefix a [4,6,5,7,0,2] 30 :=
  Boolean.leaf_sound a [4,6,5,7,0,2] 30 cert1168 (by decide +kernel)

def cert1169 : Leaf := ⟨⟨100,48,0,54,70,151,310,54,38⟩,[(2,5)],[(7,3,5),(3,5,2)],⟨19,70,44,137,49,104,454,390,278⟩,⟨19,70,44,137,49,104,192,384,272⟩,[⟨8,1181747998477791052919,⟨55,127,63,153,55,127,255,128,17⟩⟩,⟨0,1285813291192731846075392,⟨466,70,46,136,502,110,192,384,466⟩⟩,⟨6,1214838002217255873545217,⟨415,6,44,393,445,44,128,384,284⟩⟩]⟩
theorem node1169 : UpperPrefix a [4,6,5,7,0,3] 30 :=
  Boolean.leaf_sound a [4,6,5,7,0,3] 30 cert1169 (by decide +kernel)

def cert1170 : Leaf := ⟨⟨224,160,194,98,194,130,36,107,235⟩,[],[(2,7,6)],⟨19,70,44,137,49,352,194,388,280⟩,⟨19,70,44,137,49,352,194,388,272⟩,[⟨4,1212771908333105663147521,⟨79,70,238,239,239,486,226,486,494⟩⟩,⟨8,1184195629919480401079,⟨19,95,127,203,55,127,203,223,17⟩⟩,⟨3,1210110019761865325874383,⟨19,87,119,243,49,369,243,503,272⟩⟩,⟨0,1210110019745648605207552,⟨18,70,110,238,48,352,226,486,272⟩⟩]⟩
theorem node1170 : UpperPrefix a [4,6,5,7,0,8,1,2] 30 :=
  Boolean.leaf_sound a [4,6,5,7,0,8,1,2] 30 cert1170 (by decide +kernel)

def cert1171 : Leaf := ⟨⟨228,168,128,52,198,134,300,53,165⟩,[],[],⟨19,70,44,137,49,352,194,392,276⟩,⟨19,70,44,137,49,352,194,392,272⟩,[⟨8,1181745671705010914359,⟨19,95,63,137,55,127,203,136,17⟩⟩,⟨0,1210110019745648638794752,⟨18,70,110,238,48,354,230,494,272⟩⟩,⟨1,1292979563034994132647937,⟨413,68,172,393,445,480,192,392,412⟩⟩,⟨3,1238441766510040269718595,⟨307,375,308,145,49,369,499,384,272⟩⟩,⟨4,1210110019744549127166977,⟨3,70,110,239,33,354,230,494,256⟩⟩,⟨6,1292978410113489525801985,⟨415,6,172,393,445,416,130,392,412⟩⟩]⟩
theorem node1171 : UpperPrefix a [4,6,5,7,0,8,1,3] 30 :=
  Boolean.leaf_sound a [4,6,5,7,0,8,1,3] 30 cert1171 (by decide +kernel)

theorem node1172 : UpperPrefix a [4,6,5,7,0,8,1] 30 :=
  branch_upper a [4,6,5,7,0,8,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [4,6,5,7,0,8,1,0] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,0,8,1,1] 30 (by decide +kernel))
  node1170
  node1171
  (invalid_upper a [4,6,5,7,0,8,1,4] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,0,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,0,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,0,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,0,8,1,8] 30 (by decide +kernel)))

def cert1173 : Leaf := ⟨⟨96,0,147,18,66,155,315,27,139⟩,[(1,6)],[(2,6,1)],⟨19,70,44,137,49,352,196,394,282⟩,⟨19,70,44,137,49,352,196,384,272⟩,[⟨6,1214838002217255865156609,⟨415,6,44,393,445,288,132,384,284⟩⟩,⟨8,1181745671705010947191,⟨19,95,63,137,55,127,223,128,17⟩⟩,⟨5,1214839154012860560999425,⟨411,70,12,393,409,322,198,384,280⟩⟩,⟨3,1210107565286324513571939,⟨19,87,53,129,49,371,215,384,272⟩⟩,⟨7,1208926973665608176010339,⟨19,87,61,9,49,371,87,256,272⟩⟩]⟩
theorem node1173 : UpperPrefix a [4,6,5,7,0,8,2] 30 :=
  Boolean.leaf_sound a [4,6,5,7,0,8,2] 30 cert1173 (by decide +kernel)

def cert1174 : Leaf := ⟨⟨356,297,259,294,326,7,0,39,39⟩,[(6,3)],[(7,3,6),(3,6,1)],⟨19,70,44,137,49,352,200,390,278⟩,⟨19,70,44,137,49,352,200,384,272⟩,[⟨4,1212769026029344162840065,⟨79,70,238,239,239,486,238,486,494⟩⟩,⟨6,1214838002217255865156609,⟨415,6,44,393,445,288,136,384,284⟩⟩]⟩
theorem node1174 : UpperPrefix a [4,6,5,7,0,8,3] 30 :=
  Boolean.leaf_sound a [4,6,5,7,0,8,3] 30 cert1174 (by decide +kernel)

theorem node1175 : UpperPrefix a [4,6,5,7,0,8] 30 :=
  branch_upper a [4,6,5,7,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [4,6,5,7,0,8,0] 30 (by decide +kernel))
  node1172
  node1173
  node1174
  (invalid_upper a [4,6,5,7,0,8,4] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,0,8,5] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,0,8,6] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,0,8,7] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,0,8,8] 30 (by decide +kernel)))

theorem node1176 : UpperPrefix a [4,6,5,7,0] 30 :=
  branch_upper a [4,6,5,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [4,6,5,7,0,0] 30 (by decide +kernel))
  node1167
  node1168
  node1169
  (invalid_upper a [4,6,5,7,0,4] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,0,5] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,0,7] 30 (by decide +kernel))
  node1175)

def cert1177 : Leaf := ⟨⟨0,184,145,52,200,152,316,60,172⟩,[(0,4)],[(6,1,4),(1,4,0),(0,5,2)],⟨19,70,44,137,50,97,460,396,284⟩,⟨19,70,44,137,50,97,192,384,272⟩,[⟨8,1181747998477791052919,⟨55,127,63,153,55,127,255,128,17⟩⟩,⟨2,1210107565354426587677715,⟨51,115,40,153,51,113,192,384,273⟩⟩]⟩
theorem node1177 : UpperPrefix a [4,6,5,7,1,0] 30 :=
  Boolean.leaf_sound a [4,6,5,7,1,0] 30 cert1177 (by decide +kernel)

def cert1178 : Local := ⟨⟨0,0,401,304,461,0,313,57,169⟩,[(0,4),(1,5),(5,1)],[(6,1,4),(1,4,0),(2,5,4)]⟩
theorem node1178 : UpperPrefix a [4,6,5,7,1,2] 30 :=
  local_sound a [4,6,5,7,1,2] 30 cert1178 (by decide +kernel)

def cert1179 : Local := ⟨⟨0,305,0,308,325,405,309,53,37⟩,[(0,4),(2,5)],[(6,1,4),(7,3,5),(1,4,0),(3,5,2)]⟩
theorem node1179 : UpperPrefix a [4,6,5,7,1,3] 30 :=
  local_sound a [4,6,5,7,1,3] 30 cert1179 (by decide +kernel)

def cert1180 : Leaf := ⟨⟨0,425,385,0,461,157,0,45,173⟩,[(0,4),(3,6),(6,3)],[(6,1,4),(1,4,0)],⟨19,70,44,137,50,352,193,396,284⟩,⟨19,70,44,137,50,352,193,384,272⟩,[⟨4,1210402857303128201513985,⟨3,78,238,201,166,494,201,384,256⟩⟩]⟩
theorem node1180 : UpperPrefix a [4,6,5,7,1,8,0] 30 :=
  Boolean.leaf_sound a [4,6,5,7,1,8,0] 30 cert1180 (by decide +kernel)

def cert1181 : Local := ⟨⟨0,0,401,304,457,153,313,57,169⟩,[(0,4),(1,6)],[(6,1,4),(1,4,0),(2,6,1)]⟩
theorem node1181 : UpperPrefix a [4,6,5,7,1,8,2] 30 :=
  local_sound a [4,6,5,7,1,8,2] 30 cert1181 (by decide +kernel)

def cert1182 : Local := ⟨⟨0,313,273,308,325,21,0,53,37⟩,[(0,4),(6,3)],[(6,1,4),(7,3,6),(1,4,0),(3,6,1)]⟩
theorem node1182 : UpperPrefix a [4,6,5,7,1,8,3] 30 :=
  local_sound a [4,6,5,7,1,8,3] 30 cert1182 (by decide +kernel)

theorem node1183 : UpperPrefix a [4,6,5,7,1,8] 30 :=
  branch_upper a [4,6,5,7,1,8] 30 (by decide) (fin9_cases _
  node1180
  (invalid_upper a [4,6,5,7,1,8,1] 30 (by decide +kernel))
  node1181
  node1182
  (invalid_upper a [4,6,5,7,1,8,4] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,1,8,5] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,1,8,6] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,1,8,7] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,1,8,8] 30 (by decide +kernel)))

theorem node1184 : UpperPrefix a [4,6,5,7,1] 30 :=
  branch_upper a [4,6,5,7,1] 30 (by decide) (fin9_cases _
  node1177
  (invalid_upper a [4,6,5,7,1,1] 30 (by decide +kernel))
  node1178
  node1179
  (invalid_upper a [4,6,5,7,1,4] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,1,7] 30 (by decide +kernel))
  node1183)

def cert1185 : Leaf := ⟨⟨140,152,147,18,0,154,282,26,138⟩,[(4,2)],[(5,2,4),(2,4,0),(0,5,2)],⟨19,70,44,137,52,97,458,394,282⟩,⟨19,70,44,137,52,97,192,384,272⟩,[⟨6,1224301181929545190605827,⟨415,415,60,393,60,445,128,384,276⟩⟩,⟨8,1181747998477791052919,⟨55,127,63,153,55,127,255,128,17⟩⟩]⟩
theorem node1185 : UpperPrefix a [4,6,5,7,2,0] 30 :=
  Boolean.leaf_sound a [4,6,5,7,2,0] 30 cert1185 (by decide +kernel)

def cert1186 : Local := ⟨⟨396,409,403,274,0,0,283,27,139⟩,[(4,2),(5,1)],[(6,1,5),(5,2,4),(2,4,0)]⟩
theorem node1186 : UpperPrefix a [4,6,5,7,2,1] 30 :=
  local_sound a [4,6,5,7,2,1] 30 cert1186 (by decide +kernel)

def cert1187 : Local := ⟨⟨324,273,0,338,0,403,275,83,67⟩,[(2,5),(4,2)],[(5,2,4),(7,3,5),(2,4,0),(3,5,2),(3,5,4)]⟩
theorem node1187 : UpperPrefix a [4,6,5,7,2,3] 30 :=
  local_sound a [4,6,5,7,2,3] 30 cert1187 (by decide +kernel)

def cert1188 : Leaf := ⟨⟨396,409,403,0,0,155,0,27,139⟩,[(3,6),(4,2),(6,3)],[(5,2,4),(2,4,0)],⟨19,70,44,137,52,352,193,394,282⟩,⟨19,70,44,137,52,352,193,384,272⟩,[⟨6,1224301181929549481378819,⟨411,415,60,393,52,316,393,384,272⟩⟩]⟩
theorem node1188 : UpperPrefix a [4,6,5,7,2,8,0] 30 :=
  Boolean.leaf_sound a [4,6,5,7,2,8,0] 30 cert1188 (by decide +kernel)

def cert1189 : Leaf := ⟨⟨140,153,147,18,0,155,281,27,139⟩,[(4,2)],[(5,2,4),(2,4,0)],⟨19,70,44,137,52,352,194,393,281⟩,⟨19,70,44,137,52,352,194,384,272⟩,[⟨6,1224965264716203025236995,⟨411,415,188,393,52,444,395,384,272⟩⟩,⟨8,1181745671705010914359,⟨19,95,63,137,55,127,203,128,17⟩⟩]⟩
theorem node1189 : UpperPrefix a [4,6,5,7,2,8,1] 30 :=
  Boolean.leaf_sound a [4,6,5,7,2,8,1] 30 cert1189 (by decide +kernel)

def cert1190 : Local := ⟨⟨324,281,339,338,0,19,0,83,67⟩,[(4,2),(6,3)],[(5,2,4),(7,3,6),(2,4,0),(3,6,1)]⟩
theorem node1190 : UpperPrefix a [4,6,5,7,2,8,3] 30 :=
  local_sound a [4,6,5,7,2,8,3] 30 cert1190 (by decide +kernel)

theorem node1191 : UpperPrefix a [4,6,5,7,2,8] 30 :=
  branch_upper a [4,6,5,7,2,8] 30 (by decide) (fin9_cases _
  node1188
  node1189
  (invalid_upper a [4,6,5,7,2,8,2] 30 (by decide +kernel))
  node1190
  (invalid_upper a [4,6,5,7,2,8,4] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,2,8,5] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,2,8,6] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,2,8,7] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,2,8,8] 30 (by decide +kernel)))

theorem node1192 : UpperPrefix a [4,6,5,7,2] 30 :=
  branch_upper a [4,6,5,7,2] 30 (by decide) (fin9_cases _
  node1185
  node1186
  (invalid_upper a [4,6,5,7,2,2] 30 (by decide +kernel))
  node1187
  (invalid_upper a [4,6,5,7,2,4] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,2,5] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,2,6] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,2,7] 30 (by decide +kernel))
  node1191)

def cert1193 : Leaf := ⟨⟨172,168,0,54,0,158,302,46,174⟩,[(2,4),(4,2)],[(0,5,2),(0,5,4)],⟨19,70,44,137,56,97,454,390,278⟩,⟨19,70,44,137,56,97,192,384,272⟩,[⟨6,1224301181929545190605827,⟨415,415,60,393,60,445,128,384,276⟩⟩,⟨8,1181747998409075770487,⟨55,127,63,137,63,127,255,128,21⟩⟩,⟨4,1212473360210205428810753,⟨7,70,44,137,44,97,192,450,454⟩⟩]⟩
theorem node1193 : UpperPrefix a [4,6,5,7,3,0] 30 :=
  Boolean.leaf_sound a [4,6,5,7,3,0] 30 cert1193 (by decide +kernel)

def cert1194 : Leaf := ⟨⟨172,185,0,52,0,0,317,61,173⟩,[(2,4),(4,2),(5,1)],[(6,1,5)],⟨19,70,44,137,56,98,453,389,277⟩,⟨19,70,44,137,56,98,192,384,272⟩,[⟨1,1214839173153431711907841,⟨477,84,60,457,60,96,192,384,276⟩⟩,⟨8,1181747998409075770487,⟨55,127,63,137,63,127,255,128,21⟩⟩]⟩
theorem node1194 : UpperPrefix a [4,6,5,7,3,1] 30 :=
  Boolean.leaf_sound a [4,6,5,7,3,1] 30 cert1194 (by decide +kernel)

def cert1195 : Leaf := ⟨⟨488,0,0,370,0,0,315,123,235⟩,[(1,5),(2,4),(4,2),(5,1)],[],⟨19,70,44,137,56,100,451,387,275⟩,⟨19,70,44,137,56,100,192,384,272⟩,[⟨2,1224302388892041994044419,⟨475,475,56,457,56,112,192,384,272⟩⟩]⟩
theorem node1195 : UpperPrefix a [4,6,5,7,3,2] 30 :=
  Boolean.leaf_sound a [4,6,5,7,3,2] 30 cert1195 (by decide +kernel)

def cert1196 : Leaf := ⟨⟨492,441,0,0,0,158,0,126,238⟩,[(2,4),(3,6),(4,2),(6,3)],[],⟨19,70,44,137,56,352,193,390,278⟩,⟨19,70,44,137,56,352,193,384,272⟩,[⟨0,1224302337171014626051072,⟨438,502,60,392,60,352,480,384,276⟩⟩]⟩
theorem node1196 : UpperPrefix a [4,6,5,7,3,8,0] 30 :=
  Boolean.leaf_sound a [4,6,5,7,3,8,0] 30 cert1196 (by decide +kernel)

def cert1197 : Leaf := ⟨⟨40,185,0,48,0,31,317,61,45⟩,[(2,4),(4,2)],[],⟨19,70,44,137,56,352,194,389,277⟩,⟨19,70,44,137,56,352,194,384,272⟩,[⟨6,1224301181929549485573123,⟨415,415,60,393,60,316,395,384,276⟩⟩,⟨1,1214839155139033202425857,⟨413,84,60,393,60,352,192,384,276⟩⟩,⟨7,1223094075434186650420227,⟨311,375,60,265,60,352,355,256,276⟩⟩,⟨8,1181745671705015108663,⟨23,95,63,137,63,127,203,128,21⟩⟩,⟨2,1210107565286334176166915,⟨19,91,56,137,56,376,203,384,272⟩⟩]⟩
theorem node1197 : UpperPrefix a [4,6,5,7,3,8,1] 30 :=
  Boolean.leaf_sound a [4,6,5,7,3,8,1] 30 cert1197 (by decide +kernel)

def cert1198 : Leaf := ⟨⟨424,0,0,306,0,155,315,59,171⟩,[(1,6),(2,4),(4,2)],[(2,6,1)],⟨19,70,44,137,56,352,196,387,275⟩,⟨19,70,44,137,56,352,196,384,272⟩,[⟨6,1224301181927341863994371,⟨415,415,60,393,60,288,148,384,276⟩⟩]⟩
theorem node1198 : UpperPrefix a [4,6,5,7,3,8,2] 30 :=
  Boolean.leaf_sound a [4,6,5,7,3,8,2] 30 cert1198 (by decide +kernel)

theorem node1199 : UpperPrefix a [4,6,5,7,3,8] 30 :=
  branch_upper a [4,6,5,7,3,8] 30 (by decide) (fin9_cases _
  node1196
  node1197
  node1198
  (invalid_upper a [4,6,5,7,3,8,3] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,3,8,4] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,3,8,5] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,3,8,6] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,3,8,7] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,3,8,8] 30 (by decide +kernel)))

theorem node1200 : UpperPrefix a [4,6,5,7,3] 30 :=
  branch_upper a [4,6,5,7,3] 30 (by decide) (fin9_cases _
  node1193
  node1194
  node1195
  (invalid_upper a [4,6,5,7,3,3] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,3,4] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,3,5] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,3,6] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,3,7] 30 (by decide +kernel))
  node1199)

def cert1201 : Leaf := ⟨⟨300,168,129,308,12,14,44,60,44⟩,[],[(0,5,2),(1,6,5)],⟨19,70,44,137,304,97,194,396,284⟩,⟨19,70,44,137,304,97,194,384,272⟩,[⟨6,1470343854384691779994627,⟨415,415,444,393,444,445,395,384,404⟩⟩,⟨4,1210107709679415229160449,⟨3,70,110,239,288,97,194,384,256⟩⟩,⟨7,1227816441917193730393155,⟨51,375,316,9,304,97,115,256,272⟩⟩,⟨8,1181890065885566082049,⟨19,70,110,239,48,97,194,128,16⟩⟩]⟩
theorem node1201 : UpperPrefix a [4,6,5,7,8,0,1] 30 :=
  Boolean.leaf_sound a [4,6,5,7,8,0,1] 30 cert1201 (by decide +kernel)

def cert1202 : Leaf := ⟨⟨488,0,401,274,138,408,280,26,138⟩,[(1,6)],[(0,5,2),(2,6,1)],⟨19,70,44,137,304,97,196,394,282⟩,⟨19,70,44,137,304,97,196,384,272⟩,[⟨6,1214838002219457044284417,⟨415,6,60,393,316,445,132,384,276⟩⟩,⟨5,1215134373975636099238913,⟨411,70,206,393,408,459,198,384,272⟩⟩,⟨1,1210107709680514740781057,⟨17,68,108,237,304,97,196,384,272⟩⟩]⟩
theorem node1202 : UpperPrefix a [4,6,5,7,8,0,2] 30 :=
  Boolean.leaf_sound a [4,6,5,7,8,0,2] 30 cert1202 (by decide +kernel)

def cert1203 : Leaf := ⟨⟨356,296,323,358,70,262,0,102,102⟩,[(6,3)],[(7,3,6),(0,5,2),(3,6,1)],⟨19,70,44,137,304,97,200,390,278⟩,⟨19,70,44,137,304,97,200,384,272⟩,[⟨4,1210255301681587946839553,⟨239,70,110,239,422,111,238,384,384⟩⟩]⟩
theorem node1203 : UpperPrefix a [4,6,5,7,8,0,3] 30 :=
  Boolean.leaf_sound a [4,6,5,7,8,0,3] 30 cert1203 (by decide +kernel)

theorem node1204 : UpperPrefix a [4,6,5,7,8,0] 30 :=
  branch_upper a [4,6,5,7,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [4,6,5,7,8,0,0] 30 (by decide +kernel))
  node1201
  node1202
  node1203
  (invalid_upper a [4,6,5,7,8,0,4] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,8,0,8] 30 (by decide +kernel)))

def cert1205 : Leaf := ⟨⟨428,441,401,0,141,0,0,61,173⟩,[(3,6),(5,1),(6,3)],[(6,1,5)],⟨19,70,44,137,304,98,193,396,284⟩,⟨19,70,44,137,304,98,193,384,272⟩,[⟨1,1389908141902367904759809,⟨473,476,508,201,436,508,201,384,272⟩⟩]⟩
theorem node1205 : UpperPrefix a [4,6,5,7,8,1,0] 30 :=
  Boolean.leaf_sound a [4,6,5,7,8,1,0] 30 cert1205 (by decide +kernel)

def cert1206 : Leaf := ⟨⟨424,0,403,304,139,0,313,57,169⟩,[(1,6),(5,1)],[(6,1,5),(2,6,1),(2,6,5)],⟨19,70,44,137,304,98,196,393,281⟩,⟨19,70,44,137,304,98,196,384,272⟩,[⟨1,1214913014172647196459009,⟨409,68,236,393,304,96,196,384,272⟩⟩]⟩
theorem node1206 : UpperPrefix a [4,6,5,7,8,1,2] 30 :=
  Boolean.leaf_sound a [4,6,5,7,8,1,2] 30 cert1206 (by decide +kernel)

def cert1207 : Local := ⟨⟨292,313,275,310,7,0,0,55,39⟩,[(5,1),(6,3)],[(6,1,5),(7,3,6),(3,6,1)]⟩
theorem node1207 : UpperPrefix a [4,6,5,7,8,1,3] 30 :=
  local_sound a [4,6,5,7,8,1,3] 30 cert1207 (by decide +kernel)

theorem node1208 : UpperPrefix a [4,6,5,7,8,1] 30 :=
  branch_upper a [4,6,5,7,8,1] 30 (by decide) (fin9_cases _
  node1205
  (invalid_upper a [4,6,5,7,8,1,1] 30 (by decide +kernel))
  node1206
  node1207
  (invalid_upper a [4,6,5,7,8,1,4] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,8,1,8] 30 (by decide +kernel)))

def cert1209 : Leaf := ⟨⟨332,0,467,274,79,0,283,27,11⟩,[(1,5),(5,1)],[],⟨19,70,44,137,304,100,203,395,283⟩,⟨19,70,44,137,304,100,192,384,272⟩,[⟨5,1290544897936173581747217,⟨475,70,14,457,475,70,192,392,473⟩⟩,⟨2,1214839173153156828759041,⟨475,66,40,457,304,96,192,384,272⟩⟩,⟨6,1214838002217253713478657,⟨411,6,44,393,304,36,128,384,272⟩⟩,⟨7,1227816439667592939979831,⟨51,375,319,9,307,375,64,256,273⟩⟩]⟩
theorem node1209 : UpperPrefix a [4,6,5,7,8,2] 30 :=
  Boolean.leaf_sound a [4,6,5,7,8,2] 30 cert1209 (by decide +kernel)

def cert1210 : Local := ⟨⟨356,304,0,0,70,407,0,118,102⟩,[(2,5),(3,6),(6,3)],[(7,3,5),(3,5,2),(0,6,5)]⟩
theorem node1210 : UpperPrefix a [4,6,5,7,8,3,0] 30 :=
  local_sound a [4,6,5,7,8,3,0] 30 cert1210 (by decide +kernel)

def cert1211 : Leaf := ⟨⟨100,32,0,374,71,134,36,119,103⟩,[(2,5)],[(7,3,5),(3,5,2)],⟨19,70,44,137,304,104,194,389,277⟩,⟨19,70,44,137,304,104,194,384,272⟩,[⟨8,1181890206623062842385,⟨19,102,110,239,55,110,194,128,17⟩⟩,⟨0,1210107709821252237548544,⟨18,102,110,238,310,110,194,384,272⟩⟩,⟨4,1210107709820152725920769,⟨3,102,110,239,294,110,194,384,256⟩⟩]⟩
theorem node1211 : UpperPrefix a [4,6,5,7,8,3,1] 30 :=
  Boolean.leaf_sound a [4,6,5,7,8,3,1] 30 cert1211 (by decide +kernel)

def cert1212 : Local := ⟨⟨352,0,0,370,67,403,307,115,99⟩,[(1,6),(2,5)],[(7,3,5),(3,5,2),(2,6,1)]⟩
theorem node1212 : UpperPrefix a [4,6,5,7,8,3,2] 30 :=
  local_sound a [4,6,5,7,8,3,2] 30 cert1212 (by decide +kernel)

theorem node1213 : UpperPrefix a [4,6,5,7,8,3] 30 :=
  branch_upper a [4,6,5,7,8,3] 30 (by decide) (fin9_cases _
  node1210
  node1211
  node1212
  (invalid_upper a [4,6,5,7,8,3,3] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,8,3,4] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,8,3,5] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,8,3,6] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,8,3,7] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,8,3,8] 30 (by decide +kernel)))

theorem node1214 : UpperPrefix a [4,6,5,7,8] 30 :=
  branch_upper a [4,6,5,7,8] 30 (by decide) (fin9_cases _
  node1204
  node1208
  node1209
  node1213
  (invalid_upper a [4,6,5,7,8,4] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,8,8] 30 (by decide +kernel)))

theorem node1215 : UpperPrefix a [4,6,5,7] 30 :=
  branch_upper a [4,6,5,7] 30 (by decide) (fin9_cases _
  node1176
  node1184
  node1192
  node1200
  (invalid_upper a [4,6,5,7,4] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,5] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,6] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,7] 30 (by decide +kernel))
  node1214)

#print axioms node1215
end Delivery.FiniteExclusion.Sharp4x5

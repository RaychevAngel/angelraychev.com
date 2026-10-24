import LowBandCropCoverage
import LowBandCertificate000
import LowBandCertificate001
import LowBandCertificate002
import LowBandCertificate003
import LowBandCertificate004
import LowBandCertificate005
import LowBandCertificate006
import LowBandCertificate007
import LowBandCertificate008
import LowBandCertificate009
import LowBandCertificate010
import LowBandCertificate011
import LowBandCertificate012
import LowBandCertificate013
import LowBandCertificate014
import LowBandCertificate015
import LowBandCertificate016
import LowBandCertificate017
import LowBandCertificate018
import LowBandCertificate019
import LowBandCertificate020
import LowBandCertificate021
import LowBandCertificate022
import LowBandCertificate023
import LowBandCertificate024
import LowBandCertificate025
import LowBandCertificate026
import LowBandCertificate027
import LowBandCertificate028
import LowBandCertificate029
import LowBandCertificate030
import LowBandCertificate031
import LowBandCertificate032
import LowBandCertificate033
import LowBandCertificate034
import LowBandCertificate035
import LowBandCertificate036
import LowBandCertificate037
import LowBandCertificate038
import LowBandCertificate039
import LowBandCertificate040
import LowBandCertificate041
import LowBandCertificate042
import LowBandCertificate043
import LowBandCertificate044
import LowBandCertificate045
import LowBandCertificate046
import LowBandCertificate047
import LowBandCertificate048
import LowBandCertificate049
import LowBandCertificate050
import LowBandCertificate051
import LowBandCertificate052
import LowBandCertificate053
import LowBandCertificate054
import LowBandCertificate055
import LowBandCertificate056
import LowBandCertificate057
import LowBandCertificate058
import LowBandCertificate059
import LowBandCertificate060
import LowBandCertificate061
import LowBandCertificate062
import LowBandCertificate063
import LowBandCertificate064
import LowBandCertificate065
import LowBandCertificate066
import LowBandCertificate067
import LowBandCertificate068
import LowBandCertificate069
import LowBandCertificate070
import LowBandCertificate071
import LowBandCertificate072
import LowBandCertificate073
import LowBandCertificate074
import LowBandCertificate075
import LowBandCertificate076
import LowBandCertificate077
import LowBandCertificate078
import LowBandCertificate079
import LowBandCertificate080
import LowBandCertificate081
import LowBandCertificate082
import LowBandCertificate083
import LowBandCertificate084
import LowBandCertificate085
import LowBandCertificate086
import LowBandCertificate087
import LowBandCertificate088
import LowBandCertificate089
import LowBandCertificate090
import LowBandCertificate091
import LowBandCertificate092
import LowBandCertificate093
import LowBandCertificate094
import LowBandCertificate095
import LowBandCertificate096
import LowBandCertificate097
import LowBandCertificate098
import LowBandCertificate099
import LowBandCertificate100
/- Literal translation of frozen low-band records. Source SHA256:
acd744fd1e432ca6ddba473f68e6dcd5205ec3f6e5681da317b1f4ecca19ba8d. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.LowBandCertificates
open LocalArena LocalArenaRows LowBandLocal
theorem certificates (p : List Nat) (member : p ∈ LowBandCropCoverage.catalog) :
    LowBandLocal.Certificates p := by
  simp only [LowBandCropCoverage.catalog, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst p; exact LowBandCertificate000.checked
  · subst p; exact LowBandCertificate001.checked
  · subst p; exact LowBandCertificate002.checked
  · subst p; exact LowBandCertificate003.checked
  · subst p; exact LowBandCertificate004.checked
  · subst p; exact LowBandCertificate005.checked
  · subst p; exact LowBandCertificate006.checked
  · subst p; exact LowBandCertificate007.checked
  · subst p; exact LowBandCertificate008.checked
  · subst p; exact LowBandCertificate009.checked
  · subst p; exact LowBandCertificate010.checked
  · subst p; exact LowBandCertificate011.checked
  · subst p; exact LowBandCertificate012.checked
  · subst p; exact LowBandCertificate013.checked
  · subst p; exact LowBandCertificate014.checked
  · subst p; exact LowBandCertificate015.checked
  · subst p; exact LowBandCertificate016.checked
  · subst p; exact LowBandCertificate017.checked
  · subst p; exact LowBandCertificate018.checked
  · subst p; exact LowBandCertificate019.checked
  · subst p; exact LowBandCertificate020.checked
  · subst p; exact LowBandCertificate021.checked
  · subst p; exact LowBandCertificate022.checked
  · subst p; exact LowBandCertificate023.checked
  · subst p; exact LowBandCertificate024.checked
  · subst p; exact LowBandCertificate025.checked
  · subst p; exact LowBandCertificate026.checked
  · subst p; exact LowBandCertificate027.checked
  · subst p; exact LowBandCertificate028.checked
  · subst p; exact LowBandCertificate029.checked
  · subst p; exact LowBandCertificate030.checked
  · subst p; exact LowBandCertificate031.checked
  · subst p; exact LowBandCertificate032.checked
  · subst p; exact LowBandCertificate033.checked
  · subst p; exact LowBandCertificate034.checked
  · subst p; exact LowBandCertificate035.checked
  · subst p; exact LowBandCertificate036.checked
  · subst p; exact LowBandCertificate037.checked
  · subst p; exact LowBandCertificate038.checked
  · subst p; exact LowBandCertificate039.checked
  · subst p; exact LowBandCertificate040.checked
  · subst p; exact LowBandCertificate041.checked
  · subst p; exact LowBandCertificate042.checked
  · subst p; exact LowBandCertificate043.checked
  · subst p; exact LowBandCertificate044.checked
  · subst p; exact LowBandCertificate045.checked
  · subst p; exact LowBandCertificate046.checked
  · subst p; exact LowBandCertificate047.checked
  · subst p; exact LowBandCertificate048.checked
  · subst p; exact LowBandCertificate049.checked
  · subst p; exact LowBandCertificate050.checked
  · subst p; exact LowBandCertificate051.checked
  · subst p; exact LowBandCertificate052.checked
  · subst p; exact LowBandCertificate053.checked
  · subst p; exact LowBandCertificate054.checked
  · subst p; exact LowBandCertificate055.checked
  · subst p; exact LowBandCertificate056.checked
  · subst p; exact LowBandCertificate057.checked
  · subst p; exact LowBandCertificate058.checked
  · subst p; exact LowBandCertificate059.checked
  · subst p; exact LowBandCertificate060.checked
  · subst p; exact LowBandCertificate061.checked
  · subst p; exact LowBandCertificate062.checked
  · subst p; exact LowBandCertificate063.checked
  · subst p; exact LowBandCertificate064.checked
  · subst p; exact LowBandCertificate065.checked
  · subst p; exact LowBandCertificate066.checked
  · subst p; exact LowBandCertificate067.checked
  · subst p; exact LowBandCertificate068.checked
  · subst p; exact LowBandCertificate069.checked
  · subst p; exact LowBandCertificate070.checked
  · subst p; exact LowBandCertificate071.checked
  · subst p; exact LowBandCertificate072.checked
  · subst p; exact LowBandCertificate073.checked
  · subst p; exact LowBandCertificate074.checked
  · subst p; exact LowBandCertificate075.checked
  · subst p; exact LowBandCertificate076.checked
  · subst p; exact LowBandCertificate077.checked
  · subst p; exact LowBandCertificate078.checked
  · subst p; exact LowBandCertificate079.checked
  · subst p; exact LowBandCertificate080.checked
  · subst p; exact LowBandCertificate081.checked
  · subst p; exact LowBandCertificate082.checked
  · subst p; exact LowBandCertificate083.checked
  · subst p; exact LowBandCertificate084.checked
  · subst p; exact LowBandCertificate085.checked
  · subst p; exact LowBandCertificate086.checked
  · subst p; exact LowBandCertificate087.checked
  · subst p; exact LowBandCertificate088.checked
  · subst p; exact LowBandCertificate089.checked
  · subst p; exact LowBandCertificate090.checked
  · subst p; exact LowBandCertificate091.checked
  · subst p; exact LowBandCertificate092.checked
  · subst p; exact LowBandCertificate093.checked
  · subst p; exact LowBandCertificate094.checked
  · subst p; exact LowBandCertificate095.checked
  · subst p; exact LowBandCertificate096.checked
  · subst p; exact LowBandCertificate097.checked
  · subst p; exact LowBandCertificate098.checked
  · subst p; exact LowBandCertificate099.checked
  · subst p; exact LowBandCertificate100.checked
#print axioms certificates
end Delivery.LowBandCertificates

import SixTypeObjective29Transfer
import SixTypeObjective29Delivery0
import SixTypeObjective29Delivery1
import SixTypeObjective29Delivery2
import SixTypeObjective29Delivery3
import SixTypeObjective29Delivery4
import SixTypeObjective29Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate29
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern29.pattern := by
  constructor
  · exact ⟨SixTypeObjective29Transfer.data, SixTypeObjective29Transfer.checked, SixTypeObjective29Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective29Delivery0.data, SixTypeObjective29Delivery0.checked, SixTypeObjective29Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective29Delivery1.data, SixTypeObjective29Delivery1.checked, SixTypeObjective29Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective29Delivery2.data, SixTypeObjective29Delivery2.checked, SixTypeObjective29Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective29Delivery3.data, SixTypeObjective29Delivery3.checked, SixTypeObjective29Delivery3.initial_states⟩
    · exact ⟨SixTypeObjective29Delivery4.data, SixTypeObjective29Delivery4.checked, SixTypeObjective29Delivery4.initial_states⟩
    · exact ⟨SixTypeObjective29Delivery5.data, SixTypeObjective29Delivery5.checked, SixTypeObjective29Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate29

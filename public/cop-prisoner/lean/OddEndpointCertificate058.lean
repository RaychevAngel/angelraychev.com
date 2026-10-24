import OddEndpointObjective058Transfer
import OddEndpointObjective058Delivery0
import OddEndpointObjective058Delivery1
import OddEndpointObjective058Delivery2
import OddEndpointObjective058Delivery3
import OddEndpointObjective058Delivery4
import OddEndpointObjective058Delivery5
/- Translation of immutable odd-endpoint local strategies; see the export
manifest for exact archive and record pins. The exporter is untrusted.
All finite game and entry obligations below are checked by the Lean kernel. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.OddEndpointCertificate058
open LocalArena OddEndpointLocal OddEndpointCertificatesSpec GroupedArena
open OddEndpointPattern058
noncomputable def certificates : Certificates residue patchAnchor where
  transfer := OddEndpointObjective058Transfer.certificate
  delivery := by
    intro j allowed
    apply Classical.choice
    have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by
      have finite : ∀ j : Fin 6, j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by decide +kernel
      exact finite j
    rcases cases with rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨OddEndpointObjective058Delivery0.certificate⟩
    · exact ⟨OddEndpointObjective058Delivery1.certificate⟩
    · exact ⟨OddEndpointObjective058Delivery2.certificate⟩
    · exact ⟨OddEndpointObjective058Delivery3.certificate⟩
    · exact ⟨OddEndpointObjective058Delivery4.certificate⟩
    · exact ⟨OddEndpointObjective058Delivery5.certificate⟩
#print axioms certificates
end Delivery.OddEndpointCertificate058

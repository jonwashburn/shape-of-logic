import IndisputableMonolith.Gravity.Analysis.ReggeBlochOrbitTransport4D
import IndisputableMonolith.Gravity.Analysis.ReggeBlochTransportedAllOrbit4D

/-!
# Audit: transported all-orbit fold + orbit covering perm
-/

open IndisputableMonolith.Gravity.Analysis.ReggeBlochOrbitTransport4D
open IndisputableMonolith.Gravity.Analysis.ReggeBlochTransportedAllOrbit4D

#print axioms orbitCoveringPerm_covers
#print axioms orbitCoveringPerm_t11_eq_slotTransportPerm
#print axioms orbitCoveringPerm_spec
#print axioms classDot_pushforward
#print axioms phasedClassDot_pushforward
#print axioms slotOrbitDeficitKer_t11
#print axioms slotOrbitAreaCov_t11_eq
#print axioms blochFoldOrbit_t11
#print axioms m2TransportedOrbitMoment_t11
#print axioms m2TransportedOrbitSlotCoeffFull_eq_trunc_of_ker0
#print axioms m2TransportedOrbitSlotCoeffFull_smul
#print axioms reggeBlochTransportedAllOrbit4DStatus_flags

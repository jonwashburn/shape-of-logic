import IndisputableMonolith.Gravity.Analysis.OrderSensitiveHistoryResponse4D

/-!
Axiom audit for OrderSensitiveHistoryResponse4D. Load-bearing finite gate must
report the base triple (or a subset). Reject silent `sorryAx`.
-/

open IndisputableMonolith.Gravity.Analysis.OrderSensitiveHistoryResponse4D

#print axioms fingerprint_separates_cfgAB
#print axioms historyResponse_separates_cfgAB
#print axioms finiteCertificate_cfgAB
#print axioms edgeAction_separates_cfgAB
#print axioms responseDiff_cfgAB_not_in_MetricEdgeImage
#print axioms orderSensitive_finite_gate_cfgAB
#print axioms decoy_depthOne_blind
#print axioms discovery_pair_is_certificate_cfgAB

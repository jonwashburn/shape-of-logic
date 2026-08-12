import IndisputableMonolith.Gravity.SevenGaps.HKTOneSiteCounterexample

/-!
# Axiom audit: HKT one-site rigidity falsification
-/

open IndisputableMonolith.Gravity.SevenGaps.HKTOneSiteCounterexample

#check one_site_wronskians_vacuous
#check quarticOneSiteHKT
#check not_HKTRigidityStatement_one

#print axioms one_site_wronskians_vacuous
#print axioms not_HKTRigidityStatement_one
#print axioms bracket_quarticHam_quarticHam

import MSTNF.r2.CedarBridge

/-! Axiom audit for the B2 Cedar bridge (port + DuplicateInvariance
discharge). Expected roots: `propext`, `Classical.choice`, `Quot.sound`
only (the pin's own proof is classical). -/

#print axioms MSTNFR2.CedarBridge.sortedBy_equiv_implies_eq
#print axioms MSTNFR2.CedarBridge.insertCanonical_sortedBy
#print axioms MSTNFR2.CedarBridge.insertCanonical_equiv
#print axioms MSTNFR2.CedarBridge.canonicalize_equiv
#print axioms MSTNFR2.CedarBridge.equiv_implies_canonical_eq
#print axioms MSTNFR2.CedarBridge.Set.make_make_eqv
#print axioms MSTNFR2.CedarBridge.LexN.trans
#print axioms MSTNFR2.CedarBridge.LexN.connected
#print axioms MSTNFR2.CedarBridge.toNats_inj
#print axioms MSTNFR2.CedarBridge.order_and_dup_independent
#print axioms MSTNFR2.CedarBridge.order_dup_DuplicateInvariance
#print axioms MSTNFR2.CedarBridge.cedar_bridge_bridged
#print axioms MSTNFR2.CedarBridge.cedar_bridge_sourceSection
#print axioms MSTNFR2.CedarBridge.cedar_bridge_auth_norm
#print axioms MSTNFR2.CedarBridge.cedar_bridge_dup_collision

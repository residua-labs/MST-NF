-- Axioms of the intent theorems (see README). Run after `lake build`:  lake env lean scripts/PrintAxioms.lean
import MSTNF.core.MSTNFObjectMWE
import MSTNF.algorithms.MSTNFExecutionNoFifthRoleMWE
import MSTNF.algorithms.MSTNFCanonicalDecompositionMWE
import MSTNF.algorithms.MSTNFCompletenessRepresentationMWE
import MSTNF.algorithms.MSTNecessityExecModelMWE
import MSTNF.algorithms.MSTNecessityRoleAblationMWE
import MSTNF.algorithms.MSTMinimalityRoleBasisMWE
import MSTNF.algorithms.MSTNoFifthRoleIntegrationMWE
import MSTNF.algorithms.MSTNFQuotientBeforeExecutionNFMWE
import MSTNF.algorithms.MSTNFConcreteAbstractEquivMWE
import MSTNF.core.MSTNFPredBridgeMWE
import MSTNF.algorithms.MSTNFProfileDichotomyMWE
import MSTNF.algorithms.MSTNF3FormMWE
import MSTNF.algorithms.MSTNF3Form4FormEquivMWE
import MSTNF.algorithms.MSTNF3FormOmegaForcedProbeMWE
import MSTNF.algorithms.MSTNFT1BridgeClosureMWE
import MSTNF.algorithms.MSTNFResidueAbsorptionWellFoundedMWE
import MSTNF.algorithms.MSTNFFiniteInstanceMWE
import MSTNF.r2.Active
import MSTNF.r2.Factorization
import MSTNF.r2.Decision
import MSTNF.r2.Compose
import MSTNF.r2.Finite
import MSTNF.r2.Joint
import MSTNF.r2.PreKey
import MSTNF.r2.Reason
import MSTNF.r2.CedarDedup
import MSTNF.r2.CedarBridge
import MSTNF.algorithms.MSTNFCompositionBasicMWE
import MSTNF.algorithms.MSTNFCompositionSumMWE
import MSTNF.algorithms.MSTNFCompositionSeqMWE
import MSTNF.algorithms.MSTNFCompositionProdMWE
import MSTNF.algorithms.MSTNFCompositionAtMostOneMWE
import MSTNF.algorithms.MSTNFHopMWE
import MSTNF.algorithms.MSTNFHopComposeMWE
import MSTNF.algorithms.MSTNFHopWitnessMWE
import MSTNF.algorithms.MSTNFRecComposeMWE
import MSTNF.algorithms.MSTNFResourceAdequateMWE

#print axioms MSTNFObject.exact_iff_empty_residues
#print axioms MSTNFObject.exact_iff_sound_and_complete
#print axioms MSTNFExecutionNoFifthRoleMWE.CoreExecutionProfile.noIndependentFifth_for_coreProfile
#print axioms MSTNFExecutionNoFifthRoleMWE.Generic.noIndependentFifth_iff_allRolesRepresented
#print axioms MSTNFExecutionNoFifthRoleMWE.Generic.noIndependentFifth_of_modelingCompleteness
#print axioms MSTNFCanonicalDecompositionMWE.canonical_is_coarsest
#print axioms MSTNFCanonicalDecompositionMWE.kernel_exact_iso
#print axioms MSTNFCanonicalDecompositionMWE.agree_iff_same_canonical
#print axioms MSTNFCompletenessRepresentationMWE.completeness_theorem
#print axioms MSTNecessityExecModelMWE.sameClass_sameOutcome
#print axioms MSTMinimalityRoleBasisMWE.fused_roles_lose_independent_diagnostics
#print axioms MSTMinimalityRoleBasisMWE.noninjective_simulation_requires_role_fusion
#print axioms MSTMinimalityRoleBasisMWE.standard_basis_is_minimal_independent_diagnostic_basis
#print axioms MSTNecessityRoleAblationMWE.deleting_each_role_breaks_semantics
#print axioms MSTNecessityExecModelMWE.execModel_with_all_roles_has_mstnf_profile
#print axioms MSTNoFifthRoleIntegrationMWE.extended_basis_complete
#print axioms MSTNFQuotientBeforeExecutionNFMWE.sameClass_sameOutcome
#print axioms MSTNFQuotientBeforeExecutionNFMWE.mstnf_backend_le_classic
#print axioms MSTNFConcreteAbstractEquivMWE.v_concrete_eq_abstract_on_all_fixtures
#print axioms MSTNFConcreteAbstractEquivMWE.core_concrete_eq_abstract_on_all_fixtures
#print axioms MSTNFConcreteAbstractEquivMWE.residue_concrete_eq_abstract_on_all_fixtures
#print axioms MSTNFPredBridge.exact_agrees
#print axioms MSTNFCompletenessRepresentationMWE.canonical_decomposition_faithful
#print axioms MSTNFCompletenessRepresentationMWE.residue_totality
#print axioms MSTNFCompletenessRepresentationMWE.admitted_rejected_partition
#print axioms MSTNFCompletenessRepresentationMWE.minimal_complete_basis
#print axioms MSTNFCanonicalDecompositionMWE.kernel_exact_unique_up_to_map
#print axioms MSTNoFifthRoleIntegrationMWE.profileWithFifth_iff_profile
#print axioms MSTNoFifthRoleIntegrationMWE.no_independent_deletion_countermodel_for_dependent_fifth
#print axioms MSTNF3Form4FormEquivMWE.toExecModel_fromExecModel
#print axioms MSTNF3Form4FormEquivMWE.hasMSTNFProfile_iff_3form_section
#print axioms MSTNF3Form4FormEquivMWE.fromExecModel_toExecModel_admissible
#print axioms MSTNF3Form4FormEquivMWE.fromExecModel_toExecModel_sigma
#print axioms MSTNF3Form4FormEquivMWE.fromExecModel_toExecModel_rho
#print axioms MSTNF3FormOmegaForcedProbeMWE.tag_is_omega_forced
#print axioms MSTNF3FormOmegaForcedProbeMWE.two_Lambdas_same_tag_distinct_witnesses
#print axioms MSTNFT1BridgeClosure.T1_closure
#print axioms MSTNFT1BridgeClosure.T1_parametric_in_framework
#print axioms MSTNFT1BridgeClosure.antiFiatChain_each_detects_prior_fiat
#print axioms MSTNFResidueAbsorptionWellFounded.godelStep_no_terminal
#print axioms MSTNFResidueAbsorptionWellFounded.godelStep_flip_not_wellFounded
#print axioms MSTNFExecutionNoFifthRoleMWE.Generic.roleRepresentation_iff_noDiagnostic
#print axioms MSTNFExecutionNoFifthRoleMWE.Generic.noIndependentFifth_iff_noExplicitDiagnosticWitness
#print axioms MSTNFProfileDichotomyMWE.input_dichotomy
#print axioms MSTNFProfileDichotomyMWE.representative_only_if_admitted

-- Round 2 (MST-NF-R2): the R2 intent theorems and the Cedar bridge port.
#print axioms MSTNFR2.P1_observation_factorization
#print axioms MSTNFR2.P1_factorization_converse
#print axioms MSTNFR2.P4_normalization
#print axioms MSTNFR2.P5_sequential_preservation
#print axioms MSTNFR2.P7_sum_preservation
#print axioms MSTNFR2.P8_product_preservation
#print axioms MSTNFR2.Dact_admOfD
#print axioms MSTNFR2.Dact_sigOfD
#print axioms MSTNFR2.Dact_rhoOfD
#print axioms MSTNFR2.sigma_rho_excl
#print axioms MSTNFR2.mutantQ_truth
#print axioms MSTNFR2.mutantA_truth
#print axioms MSTNFR2.mutantR_truth
#print axioms MSTNFR2.mutantS_truth
#print axioms MSTNFR2.qjoint_is_coarsest
#print axioms MSTNFR2.pkey_correct
#print axioms MSTNFR2.pkey_collision
#print axioms MSTNFR2.reasonValid_without_refuting
#print axioms MSTNFR2.cedarIF_bridged
#print axioms MSTNFR2.CedarBridge.isAuthorized_error_plus_permit
#print axioms MSTNFR2.CedarBridge.order_and_dup_independent
#print axioms MSTNFR2.CedarBridge.order_dup_DuplicateInvariance
#print axioms MSTNFR2.CedarBridge.cedar_bridge_bridged
#print axioms MSTNFR2.CedarBridge.cedar_bridge_sourceSection
#print axioms MSTNFR2.CedarBridge.cedar_bridge_auth_norm
#print axioms MSTNFR2.CedarBridge.cedar_bridge_dup_collision
#print axioms MSTNFR2.CedarBridge.cedar_bridge_erase_classify
#print axioms MSTNFR2.CedarBridge.cedar_bridge_deny_carries_full
#print axioms MSTNFR2.CedarBridge.cedar_bridge_permit_collision
#print axioms MSTNFR2.CedarBridge.cedar_bridge_forbid_collision
#print axioms MSTNFR2.CedarBridge.denialKind_noPermit
#print axioms MSTNFR2.CedarBridge.denialKind_forbidDetermined
#print axioms MSTNFFiniteInstanceMWE.core_hasMSTNFProfile
#print axioms MSTNFFiniteInstanceMWE.check_reference_eq_lifted
#print axioms MSTNFFiniteInstanceMWE.check_section_normalization
#print axioms MSTNFFiniteInstanceMWE.check_double_failure
#print axioms MSTNFFiniteInstanceMWE.check_coarse_mismatch
#print axioms MSTNFFiniteInstanceMWE.base6_hasMSTNFProfile
#print axioms MSTNFFiniteInstanceMWE.mutantX_exclusive_violation
#print axioms MSTNFFiniteInstanceMWE.mutantSec_section_violation
#print axioms NfCompose.parts_profile
#print axioms NfCompose.bool_and_true
#print axioms NfCompose.sigma_eq_snd
#print axioms NfCompose.option_some_ne_none
#print axioms NfCompose.sum_active_iff
#print axioms NfCompose.sum_profile
#print axioms NfCompose.seq_profile
#print axioms NfCompose.seqObserve_profile
#print axioms NfCompose.observeM1_profile
#print axioms NfCompose.observeM2_profile
#print axioms NfCompose.observe_does_not_factor
#print axioms NfCompose.observe_no_respects
#print axioms NfCompose.prod_active_iff
#print axioms NfCompose.prod_profile
#print axioms NfCompose.sum_atMost_iff
#print axioms NfCompose.seq_atMost_of_stage1
#print axioms NfCompose.prod_atMost
#print axioms NfCompose.admitPoint_profile
#print axioms NfCompose.admitPoint_atMost
#print axioms NfCompose.refusePoint_profile
#print axioms NfCompose.seq_stage2_collision_stays
#print axioms NfCompose.seq_stage2_source_fails
#print axioms NfCompose.seq_stage1_collision_blocked
#print axioms NfCompose.seq_stage1_source_fails
#print axioms NfCompose.prod_atMost_while_left_fails
#print axioms NfCompose.two_profile
#print axioms NfCompose.two_sum_profile
#print axioms NfCompose.two_sum_not_atMost
#print axioms NfCompose.hopModel_profile
#print axioms NfCompose.hop_rho_none_iff_admissible
#print axioms NfCompose.hopCorrect_iff_exact
#print axioms NfCompose.seq_residue_none_iff
#print axioms NfCompose.seq_residue_empty_iff
#print axioms NfCompose.seqAssocRep_left_inv
#print axioms NfCompose.seqAssocRep_right_inv
#print axioms NfCompose.seqAssocRes_left_inv
#print axioms NfCompose.seqAssocRes_right_inv
#print axioms NfCompose.seqAssocOut_left_inv
#print axioms NfCompose.seqAssocOut_right_inv
#print axioms NfCompose.seqAssocRes_s1s1
#print axioms NfCompose.seqAssocRes_s1s2
#print axioms NfCompose.seqAssocRes_s2
#print axioms NfCompose.seq_assoc_laws
#print axioms NfCompose.seq_assoc_evalRaw
#print axioms NfCompose.seqResMap_s1
#print axioms NfCompose.seqResMap_s2
#print axioms NfCompose.seqRepMap_both
#print axioms NfCompose.seqCong_feed_q
#print axioms NfCompose.seqCong_feed_q_inv
#print axioms NfCompose.hop_eval_eq_obs_seq
#print axioms NfCompose.hopCorrect_iff_obsSeq
#print axioms NfCompose.hop_admissible_iff
#print axioms NfCompose.hop_sigma_eq
#print axioms NfCompose.hop_seq_correct
#print axioms NfCompose.hop_seq_correct_from
#print axioms NfCompose.hopSeq_admissible
#print axioms NfCompose.hopSeq_correct_iff
#print axioms NfCompose.hop_seq_correct_direct
#print axioms NfCompose.hopObsSeq_comp
#print axioms NfCompose.hopObsSeq_chain3
#print axioms NfCompose.hop_sum_admissible
#print axioms NfCompose.hop_sum_correct_iff
#print axioms NfCompose.hop_sum_one_target
#print axioms NfCompose.hop_prod_admissible
#print axioms NfCompose.hop_prod_correct
#print axioms NfCompose.hop_prod_correct_left
#print axioms NfCompose.hop_prod_correct_right
#print axioms NfCompose.Fam.qf_iff
#print axioms NfCompose.clockHopModel_profile
#print axioms NfCompose.clock_resourceOk_iff
#print axioms NfCompose.transFam_profile
#print axioms NfCompose.clock_hop_seq_correct
#print axioms NfCompose.clock_const_iff
#print axioms NfCompose.transSigma_input
#print axioms NfCompose.bootstrap_instance
#print axioms NfCompose.HopWitness.pt_profile
#print axioms NfCompose.HopWitness.badB_other_laws
#print axioms NfCompose.HopWitness.badB_not_qf
#print axioms NfCompose.HopWitness.eqN_sound
#print axioms NfCompose.HopWitness.eqT_unsound
#print axioms NfCompose.HopWitness.hopCorrect_of_all
#print axioms NfCompose.HopWitness.not_hopCorrect_of
#print axioms NfCompose.HopWitness.not_hopObsSeq_of
#print axioms NfCompose.HopWitness.clock_of_all
#print axioms NfCompose.HopWitness.not_clock_of
#print axioms NfCompose.HopWitness.direct_needs_hAB
#print axioms NfCompose.HopWitness.direct_needs_hBC
#print axioms NfCompose.HopWitness.direct_needs_hqB
#print axioms NfCompose.HopWitness.direct_needs_heqB
#print axioms NfCompose.HopWitness.hopHop_needs_hBC
#print axioms NfCompose.HopWitness.hopHop_needs_hqB
#print axioms NfCompose.HopWitness.hopHop_needs_heqB
#print axioms NfCompose.HopWitness.obsSeq_needs_h12
#print axioms NfCompose.HopWitness.obsSeq_needs_h23
#print axioms NfCompose.HopWitness.obsSeq_needs_hqB
#print axioms NfCompose.HopWitness.prod_needs_h1
#print axioms NfCompose.HopWitness.prod_needs_h2
#print axioms NfCompose.HopWitness.cpt_qf
#print axioms NfCompose.HopWitness.cbadB_not_qf
#print axioms NfCompose.HopWitness.clock_needs_hAB
#print axioms NfCompose.HopWitness.clock_needs_hBC
#print axioms NfCompose.HopWitness.clock_needs_hqB
#print axioms NfCompose.HopWitness.clock_needs_heqB
#print axioms NfCompose.HopWitness.clock_lim_minimal
#print axioms NfCompose.HopWitness.boot_needs_hadm
#print axioms NfCompose.HopWitness.boot_needs_hfix
#print axioms NfCompose.Rec.TreeSig.induction
#print axioms NfCompose.Rec.TreeSig.map_congr_mem
#print axioms NfCompose.Rec.TreeSig.foldN_stable
#print axioms NfCompose.Rec.TreeSig.fold_eq
#print axioms NfCompose.Rec.TreeSig.eq_fold
#print axioms NfCompose.Rec.TreeSig.fold_fusion
#print axioms NfCompose.Rec.forall_mem_map
#print axioms NfCompose.Rec.all_eq_true'
#print axioms NfCompose.Rec.firstFail_eq_none
#print axioms NfCompose.Rec.allSome_eq_none
#print axioms NfCompose.Rec.combineRho_eq_none
#print axioms NfCompose.Rec.stepAlg_out
#print axioms NfCompose.Rec.stepAlg_adm
#print axioms NfCompose.Rec.stepAlg_rho
#print axioms NfCompose.Rec.stepAlg_sig
#print axioms NfCompose.Rec.rec_qf
#print axioms NfCompose.Rec.rec_rho_none_iff
#print axioms NfCompose.Rec.rec_as
#print axioms NfCompose.Rec.rec_rt
#print axioms NfCompose.Rec.rec_rp
#print axioms NfCompose.Rec.recModel_profile
#print axioms NfCompose.Rec.recModel_rho_none_iff
#print axioms NfCompose.Rec.firstFail_some
#print axioms NfCompose.Rec.recModel_rho_path
#print axioms NfCompose.Rec.hopCorrect_of_rel
#print axioms NfCompose.Rec.hopCorrect_of_localSquares
#print axioms NfCompose.Rec.local_of_forms
#print axioms NfCompose.Rec.obs_eval_of_fusion
#print axioms NfCompose.Rec.hopCorrect_of_fusion
#print axioms NfCompose.Rec.clockHopCorrect_of_stepRel
#print axioms NfCompose.Rec.Necessity.eqInt_iff
#print axioms NfCompose.Rec.Necessity.good_rp
#print axioms NfCompose.Rec.Necessity.good_rep
#print axioms NfCompose.Rec.Necessity.good_semA
#print axioms NfCompose.Rec.Necessity.good_evalB
#print axioms NfCompose.Rec.Necessity.good_sq
#print axioms NfCompose.Rec.Necessity.good_admB
#print axioms NfCompose.Rec.Necessity.correct_hop
#print axioms NfCompose.Rec.Necessity.not_hopCorrect_at
#print axioms NfCompose.Rec.Necessity.sq_other
#print axioms NfCompose.Rec.Necessity.sq_fails
#print axioms NfCompose.Rec.Necessity.sq_needed
#print axioms NfCompose.Rec.Necessity.admB_other
#print axioms NfCompose.Rec.Necessity.admB_fails
#print axioms NfCompose.Rec.Necessity.admB_needed
#print axioms NfCompose.Rec.Necessity.rp_fails
#print axioms NfCompose.Rec.Necessity.rp_rep
#print axioms NfCompose.Rec.Necessity.rp_needed
#print axioms NfCompose.Rec.Necessity.rep_rp
#print axioms NfCompose.Rec.Necessity.rep_fails
#print axioms NfCompose.Rec.Necessity.rep_needed
#print axioms NfCompose.Rec.Necessity.eq_fails
#print axioms NfCompose.Rec.Necessity.eq_needed
#print axioms NfCompose.Rec.Necessity.semA_fails
#print axioms NfCompose.Rec.Necessity.semA_needed
#print axioms NfCompose.Rec.Necessity.evalB_fails
#print axioms NfCompose.Rec.Necessity.evalB_needed
#print axioms NfCompose.Rec.Necessity.noNeg_eq
#print axioms NfCompose.Rec.Necessity.step_loc_other
#print axioms NfCompose.Rec.Necessity.step_loc_fails
#print axioms NfCompose.Rec.Necessity.step_loc_needed
#print axioms NfCompose.Rec.Necessity.step_rp_needed
#print axioms NfCompose.Rec.Necessity.step_root_needed
#print axioms NfCompose.Rec.Necessity.step_eq_needed
#print axioms NfCompose.Rec.Necessity.qkids_id
#print axioms NfCompose.Rec.Necessity.ok_qf
#print axioms NfCompose.Rec.Necessity.ok_as
#print axioms NfCompose.Rec.Necessity.ok_rt
#print axioms NfCompose.Rec.Necessity.ok_rp
#print axioms NfCompose.Rec.Necessity.ok_profile
#print axioms NfCompose.Rec.Necessity.qkids_fails
#print axioms NfCompose.Rec.Necessity.q_qf
#print axioms NfCompose.Rec.Necessity.q_as
#print axioms NfCompose.Rec.Necessity.q_rt
#print axioms NfCompose.Rec.Necessity.q_rp
#print axioms NfCompose.Rec.Necessity.qkids_needed
#print axioms NfCompose.Rec.Necessity.qf_fails
#print axioms NfCompose.Rec.Necessity.qf_as
#print axioms NfCompose.Rec.Necessity.qf_rt
#print axioms NfCompose.Rec.Necessity.qf_rp
#print axioms NfCompose.Rec.Necessity.qf_needed
#print axioms NfCompose.Rec.Necessity.as_fails
#print axioms NfCompose.Rec.Necessity.as_qf
#print axioms NfCompose.Rec.Necessity.as_rt
#print axioms NfCompose.Rec.Necessity.as_rp
#print axioms NfCompose.Rec.Necessity.as_needed
#print axioms NfCompose.Rec.Necessity.rt_fails
#print axioms NfCompose.Rec.Necessity.rt_qf
#print axioms NfCompose.Rec.Necessity.rt_as
#print axioms NfCompose.Rec.Necessity.rt_rp
#print axioms NfCompose.Rec.Necessity.rt_needed
#print axioms NfCompose.Rec.Necessity.rp_fails'
#print axioms NfCompose.Rec.Necessity.rp_qf
#print axioms NfCompose.Rec.Necessity.rp_as
#print axioms NfCompose.Rec.Necessity.rp_rt
#print axioms NfCompose.Rec.Necessity.rp_needed'
#print axioms NfCompose.Rec.Necessity.path_rho
#print axioms NfCompose.Rec.TreeSig.step_induction
#print axioms NfCompose.resourceAdequate
#print axioms NfCompose.resourceAdequateExact
#print axioms NfCompose.nondegenerate
#print axioms NfCompose.resourceAdequateExact_stronger
#print axioms NfCompose.resourceAdequate_seq
#print axioms NfCompose.resourceAdequateExact_seq
#print axioms NfCompose.resourceAdequate_of_empty
#print axioms NfCompose.all_resource_not_adequate
#print axioms NfCompose.AdequateWitness.unitLayer
#print axioms NfCompose.AdequateWitness.clock_correct_but_not_adequate
#print axioms NfCompose.AdequateWitness.vacuous_adequate_example
#print axioms NfCompose.AdequateWitness.image_needed

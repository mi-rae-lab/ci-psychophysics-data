import SMD

-- One direct #print axioms command for each named theorem declared in the eight SMD source modules.

-- SMD/Arith.lean
#print axioms SMD.sumTo_zero
#print axioms SMD.sumTo_succ
#print axioms SMD.sumQ_zero
#print axioms SMD.sumQ_succ
#print axioms SMD.sumZ_zero
#print axioms SMD.sumZ_succ
#print axioms SMD.sumTo_congr
#print axioms SMD.sumQ_congr
#print axioms SMD.sumTo_add
#print axioms SMD.sumTo_le
#print axioms SMD.sumTo_eq_zero
#print axioms SMD.le_sumTo
#print axioms SMD.sumTo_split
#print axioms SMD.sumTo_succ'
#print axioms SMD.sumQ_div
#print axioms SMD.natCast_sumTo
#print axioms SMD.div_le_div_iff_of_pos
#print axioms SMD.div_lt_div_iff_of_pos
#print axioms SMD.frac_lt_twentieth
#print axioms SMD.natCast_ite
#print axioms SMD.ite_div_eq
#print axioms SMD.choose_zero_right
#print axioms SMD.choose_zero_succ
#print axioms SMD.choose_succ_succ
#print axioms SMD.choose_eq_zero_of_lt
#print axioms SMD.choose_self
#print axioms SMD.choose_pos
#print axioms SMD.vandermonde
#print axioms SMD.zipWith_add_getD
#print axioms SMD.append_zero_getD
#print axioms SMD.pascalRow_length
#print axioms SMD.pascalRow_getD
#print axioms SMD.arr_getD
#print axioms SMD.choose_eq_chooseFast

-- SMD/Exact.lean
#print axioms SMD.natCast_pow
#print axioms SMD.three_pow_pos
#print axioms SMD.third_pows
#print axioms SMD.geThirdDen_pos
#print axioms SMD.geThird_frac
#print axioms SMD.geThirdSig_iff
#print axioms SMD.sum_choose_two_pow
#print axioms SMD.geThirdNum_eq
#print axioms SMD.geThirdNum_le
#print axioms SMD.geThirdNum_pos
#print axioms SMD.geThirdNum_zero
#print axioms SMD.fgSpecM_eq
#print axioms SMD.fg_window
#print axioms SMD.fgSpec_degenerate
#print axioms SMD.fg_frac
#print axioms SMD.fgDen_pos
#print axioms SMD.fgSig_iff

-- SMD/Target.lean
#print axioms SMD.powList_getD
#print axioms SMD.zsum_congr
#print axioms SMD.term_with
#print axioms SMD.tailLeWith_eq
#print axioms SMD.tailGeWith_eq
#print axioms SMD.tailLe_eq_tailLeFast
#print axioms SMD.tailGe_eq_tailGeFast
#print axioms SMD.intCast_pos_iff
#print axioms SMD.intCast_neg_iff
#print axioms SMD.sq_div
#print axioms SMD.negZ2_iff
#print axioms SMD.isNegQ_scale
#print axioms SMD.lt_twentieth_iff
#print axioms SMD.belowSig_iff
#print axioms SMD.aboveSig_iff

-- SMD/Rng.lean
#print axioms SMD.intF_lt
#print axioms SMD.int_lt
#print axioms SMD.drawRove_bounds
#print axioms SMD.plan_targetPos
#print axioms SMD.plan_roves
#print axioms SMD.swapL_length
#print axioms SMD.swapL_perm
#print axioms SMD.fy_perm
#print axioms SMD.range60_count
#print axioms SMD.qsmdOrder_each_once
#print axioms SMD.cellTable_length
#print axioms SMD.answerTable_length
#print axioms SMD.cellTable_count
#print axioms SMD.answer_counts
#print axioms SMD.range_map_cellOf
#print axioms SMD.qsmdOrder_cell_count

-- SMD/Stair.lean
#print axioms SMD.reqDir_cases
#print axioms SMD.newH_le
#print axioms SMD.step_h_le
#print axioms SMD.stepFor_le
#print axioms SMD.reqStepOf_le
#print axioms SMD.newH_near
#print axioms SMD.step_h_near
#print axioms SMD.step_wrong
#print axioms SMD.step_second_correct
#print axioms SMD.step_first_correct
#print axioms SMD.step_invalid
#print axioms SMD.isRev_moved
#print axioms SMD.moveOf_of_moved
#print axioms SMD.stepValid_revs
#print axioms SMD.step_revs
#print axioms SMD.step_blocked_no_rev
#print axioms SMD.step_size_rule
#print axioms SMD.init_noClamp
#print axioms SMD.wonCfg_ceilH
#print axioms SMD.wonCfg_floorH
#print axioms SMD.wonCfg_coarseH
#print axioms SMD.wonCfg_fineH
#print axioms SMD.wonCfg_switchFrom
#print axioms SMD.isBlocked_up
#print axioms SMD.isBlocked_down
#print axioms SMD.noClamp_core
#print axioms SMD.stepValid_noClamp
#print axioms SMD.step_noClamp
#print axioms SMD.run_noClamp_aux
#print axioms SMD.run_no_clamp
#print axioms SMD.init_inv
#print axioms SMD.endCheck_running
#print axioms SMD.step_attempts
#print axioms SMD.step_inv
#print axioms SMD.run_ends_aux
#print axioms SMD.run_ends
#print axioms SMD.sum_bounds
#print axioms SMD.threshold_bounds
#print axioms SMD.step_revs_le
#print axioms SMD.run_bounds
#print axioms SMD.run_threshold_bounds

-- SMD/Classify.lean
#print axioms SMD.firstStatus_cases
#print axioms SMD.window_some
#print axioms SMD.refineCore_cases
#print axioms SMD.firstStatus_not_refined
#print axioms SMD.numeric_iff
#print axioms SMD.zero_alarm_unreliable
#print axioms SMD.both_ends_unreliable
#print axioms SMD.above_iff
#print axioms SMD.classify_thr
#print axioms SMD.numeric_thr_bounds

-- SMD/Summary.lean
#print axioms SMD.settle_final_iff
#print axioms SMD.settle_ne_provisional
#print axioms SMD.twoDone_final
#print axioms SMD.three_final
#print axioms SMD.summaryOf_cases
#print axioms SMD.summaryOf_final
#print axioms SMD.final_all_num
#print axioms SMD.provisional_iff
#print axioms SMD.decided_of_three
#print axioms SMD.third_needed_iff
#print axioms SMD.two_final_close
#print axioms SMD.meanQ_bounds
#print axioms SMD.final_value_bounds

-- SMD/Const.lean
#print axioms SMD.cstep_invalid_same
#print axioms SMD.cstep_valid_next
#print axioms SMD.cinit_inv
#print axioms SMD.cstep_inv
#print axioms SMD.cstep_valid_mono
#print axioms SMD.crun_props
#print axioms SMD.crun_ends_gen
#print axioms SMD.crun_ends
#print axioms SMD.range_map_getD
#print axioms SMD.crun_complete
#print axioms SMD.score_only_complete
#print axioms SMD.crun_nValid

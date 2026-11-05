// 계단법 — 화면·소리와 떨어진 순수 상태 전이 (Won 2007: 2-up 1-down, 0.176 rpo 시작, ×1.414 한 칸, 반전 13번, 마지막 8번 평균)
// 밀도는 칸 k (0 = 0.125 rpo … 13 = 11.314 rpo). 반전 값은 milli-rpo 정수(DENS_MILLI[k]).
// 방향: +1 = 촘촘하게(어렵게), −1 = 성기게(쉽게). 0 에서 −1 · 13 에서 +1 요청 = 막힌 이동(이동도 반전도 아님).
// 상태는 그대로 두고 새 상태와 전이 기록을 돌려준다.
'use strict';

const clone = o => JSON.parse(JSON.stringify(o));

const Stair = (() => {
  function cfgFrom(P) {
    const s = P.staircase;
    return {
      version: s.version, dens: s.densities_milli.slice(), startK: s.start_index, minK: s.min_index, maxK: s.max_index,
      nHarder: s.correct_required_for_harder, nEasier: s.incorrect_required_for_easier, stepK: s.step_index,
      totalReversals: s.total_reversals, retained: s.retained_reversals, maxValid: s.max_valid_trials, maxTechnical: s.max_technical_failures,
      // 분석(js/analysis.js): 분석 구간에서 끝에 막힌 이동을 몇 번까지 숫자 역치로 둘지 — 계단 자체에는 쓰지 않음
      blocksMax: P.analysis && Number.isInteger(P.analysis.boundary_blocks_allowed_in_window) ? P.analysis.boundary_blocks_allowed_in_window : 0,
    };
  }
  function init(cfg) {
    if (cfg.nEasier !== 1 || cfg.stepK !== 1) throw new Error('이 구현은 1번 틀리면 한 칸 쉬워지는 규칙만 지원');
    if (![cfg.startK, cfg.minK, cfg.maxK].every(Number.isInteger) || !(cfg.minK <= cfg.startK && cfg.startK <= cfg.maxK)) throw new Error('칸 범위가 이상함');
    if (cfg.dens.length !== cfg.maxK + 1 || !cfg.dens.every(Number.isSafeInteger)) throw new Error('밀도 표가 이상함');
    return { k: cfg.startK, correctStreak: 0, lastDir: null, reversals: [], attemptCount: 0, validCount: 0, technicalCount: 0, moves: 0, processed: [], status: 'running' };
  }
  // outcome = { trialId, presentedK, valid, correct, reason }
  function step(state, cfg, outcome) {
    if (state.processed.includes(outcome.trialId)) return { duplicate: true, state, tr: null };
    if (state.status !== 'running') throw new Error('이미 끝난 계단: ' + state.status);
    if (outcome.presentedK !== state.k) throw new Error(`제시 칸 ${outcome.presentedK} ≠ 계단 상태 ${state.k}`);
    const next = clone(state);
    next.attemptCount++;
    next.processed.push(outcome.trialId);
    const tr = {
      trialId: outcome.trialId, attemptNo: next.attemptCount, validNo: null, presentedK: state.k, presentedMilli: cfg.dens[state.k],
      valid: !!outcome.valid, correct: outcome.valid ? !!outcome.correct : null, reason: outcome.valid ? null : (outcome.reason || 'invalid'),
      preStreak: state.correctStreak, postStreak: state.correctStreak, requestedDir: 0,
      move: 'NONE', reversal: false, reversalNo: null, reversalAtBound: null, blockedAt: null,
      nextK: state.k, nextPresented: null, statusAfter: null,
    };
    if (!outcome.valid) {
      // 기술적 실패: attempt 만 세고 칸·streak·반전은 그대로
      next.technicalCount++;
      tr.move = 'INVALID_NO_CHANGE';
      if (next.technicalCount >= cfg.maxTechnical) next.status = 'technical_failure';
    } else {
      next.validCount++;
      tr.validNo = next.validCount;
      let dir = 0;
      if (outcome.correct) {
        next.correctStreak++;
        if (next.correctStreak >= cfg.nHarder) { next.correctStreak = 0; dir = +1; }   // 이동에 쓴 정답 쌍은 다시 쓰지 않음
      } else {
        next.correctStreak = 0;
        dir = -1;
      }
      tr.requestedDir = dir;
      tr.postStreak = next.correctStreak;
      if (dir === 0) tr.move = 'STAY';
      else {
        const blocked = (dir > 0 && state.k >= cfg.maxK) || (dir < 0 && state.k <= cfg.minK);
        if (blocked) {
          tr.move = 'BLOCKED_ZERO_MOVE';
          tr.blockedAt = dir > 0 ? 'hard' : 'easy';
        } else {
          // 반전은 실제 이동에만. 막힌 0 이동은 반전이 될 수 없음
          const reversal = state.lastDir !== null && dir !== state.lastDir;
          next.k = state.k + dir * cfg.stepK;
          tr.move = 'MOVE';
          if (reversal) {
            const b = state.k === cfg.minK ? 'easy' : state.k === cfg.maxK ? 'hard' : null;
            // 반전 값 = 이동하기 전, 이 시행에서 실제로 제시한 밀도
            next.reversals.push({ k: state.k, milli: cfg.dens[state.k], validNo: tr.validNo, attemptNo: tr.attemptNo, trialId: outcome.trialId, dirAfter: dir, atBound: b });
            tr.reversal = true;
            tr.reversalNo = next.reversals.length;
            tr.reversalAtBound = b;
          }
          next.lastDir = dir;
          next.moves++;
        }
      }
      if (next.reversals.length >= cfg.totalReversals) next.status = 'reversal_target_reached';
      else if (next.validCount >= cfg.maxValid) next.status = 'trial_cap_before_reversal_target';
    }
    tr.nextK = next.k;
    tr.nextPresented = next.status === 'running';   // 끝났으면 다음 칸은 계획만 되고 제시되지 않음
    tr.statusAfter = next.status;
    return { duplicate: false, state: next, tr };
  }
  // 역치 = 마지막 retained 개 반전에서 제시한 밀도의 산술 평균 (rpo). 정확한 합(milli-rpo 정수)·개수를 함께
  //   thr = sumMilli / (1000 · count) — 숫자 검증도 같은 식으로 (analysis.numericResultIssue)
  function threshold(state, cfg) {
    const R = state.reversals.length;
    if (R < cfg.totalReversals) return null;
    const kept = state.reversals.slice(R - cfg.retained);
    const sumMilli = kept.reduce((s, r) => s + r.milli, 0);
    const thr = sumMilli / (1000 * kept.length);
    if (!Number.isFinite(thr) || kept.length !== cfg.retained) return null;
    return { thr, sumMilli, count: kept.length, retainedMilli: kept.map(r => r.milli), allMilli: state.reversals.map(r => r.milli) };
  }
  return { cfgFrom, init, step, threshold };
})();

if (typeof module !== 'undefined') module.exports = { Stair };

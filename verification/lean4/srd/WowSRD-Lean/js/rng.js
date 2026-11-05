// 난수 — xoshiro128** (Blackman & Vigna). 시드와 시행마다의 상태(128비트, 16진 32자)를 기록해 같은 추출을 다시 만들 수 있게 함.
// README §5.3 'RNG 알고리즘·버전·seed 를 고정', §13 '저장 후 재개 시 RNG 상태 일치'.
// 기준값: 상태 [1,2,3,4] → 11520, 0, 5927040, 70819200, 2031721883, … (js/tests.js 에서 파이썬 계산값과 대조)
'use strict';

const Rng = (() => {
  const ALGO = 'xoshiro128**-v1';
  const rotl = (x, k) => (x << k) | (x >>> (32 - k));
  const hexOf = s => Array.from(s, v => (v >>> 0).toString(16).padStart(8, '0')).join('');

  function make(words) {
    const s = Uint32Array.from(words);
    if (!(s[0] | s[1] | s[2] | s[3])) throw new Error('RNG 상태가 모두 0');
    function u32() {
      const r = Math.imul(rotl(Math.imul(s[1], 5), 7), 9) >>> 0;
      const t = s[1] << 9;
      s[2] ^= s[0]; s[3] ^= s[1]; s[1] ^= s[2]; s[0] ^= s[3];
      s[2] ^= t; s[3] = rotl(s[3], 11);
      return r;
    }
    // 0 … n−1 고르게 (기각 표집: 2^32 를 n 으로 나눈 나머지 쪽은 버림)
    function int(n) {
      if (!(n >= 1 && n <= 0x100000000 && Number.isInteger(n))) throw new Error('int(n): n 이 이상함 ' + n);
      const lim = Math.floor(0x100000000 / n) * n;
      let x;
      do { x = u32(); } while (x >= lim);
      return x % n;
    }
    return { u32, int, hex: () => hexOf(s), words: () => Array.from(s) };
  }
  function fromHex(h) {
    if (!/^[0-9a-f]{32}$/.test(h)) throw new Error('RNG 상태 형식이 틀림: ' + h);
    return make([0, 1, 2, 3].map(i => parseInt(h.slice(i * 8, i * 8 + 8), 16) >>> 0));
  }
  function freshSeedHex() {
    const a = new Uint32Array(4);
    crypto.getRandomValues(a);
    if (!(a[0] | a[1] | a[2] | a[3])) a[0] = 1;
    return hexOf(a);
  }
  return { ALGO, make, fromHex, freshSeedHex };
})();

if (typeof module !== 'undefined') module.exports = Rng;

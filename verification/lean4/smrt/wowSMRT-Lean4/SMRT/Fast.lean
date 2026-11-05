import SMRT.Exact
import SMRT.Fisher2

/-!
# 대조 실행 파일의 빠른 길 = 증명된 정의 (Claude, 2026-10-22)

대조 실행 파일은 파스칼 행 0 … m 을 한 번만 만들어(앞 행에서 다음 행 — `pascalRow` 의 정의 그대로) 표마다 꺼내 씀.
`rowsArr_getD` : 그렇게 만든 행 = `pascalRow n` (n ≤ m) → `geThirdNum_fast` · `f2Num_fast` · `f2Den_fast` 로
실행 파일이 쓰는 식이 증명된 `geThirdNum` · `f2Num` · `f2Den` 과 같음.
-/

namespace SMRT

/-- 행 r 부터 k 개: r, 다음 행, … -/
def rowsFrom (r : List Nat) : Nat → List (List Nat)
  | 0 => []
  | k + 1 => r :: rowsFrom (pascalNext r) k

theorem rowsFrom_length (r : List Nat) : ∀ k, (rowsFrom r k).length = k
  | 0 => rfl
  | k + 1 => by simp [rowsFrom, rowsFrom_length _ k]

theorem rowsFrom_getD : ∀ (k n i : Nat), i < k → (rowsFrom (pascalRow n) k).getD i [] = pascalRow (n + i)
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, n, 0, _ => by simp [rowsFrom]
  | k + 1, n, i + 1, h => by
    simp only [rowsFrom, List.getD_cons_succ]
    have : pascalNext (pascalRow n) = pascalRow (n + 1) := rfl
    rw [this, rowsFrom_getD k (n + 1) i (by omega)]
    congr 1; omega

/-- 행 0 … m (배열) -/
def rowsArr (m : Nat) : Array (Array Nat) := ((rowsFrom (pascalRow 0) (m + 1)).map List.toArray).toArray

theorem rowsArr_getD (m n : Nat) (h : n ≤ m) : (rowsArr m).getD n #[] = (pascalRow n).toArray := by
  unfold rowsArr
  rw [arr_getD]
  have hl : n < (rowsFrom (pascalRow 0) (m + 1)).length := by rw [rowsFrom_length]; omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  rw [List.getElem?_eq_getElem hl]
  simp only [Option.map_some, Option.getD_some]
  have := rowsFrom_getD (m + 1) 0 n (by omega)
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl] at this
  simp only [Option.getD_some, Nat.zero_add] at this
  rw [this]

/-- 실행 파일의 1/3 이항 분자 = 증명된 `geThirdNum` -/
theorem geThirdNum_fast (m n k : Nat) (h : n ≤ m) : geThirdNumWith ((rowsArr m).getD n #[]) n k = geThirdNum n k := by
  rw [rowsArr_getD m n h, geThirdNum_with]

/-- 실행 파일의 양측 Fisher 분자 · 분모 = 증명된 `f2Num` · `f2Den` -/
theorem f2Num_fast (m a b c d : Nat) (h1 : a + b ≤ m) (h2 : c + d ≤ m) :
    f2NumWith ((rowsArr m).getD (a + b) #[]) ((rowsArr m).getD (c + d) #[]) a c = f2Num a b c d := by
  rw [rowsArr_getD m _ h1, rowsArr_getD m _ h2, f2Num_with]

theorem f2Den_fast (m a b c d : Nat) (h : a + b + (c + d) ≤ m) :
    ((rowsArr m).getD (a + b + (c + d)) #[]).getD (a + c) 0 = f2Den a b c d := by
  rw [rowsArr_getD m _ h, f2Den_with]

end SMRT

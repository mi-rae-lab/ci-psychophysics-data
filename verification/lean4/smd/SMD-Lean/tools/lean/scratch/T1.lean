example (h : Nat) (hh : h ≤ 116) : ((min 120 (max 0 ((h : Int) + 4).toNat) : Nat) : Int) = (h : Int) + 4 := by omega
example (h : Nat) (hh : 4 ≤ h) (h2 : h ≤ 120) : ((min 120 (max 0 ((h : Int) + -1 * 4).toNat) : Nat) : Int) = (h : Int) + -1 * 4 := by omega
example (h : Nat) (hh : h % 4 = 0) (h1 : ¬ h ≥ 120) : h + 4 ≤ 120 := by omega

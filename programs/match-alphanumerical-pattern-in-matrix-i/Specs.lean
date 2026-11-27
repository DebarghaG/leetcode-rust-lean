import Aegis.FindPattern.Code.Funs

/-!
# Specifications of `Aegis.FindPattern.find_pattern`

LeetCode problem `match-alphanumerical-pattern-in-matrix-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.FindPattern

def isDigitCode (c : Nat) : Prop := 48 ≤ c ∧ c ≤ 57

def isLowerCode (c : Nat) : Prop := 97 ≤ c ∧ c ≤ 122

def boardCell (board : Slice (alloc.vec.Vec I64)) (i j : Int) : Int :=
  (((board.val)[i.toNat]!).val[j.toNat]!).val

def patternCell (pattern : Slice (alloc.vec.Vec U8)) (u v : Nat) : Nat :=
  (((pattern.val)[u]!).val[v]!).val

def matchingPlacement (board : Slice (alloc.vec.Vec I64))
    (pattern : Slice (alloc.vec.Vec U8)) (n m p q : Nat) (R C : Int) : Prop :=
  0 ≤ R ∧ R + (p : Int) ≤ (n : Int) ∧ 0 ≤ C ∧ C + (q : Int) ≤ (m : Int) ∧
    (∀ u : Nat, u < p → ∀ v : Nat, v < q →
      (isDigitCode (patternCell pattern u v) →
        boardCell board (R + (u : Int)) (C + (v : Int)) =
          (patternCell pattern u v : Int) - 48)) ∧
    (∀ u : Nat, u < p → ∀ v : Nat, v < q →
      ∀ u' : Nat, u' < p → ∀ v' : Nat, v' < q →
        (patternCell pattern u v = patternCell pattern u' v' ↔
          boardCell board (R + (u : Int)) (C + (v : Int)) =
            boardCell board (R + (u' : Int)) (C + (v' : Int))))

def AnsEq (ans : alloc.vec.Vec I64) (a b : Int) : Prop :=
  ans.val.length = 2 ∧ (ans.val[0]!).val = a ∧ (ans.val[1]!).val = b

/-- The function returns a vector ans of length 2. If at least one matching placement exists, then ans=[R,C] where (R,C) is a matching placement and for every matching placement (R',C'), either R<R', or R=R' and C<=C'. If no matching placement exists, then ans=[-1,-1].
  Preconditions: Let n=len(board), m=len(board[0]), p=len(pattern), q=len(pattern[0]). Assume 1<=n<=50, 1<=m<=50, every row of board has length m, 1<=p<=50, 1<=q<=50, every row of pattern has length q, every board[i][j] satisfies 0<=board[i][j]<=9, and every pattern[u][v] is either an ASCII digit code (48<=pattern[u][v]<=57) or an ASCII lowercase letter code (97<=pattern[u][v]<=122). For this specification, a placement (R,C) matches pattern if 0<=R<=n-p, 0<=C<=m-q, and for all u,v,u',v' with 0<=u,u'<p and 0<=v,v'<q: (1) if pattern[u][v] is a digit code then board[R+u][C+v]=pattern[u][v]-48; and (2) pattern[u][v]=pattern[u'][v'] iff board[R+u][C+v]=board[R+u'][C+v']. -/
theorem spec_1 (board : Slice (alloc.vec.Vec I64))
    (pattern : Slice (alloc.vec.Vec U8)) (n m p q : Nat)
    (hbn : board.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
    (hbm : ∀ row ∈ board.val, row.val.length = m)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 50)
    (hbp : pattern.val.length = p)
    (hp1 : 1 ≤ p) (hp2 : p ≤ 50)
    (hbq : ∀ row ∈ pattern.val, row.val.length = q)
    (hq1 : 1 ≤ q) (hq2 : q ≤ 50)
    (hboard : ∀ i, i < n → ∀ j, j < m →
      0 ≤ boardCell board (i : Int) (j : Int) ∧ boardCell board (i : Int) (j : Int) ≤ 9)
    (hpat : ∀ u, u < p → ∀ v, v < q →
      isDigitCode (patternCell pattern u v) ∨ isLowerCode (patternCell pattern u v)) :
    ∃ ans, Aegis.FindPattern.find_pattern board pattern = ok ans ∧
      ans.val.length = 2 ∧
      ((∃ R C, matchingPlacement board pattern n m p q R C) →
        ∃ R C, (ans.val[0]!).val = R ∧ (ans.val[1]!).val = C ∧
          matchingPlacement board pattern n m p q R C ∧
          ∀ R' C', matchingPlacement board pattern n m p q R' C' →
            R < R' ∨ (R = R' ∧ C ≤ C')) ∧
      ((¬ ∃ R C, matchingPlacement board pattern n m p q R C) → AnsEq ans (-1) (-1)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (board : Slice (alloc.vec.Vec I64))
    (pattern : Slice (alloc.vec.Vec U8)) (n m p q : Nat)
    (hbn : board.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
    (hbm : ∀ row ∈ board.val, row.val.length = m)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 50)
    (hbp : pattern.val.length = p)
    (hp1 : 1 ≤ p) (hp2 : p ≤ 50)
    (hbq : ∀ row ∈ pattern.val, row.val.length = q)
    (hq1 : 1 ≤ q) (hq2 : q ≤ 50)
    (hboard : ∀ i, i < n → ∀ j, j < m →
      0 ≤ boardCell board (i : Int) (j : Int) ∧ boardCell board (i : Int) (j : Int) ≤ 9)
    (hpat : ∀ u, u < p → ∀ v, v < q →
      isDigitCode (patternCell pattern u v) ∨ isLowerCode (patternCell pattern u v)), ∃ ans, Aegis.FindPattern.find_pattern board pattern = ok ans ∧
      ans.val.length = 2 ∧
      ((∃ R C, matchingPlacement board pattern n m p q R C) →
        ∃ R C, (ans.val[0]!).val = R ∧ (ans.val[1]!).val = C ∧
          matchingPlacement board pattern n m p q R C ∧
          ∀ R' C', matchingPlacement board pattern n m p q R' C' →
            R < R' ∨ (R = R' ∧ C ≤ C')) ∧
      ((¬ ∃ R C, matchingPlacement board pattern n m p q R C) → AnsEq ans (-1) (-1))) := by
  sorry

/-- The function returns a result vector ans; it does not fail.
  Preconditions: Let n=len(board), m=len(board[0]), p=len(pattern), q=len(pattern[0]). Assume 1<=n<=50, 1<=m<=50, every row of board has length m, 1<=p<=50, 1<=q<=50, every row of pattern has length q, every board[i][j] satisfies 0<=board[i][j]<=9, and every pattern[u][v] is either an ASCII digit code (48<=pattern[u][v]<=57) or an ASCII lowercase letter code (97<=pattern[u][v]<=122). -/
theorem spec_2 (board : Slice (alloc.vec.Vec I64))
    (pattern : Slice (alloc.vec.Vec U8)) (n m p q : Nat)
    (hbn : board.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
    (hbm : ∀ row ∈ board.val, row.val.length = m)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 50)
    (hbp : pattern.val.length = p)
    (hp1 : 1 ≤ p) (hp2 : p ≤ 50)
    (hbq : ∀ row ∈ pattern.val, row.val.length = q)
    (hq1 : 1 ≤ q) (hq2 : q ≤ 50)
    (hboard : ∀ i, i < n → ∀ j, j < m →
      0 ≤ boardCell board (i : Int) (j : Int) ∧ boardCell board (i : Int) (j : Int) ≤ 9)
    (hpat : ∀ u, u < p → ∀ v, v < q →
      isDigitCode (patternCell pattern u v) ∨ isLowerCode (patternCell pattern u v)) :
    ∃ ans, Aegis.FindPattern.find_pattern board pattern = ok ans := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (board : Slice (alloc.vec.Vec I64))
    (pattern : Slice (alloc.vec.Vec U8)) (n m p q : Nat)
    (hbn : board.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
    (hbm : ∀ row ∈ board.val, row.val.length = m)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 50)
    (hbp : pattern.val.length = p)
    (hp1 : 1 ≤ p) (hp2 : p ≤ 50)
    (hbq : ∀ row ∈ pattern.val, row.val.length = q)
    (hq1 : 1 ≤ q) (hq2 : q ≤ 50)
    (hboard : ∀ i, i < n → ∀ j, j < m →
      0 ≤ boardCell board (i : Int) (j : Int) ∧ boardCell board (i : Int) (j : Int) ≤ 9)
    (hpat : ∀ u, u < p → ∀ v, v < q →
      isDigitCode (patternCell pattern u v) ∨ isLowerCode (patternCell pattern u v)), ∃ ans, Aegis.FindPattern.find_pattern board pattern = ok ans) := by
  sorry

/-- Whenever the function returns ans, ans=[-1,-1] if and only if there is no matching placement (R,C).
  Preconditions: Let n=len(board), m=len(board[0]), p=len(pattern), q=len(pattern[0]). Assume 1<=n<=50, 1<=m<=50, every row of board has length m, 1<=p<=50, 1<=q<=50, every row of pattern has length q, every board[i][j] satisfies 0<=board[i][j]<=9, and every pattern[u][v] is either an ASCII digit code or an ASCII lowercase letter code. Define a matching placement as in spec_1: 0<=R<=n-p, 0<=C<=m-q, digit cells agree, and pattern-character equality coincides with board-value equality in the window. -/
theorem spec_3 (board : Slice (alloc.vec.Vec I64))
    (pattern : Slice (alloc.vec.Vec U8)) (n m p q : Nat)
    (hbn : board.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
    (hbm : ∀ row ∈ board.val, row.val.length = m)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 50)
    (hbp : pattern.val.length = p)
    (hp1 : 1 ≤ p) (hp2 : p ≤ 50)
    (hbq : ∀ row ∈ pattern.val, row.val.length = q)
    (hq1 : 1 ≤ q) (hq2 : q ≤ 50)
    (hboard : ∀ i, i < n → ∀ j, j < m →
      0 ≤ boardCell board (i : Int) (j : Int) ∧ boardCell board (i : Int) (j : Int) ≤ 9)
    (hpat : ∀ u, u < p → ∀ v, v < q →
      isDigitCode (patternCell pattern u v) ∨ isLowerCode (patternCell pattern u v)) :
    ∀ ans, Aegis.FindPattern.find_pattern board pattern = ok ans →
      (AnsEq ans (-1) (-1) ↔
        ¬ ∃ R C, matchingPlacement board pattern n m p q R C) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (board : Slice (alloc.vec.Vec I64))
    (pattern : Slice (alloc.vec.Vec U8)) (n m p q : Nat)
    (hbn : board.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
    (hbm : ∀ row ∈ board.val, row.val.length = m)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 50)
    (hbp : pattern.val.length = p)
    (hp1 : 1 ≤ p) (hp2 : p ≤ 50)
    (hbq : ∀ row ∈ pattern.val, row.val.length = q)
    (hq1 : 1 ≤ q) (hq2 : q ≤ 50)
    (hboard : ∀ i, i < n → ∀ j, j < m →
      0 ≤ boardCell board (i : Int) (j : Int) ∧ boardCell board (i : Int) (j : Int) ≤ 9)
    (hpat : ∀ u, u < p → ∀ v, v < q →
      isDigitCode (patternCell pattern u v) ∨ isLowerCode (patternCell pattern u v)), ∀ ans, Aegis.FindPattern.find_pattern board pattern = ok ans →
      (AnsEq ans (-1) (-1) ↔
        ¬ ∃ R C, matchingPlacement board pattern n m p q R C)) := by
  sorry

/-- Whenever the function returns ans and ans!=[-1,-1], the pair (ans[0],ans[1]) is a matching placement: 0<=ans[0]<=n-p, 0<=ans[1]<=m-q, every digit pattern cell equals the corresponding board digit, and equal pattern characters correspond to equal board values while different pattern characters correspond to different board values within the selected window.
  Preconditions: Let n=len(board), m=len(board[0]), p=len(pattern), q=len(pattern[0]). Assume 1<=n<=50, 1<=m<=50, every row of board has length m, 1<=p<=50, 1<=q<=50, every row of pattern has length q, every board[i][j] satisfies 0<=board[i][j]<=9, and every pattern[u][v] is either an ASCII digit code or an ASCII lowercase letter code. Define a matching placement as in spec_1. -/
theorem spec_4 (board : Slice (alloc.vec.Vec I64))
    (pattern : Slice (alloc.vec.Vec U8)) (n m p q : Nat)
    (hbn : board.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
    (hbm : ∀ row ∈ board.val, row.val.length = m)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 50)
    (hbp : pattern.val.length = p)
    (hp1 : 1 ≤ p) (hp2 : p ≤ 50)
    (hbq : ∀ row ∈ pattern.val, row.val.length = q)
    (hq1 : 1 ≤ q) (hq2 : q ≤ 50)
    (hboard : ∀ i, i < n → ∀ j, j < m →
      0 ≤ boardCell board (i : Int) (j : Int) ∧ boardCell board (i : Int) (j : Int) ≤ 9)
    (hpat : ∀ u, u < p → ∀ v, v < q →
      isDigitCode (patternCell pattern u v) ∨ isLowerCode (patternCell pattern u v)) :
    ∀ ans, Aegis.FindPattern.find_pattern board pattern = ok ans →
      ¬ AnsEq ans (-1) (-1) →
        matchingPlacement board pattern n m p q (ans.val[0]!).val (ans.val[1]!).val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (board : Slice (alloc.vec.Vec I64))
    (pattern : Slice (alloc.vec.Vec U8)) (n m p q : Nat)
    (hbn : board.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
    (hbm : ∀ row ∈ board.val, row.val.length = m)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 50)
    (hbp : pattern.val.length = p)
    (hp1 : 1 ≤ p) (hp2 : p ≤ 50)
    (hbq : ∀ row ∈ pattern.val, row.val.length = q)
    (hq1 : 1 ≤ q) (hq2 : q ≤ 50)
    (hboard : ∀ i, i < n → ∀ j, j < m →
      0 ≤ boardCell board (i : Int) (j : Int) ∧ boardCell board (i : Int) (j : Int) ≤ 9)
    (hpat : ∀ u, u < p → ∀ v, v < q →
      isDigitCode (patternCell pattern u v) ∨ isLowerCode (patternCell pattern u v)), ∀ ans, Aegis.FindPattern.find_pattern board pattern = ok ans →
      ¬ AnsEq ans (-1) (-1) →
        matchingPlacement board pattern n m p q (ans.val[0]!).val (ans.val[1]!).val) := by
  sorry

/-- Whenever the function returns ans and ans!=[-1,-1], for every matching placement (R',C'), ans[0]<=R'.
  Preconditions: Let n=len(board), m=len(board[0]), p=len(pattern), q=len(pattern[0]). Assume 1<=n<=50, 1<=m<=50, every row of board has length m, 1<=p<=50, 1<=q<=50, every row of pattern has length q, every board[i][j] satisfies 0<=board[i][j]<=9, and every pattern[u][v] is either an ASCII digit code or an ASCII lowercase letter code. Define a matching placement as in spec_1. -/
theorem spec_5 (board : Slice (alloc.vec.Vec I64))
    (pattern : Slice (alloc.vec.Vec U8)) (n m p q : Nat)
    (hbn : board.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
    (hbm : ∀ row ∈ board.val, row.val.length = m)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 50)
    (hbp : pattern.val.length = p)
    (hp1 : 1 ≤ p) (hp2 : p ≤ 50)
    (hbq : ∀ row ∈ pattern.val, row.val.length = q)
    (hq1 : 1 ≤ q) (hq2 : q ≤ 50)
    (hboard : ∀ i, i < n → ∀ j, j < m →
      0 ≤ boardCell board (i : Int) (j : Int) ∧ boardCell board (i : Int) (j : Int) ≤ 9)
    (hpat : ∀ u, u < p → ∀ v, v < q →
      isDigitCode (patternCell pattern u v) ∨ isLowerCode (patternCell pattern u v)) :
    ∀ ans, Aegis.FindPattern.find_pattern board pattern = ok ans →
      ¬ AnsEq ans (-1) (-1) →
        ∀ R' C', matchingPlacement board pattern n m p q R' C' →
          (ans.val[0]!).val ≤ R' := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (board : Slice (alloc.vec.Vec I64))
    (pattern : Slice (alloc.vec.Vec U8)) (n m p q : Nat)
    (hbn : board.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
    (hbm : ∀ row ∈ board.val, row.val.length = m)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 50)
    (hbp : pattern.val.length = p)
    (hp1 : 1 ≤ p) (hp2 : p ≤ 50)
    (hbq : ∀ row ∈ pattern.val, row.val.length = q)
    (hq1 : 1 ≤ q) (hq2 : q ≤ 50)
    (hboard : ∀ i, i < n → ∀ j, j < m →
      0 ≤ boardCell board (i : Int) (j : Int) ∧ boardCell board (i : Int) (j : Int) ≤ 9)
    (hpat : ∀ u, u < p → ∀ v, v < q →
      isDigitCode (patternCell pattern u v) ∨ isLowerCode (patternCell pattern u v)), ∀ ans, Aegis.FindPattern.find_pattern board pattern = ok ans →
      ¬ AnsEq ans (-1) (-1) →
        ∀ R' C', matchingPlacement board pattern n m p q R' C' →
          (ans.val[0]!).val ≤ R') := by
  sorry

/-- Whenever the function returns ans and ans!=[-1,-1], for every matching placement (R',C') with R'=ans[0], ans[1]<=C'.
  Preconditions: Let n=len(board), m=len(board[0]), p=len(pattern), q=len(pattern[0]). Assume 1<=n<=50, 1<=m<=50, every row of board has length m, 1<=p<=50, 1<=q<=50, every row of pattern has length q, every board[i][j] satisfies 0<=board[i][j]<=9, and every pattern[u][v] is either an ASCII digit code or an ASCII lowercase letter code. Define a matching placement as in spec_1. -/
theorem spec_6 (board : Slice (alloc.vec.Vec I64))
    (pattern : Slice (alloc.vec.Vec U8)) (n m p q : Nat)
    (hbn : board.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
    (hbm : ∀ row ∈ board.val, row.val.length = m)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 50)
    (hbp : pattern.val.length = p)
    (hp1 : 1 ≤ p) (hp2 : p ≤ 50)
    (hbq : ∀ row ∈ pattern.val, row.val.length = q)
    (hq1 : 1 ≤ q) (hq2 : q ≤ 50)
    (hboard : ∀ i, i < n → ∀ j, j < m →
      0 ≤ boardCell board (i : Int) (j : Int) ∧ boardCell board (i : Int) (j : Int) ≤ 9)
    (hpat : ∀ u, u < p → ∀ v, v < q →
      isDigitCode (patternCell pattern u v) ∨ isLowerCode (patternCell pattern u v)) :
    ∀ ans, Aegis.FindPattern.find_pattern board pattern = ok ans →
      ¬ AnsEq ans (-1) (-1) →
        ∀ R' C', matchingPlacement board pattern n m p q R' C' →
          R' = (ans.val[0]!).val → (ans.val[1]!).val ≤ C' := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (board : Slice (alloc.vec.Vec I64))
    (pattern : Slice (alloc.vec.Vec U8)) (n m p q : Nat)
    (hbn : board.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
    (hbm : ∀ row ∈ board.val, row.val.length = m)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 50)
    (hbp : pattern.val.length = p)
    (hp1 : 1 ≤ p) (hp2 : p ≤ 50)
    (hbq : ∀ row ∈ pattern.val, row.val.length = q)
    (hq1 : 1 ≤ q) (hq2 : q ≤ 50)
    (hboard : ∀ i, i < n → ∀ j, j < m →
      0 ≤ boardCell board (i : Int) (j : Int) ∧ boardCell board (i : Int) (j : Int) ≤ 9)
    (hpat : ∀ u, u < p → ∀ v, v < q →
      isDigitCode (patternCell pattern u v) ∨ isLowerCode (patternCell pattern u v)), ∀ ans, Aegis.FindPattern.find_pattern board pattern = ok ans →
      ¬ AnsEq ans (-1) (-1) →
        ∀ R' C', matchingPlacement board pattern n m p q R' C' →
          R' = (ans.val[0]!).val → (ans.val[1]!).val ≤ C') := by
  sorry

/-- Whenever the function returns ans and ans!=[-1,-1], 0<=ans[0]<=n-p and 0<=ans[1]<=m-q; in particular, the selected p by q window fits inside board.
  Preconditions: Let n=len(board), m=len(board[0]), p=len(pattern), q=len(pattern[0]). Assume 1<=n<=50, 1<=m<=50, every row of board has length m, 1<=p<=50, 1<=q<=50, every row of pattern has length q, every board[i][j] satisfies 0<=board[i][j]<=9, and every pattern[u][v] is either an ASCII digit code or an ASCII lowercase letter code. -/
theorem spec_7 (board : Slice (alloc.vec.Vec I64))
    (pattern : Slice (alloc.vec.Vec U8)) (n m p q : Nat)
    (hbn : board.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
    (hbm : ∀ row ∈ board.val, row.val.length = m)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 50)
    (hbp : pattern.val.length = p)
    (hp1 : 1 ≤ p) (hp2 : p ≤ 50)
    (hbq : ∀ row ∈ pattern.val, row.val.length = q)
    (hq1 : 1 ≤ q) (hq2 : q ≤ 50)
    (hboard : ∀ i, i < n → ∀ j, j < m →
      0 ≤ boardCell board (i : Int) (j : Int) ∧ boardCell board (i : Int) (j : Int) ≤ 9)
    (hpat : ∀ u, u < p → ∀ v, v < q →
      isDigitCode (patternCell pattern u v) ∨ isLowerCode (patternCell pattern u v)) :
    ∀ ans, Aegis.FindPattern.find_pattern board pattern = ok ans →
      ¬ AnsEq ans (-1) (-1) →
        0 ≤ (ans.val[0]!).val ∧ (ans.val[0]!).val + (p : Int) ≤ (n : Int) ∧
          0 ≤ (ans.val[1]!).val ∧ (ans.val[1]!).val + (q : Int) ≤ (m : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (board : Slice (alloc.vec.Vec I64))
    (pattern : Slice (alloc.vec.Vec U8)) (n m p q : Nat)
    (hbn : board.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
    (hbm : ∀ row ∈ board.val, row.val.length = m)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 50)
    (hbp : pattern.val.length = p)
    (hp1 : 1 ≤ p) (hp2 : p ≤ 50)
    (hbq : ∀ row ∈ pattern.val, row.val.length = q)
    (hq1 : 1 ≤ q) (hq2 : q ≤ 50)
    (hboard : ∀ i, i < n → ∀ j, j < m →
      0 ≤ boardCell board (i : Int) (j : Int) ∧ boardCell board (i : Int) (j : Int) ≤ 9)
    (hpat : ∀ u, u < p → ∀ v, v < q →
      isDigitCode (patternCell pattern u v) ∨ isLowerCode (patternCell pattern u v)), ∀ ans, Aegis.FindPattern.find_pattern board pattern = ok ans →
      ¬ AnsEq ans (-1) (-1) →
        0 ≤ (ans.val[0]!).val ∧ (ans.val[0]!).val + (p : Int) ≤ (n : Int) ∧
          0 ≤ (ans.val[1]!).val ∧ (ans.val[1]!).val + (q : Int) ≤ (m : Int)) := by
  sorry

/-- Whenever the function returns ans and ans!=[-1,-1], for all 0<=u,u'<p and 0<=v,v'<q, if pattern[u][v]=pattern[u'][v'] then board[ans[0]+u][ans[1]+v]=board[ans[0]+u'][ans[1]+v'].
  Preconditions: Let n=len(board), m=len(board[0]), p=len(pattern), q=len(pattern[0]). Assume 1<=n<=50, 1<=m<=50, every row of board has length m, 1<=p<=50, 1<=q<=50, every row of pattern has length q, every board[i][j] satisfies 0<=board[i][j]<=9, and every pattern[u][v] is either an ASCII digit code or an ASCII lowercase letter code. Define a matching placement as in spec_1. -/
theorem spec_8 (board : Slice (alloc.vec.Vec I64))
    (pattern : Slice (alloc.vec.Vec U8)) (n m p q : Nat)
    (hbn : board.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
    (hbm : ∀ row ∈ board.val, row.val.length = m)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 50)
    (hbp : pattern.val.length = p)
    (hp1 : 1 ≤ p) (hp2 : p ≤ 50)
    (hbq : ∀ row ∈ pattern.val, row.val.length = q)
    (hq1 : 1 ≤ q) (hq2 : q ≤ 50)
    (hboard : ∀ i, i < n → ∀ j, j < m →
      0 ≤ boardCell board (i : Int) (j : Int) ∧ boardCell board (i : Int) (j : Int) ≤ 9)
    (hpat : ∀ u, u < p → ∀ v, v < q →
      isDigitCode (patternCell pattern u v) ∨ isLowerCode (patternCell pattern u v)) :
    ∀ ans, Aegis.FindPattern.find_pattern board pattern = ok ans →
      ¬ AnsEq ans (-1) (-1) →
        ∀ u, u < p → ∀ v, v < q → ∀ u', u' < p → ∀ v', v' < q →
          patternCell pattern u v = patternCell pattern u' v' →
            boardCell board ((ans.val[0]!).val + (u : Int))
                ((ans.val[1]!).val + (v : Int)) =
              boardCell board ((ans.val[0]!).val + (u' : Int))
                ((ans.val[1]!).val + (v' : Int)) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (board : Slice (alloc.vec.Vec I64))
    (pattern : Slice (alloc.vec.Vec U8)) (n m p q : Nat)
    (hbn : board.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
    (hbm : ∀ row ∈ board.val, row.val.length = m)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 50)
    (hbp : pattern.val.length = p)
    (hp1 : 1 ≤ p) (hp2 : p ≤ 50)
    (hbq : ∀ row ∈ pattern.val, row.val.length = q)
    (hq1 : 1 ≤ q) (hq2 : q ≤ 50)
    (hboard : ∀ i, i < n → ∀ j, j < m →
      0 ≤ boardCell board (i : Int) (j : Int) ∧ boardCell board (i : Int) (j : Int) ≤ 9)
    (hpat : ∀ u, u < p → ∀ v, v < q →
      isDigitCode (patternCell pattern u v) ∨ isLowerCode (patternCell pattern u v)), ∀ ans, Aegis.FindPattern.find_pattern board pattern = ok ans →
      ¬ AnsEq ans (-1) (-1) →
        ∀ u, u < p → ∀ v, v < q → ∀ u', u' < p → ∀ v', v' < q →
          patternCell pattern u v = patternCell pattern u' v' →
            boardCell board ((ans.val[0]!).val + (u : Int))
                ((ans.val[1]!).val + (v : Int)) =
              boardCell board ((ans.val[0]!).val + (u' : Int))
                ((ans.val[1]!).val + (v' : Int))) := by
  sorry

/-- Whenever the function returns ans and ans!=[-1,-1], for all 0<=u,u'<p and 0<=v,v'<q, if pattern[u][v]!=pattern[u'][v'] then board[ans[0]+u][ans[1]+v]!=board[ans[0]+u'][ans[1]+v'].
  Preconditions: Let n=len(board), m=len(board[0]), p=len(pattern), q=len(pattern[0]). Assume 1<=n<=50, 1<=m<=50, every row of board has length m, 1<=p<=50, 1<=q<=50, every row of pattern has length q, every board[i][j] satisfies 0<=board[i][j]<=9, and every pattern[u][v] is either an ASCII digit code or an ASCII lowercase letter code. Define a matching placement as in spec_1. -/
theorem spec_9 (board : Slice (alloc.vec.Vec I64))
    (pattern : Slice (alloc.vec.Vec U8)) (n m p q : Nat)
    (hbn : board.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
    (hbm : ∀ row ∈ board.val, row.val.length = m)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 50)
    (hbp : pattern.val.length = p)
    (hp1 : 1 ≤ p) (hp2 : p ≤ 50)
    (hbq : ∀ row ∈ pattern.val, row.val.length = q)
    (hq1 : 1 ≤ q) (hq2 : q ≤ 50)
    (hboard : ∀ i, i < n → ∀ j, j < m →
      0 ≤ boardCell board (i : Int) (j : Int) ∧ boardCell board (i : Int) (j : Int) ≤ 9)
    (hpat : ∀ u, u < p → ∀ v, v < q →
      isDigitCode (patternCell pattern u v) ∨ isLowerCode (patternCell pattern u v)) :
    ∀ ans, Aegis.FindPattern.find_pattern board pattern = ok ans →
      ¬ AnsEq ans (-1) (-1) →
        ∀ u, u < p → ∀ v, v < q → ∀ u', u' < p → ∀ v', v' < q →
          patternCell pattern u v ≠ patternCell pattern u' v' →
            boardCell board ((ans.val[0]!).val + (u : Int))
                ((ans.val[1]!).val + (v : Int)) ≠
              boardCell board ((ans.val[0]!).val + (u' : Int))
                ((ans.val[1]!).val + (v' : Int)) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (board : Slice (alloc.vec.Vec I64))
    (pattern : Slice (alloc.vec.Vec U8)) (n m p q : Nat)
    (hbn : board.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
    (hbm : ∀ row ∈ board.val, row.val.length = m)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 50)
    (hbp : pattern.val.length = p)
    (hp1 : 1 ≤ p) (hp2 : p ≤ 50)
    (hbq : ∀ row ∈ pattern.val, row.val.length = q)
    (hq1 : 1 ≤ q) (hq2 : q ≤ 50)
    (hboard : ∀ i, i < n → ∀ j, j < m →
      0 ≤ boardCell board (i : Int) (j : Int) ∧ boardCell board (i : Int) (j : Int) ≤ 9)
    (hpat : ∀ u, u < p → ∀ v, v < q →
      isDigitCode (patternCell pattern u v) ∨ isLowerCode (patternCell pattern u v)), ∀ ans, Aegis.FindPattern.find_pattern board pattern = ok ans →
      ¬ AnsEq ans (-1) (-1) →
        ∀ u, u < p → ∀ v, v < q → ∀ u', u' < p → ∀ v', v' < q →
          patternCell pattern u v ≠ patternCell pattern u' v' →
            boardCell board ((ans.val[0]!).val + (u : Int))
                ((ans.val[1]!).val + (v : Int)) ≠
              boardCell board ((ans.val[0]!).val + (u' : Int))
                ((ans.val[1]!).val + (v' : Int))) := by
  sorry

/-- Whenever the function returns ans and ans!=[-1,-1], for every 0<=u<p and 0<=v<q such that pattern[u][v] is an ASCII digit code, board[ans[0]+u][ans[1]+v]=pattern[u][v]-48.
  Preconditions: Let n=len(board), m=len(board[0]), p=len(pattern), q=len(pattern[0]). Assume 1<=n<=50, 1<=m<=50, every row of board has length m, 1<=p<=50, 1<=q<=50, every row of pattern has length q, every board[i][j] satisfies 0<=board[i][j]<=9, and every pattern[u][v] is either an ASCII digit code or an ASCII lowercase letter code. Define a matching placement as in spec_1. -/
theorem spec_10 (board : Slice (alloc.vec.Vec I64))
    (pattern : Slice (alloc.vec.Vec U8)) (n m p q : Nat)
    (hbn : board.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
    (hbm : ∀ row ∈ board.val, row.val.length = m)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 50)
    (hbp : pattern.val.length = p)
    (hp1 : 1 ≤ p) (hp2 : p ≤ 50)
    (hbq : ∀ row ∈ pattern.val, row.val.length = q)
    (hq1 : 1 ≤ q) (hq2 : q ≤ 50)
    (hboard : ∀ i, i < n → ∀ j, j < m →
      0 ≤ boardCell board (i : Int) (j : Int) ∧ boardCell board (i : Int) (j : Int) ≤ 9)
    (hpat : ∀ u, u < p → ∀ v, v < q →
      isDigitCode (patternCell pattern u v) ∨ isLowerCode (patternCell pattern u v)) :
    ∀ ans, Aegis.FindPattern.find_pattern board pattern = ok ans →
      ¬ AnsEq ans (-1) (-1) →
        ∀ u, u < p → ∀ v, v < q → isDigitCode (patternCell pattern u v) →
          boardCell board ((ans.val[0]!).val + (u : Int))
              ((ans.val[1]!).val + (v : Int)) =
            (patternCell pattern u v : Int) - 48 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (board : Slice (alloc.vec.Vec I64))
    (pattern : Slice (alloc.vec.Vec U8)) (n m p q : Nat)
    (hbn : board.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
    (hbm : ∀ row ∈ board.val, row.val.length = m)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 50)
    (hbp : pattern.val.length = p)
    (hp1 : 1 ≤ p) (hp2 : p ≤ 50)
    (hbq : ∀ row ∈ pattern.val, row.val.length = q)
    (hq1 : 1 ≤ q) (hq2 : q ≤ 50)
    (hboard : ∀ i, i < n → ∀ j, j < m →
      0 ≤ boardCell board (i : Int) (j : Int) ∧ boardCell board (i : Int) (j : Int) ≤ 9)
    (hpat : ∀ u, u < p → ∀ v, v < q →
      isDigitCode (patternCell pattern u v) ∨ isLowerCode (patternCell pattern u v)), ∀ ans, Aegis.FindPattern.find_pattern board pattern = ok ans →
      ¬ AnsEq ans (-1) (-1) →
        ∀ u, u < p → ∀ v, v < q → isDigitCode (patternCell pattern u v) →
          boardCell board ((ans.val[0]!).val + (u : Int))
              ((ans.val[1]!).val + (v : Int)) =
            (patternCell pattern u v : Int) - 48) := by
  sorry

end AegisSpec.FindPattern

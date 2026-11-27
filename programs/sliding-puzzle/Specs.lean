import Aegis.SlidingPuzzle.Code.Funs

/-!
# Specifications of `Aegis.SlidingPuzzle.sliding_puzzle`

LeetCode problem `sliding-puzzle`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.SlidingPuzzle

  def rowList (board : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : List Int :=
    ((board.list.toList[i]?).map (fun row => row.slice.list.toList.map (fun x => x.val))).getD []

  def entries (board : Slice (alloc.vec.Vec Std.I64)) : List Int :=
    rowList board 0 ++ rowList board 1

  def cell (board : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Int :=
    (rowList board i)[j]?.getD 0

  def Pre (board : Slice (alloc.vec.Vec Std.I64)) : Prop :=
    board.leng = 2 ∧
    (rowList board 0).length = 3 ∧
    (rowList board 1).length = 3 ∧
    (∀ x ∈ entries board, 0 ≤ x ∧ x ≤ 5) ∧
    (entries board).Nodup

  abbrev State : Type := Fin 2 → Fin 3 → Int

  def solved : State :=
    fun i j =>
      if i.val = 0 then (if j.val = 0 then 1 else if j.val = 1 then 2 else 3)
      else (if j.val = 0 then 4 else if j.val = 1 then 5 else 0)

  def stateEntries (s : State) : List Int :=
    [s 0 0, s 0 1, s 0 2, s 1 0, s 1 1, s 1 2]

  def toState (board : Slice (alloc.vec.Vec Std.I64)) : State :=
    fun i j => cell board i.val j.val

  def ValidMove (s t : State) : Prop :=
    ∃ (i i' : Fin 2) (j j' : Fin 3),
      s i j = 0 ∧
      Int.natAbs ((i.val : Int) - (i'.val : Int)) +
        Int.natAbs ((j.val : Int) - (j'.val : Int)) = 1 ∧
      t = (fun a b => if a = i ∧ b = j then s i' j'
                      else if a = i' ∧ b = j' then s i j
                      else s a b)

  def MovesTo (s t : State) : Nat → Prop
    | 0 => s = t
    | n + 1 => ∃ u : State, MovesTo s u n ∧ ValidMove u t

  def Reachable (s t : State) : Prop := ∃ k : Nat, MovesTo s t k

  def Solved (board : Slice (alloc.vec.Vec Std.I64)) : Prop :=
    cell board 0 0 = 1 ∧ cell board 0 1 = 2 ∧ cell board 0 2 = 3 ∧
    cell board 1 0 = 4 ∧ cell board 1 1 = 5 ∧ cell board 1 2 = 0

  def inversions : List Int → Nat
    | [] => 0
    | x :: xs => xs.countP (fun y => decide (x > y)) + inversions xs

  def nonzeroEntries (board : Slice (alloc.vec.Vec Std.I64)) : List Int :=
    (entries board).filter (fun x => decide (x ≠ 0))

  def inv (board : Slice (alloc.vec.Vec Std.I64)) : Nat :=
    inversions (nonzeroEntries board)

  def stateInv (s : State) : Nat :=
    inversions ((stateEntries s).filter (fun x => decide (x ≠ 0)))

  /-- Define a state to be a 2 x 3 array containing the six values 0,1,2,3,4,5, each exactly once. Call a state solved when it is [[1,2,3],[4,5,0]]. A valid move from a state s is: let (i,j) be the unique cell with s[i][j]=0; choose a cell (i',j') with 0 <= i' < 2, 0 <= j' < 3 and |i-i'| + |j-j'| = 1; swap s[i][j] and s[i'][j']. A k-move sequence from board to solved is a list s_0,...,s_k of states with s_0=board, s_k=solved, and each s_{t+1} obtained from s_t by one valid move. The function returns a result r, and either: (1) r = -1 and there is no k >= 0 for which a k-move sequence from board to solved exists; or (2) r >= 0, there exists an r-move sequence from board to solved, and for every k with 0 <= k < r no k-move sequence from board to solved exists.
    Preconditions: len(board) = 2; len(board[0]) = len(board[1]) = 3; for every i with 0 <= i < 2 and j with 0 <= j < 3, board[i][j] is an integer with 0 <= board[i][j] <= 5; the six entries board[0][0], board[0][1], board[0][2], board[1][0], board[1][1], board[1][2] are pairwise distinct. -/
  theorem spec_1 (board : Slice (alloc.vec.Vec Std.I64)) (h : Pre board) :
      ∃ r : Std.I64, Aegis.SlidingPuzzle.sliding_puzzle board = ok r ∧
        ((r.val = -1 ∧ ∀ k : Nat, ¬ MovesTo (toState board) solved k) ∨
         (0 ≤ r.val ∧ MovesTo (toState board) solved r.val.toNat ∧
          ∀ k : Nat, k < r.val.toNat → ¬ MovesTo (toState board) solved k)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (board : Slice (alloc.vec.Vec Std.I64)) (h : Pre board), ∃ r : Std.I64, Aegis.SlidingPuzzle.sliding_puzzle board = ok r ∧
          ((r.val = -1 ∧ ∀ k : Nat, ¬ MovesTo (toState board) solved k) ∨
           (0 ≤ r.val ∧ MovesTo (toState board) solved r.val.toNat ∧
            ∀ k : Nat, k < r.val.toNat → ¬ MovesTo (toState board) solved k))) := by
    sorry

  /-- For every board satisfying the preconditions, the function returns a result r; it does not fail.
    Preconditions: len(board) = 2; len(board[0]) = len(board[1]) = 3; for every i with 0 <= i < 2 and j with 0 <= j < 3, board[i][j] is an integer with 0 <= board[i][j] <= 5; the six entries board[0][0], board[0][1], board[0][2], board[1][0], board[1][1], board[1][2] are pairwise distinct. -/
  theorem spec_2 (board : Slice (alloc.vec.Vec Std.I64)) (h : Pre board) :
      ∃ r : Std.I64, Aegis.SlidingPuzzle.sliding_puzzle board = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (board : Slice (alloc.vec.Vec Std.I64)) (h : Pre board), ∃ r : Std.I64, Aegis.SlidingPuzzle.sliding_puzzle board = ok r) := by
    sorry

  /-- Whenever the function returns a result r, either r = -1, or both 0 <= r and r <= 719.
    Preconditions: len(board) = 2; len(board[0]) = len(board[1]) = 3; for every i with 0 <= i < 2 and j with 0 <= j < 3, board[i][j] is an integer with 0 <= board[i][j] <= 5; the six entries board[0][0], board[0][1], board[0][2], board[1][0], board[1][1], board[1][2] are pairwise distinct. -/
  theorem spec_3 (board : Slice (alloc.vec.Vec Std.I64)) (h : Pre board) (r : Std.I64)
      (hret : Aegis.SlidingPuzzle.sliding_puzzle board = ok r) :
      r.val = -1 ∨ (0 ≤ r.val ∧ r.val ≤ 719) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (board : Slice (alloc.vec.Vec Std.I64)) (h : Pre board) (r : Std.I64)
        (hret : Aegis.SlidingPuzzle.sliding_puzzle board = ok r), r.val = -1 ∨ (0 ≤ r.val ∧ r.val ≤ 719)) := by
    sorry

  /-- The function returns a result r, and r = 0 if and only if board is solved, i.e. if and only if board[0][0]=1, board[0][1]=2, board[0][2]=3, board[1][0]=4, board[1][1]=5, and board[1][2]=0.
    Preconditions: len(board) = 2; len(board[0]) = len(board[1]) = 3; for every i with 0 <= i < 2 and j with 0 <= j < 3, board[i][j] is an integer with 0 <= board[i][j] <= 5; the six entries board[0][0], board[0][1], board[0][2], board[1][0], board[1][1], board[1][2] are pairwise distinct. -/
  theorem spec_4 (board : Slice (alloc.vec.Vec Std.I64)) (h : Pre board) :
      ∃ r : Std.I64, Aegis.SlidingPuzzle.sliding_puzzle board = ok r ∧
        (r.val = 0 ↔ Solved board) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (board : Slice (alloc.vec.Vec Std.I64)) (h : Pre board), ∃ r : Std.I64, Aegis.SlidingPuzzle.sliding_puzzle board = ok r ∧
          (r.val = 0 ↔ Solved board)) := by
    sorry

  /-- If there exists a valid move from board to the solved state [[1,2,3],[4,5,0]] (equivalently, if board becomes solved by swapping its unique 0 with one 4-directionally adjacent tile), then the function returns r = 1.
    Preconditions: len(board) = 2; len(board[0]) = len(board[1]) = 3; for every i with 0 <= i < 2 and j with 0 <= j < 3, board[i][j] is an integer with 0 <= board[i][j] <= 5; the six entries board[0][0], board[0][1], board[0][2], board[1][0], board[1][1], board[1][2] are pairwise distinct. -/
  theorem spec_5 (board : Slice (alloc.vec.Vec Std.I64)) (h : Pre board)
      (hmove : ValidMove (toState board) solved) :
      ∃ r : Std.I64, Aegis.SlidingPuzzle.sliding_puzzle board = ok r ∧ r.val = 1 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (board : Slice (alloc.vec.Vec Std.I64)) (h : Pre board)
        (hmove : ValidMove (toState board) solved), ∃ r : Std.I64, Aegis.SlidingPuzzle.sliding_puzzle board = ok r ∧ r.val = 1) := by
    sorry

  /-- Let L be the list of the five nonzero entries of board taken in row-major order (omitting the unique 0), and let inv(board) be the number of pairs (p,q) with 0 <= p < q < 5 and L[p] > L[q]. If inv(board) is odd, then the function returns r = -1.
    Preconditions: len(board) = 2; len(board[0]) = len(board[1]) = 3; for every i with 0 <= i < 2 and j with 0 <= j < 3, board[i][j] is an integer with 0 <= board[i][j] <= 5; the six entries board[0][0], board[0][1], board[0][2], board[1][0], board[1][1], board[1][2] are pairwise distinct. -/
  theorem spec_6 (board : Slice (alloc.vec.Vec Std.I64)) (h : Pre board)
      (hinv : inv board % 2 = 1) :
      ∃ r : Std.I64, Aegis.SlidingPuzzle.sliding_puzzle board = ok r ∧ r.val = -1 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (board : Slice (alloc.vec.Vec Std.I64)) (h : Pre board)
        (hinv : inv board % 2 = 1), ∃ r : Std.I64, Aegis.SlidingPuzzle.sliding_puzzle board = ok r ∧ r.val = -1) := by
    sorry

  /-- Let L be the list of the five nonzero entries of board taken in row-major order (omitting the unique 0), and let inv(board) be the number of pairs (p,q) with 0 <= p < q < 5 and L[p] > L[q]. If inv(board) is even, then the function returns a result r with r >= 0.
    Preconditions: len(board) = 2; len(board[0]) = len(board[1]) = 3; for every i with 0 <= i < 2 and j with 0 <= j < 3, board[i][j] is an integer with 0 <= board[i][j] <= 5; the six entries board[0][0], board[0][1], board[0][2], board[1][0], board[1][1], board[1][2] are pairwise distinct. -/
  theorem spec_7 (board : Slice (alloc.vec.Vec Std.I64)) (h : Pre board)
      (hinv : inv board % 2 = 0) :
      ∃ r : Std.I64, Aegis.SlidingPuzzle.sliding_puzzle board = ok r ∧ 0 ≤ r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (board : Slice (alloc.vec.Vec Std.I64)) (h : Pre board)
        (hinv : inv board % 2 = 0), ∃ r : Std.I64, Aegis.SlidingPuzzle.sliding_puzzle board = ok r ∧ 0 ≤ r.val) := by
    sorry

  /-- If the function returns a result r with r >= 0, then there exists a sequence of exactly r valid moves that transforms board into [[1,2,3],[4,5,0]], where a valid move swaps the unique 0 with a 4-directionally adjacent tile.
    Preconditions: len(board) = 2; len(board[0]) = len(board[1]) = 3; for every i with 0 <= i < 2 and j with 0 <= j < 3, board[i][j] is an integer with 0 <= board[i][j] <= 5; the six entries board[0][0], board[0][1], board[0][2], board[1][0], board[1][1], board[1][2] are pairwise distinct. -/
  theorem spec_8 (board : Slice (alloc.vec.Vec Std.I64)) (h : Pre board) (r : Std.I64)
      (hret : Aegis.SlidingPuzzle.sliding_puzzle board = ok r) (hge : 0 ≤ r.val) :
      MovesTo (toState board) solved r.val.toNat := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (board : Slice (alloc.vec.Vec Std.I64)) (h : Pre board) (r : Std.I64)
        (hret : Aegis.SlidingPuzzle.sliding_puzzle board = ok r) (hge : 0 ≤ r.val), MovesTo (toState board) solved r.val.toNat) := by
    sorry

  /-- If the function returns a result r with r >= 0, then for every k with 0 <= k < r there is no sequence of exactly k valid moves transforming board into [[1,2,3],[4,5,0]], where a valid move swaps the unique 0 with a 4-directionally adjacent tile.
    Preconditions: len(board) = 2; len(board[0]) = len(board[1]) = 3; for every i with 0 <= i < 2 and j with 0 <= j < 3, board[i][j] is an integer with 0 <= board[i][j] <= 5; the six entries board[0][0], board[0][1], board[0][2], board[1][0], board[1][1], board[1][2] are pairwise distinct. -/
  theorem spec_9 (board : Slice (alloc.vec.Vec Std.I64)) (h : Pre board) (r : Std.I64)
      (hret : Aegis.SlidingPuzzle.sliding_puzzle board = ok r) (hge : 0 ≤ r.val) :
      ∀ k : Nat, k < r.val.toNat → ¬ MovesTo (toState board) solved k := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (board : Slice (alloc.vec.Vec Std.I64)) (h : Pre board) (r : Std.I64)
        (hret : Aegis.SlidingPuzzle.sliding_puzzle board = ok r) (hge : 0 ≤ r.val), ∀ k : Nat, k < r.val.toNat → ¬ MovesTo (toState board) solved k) := by
    sorry

  /-- If the function returns r = -1, then for every k >= 0 there is no sequence of exactly k valid moves transforming board into [[1,2,3],[4,5,0]], where a valid move swaps the unique 0 with a 4-directionally adjacent tile.
    Preconditions: len(board) = 2; len(board[0]) = len(board[1]) = 3; for every i with 0 <= i < 2 and j with 0 <= j < 3, board[i][j] is an integer with 0 <= board[i][j] <= 5; the six entries board[0][0], board[0][1], board[0][2], board[1][0], board[1][1], board[1][2] are pairwise distinct. -/
  theorem spec_10 (board : Slice (alloc.vec.Vec Std.I64)) (h : Pre board) (r : Std.I64)
      (hret : Aegis.SlidingPuzzle.sliding_puzzle board = ok r) (hneg : r.val = -1) :
      ∀ k : Nat, ¬ MovesTo (toState board) solved k := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (board : Slice (alloc.vec.Vec Std.I64)) (h : Pre board) (r : Std.I64)
        (hret : Aegis.SlidingPuzzle.sliding_puzzle board = ok r) (hneg : r.val = -1), ∀ k : Nat, ¬ MovesTo (toState board) solved k) := by
    sorry

  /-- Suppose the function returns a result r with r >= 0, and let (i,j) be the unique cell with board[i][j]=0. Then r mod 2 = (i + j + 1) mod 2.
    Preconditions: len(board) = 2; len(board[0]) = len(board[1]) = 3; for every i with 0 <= i < 2 and j with 0 <= j < 3, board[i][j] is an integer with 0 <= board[i][j] <= 5; the six entries board[0][0], board[0][1], board[0][2], board[1][0], board[1][1], board[1][2] are pairwise distinct. -/
  theorem spec_11 (board : Slice (alloc.vec.Vec Std.I64)) (h : Pre board) (r : Std.I64)
      (hret : Aegis.SlidingPuzzle.sliding_puzzle board = ok r) (hge : 0 ≤ r.val)
      (i : Nat) (hi : i < 2) (j : Nat) (hj : j < 3) (hzero : cell board i j = 0) :
      r.val % 2 = ((i : Int) + (j : Int) + 1) % 2 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (board : Slice (alloc.vec.Vec Std.I64)) (h : Pre board) (r : Std.I64)
        (hret : Aegis.SlidingPuzzle.sliding_puzzle board = ok r) (hge : 0 ≤ r.val)
        (i : Nat) (hi : i < 2) (j : Nat) (hj : j < 3) (hzero : cell board i j = 0), r.val % 2 = ((i : Int) + (j : Int) + 1) % 2) := by
    sorry

  /-- Let r be the result of the function on board and let r' be the result of the function on board'. Then r' = -1 if and only if r = -1.
    Preconditions: board satisfies: len(board) = 2; len(board[0]) = len(board[1]) = 3; for every i with 0 <= i < 2 and j with 0 <= j < 3, board[i][j] is an integer with 0 <= board[i][j] <= 5; the six entries of board are pairwise distinct. Also board' is any 2 x 3 state obtained from board by one valid move (swapping the unique 0 with a 4-directionally adjacent tile), so board' satisfies the same preconditions. -/
  theorem spec_12 (board board' : Slice (alloc.vec.Vec Std.I64)) (h : Pre board)
      (h' : Pre board') (hmove : ValidMove (toState board) (toState board')) :
      ∃ r r' : Std.I64, Aegis.SlidingPuzzle.sliding_puzzle board = ok r ∧
        Aegis.SlidingPuzzle.sliding_puzzle board' = ok r' ∧ (r'.val = -1 ↔ r.val = -1) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (board board' : Slice (alloc.vec.Vec Std.I64)) (h : Pre board)
        (h' : Pre board') (hmove : ValidMove (toState board) (toState board')), ∃ r r' : Std.I64, Aegis.SlidingPuzzle.sliding_puzzle board = ok r ∧
          Aegis.SlidingPuzzle.sliding_puzzle board' = ok r' ∧ (r'.val = -1 ↔ r.val = -1)) := by
    sorry

  /-- Let r be the result of the function on board and let r' be the result of the function on board'. If r >= 0 and r' >= 0, then r' = r - 1 or r' = r + 1.
    Preconditions: len(board) = 2; len(board[0]) = len(board[1]) = 3; for every i with 0 <= i < 2 and j with 0 <= j < 3, board[i][j] is an integer with 0 <= board[i][j] <= 5; the six entries board[0][0], board[0][1], board[0][2], board[1][0], board[1][1], board[1][2] are pairwise distinct. Also board' is any 2 x 3 state obtained from board by one valid move (swapping the unique 0 with a 4-directionally adjacent tile). -/
  theorem spec_13 (board board' : Slice (alloc.vec.Vec Std.I64)) (h : Pre board)
      (h' : Pre board') (hmove : ValidMove (toState board) (toState board'))
      (r r' : Std.I64) (hret : Aegis.SlidingPuzzle.sliding_puzzle board = ok r)
      (hret' : Aegis.SlidingPuzzle.sliding_puzzle board' = ok r')
      (hge : 0 ≤ r.val) (hge' : 0 ≤ r'.val) :
      r'.val = r.val - 1 ∨ r'.val = r.val + 1 := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (board board' : Slice (alloc.vec.Vec Std.I64)) (h : Pre board)
        (h' : Pre board') (hmove : ValidMove (toState board) (toState board'))
        (r r' : Std.I64) (hret : Aegis.SlidingPuzzle.sliding_puzzle board = ok r)
        (hret' : Aegis.SlidingPuzzle.sliding_puzzle board' = ok r')
        (hge : 0 ≤ r.val) (hge' : 0 ≤ r'.val), r'.val = r.val - 1 ∨ r'.val = r.val + 1) := by
    sorry

  end AegisSpec.SlidingPuzzle

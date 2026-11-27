import Aegis.ConnectSticks.Code.Funs

/-!
# Specifications of `Aegis.ConnectSticks.connect_sticks`

LeetCode problem `minimum-cost-to-connect-sticks`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.ConnectSticks

namespace AegisSpec.ConnectSticks

def contents (sticks : Slice Std.I64) : List ℤ := sticks.val.map (fun x => x.val)

def MergeStep (l l' : List ℤ) (c : ℤ) : Prop :=
  ∃ l₁ l₂ l₃ : List ℤ, ∃ x y : ℤ,
    l = l₁ ++ x :: l₂ ++ y :: l₃ ∧ l' = (x + y) :: (l₁ ++ l₂ ++ l₃) ∧ c = x + y

inductive MergeChain : ℕ → List ℤ → List ℤ → ℤ → Prop where

  | nil (l : List ℤ) : MergeChain 0 l l 0

  | step {k : ℕ} {l l' l'' : List ℤ} {c t : ℤ} :
      MergeStep l l' c → MergeChain k l' l'' t → MergeChain (k + 1) l l'' (c + t)

def CompleteMergeCost (l : List ℤ) (t : ℤ) : Prop :=
  ∃ l' : List ℤ, MergeChain (l.length - 1) l l' t ∧ l'.length = 1

def IsMinMergeCost (l : List ℤ) (r : ℤ) : Prop :=
  CompleteMergeCost l r ∧ ∀ t : ℤ, CompleteMergeCost l t → r ≤ t

def IsNondecreasing (l : List ℤ) : Prop := l.Pairwise (· ≤ ·)

def weightedTail : List ℤ → ℤ
  | [] => 0
  | v :: vs => ((vs.length + 1 : ℕ) : ℤ) * v + weightedTail vs

def sortedCostBound : List ℤ → ℤ
  | a₀ :: a₁ :: rest => ((rest.length + 1 : ℕ) : ℤ) * (a₀ + a₁) + weightedTail rest
  | _ => 0

/-- connect_sticks(sticks) returns a result r and r is the minimum possible total merge cost for sticks. Formally, a complete merge sequence starts with the multiset of the n stick lengths, consists of n-1 steps, each step chooses two current lengths x and y, removes them, inserts x+y, and adds x+y to a running total; for n=1 the empty sequence has cost 0. The value r equals the minimum of the running total over all complete merge sequences.
  Preconditions: Let n = len(sticks). 1 <= n <= 10000 and for every i with 0 <= i < n, 1 <= sticks[i] <= 10000. -/
theorem spec_1 (sticks : Slice Std.I64)
    (h_n_ge : 1 ≤ (contents sticks).length)
    (h_n_le : (contents sticks).length ≤ 10000)
    (h_pos : ∀ (i : ℕ) (hi : i < (contents sticks).length), 1 ≤ (contents sticks)[i])
    (h_le : ∀ (i : ℕ) (hi : i < (contents sticks).length), (contents sticks)[i] ≤ 10000) :
    ∃ r : Std.I64, connect_sticks sticks = ok r ∧ IsMinMergeCost (contents sticks) r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (sticks : Slice Std.I64)
    (h_n_ge : 1 ≤ (contents sticks).length)
    (h_n_le : (contents sticks).length ≤ 10000)
    (h_pos : ∀ (i : ℕ) (hi : i < (contents sticks).length), 1 ≤ (contents sticks)[i])
    (h_le : ∀ (i : ℕ) (hi : i < (contents sticks).length), (contents sticks)[i] ≤ 10000), ∃ r : Std.I64, connect_sticks sticks = ok r ∧ IsMinMergeCost (contents sticks) r.val) := by
  sorry

/-- connect_sticks(sticks) returns a result r and does not fail (no i64 overflow, panic, or out-of-bounds access).
  Preconditions: Let n = len(sticks). n >= 1, for every i with 0 <= i < n, sticks[i] >= 1, and (n-1) * sum_{i=0}^{n-1} sticks[i] <= 9223372036854775807. -/
theorem spec_2 (sticks : Slice Std.I64)
    (h_n_ge : 1 ≤ (contents sticks).length)
    (h_pos : ∀ (i : ℕ) (hi : i < (contents sticks).length), 1 ≤ (contents sticks)[i])
    (h_bound : (((contents sticks).length - 1 : ℕ) : ℤ) * (contents sticks).sum
      ≤ 9223372036854775807) :
    ∃ r : Std.I64, connect_sticks sticks = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (sticks : Slice Std.I64)
    (h_n_ge : 1 ≤ (contents sticks).length)
    (h_pos : ∀ (i : ℕ) (hi : i < (contents sticks).length), 1 ≤ (contents sticks)[i])
    (h_bound : (((contents sticks).length - 1 : ℕ) : ℤ) * (contents sticks).sum
      ≤ 9223372036854775807), ∃ r : Std.I64, connect_sticks sticks = ok r) := by
  sorry

/-- connect_sticks(sticks) returns a result r and r = 0.
  Preconditions: len(sticks) = 1 and sticks[0] >= 1. -/
theorem spec_3 (sticks : Slice Std.I64) (a : ℤ)
    (h_len : contents sticks = [a]) (h_pos : 1 ≤ a) :
    ∃ r : Std.I64, connect_sticks sticks = ok r ∧ r.val = 0 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (sticks : Slice Std.I64) (a : ℤ)
    (h_len : contents sticks = [a]) (h_pos : 1 ≤ a), ∃ r : Std.I64, connect_sticks sticks = ok r ∧ r.val = 0) := by
  sorry

/-- connect_sticks(sticks) returns a result r and r = sticks[0] + sticks[1].
  Preconditions: len(sticks) = 2, sticks[0] >= 1, sticks[1] >= 1, and sticks[0] + sticks[1] <= 9223372036854775807. -/
theorem spec_4 (sticks : Slice Std.I64) (a b : ℤ)
    (h_len : contents sticks = [a, b]) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h_sum : a + b ≤ 9223372036854775807) :
    ∃ r : Std.I64, connect_sticks sticks = ok r ∧ r.val = a + b := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (sticks : Slice Std.I64) (a b : ℤ)
    (h_len : contents sticks = [a, b]) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h_sum : a + b ≤ 9223372036854775807), ∃ r : Std.I64, connect_sticks sticks = ok r ∧ r.val = a + b) := by
  sorry

/-- Whenever connect_sticks(sticks) returns a result r, r >= sum_{i=0}^{n-1} sticks[i].
  Preconditions: Let n = len(sticks). n >= 2 and for every i with 0 <= i < n, sticks[i] >= 1. -/
theorem spec_5 (sticks : Slice Std.I64)
    (h_n_ge : 2 ≤ (contents sticks).length)
    (h_pos : ∀ (i : ℕ) (hi : i < (contents sticks).length), 1 ≤ (contents sticks)[i])
    (r : Std.I64) (hr : connect_sticks sticks = ok r) :
    (contents sticks).sum ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (sticks : Slice Std.I64)
    (h_n_ge : 2 ≤ (contents sticks).length)
    (h_pos : ∀ (i : ℕ) (hi : i < (contents sticks).length), 1 ≤ (contents sticks)[i])
    (r : Std.I64) (hr : connect_sticks sticks = ok r), (contents sticks).sum ≤ r.val) := by
  sorry

/-- Whenever connect_sticks(sticks) returns a result r, r <= (n-1) * sum_{i=0}^{n-1} sticks[i].
  Preconditions: Let n = len(sticks). n >= 1 and for every i with 0 <= i < n, sticks[i] >= 1. -/
theorem spec_6 (sticks : Slice Std.I64)
    (h_n_ge : 1 ≤ (contents sticks).length)
    (h_pos : ∀ (i : ℕ) (hi : i < (contents sticks).length), 1 ≤ (contents sticks)[i])
    (r : Std.I64) (hr : connect_sticks sticks = ok r) :
    r.val ≤ (((contents sticks).length - 1 : ℕ) : ℤ) * (contents sticks).sum := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (sticks : Slice Std.I64)
    (h_n_ge : 1 ≤ (contents sticks).length)
    (h_pos : ∀ (i : ℕ) (hi : i < (contents sticks).length), 1 ≤ (contents sticks)[i])
    (r : Std.I64) (hr : connect_sticks sticks = ok r), r.val ≤ (((contents sticks).length - 1 : ℕ) : ℤ) * (contents sticks).sum) := by
  sorry

/-- Whenever connect_sticks(sticks) returns a result r, r >= S + (n-1) * m.
  Preconditions: Let n = len(sticks). n >= 3, for every i with 0 <= i < n, sticks[i] >= 1. Let S = sum_{i=0}^{n-1} sticks[i] and let m = min_{0 <= i < n} sticks[i]. -/
theorem spec_7 (sticks : Slice Std.I64) (m : ℤ)
    (h_n_ge : 3 ≤ (contents sticks).length)
    (h_pos : ∀ (i : ℕ) (hi : i < (contents sticks).length), 1 ≤ (contents sticks)[i])
    (h_min : (contents sticks).min? = some m)
    (r : Std.I64) (hr : connect_sticks sticks = ok r) :
    (contents sticks).sum + (((contents sticks).length - 1 : ℕ) : ℤ) * m ≤ r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (sticks : Slice Std.I64) (m : ℤ)
    (h_n_ge : 3 ≤ (contents sticks).length)
    (h_pos : ∀ (i : ℕ) (hi : i < (contents sticks).length), 1 ≤ (contents sticks)[i])
    (h_min : (contents sticks).min? = some m)
    (r : Std.I64) (hr : connect_sticks sticks = ok r), (contents sticks).sum + (((contents sticks).length - 1 : ℕ) : ℤ) * m ≤ r.val) := by
  sorry

/-- Whenever connect_sticks(sticks) returns a result r, let S = sticks[0] + sticks[1] + sticks[2] and M = max(sticks[0], sticks[1], sticks[2]); then r = 2 * S - M.
  Preconditions: len(sticks) = 3 and sticks[0] >= 1, sticks[1] >= 1, sticks[2] >= 1. -/
theorem spec_8 (sticks : Slice Std.I64) (a b c : ℤ)
    (h_len : contents sticks = [a, b, c]) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (r : Std.I64) (hr : connect_sticks sticks = ok r) :
    r.val = 2 * (a + b + c) - max a (max b c) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (sticks : Slice Std.I64) (a b c : ℤ)
    (h_len : contents sticks = [a, b, c]) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (r : Std.I64) (hr : connect_sticks sticks = ok r), r.val = 2 * (a + b + c) - max a (max b c)) := by
  sorry

/-- Whenever connect_sticks(sticks) returns a result r and connect_sticks(sticks') returns a result r', we have r = r'.
  Preconditions: Let n = len(sticks). n >= 1 and for every i with 0 <= i < n, sticks[i] >= 1. Let pi be any permutation of {0, ..., n-1}, and define sticks' by sticks'[i] = sticks[pi(i)] for 0 <= i < n. -/
theorem spec_9 (sticks sticks' : Slice Std.I64)
    (h_n_ge : 1 ≤ (contents sticks).length)
    (h_pos : ∀ (i : ℕ) (hi : i < (contents sticks).length), 1 ≤ (contents sticks)[i])
    (h_perm : (contents sticks').Perm (contents sticks))
    (r r' : Std.I64)
    (hr : connect_sticks sticks = ok r) (hr' : connect_sticks sticks' = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (sticks sticks' : Slice Std.I64)
    (h_n_ge : 1 ≤ (contents sticks).length)
    (h_pos : ∀ (i : ℕ) (hi : i < (contents sticks).length), 1 ≤ (contents sticks)[i])
    (h_perm : (contents sticks').Perm (contents sticks))
    (r r' : Std.I64)
    (hr : connect_sticks sticks = ok r) (hr' : connect_sticks sticks' = ok r'), r.val = r'.val) := by
  sorry

/-- Whenever connect_sticks(sticks) returns a result r and connect_sticks(sticks') returns a result r', we have r' = c * r.
  Preconditions: Let n = len(sticks). n >= 1, for every i with 0 <= i < n, sticks[i] >= 1, and let c >= 1 be an integer. Define sticks'[i] = c * sticks[i] for 0 <= i < n, and assume c * sticks[i] <= 9223372036854775807 for every i. -/
theorem spec_10 (sticks sticks' : Slice Std.I64) (c : ℤ)
    (h_c : 1 ≤ c)
    (h_n_ge : 1 ≤ (contents sticks).length)
    (h_pos : ∀ (i : ℕ) (hi : i < (contents sticks).length), 1 ≤ (contents sticks)[i])
    (h_scale : contents sticks' = (contents sticks).map (fun x => c * x))
    (h_bounded : ∀ (i : ℕ) (hi : i < (contents sticks).length),
      c * (contents sticks)[i] ≤ 9223372036854775807)
    (r r' : Std.I64)
    (hr : connect_sticks sticks = ok r) (hr' : connect_sticks sticks' = ok r') :
    r'.val = c * r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (sticks sticks' : Slice Std.I64) (c : ℤ)
    (h_c : 1 ≤ c)
    (h_n_ge : 1 ≤ (contents sticks).length)
    (h_pos : ∀ (i : ℕ) (hi : i < (contents sticks).length), 1 ≤ (contents sticks)[i])
    (h_scale : contents sticks' = (contents sticks).map (fun x => c * x))
    (h_bounded : ∀ (i : ℕ) (hi : i < (contents sticks).length),
      c * (contents sticks)[i] ≤ 9223372036854775807)
    (r r' : Std.I64)
    (hr : connect_sticks sticks = ok r) (hr' : connect_sticks sticks' = ok r'), r'.val = c * r.val) := by
  sorry

/-- Whenever connect_sticks(a) returns a result r_a and connect_sticks(b) returns a result r_b, we have r_a <= r_b.
  Preconditions: Let n >= 1. Let a and b be two slices of length n with a[i] >= 1 and b[i] >= 1 for every 0 <= i < n, and a[i] <= b[i] for every 0 <= i < n. -/
theorem spec_11 (a b : Slice Std.I64) (n : ℕ)
    (h_n : 1 ≤ n)
    (h_len_a : (contents a).length = n)
    (h_len_b : (contents b).length = n)
    (h_a_pos : ∀ x ∈ contents a, 1 ≤ x)
    (h_b_pos : ∀ x ∈ contents b, 1 ≤ x)
    (h_le : List.Forall₂ (fun x y => x ≤ y) (contents a) (contents b))
    (r_a r_b : Std.I64)
    (hr_a : connect_sticks a = ok r_a) (hr_b : connect_sticks b = ok r_b) :
    r_a.val ≤ r_b.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (a b : Slice Std.I64) (n : ℕ)
    (h_n : 1 ≤ n)
    (h_len_a : (contents a).length = n)
    (h_len_b : (contents b).length = n)
    (h_a_pos : ∀ x ∈ contents a, 1 ≤ x)
    (h_b_pos : ∀ x ∈ contents b, 1 ≤ x)
    (h_le : List.Forall₂ (fun x y => x ≤ y) (contents a) (contents b))
    (r_a r_b : Std.I64)
    (hr_a : connect_sticks a = ok r_a) (hr_b : connect_sticks b = ok r_b), r_a.val ≤ r_b.val) := by
  sorry

/-- Whenever connect_sticks(sticks) returns a result r, there exists a complete sequence of n-1 pairwise merges of the sticks whose total accumulated merge cost is exactly r.
  Preconditions: Let n = len(sticks). n >= 1 and for every i with 0 <= i < n, sticks[i] >= 1. -/
theorem spec_12 (sticks : Slice Std.I64)
    (h_n_ge : 1 ≤ (contents sticks).length)
    (h_pos : ∀ (i : ℕ) (hi : i < (contents sticks).length), 1 ≤ (contents sticks)[i])
    (r : Std.I64) (hr : connect_sticks sticks = ok r) :
    CompleteMergeCost (contents sticks) r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (sticks : Slice Std.I64)
    (h_n_ge : 1 ≤ (contents sticks).length)
    (h_pos : ∀ (i : ℕ) (hi : i < (contents sticks).length), 1 ≤ (contents sticks)[i])
    (r : Std.I64) (hr : connect_sticks sticks = ok r), CompleteMergeCost (contents sticks) r.val) := by
  sorry

/-- Whenever connect_sticks(sticks) returns a result r, r <= C.
  Preconditions: Let n = len(sticks). n >= 2 and for every i with 0 <= i < n, sticks[i] >= 1. Let a0 <= a1 <= ... <= a_{n-1} be the nondecreasing sorted version of sticks, and define C = (n-1)*(a0+a1) + sum_{i=2}^{n-1} (n-i)*a_i (the sum is empty when n=2). -/
theorem spec_13 (sticks : Slice Std.I64) (sorted : List ℤ)
    (h_n_ge : 2 ≤ (contents sticks).length)
    (h_pos : ∀ (i : ℕ) (hi : i < (contents sticks).length), 1 ≤ (contents sticks)[i])
    (h_perm : sorted.Perm (contents sticks))
    (h_sorted : IsNondecreasing sorted)
    (r : Std.I64) (hr : connect_sticks sticks = ok r) :
    r.val ≤ sortedCostBound sorted := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (sticks : Slice Std.I64) (sorted : List ℤ)
    (h_n_ge : 2 ≤ (contents sticks).length)
    (h_pos : ∀ (i : ℕ) (hi : i < (contents sticks).length), 1 ≤ (contents sticks)[i])
    (h_perm : sorted.Perm (contents sticks))
    (h_sorted : IsNondecreasing sorted)
    (r : Std.I64) (hr : connect_sticks sticks = ok r), r.val ≤ sortedCostBound sorted) := by
  sorry

end AegisSpec.ConnectSticks

import Aegis.LastStoneWeight.Code.Funs

/-!
# Specifications of `Aegis.LastStoneWeight.last_stone_weight`

LeetCode problem `last-stone-weight`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.LastStoneWeight

open Aegis.LastStoneWeight (last_stone_weight)

def weights (stones : Slice Std.I64) : List ℤ := stones.val.map (fun s => s.val)

def IsValid (stones : Slice Std.I64) : Prop :=
  1 ≤ stones.val.length ∧ stones.val.length ≤ 30 ∧
    ∀ (i : Nat) (_ : i < stones.val.length),
      1 ≤ (stones.val[i]).val ∧ (stones.val[i]).val ≤ 1000

def sortedWeights (l : List ℤ) : List ℤ := l.mergeSort (fun a b => a ≤ b)

theorem sortedWeights_length (l : List ℤ) : (sortedWeights l).length = l.length := by
  simp [sortedWeights]

def gameStep (l : List ℤ) : List ℤ :=
  match (sortedWeights l).reverse with
  | [] => []
  | [_] => l
  | y :: x :: rest => rest ++ (if y = x then [] else [y - x])

theorem gameStep_length (l : List ℤ) (h : 2 ≤ l.length) : (gameStep l).length < l.length := by
  have hlen : (sortedWeights l).length = l.length := sortedWeights_length l
  unfold gameStep
  split
  · rename_i hnil
    have h0 : l.length = 0 := by
      have := congrArg List.length hnil
      simp only [List.length_reverse, List.length_nil] at this
      omega
    simp only [List.length_nil]
    omega
  · rename_i a hsingle
    exfalso
    have h1 : l.length = 1 := by
      have := congrArg List.length hsingle
      simpa [List.length_reverse, hlen] using this
    omega
  · rename_i y x rest hcons
    have h2 : l.length = rest.length + 2 := by
      have := congrArg List.length hcons
      simp only [List.length_reverse, List.length_cons] at this
      omega
    simp only [List.length_append]
    split <;> simp <;> omega

def game (l : List ℤ) : ℤ :=
  if _h : 2 ≤ l.length then game (gameStep l)
  else match l with
       | [] => 0
       | a :: _ => a
termination_by l.length
decreasing_by exact gameStep_length l _h

inductive GamePath : List ℤ → List ℤ → Prop where
  | refl (l : List ℤ) : GamePath l l
  | step {l n : List ℤ} : GamePath (gameStep l) n → GamePath l n

def maxWeight (l : List ℤ) : ℤ := l.max?.getD 0

def sumOthers (l : List ℤ) (m : Nat) : ℤ := l.sum - l.getD m 0

def eraseTwo {α : Type} (l : List α) (p q : Nat) : List α :=
  (l.zipIdx.filter (fun x => x.2 != p && x.2 != q)).map Prod.fst

/-- Whenever last_stone_weight(stones) returns a result r, r is the terminal value of the following game. Start with the multiset S = {stones[0], ..., stones[len(stones)-1]}. While S has at least two elements, let y be a maximum element of S and let x be a maximum element of S after deleting one occurrence of y (so x <= y are the two largest elements, with ties allowed); delete one occurrence of x and one occurrence of y, and if y > x insert one occurrence of y - x, while if y = x insert nothing. When S has at most one element, r is the sole element if S is nonempty and r = 0 if S is empty. This terminal value is independent of which equal largest elements are chosen at a tie.
  Preconditions: stones is a slice of 64-bit integers with 1 <= len(stones) <= 30 and, for every i with 0 <= i < len(stones), 1 <= stones[i] <= 1000. -/
theorem spec_1 (stones : Slice Std.I64) (hvalid : IsValid stones) (r : Std.I64)
    (hres : last_stone_weight stones = ok r) :
    r.val = game (weights stones) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (stones : Slice Std.I64) (hvalid : IsValid stones) (r : Std.I64)
    (hres : last_stone_weight stones = ok r), r.val = game (weights stones)) := by
  sorry

/-- For every input satisfying the preconditions, last_stone_weight(stones) returns a result r; it does not fail, panic, access out of bounds, or perform an out-of-range 64-bit arithmetic operation. Every stone weight occurring during the game is a nonnegative integer at most 1000, so all subtractions y - x stay within the 64-bit range.
  Preconditions: stones is a slice of 64-bit integers with 1 <= len(stones) <= 30 and, for every i with 0 <= i < len(stones), 1 <= stones[i] <= 1000. -/
theorem spec_2 (stones : Slice Std.I64) (hvalid : IsValid stones) :
    ∃ r : Std.I64, last_stone_weight stones = ok r ∧ 0 ≤ r.val ∧ r.val ≤ 1000 ∧
      ∀ s : List ℤ, GamePath (weights stones) s → ∀ x ∈ s, 0 ≤ x ∧ x ≤ 1000 := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (stones : Slice Std.I64) (hvalid : IsValid stones), ∃ r : Std.I64, last_stone_weight stones = ok r ∧ 0 ≤ r.val ∧ r.val ≤ 1000 ∧
      ∀ s : List ℤ, GamePath (weights stones) s → ∀ x ∈ s, 0 ≤ x ∧ x ≤ 1000) := by
  sorry

/-- Whenever the function returns r, 0 <= r <= max{stones[i] | 0 <= i < len(stones)}.
  Preconditions: stones is a slice of 64-bit integers with 1 <= len(stones) <= 30 and, for every i with 0 <= i < len(stones), 1 <= stones[i] <= 1000. -/
theorem spec_3 (stones : Slice Std.I64) (hvalid : IsValid stones) (r : Std.I64)
    (hres : last_stone_weight stones = ok r) :
    0 ≤ r.val ∧ r.val ≤ maxWeight (weights stones) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (stones : Slice Std.I64) (hvalid : IsValid stones) (r : Std.I64)
    (hres : last_stone_weight stones = ok r), 0 ≤ r.val ∧ r.val ≤ maxWeight (weights stones)) := by
  sorry

/-- Whenever the function returns r, r is congruent to the total sum sum_{i=0}^{len(stones)-1} stones[i] modulo 2.
  Preconditions: stones is a slice of 64-bit integers with 1 <= len(stones) <= 30 and, for every i with 0 <= i < len(stones), 1 <= stones[i] <= 1000. -/
theorem spec_4 (stones : Slice Std.I64) (hvalid : IsValid stones) (r : Std.I64)
    (hres : last_stone_weight stones = ok r) :
    ∃ k : ℤ, (weights stones).sum - r.val = 2 * k := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (stones : Slice Std.I64) (hvalid : IsValid stones) (r : Std.I64)
    (hres : last_stone_weight stones = ok r), ∃ k : ℤ, (weights stones).sum - r.val = 2 * k) := by
  sorry

/-- Whenever the function returns r, r = stones[0].
  Preconditions: stones is a valid input (1 <= len(stones) <= 30 and 1 <= stones[i] <= 1000 for every i) and len(stones) = 1. -/
theorem spec_5 (stones : Slice Std.I64) (hvalid : IsValid stones)
    (hlen : stones.val.length = 1) (r : Std.I64)
    (hres : last_stone_weight stones = ok r) :
    r.val = (stones.val[0]).val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (stones : Slice Std.I64) (hvalid : IsValid stones)
    (hlen : stones.val.length = 1) (r : Std.I64)
    (hres : last_stone_weight stones = ok r), r.val = (stones.val[0]).val) := by
  sorry

/-- Whenever the function returns r, r = |stones[0] - stones[1]|.
  Preconditions: stones is a valid input (1 <= len(stones) <= 30 and 1 <= stones[i] <= 1000 for every i) and len(stones) = 2. -/
theorem spec_6 (stones : Slice Std.I64) (hvalid : IsValid stones)
    (hlen : stones.val.length = 2) (r : Std.I64)
    (hres : last_stone_weight stones = ok r) :
    r.val = |(stones.val[0]).val - (stones.val[1]).val| := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (stones : Slice Std.I64) (hvalid : IsValid stones)
    (hlen : stones.val.length = 2) (r : Std.I64)
    (hres : last_stone_weight stones = ok r), r.val = |(stones.val[0]).val - (stones.val[1]).val|) := by
  sorry

/-- Whenever the function returns r, r = w if n is odd, and r = 0 if n is even.
  Preconditions: stones is a valid input with n = len(stones) >= 3, and there is a weight w with 1 <= w <= 1000 such that stones[i] = w for every i with 0 <= i < n. -/
theorem spec_7 (stones : Slice Std.I64) (hvalid : IsValid stones) (w : ℤ)
    (hw1 : 1 ≤ w) (hw1000 : w ≤ 1000)
    (hn : 3 ≤ stones.val.length)
    (hall : ∀ (i : Nat) (_ : i < stones.val.length), (stones.val[i]).val = w)
    (r : Std.I64) (hres : last_stone_weight stones = ok r) :
    r.val = if stones.val.length % 2 = 1 then w else 0 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (stones : Slice Std.I64) (hvalid : IsValid stones) (w : ℤ)
    (hw1 : 1 ≤ w) (hw1000 : w ≤ 1000)
    (hn : 3 ≤ stones.val.length)
    (hall : ∀ (i : Nat) (_ : i < stones.val.length), (stones.val[i]).val = w)
    (r : Std.I64) (hres : last_stone_weight stones = ok r), r.val = if stones.val.length % 2 = 1 then w else 0) := by
  sorry

/-- Whenever the two calls return results, last_stone_weight(stones) = last_stone_weight(stones').
  Preconditions: stones and stones' are two valid inputs (each length between 1 and 30, each entry between 1 and 1000), and stones' is a permutation of stones, i.e. the two slices have the same length and the same multiset of weights. -/
theorem spec_8 (stones stones' : Slice Std.I64) (hvalid : IsValid stones)
    (hvalid' : IsValid stones') (hperm : (weights stones).Perm (weights stones'))
    (r r' : Std.I64) (hres : last_stone_weight stones = ok r)
    (hres' : last_stone_weight stones' = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (stones stones' : Slice Std.I64) (hvalid : IsValid stones)
    (hvalid' : IsValid stones') (hperm : (weights stones).Perm (weights stones'))
    (r r' : Std.I64) (hres : last_stone_weight stones = ok r)
    (hres' : last_stone_weight stones' = ok r'), r.val = r'.val) := by
  sorry

/-- Whenever both calls return results, last_stone_weight(scaled) = c * last_stone_weight(stones).
  Preconditions: stones is a valid input, c is a positive integer, and for every i with 0 <= i < len(stones), 1 <= c * stones[i] <= 1000; let scaled be the valid slice with scaled[i] = c * stones[i]. -/
theorem spec_9 (stones scaled : Slice Std.I64) (c : ℤ) (hvalid : IsValid stones) (hc : 0 < c)
    (hmul : ∀ (i : Nat) (_ : i < stones.val.length),
      1 ≤ c * (stones.val[i]).val ∧ c * (stones.val[i]).val ≤ 1000)
    (hscaled : weights scaled = (weights stones).map (fun w => c * w))
    (r r' : Std.I64) (hres : last_stone_weight stones = ok r)
    (hres' : last_stone_weight scaled = ok r') :
    r'.val = c * r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (stones scaled : Slice Std.I64) (c : ℤ) (hvalid : IsValid stones) (hc : 0 < c)
    (hmul : ∀ (i : Nat) (_ : i < stones.val.length),
      1 ≤ c * (stones.val[i]).val ∧ c * (stones.val[i]).val ≤ 1000)
    (hscaled : weights scaled = (weights stones).map (fun w => c * w))
    (r r' : Std.I64) (hres : last_stone_weight stones = ok r)
    (hres' : last_stone_weight scaled = ok r'), r'.val = c * r.val) := by
  sorry

/-- Whenever the function returns r, r = stones[m] - sum_{0 <= i < len(stones), i != m} stones[i].
  Preconditions: stones is a valid input and there exists an index m with 0 <= m < len(stones) such that stones[m] > sum_{0 <= i < len(stones), i != m} stones[i]. -/
theorem spec_10 (stones : Slice Std.I64) (hvalid : IsValid stones) (m : Nat)
    (hm : m < stones.val.length) (hbig : sumOthers (weights stones) m < (stones.val[m]).val)
    (r : Std.I64) (hres : last_stone_weight stones = ok r) :
    r.val = (stones.val[m]).val - sumOthers (weights stones) m := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (stones : Slice Std.I64) (hvalid : IsValid stones) (m : Nat)
    (hm : m < stones.val.length) (hbig : sumOthers (weights stones) m < (stones.val[m]).val)
    (r : Std.I64) (hres : last_stone_weight stones = ok r), r.val = (stones.val[m]).val - sumOthers (weights stones) m) := by
  sorry

/-- Whenever both calls return results, last_stone_weight(stones) = last_stone_weight(stones').
  Preconditions: stones is a valid input with n = len(stones) >= 3, M = max{stones[i] | 0 <= i < n}, and at least two indices p < q with stones[p] = stones[q] = M; let stones' be the slice of length n - 2 obtained by deleting stones[p] and stones[q]. -/
theorem spec_11 (stones stones' : Slice Std.I64) (hvalid : IsValid stones)
    (hn : 3 ≤ stones.val.length) (M : ℤ) (hM : M = maxWeight (weights stones))
    (p q : Nat) (hp : p < stones.val.length) (hq : q < stones.val.length) (hpq : p < q)
    (hpM : (stones.val[p]).val = M) (hqM : (stones.val[q]).val = M)
    (hsp : weights stones' = eraseTwo (weights stones) p q)
    (r r' : Std.I64) (hres : last_stone_weight stones = ok r)
    (hres' : last_stone_weight stones' = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (stones stones' : Slice Std.I64) (hvalid : IsValid stones)
    (hn : 3 ≤ stones.val.length) (M : ℤ) (hM : M = maxWeight (weights stones))
    (p q : Nat) (hp : p < stones.val.length) (hq : q < stones.val.length) (hpq : p < q)
    (hpM : (stones.val[p]).val = M) (hqM : (stones.val[q]).val = M)
    (hsp : weights stones' = eraseTwo (weights stones) p q)
    (r r' : Std.I64) (hres : last_stone_weight stones = ok r)
    (hres' : last_stone_weight stones' = ok r'), r.val = r'.val) := by
  sorry

/-- Whenever the function returns r, r < max{stones[i] | 0 <= i < len(stones)}.
  Preconditions: stones is a valid input with len(stones) >= 2, and not all entries of stones are equal, i.e. there exist i and j with stones[i] != stones[j]. -/
theorem spec_12 (stones : Slice Std.I64) (hvalid : IsValid stones)
    (hn : 2 ≤ stones.val.length)
    (hne : ∃ w₁ ∈ weights stones, ∃ w₂ ∈ weights stones, w₁ ≠ w₂)
    (r : Std.I64) (hres : last_stone_weight stones = ok r) :
    r.val < maxWeight (weights stones) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (stones : Slice Std.I64) (hvalid : IsValid stones)
    (hn : 2 ≤ stones.val.length)
    (hne : ∃ w₁ ∈ weights stones, ∃ w₂ ∈ weights stones, w₁ ≠ w₂)
    (r : Std.I64) (hres : last_stone_weight stones = ok r), r.val < maxWeight (weights stones)) := by
  sorry

/-- Whenever the function returns r, r = 0.
  Preconditions: stones is a valid input and there exists an index m with 0 <= m < len(stones) such that stones[m] = sum_{0 <= i < len(stones), i != m} stones[i]. -/
theorem spec_13 (stones : Slice Std.I64) (hvalid : IsValid stones) (m : Nat)
    (hm : m < stones.val.length) (heq : (stones.val[m]).val = sumOthers (weights stones) m)
    (r : Std.I64) (hres : last_stone_weight stones = ok r) :
    r.val = 0 := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (stones : Slice Std.I64) (hvalid : IsValid stones) (m : Nat)
    (hm : m < stones.val.length) (heq : (stones.val[m]).val = sumOthers (weights stones) m)
    (r : Std.I64) (hres : last_stone_weight stones = ok r), r.val = 0) := by
  sorry

/-- Whenever the function returns r, there exist signs e_i in {-1, +1} for i = 0, ..., len(stones)-1 such that r = |sum_{i=0}^{len(stones)-1} e_i * stones[i]|.
  Preconditions: stones is a slice of 64-bit integers with 1 <= len(stones) <= 30 and, for every i with 0 <= i < len(stones), 1 <= stones[i] <= 1000. -/
theorem spec_14 (stones : Slice Std.I64) (hvalid : IsValid stones) (r : Std.I64)
    (hres : last_stone_weight stones = ok r) :
    ∃ e : List ℤ, e.length = (weights stones).length ∧ (∀ x ∈ e, x = 1 ∨ x = -1) ∧
      r.val = |(List.zipWith (fun a b => a * b) e (weights stones)).sum| := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (stones : Slice Std.I64) (hvalid : IsValid stones) (r : Std.I64)
    (hres : last_stone_weight stones = ok r), ∃ e : List ℤ, e.length = (weights stones).length ∧ (∀ x ∈ e, x = 1 ∨ x = -1) ∧
      r.val = |(List.zipWith (fun a b => a * b) e (weights stones)).sum|) := by
  sorry

end AegisSpec.LastStoneWeight

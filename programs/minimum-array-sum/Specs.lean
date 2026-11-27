import Aegis.MinArraySum.Code.Funs

/-!
# Specifications of `Aegis.MinArraySum.min_array_sum`

LeetCode problem `minimum-array-sum`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinArraySum

def ceilHalf (x : Int) : Int := (x + 1) / 2

def nth (l : List I64) (i : Nat) : Int :=
  match l[i]? with
  | some x => x.val
  | none => 0

def total (l : List I64) : Int := (l.map (fun x => x.val)).sum

def halves (l : List I64) (n : Nat) : List Int := (List.range n).map (fun i => nth l i / 2)

def countGe (l : List I64) (n : Nat) (k : Int) : Nat :=
  ((List.range n).filter (fun i => decide (k ≤ nth l i))).length

def minList : List Int → Int
  | [] => 0
  | x :: xs => xs.foldr min x

def insertDesc (x : Int) : List Int → List Int
  | [] => [x]
  | y :: ys => if y ≤ x then x :: y :: ys else y :: insertDesc x ys

def sortDesc : List Int → List Int
  | [] => []
  | x :: xs => insertDesc x (sortDesc xs)

def sumTop (l : List Int) (j : Nat) : Int := ((sortDesc l).take j).sum

inductive Op where
  | one (i : Nat)
  | two (i : Nat)
  deriving DecidableEq, Repr

namespace Op

def index : Op → Nat
  | one i => i
  | two i => i

def apply (k : Int) (op : Op) (s : Nat → Int) : Nat → Int :=
  match op with
  | one i => fun j => if j = i then ceilHalf (s j) else s j
  | two i => fun j => if j = i then s j - k else s j

end Op

def initState (l : List I64) : Nat → Int := fun i => nth l i

def runOps (k : Int) : List Op → (Nat → Int) → (Nat → Int)
  | [], s => s
  | op :: rest, s => runOps k rest (op.apply k s)

def stateSum (n : Nat) (s : Nat → Int) : Int := ((List.range n).map s).sum

def PrefixOk (k : Int) : (Nat → Int) → List Op → Prop
  | _s, [] => True
  | s, op :: rest => (∀ i, op = Op.two i → k ≤ s i) ∧ PrefixOk k (op.apply k s) rest

def countOne (ops : List Op) : Nat :=
  ops.countP (fun o => match o with | Op.one _ => true | _ => false)

def countTwo (ops : List Op) : Nat :=
  ops.countP (fun o => match o with | Op.two _ => true | _ => false)

def countOneAt (i : Nat) (ops : List Op) : Nat :=
  (ops.filter (fun o => match o with | Op.one j => decide (j = i) | _ => false)).length

def countTwoAt (i : Nat) (ops : List Op) : Nat :=
  (ops.filter (fun o => match o with | Op.two j => decide (j = i) | _ => false)).length

def ValidSeq (l : List I64) (k : Int) (op1 op2 : Int) (ops : List Op) : Prop :=
  (∀ op ∈ ops, op.index < l.length) ∧
    (∀ i, countOneAt i ops ≤ 1) ∧
    (∀ i, countTwoAt i ops ≤ 1) ∧
    (countOne ops : Int) ≤ op1 ∧
    (countTwo ops : Int) ≤ op2 ∧
    PrefixOk k (initState l) ops

/-- The function returns a result r (so it does not fail). Define a state as a function from indices 0..n-1 to integers, initially s(i) = nums[i]. A valid operation is either (1,i) or (2,i). A finite sequence of operations is valid if: (a) each (1,i) occurs at most once and each (2,i) occurs at most once; (b) the number of (1,i) operations is at most op1 and the number of (2,i) operations is at most op2; (c) whenever an operation (2,i) occurs, the current value s(i) is at least k; and (d) applying (1,i) changes s(i) to ceil(s(i)/2) = (s(i)+1) div 2, while applying (2,i) changes s(i) to s(i)-k. For a valid sequence, let final_sum be sum_{i=0}^{n-1} s(i) after all operations. Then r = min { final_sum | valid sequence }.
  Preconditions: n = len(nums); 1 <= n <= 100; for every i with 0 <= i < n, 0 <= nums[i] <= 100000; 0 <= k <= 100000; 0 <= op1 <= n; 0 <= op2 <= n. -/
theorem spec_1 (nums : Slice I64) (k op1 op2 : I64) (n : Nat)
    (hn : nums.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hbnd : ∀ i, i < n → 0 ≤ nth nums.val i ∧ nth nums.val i ≤ 100000)
    (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ 100000)
    (ho1a : 0 ≤ op1.val) (ho1b : op1.val ≤ (n : Int))
    (ho2a : 0 ≤ op2.val) (ho2b : op2.val ≤ (n : Int)) :
    ∃ r, Aegis.MinArraySum.min_array_sum nums k op1 op2 = ok r ∧
      IsLeast { v : Int | ∃ ops : List Op,
          ValidSeq nums.val k.val op1.val op2.val ops ∧
            v = stateSum n (runOps k.val ops (initState nums.val)) } r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64) (k op1 op2 : I64) (n : Nat)
    (hn : nums.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hbnd : ∀ i, i < n → 0 ≤ nth nums.val i ∧ nth nums.val i ≤ 100000)
    (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ 100000)
    (ho1a : 0 ≤ op1.val) (ho1b : op1.val ≤ (n : Int))
    (ho2a : 0 ≤ op2.val) (ho2b : op2.val ≤ (n : Int)), ∃ r, Aegis.MinArraySum.min_array_sum nums k op1 op2 = ok r ∧
      IsLeast { v : Int | ∃ ops : List Op,
          ValidSeq nums.val k.val op1.val op2.val ops ∧
            v = stateSum n (runOps k.val ops (initState nums.val)) } r.val) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a value of the form Result.ok r for some integer r; it does not panic, overflow, or access an out-of-bounds index.
  Preconditions: n = len(nums); 1 <= n <= 100; for every i with 0 <= i < n, 0 <= nums[i] <= 100000; 0 <= k <= 100000; 0 <= op1 <= n; 0 <= op2 <= n. -/
theorem spec_2 (nums : Slice I64) (k op1 op2 : I64) (n : Nat)
    (hn : nums.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hbnd : ∀ i, i < n → 0 ≤ nth nums.val i ∧ nth nums.val i ≤ 100000)
    (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ 100000)
    (ho1a : 0 ≤ op1.val) (ho1b : op1.val ≤ (n : Int))
    (ho2a : 0 ≤ op2.val) (ho2b : op2.val ≤ (n : Int)) :
    ∃ r, Aegis.MinArraySum.min_array_sum nums k op1 op2 = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64) (k op1 op2 : I64) (n : Nat)
    (hn : nums.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hbnd : ∀ i, i < n → 0 ≤ nth nums.val i ∧ nth nums.val i ≤ 100000)
    (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ 100000)
    (ho1a : 0 ≤ op1.val) (ho1b : op1.val ≤ (n : Int))
    (ho2a : 0 ≤ op2.val) (ho2b : op2.val ≤ (n : Int)), ∃ r, Aegis.MinArraySum.min_array_sum nums k op1 op2 = ok r) := by
  sorry

/-- Let S = sum_{i=0}^{n-1} nums[i]. The function returns a result r and r <= S.
  Preconditions: n = len(nums); 1 <= n <= 100; for every i with 0 <= i < n, 0 <= nums[i] <= 100000; 0 <= k <= 100000; 0 <= op1 <= n; 0 <= op2 <= n. -/
theorem spec_3 (nums : Slice I64) (k op1 op2 : I64) (n : Nat)
    (hn : nums.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hbnd : ∀ i, i < n → 0 ≤ nth nums.val i ∧ nth nums.val i ≤ 100000)
    (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ 100000)
    (ho1a : 0 ≤ op1.val) (ho1b : op1.val ≤ (n : Int))
    (ho2a : 0 ≤ op2.val) (ho2b : op2.val ≤ (n : Int)) :
    ∃ r, Aegis.MinArraySum.min_array_sum nums k op1 op2 = ok r ∧ r.val ≤ total nums.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64) (k op1 op2 : I64) (n : Nat)
    (hn : nums.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hbnd : ∀ i, i < n → 0 ≤ nth nums.val i ∧ nth nums.val i ≤ 100000)
    (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ 100000)
    (ho1a : 0 ≤ op1.val) (ho1b : op1.val ≤ (n : Int))
    (ho2a : 0 ≤ op2.val) (ho2b : op2.val ≤ (n : Int)), ∃ r, Aegis.MinArraySum.min_array_sum nums k op1 op2 = ok r ∧ r.val ≤ total nums.val) := by
  sorry

/-- The function returns a result r and 0 <= r.
  Preconditions: n = len(nums); 1 <= n <= 100; for every i with 0 <= i < n, 0 <= nums[i] <= 100000; 0 <= k <= 100000; 0 <= op1 <= n; 0 <= op2 <= n. -/
theorem spec_4 (nums : Slice I64) (k op1 op2 : I64) (n : Nat)
    (hn : nums.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hbnd : ∀ i, i < n → 0 ≤ nth nums.val i ∧ nth nums.val i ≤ 100000)
    (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ 100000)
    (ho1a : 0 ≤ op1.val) (ho1b : op1.val ≤ (n : Int))
    (ho2a : 0 ≤ op2.val) (ho2b : op2.val ≤ (n : Int)) :
    ∃ r, Aegis.MinArraySum.min_array_sum nums k op1 op2 = ok r ∧ 0 ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64) (k op1 op2 : I64) (n : Nat)
    (hn : nums.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hbnd : ∀ i, i < n → 0 ≤ nth nums.val i ∧ nth nums.val i ≤ 100000)
    (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ 100000)
    (ho1a : 0 ≤ op1.val) (ho1b : op1.val ≤ (n : Int))
    (ho2a : 0 ≤ op2.val) (ho2b : op2.val ≤ (n : Int)), ∃ r, Aegis.MinArraySum.min_array_sum nums k op1 op2 = ok r ∧ 0 ≤ r.val) := by
  sorry

/-- Let S = sum_{i=0}^{n-1} nums[i]. The function returns r and r = min over all subsets T of {0,...,n-1} with |T| <= op1 of ( sum_{i in T} ceil(nums[i]/2) + sum_{i not in T} nums[i] ), where ceil(a/2) = (a+1) div 2.
  Preconditions: n = len(nums); 1 <= n <= 100; for every i with 0 <= i < n, 0 <= nums[i] <= 100000; k = 0; 0 <= op1 <= n; 0 <= op2 <= n. -/
theorem spec_5 (nums : Slice I64) (k op1 op2 : I64) (n : Nat)
    (hn : nums.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hbnd : ∀ i, i < n → 0 ≤ nth nums.val i ∧ nth nums.val i ≤ 100000)
    (hk : k.val = 0)
    (ho1a : 0 ≤ op1.val) (ho1b : op1.val ≤ (n : Int))
    (ho2a : 0 ≤ op2.val) (ho2b : op2.val ≤ (n : Int)) :
    ∃ r, Aegis.MinArraySum.min_array_sum nums k op1 op2 = ok r ∧
      IsLeast { v : Int | ∃ T : Finset Nat,
          T ⊆ Finset.range n ∧ (T.card : Int) ≤ op1.val ∧
            v = Finset.sum (Finset.range n)
                  (fun i => if i ∈ T then ceilHalf (nth nums.val i) else nth nums.val i) } r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64) (k op1 op2 : I64) (n : Nat)
    (hn : nums.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hbnd : ∀ i, i < n → 0 ≤ nth nums.val i ∧ nth nums.val i ≤ 100000)
    (hk : k.val = 0)
    (ho1a : 0 ≤ op1.val) (ho1b : op1.val ≤ (n : Int))
    (ho2a : 0 ≤ op2.val) (ho2b : op2.val ≤ (n : Int)), ∃ r, Aegis.MinArraySum.min_array_sum nums k op1 op2 = ok r ∧
      IsLeast { v : Int | ∃ T : Finset Nat,
          T ⊆ Finset.range n ∧ (T.card : Int) ≤ op1.val ∧
            v = Finset.sum (Finset.range n)
                  (fun i => if i ∈ T then ceilHalf (nth nums.val i) else nth nums.val i) } r.val) := by
  sorry

/-- Let S = sum_{i=0}^{n-1} nums[i] and let m be the number of indices i with 0 <= i < n and nums[i] >= k. The function returns r and r = S - k * min(op2, m).
  Preconditions: n = len(nums); 1 <= n <= 100; for every i with 0 <= i < n, 0 <= nums[i] <= 100000; 0 <= k <= 100000; op1 = 0; 0 <= op2 <= n. -/
theorem spec_6 (nums : Slice I64) (k op1 op2 : I64) (n : Nat)
    (hn : nums.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hbnd : ∀ i, i < n → 0 ≤ nth nums.val i ∧ nth nums.val i ≤ 100000)
    (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ 100000)
    (ho1 : op1.val = 0)
    (ho2a : 0 ≤ op2.val) (ho2b : op2.val ≤ (n : Int)) :
    ∃ r, Aegis.MinArraySum.min_array_sum nums k op1 op2 = ok r ∧
      r.val = total nums.val - k.val * min op2.val (countGe nums.val n k.val : Int) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64) (k op1 op2 : I64) (n : Nat)
    (hn : nums.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hbnd : ∀ i, i < n → 0 ≤ nth nums.val i ∧ nth nums.val i ≤ 100000)
    (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ 100000)
    (ho1 : op1.val = 0)
    (ho2a : 0 ≤ op2.val) (ho2b : op2.val ≤ (n : Int)), ∃ r, Aegis.MinArraySum.min_array_sum nums k op1 op2 = ok r ∧
      r.val = total nums.val - k.val * min op2.val (countGe nums.val n k.val : Int)) := by
  sorry

/-- Let S = sum_{i=0}^{n-1} nums[i] and let d_i = nums[i] div 2 for 0 <= i < n. The function returns r and r = S - (sum of the min(op1, n) largest elements of the multiset {d_0,...,d_{n-1}}). The sum of an empty multiset is 0.
  Preconditions: n = len(nums); 1 <= n <= 100; for every i with 0 <= i < n, 0 <= nums[i] <= 100000; 0 <= k <= 100000; 0 <= op1 <= n; op2 = 0. -/
theorem spec_7 (nums : Slice I64) (k op1 op2 : I64) (n : Nat)
    (hn : nums.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hbnd : ∀ i, i < n → 0 ≤ nth nums.val i ∧ nth nums.val i ≤ 100000)
    (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ 100000)
    (ho1a : 0 ≤ op1.val) (ho1b : op1.val ≤ (n : Int))
    (ho2 : op2.val = 0) :
    ∃ r, Aegis.MinArraySum.min_array_sum nums k op1 op2 = ok r ∧
      r.val = total nums.val - sumTop (halves nums.val n) (Nat.min op1.val.toNat n) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice I64) (k op1 op2 : I64) (n : Nat)
    (hn : nums.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hbnd : ∀ i, i < n → 0 ≤ nth nums.val i ∧ nth nums.val i ≤ 100000)
    (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ 100000)
    (ho1a : 0 ≤ op1.val) (ho1b : op1.val ≤ (n : Int))
    (ho2 : op2.val = 0), ∃ r, Aegis.MinArraySum.min_array_sum nums k op1 op2 = ok r ∧
      r.val = total nums.val - sumTop (halves nums.val n) (Nat.min op1.val.toNat n)) := by
  sorry

/-- Let S = sum_{i=0}^{n-1} nums[i] and let d_i = nums[i] div 2 for 0 <= i < n. The function returns r and r = S - (sum of the min(op1, n) largest elements of the multiset {d_0,...,d_{n-1}}). Equivalently, the value of op2 has no effect on the answer.
  Preconditions: n = len(nums); 1 <= n <= 100; for every i with 0 <= i < n, 0 <= nums[i] <= 100000; 0 <= k <= 100000; for every i with 0 <= i < n, nums[i] < k; 0 <= op1 <= n; 0 <= op2 <= n. -/
theorem spec_8 (nums : Slice I64) (k op1 op2 : I64) (n : Nat)
    (hn : nums.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hbnd : ∀ i, i < n → 0 ≤ nth nums.val i ∧ nth nums.val i ≤ 100000)
    (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ 100000)
    (hlt : ∀ i, i < n → nth nums.val i < k.val)
    (ho1a : 0 ≤ op1.val) (ho1b : op1.val ≤ (n : Int))
    (ho2a : 0 ≤ op2.val) (ho2b : op2.val ≤ (n : Int)) :
    ∃ r, Aegis.MinArraySum.min_array_sum nums k op1 op2 = ok r ∧
      r.val = total nums.val - sumTop (halves nums.val n) (Nat.min op1.val.toNat n) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice I64) (k op1 op2 : I64) (n : Nat)
    (hn : nums.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hbnd : ∀ i, i < n → 0 ≤ nth nums.val i ∧ nth nums.val i ≤ 100000)
    (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ 100000)
    (hlt : ∀ i, i < n → nth nums.val i < k.val)
    (ho1a : 0 ≤ op1.val) (ho1b : op1.val ≤ (n : Int))
    (ho2a : 0 ≤ op2.val) (ho2b : op2.val ≤ (n : Int)), ∃ r, Aegis.MinArraySum.min_array_sum nums k op1 op2 = ok r ∧
      r.val = total nums.val - sumTop (halves nums.val n) (Nat.min op1.val.toNat n)) := by
  sorry

/-- Let a = nums[0]. The function returns r and r = min( {a} union {ceil(a/2) if op1 >= 1} union {a-k if op2 >= 1 and a >= k} union {ceil(a/2)-k if op1 >= 1 and op2 >= 1 and ceil(a/2) >= k} union {ceil((a-k)/2) if op1 >= 1 and op2 >= 1 and a >= k} ), where ceil(x/2) = (x+1) div 2 for x >= 0.
  Preconditions: n = len(nums); n = 1; 0 <= nums[0] <= 100000; 0 <= k <= 100000; 0 <= op1 <= 1; 0 <= op2 <= 1. -/
theorem spec_9 (nums : Slice I64) (k op1 op2 : I64) (n : Nat) (a : Int)
    (hn : nums.val.length = n)
    (hn1 : n = 1)
    (ha : a = nth nums.val 0)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 100000)
    (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ 100000)
    (ho1a : 0 ≤ op1.val) (ho1b : op1.val ≤ 1)
    (ho2a : 0 ≤ op2.val) (ho2b : op2.val ≤ 1) :
    ∃ r, Aegis.MinArraySum.min_array_sum nums k op1 op2 = ok r ∧
      r.val = minList
        ([a] ++
          (if 1 ≤ op1.val then [ceilHalf a] else []) ++
          (if 1 ≤ op2.val ∧ k.val ≤ a then [a - k.val] else []) ++
          (if 1 ≤ op1.val ∧ 1 ≤ op2.val ∧ k.val ≤ ceilHalf a then [ceilHalf a - k.val]
            else []) ++
          (if 1 ≤ op1.val ∧ 1 ≤ op2.val ∧ k.val ≤ a then [ceilHalf (a - k.val)] else [])) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice I64) (k op1 op2 : I64) (n : Nat) (a : Int)
    (hn : nums.val.length = n)
    (hn1 : n = 1)
    (ha : a = nth nums.val 0)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 100000)
    (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ 100000)
    (ho1a : 0 ≤ op1.val) (ho1b : op1.val ≤ 1)
    (ho2a : 0 ≤ op2.val) (ho2b : op2.val ≤ 1), ∃ r, Aegis.MinArraySum.min_array_sum nums k op1 op2 = ok r ∧
      r.val = minList
        ([a] ++
          (if 1 ≤ op1.val then [ceilHalf a] else []) ++
          (if 1 ≤ op2.val ∧ k.val ≤ a then [a - k.val] else []) ++
          (if 1 ≤ op1.val ∧ 1 ≤ op2.val ∧ k.val ≤ ceilHalf a then [ceilHalf a - k.val]
            else []) ++
          (if 1 ≤ op1.val ∧ 1 ≤ op2.val ∧ k.val ≤ a then [ceilHalf (a - k.val)] else []))) := by
  sorry

def indexOptions (k x : Int) : List Int :=
  [x, ceilHalf x] ++
    (if k ≤ x then [x - k] else []) ++
    (if k ≤ ceilHalf x then [ceilHalf x - k] else []) ++
    (if k ≤ x then [ceilHalf (x - k)] else [])

/-- For each i with 0 <= i < n, let V_i be the set containing: nums[i]; ceil(nums[i]/2); nums[i]-k if nums[i] >= k; ceil(nums[i]/2)-k if ceil(nums[i]/2) >= k; and ceil((nums[i]-k)/2) if nums[i] >= k, where ceil(x/2) = (x+1) div 2 for x >= 0. The function returns r and r = sum_{i=0}^{n-1} min(V_i).
  Preconditions: n = len(nums); 1 <= n <= 100; for every i with 0 <= i < n, 0 <= nums[i] <= 100000; 0 <= k <= 100000; op1 = n; op2 = n. -/
theorem spec_10 (nums : Slice I64) (k op1 op2 : I64) (n : Nat)
    (hn : nums.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hbnd : ∀ i, i < n → 0 ≤ nth nums.val i ∧ nth nums.val i ≤ 100000)
    (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ 100000)
    (ho1 : op1.val = (n : Int)) (ho2 : op2.val = (n : Int)) :
    ∃ r, Aegis.MinArraySum.min_array_sum nums k op1 op2 = ok r ∧
      r.val = ((List.range n).map
        (fun i => minList (indexOptions k.val (nth nums.val i)))).sum := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice I64) (k op1 op2 : I64) (n : Nat)
    (hn : nums.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hbnd : ∀ i, i < n → 0 ≤ nth nums.val i ∧ nth nums.val i ≤ 100000)
    (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ 100000)
    (ho1 : op1.val = (n : Int)) (ho2 : op2.val = (n : Int)), ∃ r, Aegis.MinArraySum.min_array_sum nums k op1 op2 = ok r ∧
      r.val = ((List.range n).map
        (fun i => minList (indexOptions k.val (nth nums.val i)))).sum) := by
  sorry

/-- Let r be the Result.ok value returned by min_array_sum(nums, k, op1, op2) and r' be the Result.ok value returned by min_array_sum(nums, k, op1', op2). Then r >= r'.
  Preconditions: n = len(nums); 1 <= n <= 100; for every i with 0 <= i < n, 0 <= nums[i] <= 100000; 0 <= k <= 100000; 0 <= op1 <= op1' <= n; 0 <= op2 <= n. -/
theorem spec_11 (nums : Slice I64) (k op1 op1' op2 : I64) (n : Nat)
    (hn : nums.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hbnd : ∀ i, i < n → 0 ≤ nth nums.val i ∧ nth nums.val i ≤ 100000)
    (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ 100000)
    (hp0 : 0 ≤ op1.val) (hp1 : op1.val ≤ op1'.val) (hp2 : op1'.val ≤ (n : Int))
    (ho2a : 0 ≤ op2.val) (ho2b : op2.val ≤ (n : Int)) :
    ∃ r r', Aegis.MinArraySum.min_array_sum nums k op1 op2 = ok r ∧
      Aegis.MinArraySum.min_array_sum nums k op1' op2 = ok r' ∧ r'.val ≤ r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice I64) (k op1 op1' op2 : I64) (n : Nat)
    (hn : nums.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hbnd : ∀ i, i < n → 0 ≤ nth nums.val i ∧ nth nums.val i ≤ 100000)
    (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ 100000)
    (hp0 : 0 ≤ op1.val) (hp1 : op1.val ≤ op1'.val) (hp2 : op1'.val ≤ (n : Int))
    (ho2a : 0 ≤ op2.val) (ho2b : op2.val ≤ (n : Int)), ∃ r r', Aegis.MinArraySum.min_array_sum nums k op1 op2 = ok r ∧
      Aegis.MinArraySum.min_array_sum nums k op1' op2 = ok r' ∧ r'.val ≤ r.val) := by
  sorry

/-- Let r be the Result.ok value returned by min_array_sum(nums, k, op1, op2) and r' be the Result.ok value returned by min_array_sum(nums, k, op1, op2'). Then r >= r'.
  Preconditions: n = len(nums); 1 <= n <= 100; for every i with 0 <= i < n, 0 <= nums[i] <= 100000; 0 <= k <= 100000; 0 <= op1 <= n; 0 <= op2 <= op2' <= n. -/
theorem spec_12 (nums : Slice I64) (k op1 op2 op2' : I64) (n : Nat)
    (hn : nums.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hbnd : ∀ i, i < n → 0 ≤ nth nums.val i ∧ nth nums.val i ≤ 100000)
    (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ 100000)
    (ho1a : 0 ≤ op1.val) (ho1b : op1.val ≤ (n : Int))
    (hq0 : 0 ≤ op2.val) (hq1 : op2.val ≤ op2'.val) (hq2 : op2'.val ≤ (n : Int)) :
    ∃ r r', Aegis.MinArraySum.min_array_sum nums k op1 op2 = ok r ∧
      Aegis.MinArraySum.min_array_sum nums k op1 op2' = ok r' ∧ r'.val ≤ r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice I64) (k op1 op2 op2' : I64) (n : Nat)
    (hn : nums.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hbnd : ∀ i, i < n → 0 ≤ nth nums.val i ∧ nth nums.val i ≤ 100000)
    (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ 100000)
    (ho1a : 0 ≤ op1.val) (ho1b : op1.val ≤ (n : Int))
    (hq0 : 0 ≤ op2.val) (hq1 : op2.val ≤ op2'.val) (hq2 : op2'.val ≤ (n : Int)), ∃ r r', Aegis.MinArraySum.min_array_sum nums k op1 op2 = ok r ∧
      Aegis.MinArraySum.min_array_sum nums k op1 op2' = ok r' ∧ r'.val ≤ r.val) := by
  sorry

end AegisSpec.MinArraySum

import Aegis.MinUnlockedIndices.Code.Funs

/-!
# Specifications of `Aegis.MinUnlockedIndices.min_unlocked_indices`

LeetCode problem `minimum-unlocked-indices-to-sort-nums`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinUnlockedIndices

def contents (s : Slice Std.I64) : List ℤ := s.val.map (fun x => x.val)

def idx (l : List ℤ) (i : ℕ) : ℤ := l.getD i 0

def Sorted (l : List ℤ) : Prop := ∀ i, i + 1 < l.length → idx l i ≤ idx l (i + 1)

def Binary (l : List ℤ) : Prop := ∀ i, i < l.length → idx l i = 0 ∨ idx l i = 1

def SwapStep (L' a b : List ℤ) : Prop :=
  ∃ i, i + 1 < a.length ∧ L'[i]? = some 0 ∧ idx a i - idx a (i + 1) = 1 ∧
    b = (a.set i (idx a (i + 1))).set (i + 1) (idx a i)

def Reachable (L' a b : List ℤ) : Prop := Relation.ReflTransGen (SwapStep L') a b

def Sortable (nums L' : List ℤ) : Prop := ∃ k, Reachable L' nums k ∧ Sorted k

def UnlockingMask (n : ℕ) (locked L' : List ℤ) : Prop :=
  L'.length = n ∧ Binary L' ∧ ∀ i, i < n → idx L' i ≤ idx locked i

def unlockCount (locked L' : List ℤ) : ℕ :=
  ((Finset.range locked.length).filter (fun i => idx locked i = 1 ∧ idx L' i = 0)).card

def lockedCount (locked : List ℤ) (n : ℕ) : ℕ :=
  ((Finset.range n).filter (fun i => idx locked i = 1)).card

def ThreeBeforeOne (l : List ℤ) : Prop :=
  ∃ i j, i < j ∧ j < l.length ∧ idx l i = 3 ∧ idx l j = 1

def HasLater (l : List ℤ) (i : ℕ) (w : ℤ) : Prop :=
  ∃ j, i < j ∧ j < l.length ∧ idx l j = w

def IsLastIndex (l : List ℤ) (v last : ℤ) : Prop :=
  (last = -1 ∧ ∀ i, i < l.length → idx l i ≠ v) ∨
    (∃ j : ℕ, last = (j : ℤ) ∧ j < l.length ∧ idx l j = v ∧
      ∀ k : ℕ, j < k → k < l.length → idx l k ≠ v)

def IsPairStart (l : List ℤ) (v w : ℤ) (p : ℤ) : Prop :=
  (p = (l.length : ℤ) ∧ ∀ i, i < l.length → ¬ (idx l i = v ∧ HasLater l i w)) ∨
    (∃ i : ℕ, p = (i : ℤ) ∧ i < l.length ∧ idx l i = v ∧ HasLater l i w ∧
      ∀ k : ℕ, k < i → ¬ (idx l k = v ∧ HasLater l k w))

abbrev InR (p1 last1 p2 last2 : ℤ) (i : ℕ) : Prop :=
  (p1 ≤ (i : ℤ) ∧ (i : ℤ) < last1) ∨ (p2 ≤ (i : ℤ) ∧ (i : ℤ) < last2)

def starMask (locked : List ℤ) (p1 last1 p2 last2 : ℤ) : List ℤ :=
  (List.range locked.length).map
    (fun i => if idx locked i = 0 ∨ InR p1 last1 p2 last2 i then (0 : ℤ) else 1)

def inRCount (locked : List ℤ) (n : ℕ) (p1 last1 p2 last2 : ℤ) : ℕ :=
  ((Finset.range n).filter (fun i => idx locked i = 1 ∧ InR p1 last1 p2 last2 i)).card

/-- Let an unlocking mask be any length-n binary list L' with L'[i] <= locked[i] for every 0 <= i < n. Let Sortable(nums,L') mean that there is a finite sequence of arrays a_0,...,a_k such that a_0 = nums, a_k is nondecreasing (a_k[i] <= a_k[i+1] for every 0 <= i < n-1), and each a_{t+1} is obtained from a_t by choosing an index i < n-1 with L'[i] = 0 and a_t[i] - a_t[i+1] = 1, then swapping a_t[i] and a_t[i+1]. The function returns a result r, and: if at least one unlocking mask L' makes Sortable(nums,L') true, then r is the minimum, over all such L', of the number of indices i with locked[i] = 1 and L'[i] = 0; if no unlocking mask makes Sortable(nums,L') true, then r = -1.
  Preconditions: Let n = len(nums). n >= 1; len(locked) = n; for every i with 0 <= i < n, 1 <= nums[i] <= 3 and locked[i] is 0 or 1. -/
theorem spec_1 (nums locked : Slice Std.I64) (n : ℕ)
    (hn : n = (contents nums).length) (hpos : 1 ≤ n)
    (hlen : (contents locked).length = n)
    (hnum : ∀ i, i < n → 1 ≤ idx (contents nums) i ∧ idx (contents nums) i ≤ 3)
    (hlock : ∀ i, i < n → idx (contents locked) i = 0 ∨ idx (contents locked) i = 1) :
    ∃ r, Aegis.MinUnlockedIndices.min_unlocked_indices nums locked = ok r ∧
      ((∃ L', UnlockingMask n (contents locked) L' ∧ Sortable (contents nums) L') →
        (∃ L', UnlockingMask n (contents locked) L' ∧ Sortable (contents nums) L' ∧
            r.val = (unlockCount (contents locked) L' : ℤ)) ∧
          (∀ L', UnlockingMask n (contents locked) L' → Sortable (contents nums) L' →
            r.val ≤ (unlockCount (contents locked) L' : ℤ))) ∧
      ((¬ ∃ L', UnlockingMask n (contents locked) L' ∧ Sortable (contents nums) L') →
        r.val = -1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums locked : Slice Std.I64) (n : ℕ)
    (hn : n = (contents nums).length) (hpos : 1 ≤ n)
    (hlen : (contents locked).length = n)
    (hnum : ∀ i, i < n → 1 ≤ idx (contents nums) i ∧ idx (contents nums) i ≤ 3)
    (hlock : ∀ i, i < n → idx (contents locked) i = 0 ∨ idx (contents locked) i = 1), ∃ r, Aegis.MinUnlockedIndices.min_unlocked_indices nums locked = ok r ∧
      ((∃ L', UnlockingMask n (contents locked) L' ∧ Sortable (contents nums) L') →
        (∃ L', UnlockingMask n (contents locked) L' ∧ Sortable (contents nums) L' ∧
            r.val = (unlockCount (contents locked) L' : ℤ)) ∧
          (∀ L', UnlockingMask n (contents locked) L' → Sortable (contents nums) L' →
            r.val ≤ (unlockCount (contents locked) L' : ℤ))) ∧
      ((¬ ∃ L', UnlockingMask n (contents locked) L' ∧ Sortable (contents nums) L') →
        r.val = -1)) := by
  sorry

/-- The function returns a result r; it does not fail, panic, overflow, or go out of bounds on any input satisfying the preconditions.
  Preconditions: Let n = len(nums). n >= 1; len(locked) = n; for every i with 0 <= i < n, 1 <= nums[i] <= 3 and locked[i] is 0 or 1. -/
theorem spec_2 (nums locked : Slice Std.I64) (n : ℕ)
    (hn : n = (contents nums).length) (hpos : 1 ≤ n)
    (hlen : (contents locked).length = n)
    (hnum : ∀ i, i < n → 1 ≤ idx (contents nums) i ∧ idx (contents nums) i ≤ 3)
    (hlock : ∀ i, i < n → idx (contents locked) i = 0 ∨ idx (contents locked) i = 1) :
    ∃ r, Aegis.MinUnlockedIndices.min_unlocked_indices nums locked = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums locked : Slice Std.I64) (n : ℕ)
    (hn : n = (contents nums).length) (hpos : 1 ≤ n)
    (hlen : (contents locked).length = n)
    (hnum : ∀ i, i < n → 1 ≤ idx (contents nums) i ∧ idx (contents nums) i ≤ 3)
    (hlock : ∀ i, i < n → idx (contents locked) i = 0 ∨ idx (contents locked) i = 1), ∃ r, Aegis.MinUnlockedIndices.min_unlocked_indices nums locked = ok r) := by
  sorry

/-- Whenever the function returns r, either r = -1, or 0 <= r <= n.
  Preconditions: Let n = len(nums). n >= 1; len(locked) = n; for every i with 0 <= i < n, 1 <= nums[i] <= 3 and locked[i] is 0 or 1. -/
theorem spec_3 (nums locked : Slice Std.I64) (n : ℕ)
    (hn : n = (contents nums).length) (hpos : 1 ≤ n)
    (hlen : (contents locked).length = n)
    (hnum : ∀ i, i < n → 1 ≤ idx (contents nums) i ∧ idx (contents nums) i ≤ 3)
    (hlock : ∀ i, i < n → idx (contents locked) i = 0 ∨ idx (contents locked) i = 1) :
    ∀ r, Aegis.MinUnlockedIndices.min_unlocked_indices nums locked = ok r →
      r.val = -1 ∨ (0 ≤ r.val ∧ r.val ≤ (n : ℤ)) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums locked : Slice Std.I64) (n : ℕ)
    (hn : n = (contents nums).length) (hpos : 1 ≤ n)
    (hlen : (contents locked).length = n)
    (hnum : ∀ i, i < n → 1 ≤ idx (contents nums) i ∧ idx (contents nums) i ≤ 3)
    (hlock : ∀ i, i < n → idx (contents locked) i = 0 ∨ idx (contents locked) i = 1), ∀ r, Aegis.MinUnlockedIndices.min_unlocked_indices nums locked = ok r →
      r.val = -1 ∨ (0 ≤ r.val ∧ r.val ≤ (n : ℤ))) := by
  sorry

/-- Whenever the function returns r and r >= 0, r is at most the number of indices i with 0 <= i < n and locked[i] = 1.
  Preconditions: Let n = len(nums). n >= 1; len(locked) = n; for every i with 0 <= i < n, 1 <= nums[i] <= 3 and locked[i] is 0 or 1. -/
theorem spec_4 (nums locked : Slice Std.I64) (n : ℕ)
    (hn : n = (contents nums).length) (hpos : 1 ≤ n)
    (hlen : (contents locked).length = n)
    (hnum : ∀ i, i < n → 1 ≤ idx (contents nums) i ∧ idx (contents nums) i ≤ 3)
    (hlock : ∀ i, i < n → idx (contents locked) i = 0 ∨ idx (contents locked) i = 1) :
    ∀ r, Aegis.MinUnlockedIndices.min_unlocked_indices nums locked = ok r → 0 ≤ r.val →
      r.val ≤ (lockedCount (contents locked) n : ℤ) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums locked : Slice Std.I64) (n : ℕ)
    (hn : n = (contents nums).length) (hpos : 1 ≤ n)
    (hlen : (contents locked).length = n)
    (hnum : ∀ i, i < n → 1 ≤ idx (contents nums) i ∧ idx (contents nums) i ≤ 3)
    (hlock : ∀ i, i < n → idx (contents locked) i = 0 ∨ idx (contents locked) i = 1), ∀ r, Aegis.MinUnlockedIndices.min_unlocked_indices nums locked = ok r → 0 ≤ r.val →
      r.val ≤ (lockedCount (contents locked) n : ℤ)) := by
  sorry

/-- Whenever the function returns r, r = -1 if and only if there exist indices i and j with 0 <= i < j < n, nums[i] = 3, and nums[j] = 1.
  Preconditions: Let n = len(nums). n >= 1; len(locked) = n; for every i with 0 <= i < n, 1 <= nums[i] <= 3 and locked[i] is 0 or 1. -/
theorem spec_5 (nums locked : Slice Std.I64) (n : ℕ)
    (hn : n = (contents nums).length) (hpos : 1 ≤ n)
    (hlen : (contents locked).length = n)
    (hnum : ∀ i, i < n → 1 ≤ idx (contents nums) i ∧ idx (contents nums) i ≤ 3)
    (hlock : ∀ i, i < n → idx (contents locked) i = 0 ∨ idx (contents locked) i = 1) :
    ∀ r, Aegis.MinUnlockedIndices.min_unlocked_indices nums locked = ok r →
      (r.val = -1 ↔ ThreeBeforeOne (contents nums)) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums locked : Slice Std.I64) (n : ℕ)
    (hn : n = (contents nums).length) (hpos : 1 ≤ n)
    (hlen : (contents locked).length = n)
    (hnum : ∀ i, i < n → 1 ≤ idx (contents nums) i ∧ idx (contents nums) i ≤ 3)
    (hlock : ∀ i, i < n → idx (contents locked) i = 0 ∨ idx (contents locked) i = 1), ∀ r, Aegis.MinUnlockedIndices.min_unlocked_indices nums locked = ok r →
      (r.val = -1 ↔ ThreeBeforeOne (contents nums))) := by
  sorry

/-- The function returns 0.
  Preconditions: Let n = len(nums). n >= 1; len(locked) = n; for every i with 0 <= i < n, 1 <= nums[i] <= 3 and locked[i] is 0 or 1; moreover nums is nondecreasing, meaning nums[i] <= nums[i+1] for every 0 <= i < n-1. -/
theorem spec_6 (nums locked : Slice Std.I64) (n : ℕ)
    (hn : n = (contents nums).length) (hpos : 1 ≤ n)
    (hlen : (contents locked).length = n)
    (hnum : ∀ i, i < n → 1 ≤ idx (contents nums) i ∧ idx (contents nums) i ≤ 3)
    (hlock : ∀ i, i < n → idx (contents locked) i = 0 ∨ idx (contents locked) i = 1)
    (hmono : ∀ i, i + 1 < n → idx (contents nums) i ≤ idx (contents nums) (i + 1)) :
    Aegis.MinUnlockedIndices.min_unlocked_indices nums locked = ok (0#i64) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums locked : Slice Std.I64) (n : ℕ)
    (hn : n = (contents nums).length) (hpos : 1 ≤ n)
    (hlen : (contents locked).length = n)
    (hnum : ∀ i, i < n → 1 ≤ idx (contents nums) i ∧ idx (contents nums) i ≤ 3)
    (hlock : ∀ i, i < n → idx (contents locked) i = 0 ∨ idx (contents locked) i = 1)
    (hmono : ∀ i, i + 1 < n → idx (contents nums) i ≤ idx (contents nums) (i + 1)), Aegis.MinUnlockedIndices.min_unlocked_indices nums locked = ok (0#i64)) := by
  sorry

/-- The function returns 0 if there do not exist indices i and j with 0 <= i < j < n, nums[i] = 3, and nums[j] = 1; otherwise the function returns -1.
  Preconditions: Let n = len(nums). n >= 1; len(locked) = n; for every i with 0 <= i < n, 1 <= nums[i] <= 3 and locked[i] = 0. -/
theorem spec_7 (nums locked : Slice Std.I64) (n : ℕ)
    (hn : n = (contents nums).length) (hpos : 1 ≤ n)
    (hlen : (contents locked).length = n)
    (hnum : ∀ i, i < n → 1 ≤ idx (contents nums) i ∧ idx (contents nums) i ≤ 3)
    (hlock0 : ∀ i, i < n → idx (contents locked) i = 0) :
    (¬ ThreeBeforeOne (contents nums) →
        Aegis.MinUnlockedIndices.min_unlocked_indices nums locked = ok (0#i64)) ∧
      (ThreeBeforeOne (contents nums) →
        Aegis.MinUnlockedIndices.min_unlocked_indices nums locked = ok ((-1)#i64)) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums locked : Slice Std.I64) (n : ℕ)
    (hn : n = (contents nums).length) (hpos : 1 ≤ n)
    (hlen : (contents locked).length = n)
    (hnum : ∀ i, i < n → 1 ≤ idx (contents nums) i ∧ idx (contents nums) i ≤ 3)
    (hlock0 : ∀ i, i < n → idx (contents locked) i = 0), (¬ ThreeBeforeOne (contents nums) →
        Aegis.MinUnlockedIndices.min_unlocked_indices nums locked = ok (0#i64)) ∧
      (ThreeBeforeOne (contents nums) →
        Aegis.MinUnlockedIndices.min_unlocked_indices nums locked = ok ((-1)#i64))) := by
  sorry

/-- Whenever the function returns r and r >= 0, r = 0 if and only if nums is sortable with the original mask locked, i.e., there is a finite sequence of allowed adjacent swaps using locked[i] = 0 as the permission condition that transforms nums into a nondecreasing array.
  Preconditions: Let n = len(nums). n >= 1; len(locked) = n; for every i with 0 <= i < n, 1 <= nums[i] <= 3 and locked[i] is 0 or 1. -/
theorem spec_8 (nums locked : Slice Std.I64) (n : ℕ)
    (hn : n = (contents nums).length) (hpos : 1 ≤ n)
    (hlen : (contents locked).length = n)
    (hnum : ∀ i, i < n → 1 ≤ idx (contents nums) i ∧ idx (contents nums) i ≤ 3)
    (hlock : ∀ i, i < n → idx (contents locked) i = 0 ∨ idx (contents locked) i = 1) :
    ∀ r, Aegis.MinUnlockedIndices.min_unlocked_indices nums locked = ok r → 0 ≤ r.val →
      (r.val = 0 ↔ Sortable (contents nums) (contents locked)) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums locked : Slice Std.I64) (n : ℕ)
    (hn : n = (contents nums).length) (hpos : 1 ≤ n)
    (hlen : (contents locked).length = n)
    (hnum : ∀ i, i < n → 1 ≤ idx (contents nums) i ∧ idx (contents nums) i ≤ 3)
    (hlock : ∀ i, i < n → idx (contents locked) i = 0 ∨ idx (contents locked) i = 1), ∀ r, Aegis.MinUnlockedIndices.min_unlocked_indices nums locked = ok r → 0 ≤ r.val →
      (r.val = 0 ↔ Sortable (contents nums) (contents locked))) := by
  sorry

/-- The function returns r equal to the number of indices i such that 0 <= i < n, locked[i] = 1, and i is in R.
  Preconditions: Let n = len(nums). n >= 1; len(locked) = n; for every i with 0 <= i < n, 1 <= nums[i] <= 3 and locked[i] is 0 or 1; there do not exist indices i and j with 0 <= i < j < n, nums[i] = 3, and nums[j] = 1. Let last1 be the largest index j with nums[j] = 1, or -1 if there is none. Let p1 be the smallest index i with nums[i] = 2 for which some j > i has nums[j] = 1, or n if there is no such i. Let last2 be the largest index j with nums[j] = 2, or -1 if there is none. Let p2 be the smallest index i with nums[i] = 3 for which some j > i has nums[j] = 2, or n if there is no such i. Let R = { i | 0 <= i < n and ( (p1 <= i and i < last1) or (p2 <= i and i < last2) ) }. -/
theorem spec_9 (nums locked : Slice Std.I64) (n : ℕ)
    (hn : n = (contents nums).length) (hpos : 1 ≤ n)
    (hlen : (contents locked).length = n)
    (hnum : ∀ i, i < n → 1 ≤ idx (contents nums) i ∧ idx (contents nums) i ≤ 3)
    (hlock : ∀ i, i < n → idx (contents locked) i = 0 ∨ idx (contents locked) i = 1)
    (hnopair : ¬ ThreeBeforeOne (contents nums))
    (last1 p1 last2 p2 : ℤ)
    (hlast1 : IsLastIndex (contents nums) 1 last1)
    (hp1 : IsPairStart (contents nums) 2 1 p1)
    (hlast2 : IsLastIndex (contents nums) 2 last2)
    (hp2 : IsPairStart (contents nums) 3 2 p2) :
    ∃ r, Aegis.MinUnlockedIndices.min_unlocked_indices nums locked = ok r ∧
      r.val = (inRCount (contents locked) n p1 last1 p2 last2 : ℤ) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums locked : Slice Std.I64) (n : ℕ)
    (hn : n = (contents nums).length) (hpos : 1 ≤ n)
    (hlen : (contents locked).length = n)
    (hnum : ∀ i, i < n → 1 ≤ idx (contents nums) i ∧ idx (contents nums) i ≤ 3)
    (hlock : ∀ i, i < n → idx (contents locked) i = 0 ∨ idx (contents locked) i = 1)
    (hnopair : ¬ ThreeBeforeOne (contents nums))
    (last1 p1 last2 p2 : ℤ)
    (hlast1 : IsLastIndex (contents nums) 1 last1)
    (hp1 : IsPairStart (contents nums) 2 1 p1)
    (hlast2 : IsLastIndex (contents nums) 2 last2)
    (hp2 : IsPairStart (contents nums) 3 2 p2), ∃ r, Aegis.MinUnlockedIndices.min_unlocked_indices nums locked = ok r ∧
      r.val = (inRCount (contents locked) n p1 last1 p2 last2 : ℤ)) := by
  sorry

/-- Let r1 be the result of the function on (nums,locked1) and r2 be the result on (nums,locked2). Whenever both calls return results, either r1 = r2 = -1, or r1 >= 0, r2 >= 0, and r2 <= r1.
  Preconditions: Let n = len(nums). n >= 1; for every i with 0 <= i < n, 1 <= nums[i] <= 3. Let locked1 and locked2 be length-n binary masks. Assume locked2[i] <= locked1[i] for every 0 <= i < n, so locked2 is at least as unlocked as locked1 at every index. -/
theorem spec_10 (nums locked1 locked2 : Slice Std.I64) (n : ℕ)
    (hn : n = (contents nums).length) (hpos : 1 ≤ n)
    (hnum : ∀ i, i < n → 1 ≤ idx (contents nums) i ∧ idx (contents nums) i ≤ 3)
    (hlen1 : (contents locked1).length = n)
    (hbin1 : Binary (contents locked1))
    (hlen2 : (contents locked2).length = n)
    (hbin2 : Binary (contents locked2))
    (hle : ∀ i, i < n → idx (contents locked2) i ≤ idx (contents locked1) i) :
    ∀ r1 r2, Aegis.MinUnlockedIndices.min_unlocked_indices nums locked1 = ok r1 →
      Aegis.MinUnlockedIndices.min_unlocked_indices nums locked2 = ok r2 →
      (r1.val = -1 ∧ r2.val = -1) ∨ (0 ≤ r1.val ∧ 0 ≤ r2.val ∧ r2.val ≤ r1.val) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums locked1 locked2 : Slice Std.I64) (n : ℕ)
    (hn : n = (contents nums).length) (hpos : 1 ≤ n)
    (hnum : ∀ i, i < n → 1 ≤ idx (contents nums) i ∧ idx (contents nums) i ≤ 3)
    (hlen1 : (contents locked1).length = n)
    (hbin1 : Binary (contents locked1))
    (hlen2 : (contents locked2).length = n)
    (hbin2 : Binary (contents locked2))
    (hle : ∀ i, i < n → idx (contents locked2) i ≤ idx (contents locked1) i), ∀ r1 r2, Aegis.MinUnlockedIndices.min_unlocked_indices nums locked1 = ok r1 →
      Aegis.MinUnlockedIndices.min_unlocked_indices nums locked2 = ok r2 →
      (r1.val = -1 ∧ r2.val = -1) ∨ (0 ≤ r1.val ∧ 0 ≤ r2.val ∧ r2.val ≤ r1.val)) := by
  sorry

/-- If the function returns r1 on (nums,locked1) and r2 on (nums,locked2), then r1 = r2, and this common value is the number of indices i in R with locked1[i] = 1 (equivalently, the number with locked2[i] = 1).
  Preconditions: Let n = len(nums). n >= 1; for every i with 0 <= i < n, 1 <= nums[i] <= 3; there do not exist indices i and j with 0 <= i < j < n, nums[i] = 3, and nums[j] = 1. Let last1 be the largest index j with nums[j] = 1, or -1 if there is none. Let p1 be the smallest index i with nums[i] = 2 for which some j > i has nums[j] = 1, or n if there is no such i. Let last2 be the largest index j with nums[j] = 2, or -1 if there is none. Let p2 be the smallest index i with nums[i] = 3 for which some j > i has nums[j] = 2, or n if there is no such i. Let R = { i | 0 <= i < n and ( (p1 <= i and i < last1) or (p2 <= i and i < last2) ) }. Let locked1 and locked2 be length-n binary masks that agree on every index in R, i.e., locked1[i] = locked2[i] for every i in R. -/
theorem spec_11 (nums locked1 locked2 : Slice Std.I64) (n : ℕ)
    (hn : n = (contents nums).length) (hpos : 1 ≤ n)
    (hnum : ∀ i, i < n → 1 ≤ idx (contents nums) i ∧ idx (contents nums) i ≤ 3)
    (hnopair : ¬ ThreeBeforeOne (contents nums))
    (last1 p1 last2 p2 : ℤ)
    (hlast1 : IsLastIndex (contents nums) 1 last1)
    (hp1 : IsPairStart (contents nums) 2 1 p1)
    (hlast2 : IsLastIndex (contents nums) 2 last2)
    (hp2 : IsPairStart (contents nums) 3 2 p2)
    (hlen1 : (contents locked1).length = n)
    (hbin1 : Binary (contents locked1))
    (hlen2 : (contents locked2).length = n)
    (hbin2 : Binary (contents locked2))
    (hagree : ∀ i, i < n → InR p1 last1 p2 last2 i →
      idx (contents locked1) i = idx (contents locked2) i) :
    ∀ r1 r2, Aegis.MinUnlockedIndices.min_unlocked_indices nums locked1 = ok r1 →
      Aegis.MinUnlockedIndices.min_unlocked_indices nums locked2 = ok r2 →
      r1 = r2 ∧ r1.val = (inRCount (contents locked1) n p1 last1 p2 last2 : ℤ) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums locked1 locked2 : Slice Std.I64) (n : ℕ)
    (hn : n = (contents nums).length) (hpos : 1 ≤ n)
    (hnum : ∀ i, i < n → 1 ≤ idx (contents nums) i ∧ idx (contents nums) i ≤ 3)
    (hnopair : ¬ ThreeBeforeOne (contents nums))
    (last1 p1 last2 p2 : ℤ)
    (hlast1 : IsLastIndex (contents nums) 1 last1)
    (hp1 : IsPairStart (contents nums) 2 1 p1)
    (hlast2 : IsLastIndex (contents nums) 2 last2)
    (hp2 : IsPairStart (contents nums) 3 2 p2)
    (hlen1 : (contents locked1).length = n)
    (hbin1 : Binary (contents locked1))
    (hlen2 : (contents locked2).length = n)
    (hbin2 : Binary (contents locked2))
    (hagree : ∀ i, i < n → InR p1 last1 p2 last2 i →
      idx (contents locked1) i = idx (contents locked2) i), ∀ r1 r2, Aegis.MinUnlockedIndices.min_unlocked_indices nums locked1 = ok r1 →
      Aegis.MinUnlockedIndices.min_unlocked_indices nums locked2 = ok r2 →
      r1 = r2 ∧ r1.val = (inRCount (contents locked1) n p1 last1 p2 last2 : ℤ)) := by
  sorry

end AegisSpec.MinUnlockedIndices

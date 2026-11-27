import Aegis.MaxCandies.Code.Funs

/-!
# Specifications of `Aegis.MaxCandies.max_candies`

LeetCode problem `maximum-candies-you-can-get-from-boxes`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open scoped Classical

namespace AegisSpec.MaxCandies

def ivals (l : List Std.I64) : List ℤ := l.map (fun x => x.val)

def ivalAt (l : List Std.I64) (i : Nat) : ℤ := (ivals l).getD i 0

def intsAt (l : List (alloc.vec.Vec Std.I64)) (j : Nat) : List ℤ :=
  match l[j]? with
  | some v => ivals v.val
  | none => []

inductive Open (status : Slice Std.I64) (keys : Slice (alloc.vec.Vec Std.I64))
    (containedBoxes : Slice (alloc.vec.Vec Std.I64)) (initialBoxes : Slice Std.I64) :
    Nat → Prop

  | init_status (i : Nat) (hi : i < status.val.length)
      (hinit : (i : ℤ) ∈ ivals initialBoxes.val)
      (hstatus : ivalAt status.val i = 1) :
      Open status keys containedBoxes initialBoxes i

  | init_key (i j : Nat) (hi : i < status.val.length)
      (hinit : (i : ℤ) ∈ ivals initialBoxes.val)
      (hj : Open status keys containedBoxes initialBoxes j)
      (hkey : (i : ℤ) ∈ intsAt keys.val j) :
      Open status keys containedBoxes initialBoxes i

  | child_status (i j : Nat) (hi : i < status.val.length)
      (hj : Open status keys containedBoxes initialBoxes j)
      (hchild : (i : ℤ) ∈ intsAt containedBoxes.val j)
      (hstatus : ivalAt status.val i = 1) :
      Open status keys containedBoxes initialBoxes i

  | child_key (i j₁ j₂ : Nat) (hi : i < status.val.length)
      (hj₁ : Open status keys containedBoxes initialBoxes j₁)
      (hchild : (i : ℤ) ∈ intsAt containedBoxes.val j₁)
      (hj₂ : Open status keys containedBoxes initialBoxes j₂)
      (hkey : (i : ℤ) ∈ intsAt keys.val j₂) :
      Open status keys containedBoxes initialBoxes i

inductive Reach (containedBoxes : Slice (alloc.vec.Vec Std.I64))
    (initialBoxes : Slice Std.I64) : Nat → Prop

  | init (i : Nat) (hi : i < containedBoxes.val.length)
      (h : (i : ℤ) ∈ ivals initialBoxes.val) : Reach containedBoxes initialBoxes i

  | child (i j : Nat) (hi : i < containedBoxes.val.length)
      (hj : Reach containedBoxes initialBoxes j)
      (h : (i : ℤ) ∈ intsAt containedBoxes.val j) : Reach containedBoxes initialBoxes i

def ValidInput (status candies : Slice Std.I64)
    (keys containedBoxes : Slice (alloc.vec.Vec Std.I64)) (initialBoxes : Slice Std.I64) :
    Prop :=
  let n := status.val.length
  candies.val.length = n ∧
  keys.val.length = n ∧
  containedBoxes.val.length = n ∧
  (∀ i, i < n → ivalAt status.val i = 0 ∨ ivalAt status.val i = 1) ∧
  (∀ i, i < n → 1 ≤ ivalAt candies.val i ∧ ivalAt candies.val i ≤ 1000) ∧
  (∀ i, i < n → (intsAt keys.val i).length ≤ n) ∧
  (∀ i, i < n → ∀ x, x ∈ intsAt keys.val i → 0 ≤ x ∧ x < (n : ℤ)) ∧
  (∀ i, i < n → (intsAt keys.val i).Nodup) ∧
  (∀ i, i < n → (intsAt containedBoxes.val i).length ≤ n) ∧
  (∀ i, i < n → ∀ x, x ∈ intsAt containedBoxes.val i → 0 ≤ x ∧ x < (n : ℤ)) ∧
  (∀ i, i < n → (intsAt containedBoxes.val i).Nodup) ∧
  (∀ i, i < n → ∀ j, j < n → ∀ x, x ∈ intsAt containedBoxes.val i →
    x ∈ intsAt containedBoxes.val j → i = j) ∧
  initialBoxes.val.length ≤ n ∧
  (∀ x, x ∈ ivals initialBoxes.val → 0 ≤ x ∧ x < (n : ℤ))

/-- Let Open be the least subset of {0,...,n-1} such that for every i with 0 <= i < n, if (i occurs in initialBoxes or i occurs in containedBoxes[j] for some j in Open) and (status[i] = 1 or i occurs in keys[j] for some j in Open), then i is in Open. Whenever the function returns a result r, r = sum_{i=0}^{n-1} (candies[i] if i is in Open, and 0 otherwise).
  Preconditions: Let n = len(status). The input satisfies all problem constraints: n = len(candies) = len(keys) = len(containedBoxes) and n >= 1; for every i with 0 <= i < n, status[i] is either 0 or 1, and 1 <= candies[i] <= 1000; for every i with 0 <= i < n, len(keys[i]) <= n, every element of keys[i] lies in [0,n), and the elements of keys[i] are pairwise distinct; for every i with 0 <= i < n, len(containedBoxes[i]) <= n, every element of containedBoxes[i] lies in [0,n), and the elements of containedBoxes[i] are pairwise distinct; each box label appears in at most one of the lists containedBoxes[i] over all i; len(initialBoxes) <= n; every element of initialBoxes lies in [0,n). -/
theorem spec_1 (status candies : Slice Std.I64)
    (keys containedBoxes : Slice (alloc.vec.Vec Std.I64)) (initialBoxes : Slice Std.I64)
    (hvalid : ValidInput status candies keys containedBoxes initialBoxes)
    (hpos : 1 ≤ status.val.length)
    (r : Std.I64)
    (h : Aegis.MaxCandies.max_candies status candies keys containedBoxes initialBoxes = ok r) :
    r.val = ∑ i ∈ Finset.range status.val.length,
      (if Open status keys containedBoxes initialBoxes i then ivalAt candies.val i else 0) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (status candies : Slice Std.I64)
    (keys containedBoxes : Slice (alloc.vec.Vec Std.I64)) (initialBoxes : Slice Std.I64)
    (hvalid : ValidInput status candies keys containedBoxes initialBoxes)
    (hpos : 1 ≤ status.val.length)
    (r : Std.I64)
    (h : Aegis.MaxCandies.max_candies status candies keys containedBoxes initialBoxes = ok r), r.val = ∑ i ∈ Finset.range status.val.length,
      (if Open status keys containedBoxes initialBoxes i then ivalAt candies.val i else 0)) := by
  sorry

/-- The function returns a result r for every input satisfying the preconditions; it does not fail, panic, or overflow.
  Preconditions: Let n = len(status). The input satisfies all problem constraints: n = len(candies) = len(keys) = len(containedBoxes) and 1 <= n <= 1000; for every i with 0 <= i < n, status[i] is either 0 or 1, and 1 <= candies[i] <= 1000; for every i with 0 <= i < n, len(keys[i]) <= n, every element of keys[i] lies in [0,n), and the elements of keys[i] are pairwise distinct; for every i with 0 <= i < n, len(containedBoxes[i]) <= n, every element of containedBoxes[i] lies in [0,n), and the elements of containedBoxes[i] are pairwise distinct; each box label appears in at most one of the lists containedBoxes[i] over all i; len(initialBoxes) <= n; every element of initialBoxes lies in [0,n). -/
theorem spec_2 (status candies : Slice Std.I64)
    (keys containedBoxes : Slice (alloc.vec.Vec Std.I64)) (initialBoxes : Slice Std.I64)
    (hvalid : ValidInput status candies keys containedBoxes initialBoxes)
    (hpos : 1 ≤ status.val.length)
    (hmax : status.val.length ≤ 1000) :
    ∃ r : Std.I64,
      Aegis.MaxCandies.max_candies status candies keys containedBoxes initialBoxes = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (status candies : Slice Std.I64)
    (keys containedBoxes : Slice (alloc.vec.Vec Std.I64)) (initialBoxes : Slice Std.I64)
    (hvalid : ValidInput status candies keys containedBoxes initialBoxes)
    (hpos : 1 ≤ status.val.length)
    (hmax : status.val.length ≤ 1000), ∃ r : Std.I64,
      Aegis.MaxCandies.max_candies status candies keys containedBoxes initialBoxes = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= sum_{i=0}^{n-1} candies[i].
  Preconditions: Let n = len(status). The input satisfies all problem constraints: n = len(candies) = len(keys) = len(containedBoxes) and n >= 1; status entries are 0 or 1; candies entries are in [1,1000]; keys and containedBoxes have lengths at most n and contain only labels in [0,n), with pairwise distinct elements in each list; each box label appears in at most one containedBoxes list; len(initialBoxes) <= n and every initial label lies in [0,n). -/
theorem spec_3 (status candies : Slice Std.I64)
    (keys containedBoxes : Slice (alloc.vec.Vec Std.I64)) (initialBoxes : Slice Std.I64)
    (hvalid : ValidInput status candies keys containedBoxes initialBoxes)
    (hpos : 1 ≤ status.val.length)
    (r : Std.I64)
    (h : Aegis.MaxCandies.max_candies status candies keys containedBoxes initialBoxes = ok r) :
    0 ≤ r.val ∧
      r.val ≤ ∑ i ∈ Finset.range status.val.length, ivalAt candies.val i := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (status candies : Slice Std.I64)
    (keys containedBoxes : Slice (alloc.vec.Vec Std.I64)) (initialBoxes : Slice Std.I64)
    (hvalid : ValidInput status candies keys containedBoxes initialBoxes)
    (hpos : 1 ≤ status.val.length)
    (r : Std.I64)
    (h : Aegis.MaxCandies.max_candies status candies keys containedBoxes initialBoxes = ok r), 0 ≤ r.val ∧
      r.val ≤ ∑ i ∈ Finset.range status.val.length, ivalAt candies.val i) := by
  sorry

/-- Whenever the function returns a result r, r = 0.
  Preconditions: Let n = len(status). The input satisfies all problem constraints: n = len(candies) = len(keys) = len(containedBoxes) and n >= 1; status entries are 0 or 1; candies entries are in [1,1000]; keys and containedBoxes have lengths at most n and contain only labels in [0,n), with pairwise distinct elements in each list; each box label appears in at most one containedBoxes list; len(initialBoxes) <= n and every initial label lies in [0,n). In addition, len(initialBoxes) = 0. -/
theorem spec_4 (status candies : Slice Std.I64)
    (keys containedBoxes : Slice (alloc.vec.Vec Std.I64)) (initialBoxes : Slice Std.I64)
    (hvalid : ValidInput status candies keys containedBoxes initialBoxes)
    (hpos : 1 ≤ status.val.length)
    (hempty : initialBoxes.val.length = 0)
    (r : Std.I64)
    (h : Aegis.MaxCandies.max_candies status candies keys containedBoxes initialBoxes = ok r) :
    r.val = 0 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (status candies : Slice Std.I64)
    (keys containedBoxes : Slice (alloc.vec.Vec Std.I64)) (initialBoxes : Slice Std.I64)
    (hvalid : ValidInput status candies keys containedBoxes initialBoxes)
    (hpos : 1 ≤ status.val.length)
    (hempty : initialBoxes.val.length = 0)
    (r : Std.I64)
    (h : Aegis.MaxCandies.max_candies status candies keys containedBoxes initialBoxes = ok r), r.val = 0) := by
  sorry

/-- Whenever the function returns a result r, r = candies[0] if status[0] = 1 and box 0 occurs in initialBoxes, and r = 0 otherwise.
  Preconditions: Let n = len(status). The input satisfies all problem constraints: n = len(candies) = len(keys) = len(containedBoxes) and n >= 1; status entries are 0 or 1; candies entries are in [1,1000]; keys and containedBoxes have lengths at most n and contain only labels in [0,n), with pairwise distinct elements in each list; each box label appears in at most one containedBoxes list; len(initialBoxes) <= n and every initial label lies in [0,n). In addition, n = 1. -/
theorem spec_5 (status candies : Slice Std.I64)
    (keys containedBoxes : Slice (alloc.vec.Vec Std.I64)) (initialBoxes : Slice Std.I64)
    (hvalid : ValidInput status candies keys containedBoxes initialBoxes)
    (hpos : 1 ≤ status.val.length)
    (hone : status.val.length = 1)
    (r : Std.I64)
    (h : Aegis.MaxCandies.max_candies status candies keys containedBoxes initialBoxes = ok r) :
    r.val = if (ivalAt status.val 0 = 1 ∧ (0 : ℤ) ∈ ivals initialBoxes.val)
      then ivalAt candies.val 0 else 0 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (status candies : Slice Std.I64)
    (keys containedBoxes : Slice (alloc.vec.Vec Std.I64)) (initialBoxes : Slice Std.I64)
    (hvalid : ValidInput status candies keys containedBoxes initialBoxes)
    (hpos : 1 ≤ status.val.length)
    (hone : status.val.length = 1)
    (r : Std.I64)
    (h : Aegis.MaxCandies.max_candies status candies keys containedBoxes initialBoxes = ok r), r.val = if (ivalAt status.val 0 = 1 ∧ (0 : ℤ) ∈ ivals initialBoxes.val)
      then ivalAt candies.val 0 else 0) := by
  sorry

/-- Whenever the function returns a result r, let R be the least subset of {0,...,n-1} such that every element of initialBoxes is in R and for every j in R, every element of containedBoxes[j] is in R. Then r = sum_{i in R} candies[i].
  Preconditions: Let n = len(status). The input satisfies all problem constraints: n = len(candies) = len(keys) = len(containedBoxes) and n >= 1; status entries are 0 or 1; candies entries are in [1,1000]; keys and containedBoxes have lengths at most n and contain only labels in [0,n), with pairwise distinct elements in each list; each box label appears in at most one containedBoxes list; len(initialBoxes) <= n and every initial label lies in [0,n). In addition, status[i] = 1 for every 0 <= i < n. -/
theorem spec_6 (status candies : Slice Std.I64)
    (keys containedBoxes : Slice (alloc.vec.Vec Std.I64)) (initialBoxes : Slice Std.I64)
    (hvalid : ValidInput status candies keys containedBoxes initialBoxes)
    (hpos : 1 ≤ status.val.length)
    (hall : ∀ i, i < status.val.length → ivalAt status.val i = 1)
    (r : Std.I64)
    (h : Aegis.MaxCandies.max_candies status candies keys containedBoxes initialBoxes = ok r) :
    r.val = ∑ i ∈ Finset.range status.val.length,
      (if Reach containedBoxes initialBoxes i then ivalAt candies.val i else 0) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (status candies : Slice Std.I64)
    (keys containedBoxes : Slice (alloc.vec.Vec Std.I64)) (initialBoxes : Slice Std.I64)
    (hvalid : ValidInput status candies keys containedBoxes initialBoxes)
    (hpos : 1 ≤ status.val.length)
    (hall : ∀ i, i < status.val.length → ivalAt status.val i = 1)
    (r : Std.I64)
    (h : Aegis.MaxCandies.max_candies status candies keys containedBoxes initialBoxes = ok r), r.val = ∑ i ∈ Finset.range status.val.length,
      (if Reach containedBoxes initialBoxes i then ivalAt candies.val i else 0)) := by
  sorry

/-- Whenever the first input returns a result r and the second input returns a result r', r = r'.
  Preconditions: Let n = len(status). Both inputs satisfy all problem constraints: n = len(candies) = len(keys) = len(containedBoxes) and n >= 1; status entries are 0 or 1; candies entries are in [1,1000]; keys and containedBoxes have lengths at most n and contain only labels in [0,n), with pairwise distinct elements in each list; each box label appears in at most one containedBoxes list; initial lists have length <= n and labels in [0,n). The two inputs have identical status, candies, keys, and containedBoxes arrays, and their initialBoxes lists are A and A'. For every i with 0 <= i < n, i occurs in A if and only if i occurs in A'. -/
theorem spec_7 (status candies : Slice Std.I64)
    (keys containedBoxes : Slice (alloc.vec.Vec Std.I64))
    (A A' : Slice Std.I64)
    (hvalid : ValidInput status candies keys containedBoxes A)
    (hvalid' : ValidInput status candies keys containedBoxes A')
    (hpos : 1 ≤ status.val.length)
    (hsame : ∀ i, i < status.val.length →
      ((i : ℤ) ∈ ivals A.val ↔ (i : ℤ) ∈ ivals A'))
    (r r' : Std.I64)
    (h : Aegis.MaxCandies.max_candies status candies keys containedBoxes A = ok r)
    (h' : Aegis.MaxCandies.max_candies status candies keys containedBoxes A' = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (status candies : Slice Std.I64)
    (keys containedBoxes : Slice (alloc.vec.Vec Std.I64))
    (A A' : Slice Std.I64)
    (hvalid : ValidInput status candies keys containedBoxes A)
    (hvalid' : ValidInput status candies keys containedBoxes A')
    (hpos : 1 ≤ status.val.length)
    (hsame : ∀ i, i < status.val.length →
      ((i : ℤ) ∈ ivals A.val ↔ (i : ℤ) ∈ ivals A'))
    (r r' : Std.I64)
    (h : Aegis.MaxCandies.max_candies status candies keys containedBoxes A = ok r)
    (h' : Aegis.MaxCandies.max_candies status candies keys containedBoxes A' = ok r'), r.val = r'.val) := by
  sorry

/-- Whenever max_candies(status, candies, keys, containedBoxes, initialBoxes) returns r and max_candies(status, candies', keys, containedBoxes, initialBoxes) returns r', r = r'.
  Preconditions: Let n = len(status). The input satisfies all problem constraints: n = len(candies) = len(keys) = len(containedBoxes) and n >= 1; status entries are 0 or 1; candies entries are in [1,1000]; keys and containedBoxes have lengths at most n and contain only labels in [0,n), with pairwise distinct elements in each list; each box label appears in at most one containedBoxes list; len(initialBoxes) <= n and every initial label lies in [0,n). Let Open be the least subset of {0,...,n-1} such that for every i with 0 <= i < n, if (i occurs in initialBoxes or i occurs in containedBoxes[j] for some j in Open) and (status[i] = 1 or i occurs in keys[j] for some j in Open), then i is in Open. Let candies' be another array with 1 <= candies'[i] <= 1000 for every i, and with candies'[i] = candies[i] for every i in Open. -/
theorem spec_8 (status candies candies' : Slice Std.I64)
    (keys containedBoxes : Slice (alloc.vec.Vec Std.I64)) (initialBoxes : Slice Std.I64)
    (hvalid : ValidInput status candies keys containedBoxes initialBoxes)
    (hvalid' : ValidInput status candies' keys containedBoxes initialBoxes)
    (hpos : 1 ≤ status.val.length)
    (hsame : ∀ i, i < status.val.length →
      Open status keys containedBoxes initialBoxes i →
      ivalAt candies'.val i = ivalAt candies.val i)
    (r r' : Std.I64)
    (h : Aegis.MaxCandies.max_candies status candies keys containedBoxes initialBoxes = ok r)
    (h' : Aegis.MaxCandies.max_candies status candies' keys containedBoxes initialBoxes = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (status candies candies' : Slice Std.I64)
    (keys containedBoxes : Slice (alloc.vec.Vec Std.I64)) (initialBoxes : Slice Std.I64)
    (hvalid : ValidInput status candies keys containedBoxes initialBoxes)
    (hvalid' : ValidInput status candies' keys containedBoxes initialBoxes)
    (hpos : 1 ≤ status.val.length)
    (hsame : ∀ i, i < status.val.length →
      Open status keys containedBoxes initialBoxes i →
      ivalAt candies'.val i = ivalAt candies.val i)
    (r r' : Std.I64)
    (h : Aegis.MaxCandies.max_candies status candies keys containedBoxes initialBoxes = ok r)
    (h' : Aegis.MaxCandies.max_candies status candies' keys containedBoxes initialBoxes = ok r'), r.val = r'.val) := by
  sorry

/-- Whenever the first input returns a result r and the second input returns a result r', r' >= r.
  Preconditions: Let n = len(status). Both inputs satisfy all problem constraints: n = len(candies) = len(keys) = len(containedBoxes) and n >= 1; status entries are 0 or 1; candies entries are in [1,1000]; keys and containedBoxes have lengths at most n and contain only labels in [0,n), with pairwise distinct elements in each list; each box label appears in at most one containedBoxes list; initial lists have length <= n and labels in [0,n). The two inputs have identical status, candies, keys, and containedBoxes arrays, and their initialBoxes lists are A and A'. Every box label occurring in A also occurs in A'. -/
theorem spec_9 (status candies : Slice Std.I64)
    (keys containedBoxes : Slice (alloc.vec.Vec Std.I64))
    (A A' : Slice Std.I64)
    (hvalid : ValidInput status candies keys containedBoxes A)
    (hvalid' : ValidInput status candies keys containedBoxes A')
    (hpos : 1 ≤ status.val.length)
    (hsub : ∀ i, i < status.val.length →
      (i : ℤ) ∈ ivals A.val → (i : ℤ) ∈ ivals A')
    (r r' : Std.I64)
    (h : Aegis.MaxCandies.max_candies status candies keys containedBoxes A = ok r)
    (h' : Aegis.MaxCandies.max_candies status candies keys containedBoxes A' = ok r') :
    r.val ≤ r'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (status candies : Slice Std.I64)
    (keys containedBoxes : Slice (alloc.vec.Vec Std.I64))
    (A A' : Slice Std.I64)
    (hvalid : ValidInput status candies keys containedBoxes A)
    (hvalid' : ValidInput status candies keys containedBoxes A')
    (hpos : 1 ≤ status.val.length)
    (hsub : ∀ i, i < status.val.length →
      (i : ℤ) ∈ ivals A.val → (i : ℤ) ∈ ivals A')
    (r r' : Std.I64)
    (h : Aegis.MaxCandies.max_candies status candies keys containedBoxes A = ok r)
    (h' : Aegis.MaxCandies.max_candies status candies keys containedBoxes A' = ok r'), r.val ≤ r'.val) := by
  sorry

/-- Whenever the first input with status S returns a result r and the second input with status S' returns a result r', r' >= r.
  Preconditions: Let n = len(status). Both inputs satisfy all problem constraints: n = len(candies) = len(keys) = len(containedBoxes) and n >= 1; status entries are 0 or 1; candies entries are in [1,1000]; keys and containedBoxes have lengths at most n and contain only labels in [0,n), with pairwise distinct elements in each list; each box label appears in at most one containedBoxes list; initial lists have length <= n and labels in [0,n). The two inputs have identical candies, keys, containedBoxes, and initialBoxes arrays, and their status arrays are S and S' with S'[i] >= S[i] for every 0 <= i < n. -/
theorem spec_10 (status status' candies : Slice Std.I64)
    (keys containedBoxes : Slice (alloc.vec.Vec Std.I64)) (initialBoxes : Slice Std.I64)
    (hvalid : ValidInput status candies keys containedBoxes initialBoxes)
    (hvalid' : ValidInput status' candies keys containedBoxes initialBoxes)
    (hpos : 1 ≤ status.val.length)
    (hle : ∀ i, i < status.val.length → ivalAt status.val i ≤ ivalAt status'.val i)
    (r r' : Std.I64)
    (h : Aegis.MaxCandies.max_candies status candies keys containedBoxes initialBoxes = ok r)
    (h' : Aegis.MaxCandies.max_candies status' candies keys containedBoxes initialBoxes = ok r') :
    r.val ≤ r'.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (status status' candies : Slice Std.I64)
    (keys containedBoxes : Slice (alloc.vec.Vec Std.I64)) (initialBoxes : Slice Std.I64)
    (hvalid : ValidInput status candies keys containedBoxes initialBoxes)
    (hvalid' : ValidInput status' candies keys containedBoxes initialBoxes)
    (hpos : 1 ≤ status.val.length)
    (hle : ∀ i, i < status.val.length → ivalAt status.val i ≤ ivalAt status'.val i)
    (r r' : Std.I64)
    (h : Aegis.MaxCandies.max_candies status candies keys containedBoxes initialBoxes = ok r)
    (h' : Aegis.MaxCandies.max_candies status' candies keys containedBoxes initialBoxes = ok r'), r.val ≤ r'.val) := by
  sorry

/-- Whenever the first input with keys K returns a result r and the second input with keys K' returns a result r', r' >= r.
  Preconditions: Let n = len(status). Both inputs satisfy all problem constraints: n = len(candies) = len(keys) = len(containedBoxes) and n >= 1; status entries are 0 or 1; candies entries are in [1,1000]; keys and containedBoxes have lengths at most n and contain only labels in [0,n), with pairwise distinct elements in each list; each box label appears in at most one containedBoxes list; initial lists have length <= n and labels in [0,n). The two inputs have identical status, candies, containedBoxes, and initialBoxes arrays, and their keys arrays are K and K'. For every i with 0 <= i < n and every label x, if x occurs in K[i], then x occurs in K'[i]. -/
theorem spec_11 (status candies : Slice Std.I64)
    (K K' containedBoxes : Slice (alloc.vec.Vec Std.I64)) (initialBoxes : Slice Std.I64)
    (hvalid : ValidInput status candies K containedBoxes initialBoxes)
    (hvalid' : ValidInput status candies K' containedBoxes initialBoxes)
    (hpos : 1 ≤ status.val.length)
    (hsub : ∀ i, i < status.val.length → ∀ x, x ∈ intsAt K.val i → x ∈ intsAt K'.val i)
    (r r' : Std.I64)
    (h : Aegis.MaxCandies.max_candies status candies K containedBoxes initialBoxes = ok r)
    (h' : Aegis.MaxCandies.max_candies status candies K' containedBoxes initialBoxes = ok r') :
    r.val ≤ r'.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (status candies : Slice Std.I64)
    (K K' containedBoxes : Slice (alloc.vec.Vec Std.I64)) (initialBoxes : Slice Std.I64)
    (hvalid : ValidInput status candies K containedBoxes initialBoxes)
    (hvalid' : ValidInput status candies K' containedBoxes initialBoxes)
    (hpos : 1 ≤ status.val.length)
    (hsub : ∀ i, i < status.val.length → ∀ x, x ∈ intsAt K.val i → x ∈ intsAt K'.val i)
    (r r' : Std.I64)
    (h : Aegis.MaxCandies.max_candies status candies K containedBoxes initialBoxes = ok r)
    (h' : Aegis.MaxCandies.max_candies status candies K' containedBoxes initialBoxes = ok r'), r.val ≤ r'.val) := by
  sorry

/-- Whenever the first input with containedBoxes C returns a result r and the second input with containedBoxes C' returns a result r', r' >= r.
  Preconditions: Let n = len(status). Both inputs satisfy all problem constraints: n = len(candies) = len(keys) = len(containedBoxes) and n >= 1; status entries are 0 or 1; candies entries are in [1,1000]; keys and containedBoxes have lengths at most n and contain only labels in [0,n), with pairwise distinct elements in each list; each box label appears in at most one containedBoxes list; initial lists have length <= n and labels in [0,n). The two inputs have identical status, candies, keys, and initialBoxes arrays, and their containedBoxes arrays are C and C'. For every i with 0 <= i < n and every label x, if x occurs in C[i], then x occurs in C'[i]. -/
theorem spec_12 (status candies : Slice Std.I64)
    (keys C C' : Slice (alloc.vec.Vec Std.I64)) (initialBoxes : Slice Std.I64)
    (hvalid : ValidInput status candies keys C initialBoxes)
    (hvalid' : ValidInput status candies keys C' initialBoxes)
    (hpos : 1 ≤ status.val.length)
    (hsub : ∀ i, i < status.val.length → ∀ x, x ∈ intsAt C.val i → x ∈ intsAt C'.val i)
    (r r' : Std.I64)
    (h : Aegis.MaxCandies.max_candies status candies keys C initialBoxes = ok r)
    (h' : Aegis.MaxCandies.max_candies status candies keys C' initialBoxes = ok r') :
    r.val ≤ r'.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (status candies : Slice Std.I64)
    (keys C C' : Slice (alloc.vec.Vec Std.I64)) (initialBoxes : Slice Std.I64)
    (hvalid : ValidInput status candies keys C initialBoxes)
    (hvalid' : ValidInput status candies keys C' initialBoxes)
    (hpos : 1 ≤ status.val.length)
    (hsub : ∀ i, i < status.val.length → ∀ x, x ∈ intsAt C.val i → x ∈ intsAt C'.val i)
    (r r' : Std.I64)
    (h : Aegis.MaxCandies.max_candies status candies keys C initialBoxes = ok r)
    (h' : Aegis.MaxCandies.max_candies status candies keys C' initialBoxes = ok r'), r.val ≤ r'.val) := by
  sorry

/-- Whenever the first input with candies C returns a result r and the second input with candies C' returns a result r', r <= r'.
  Preconditions: Let n = len(status). Both inputs satisfy all problem constraints: n = len(candies) = len(keys) = len(containedBoxes) and n >= 1; status entries are 0 or 1; candies entries are in [1,1000]; keys and containedBoxes have lengths at most n and contain only labels in [0,n), with pairwise distinct elements in each list; each box label appears in at most one containedBoxes list; initial lists have length <= n and labels in [0,n). The two inputs have identical status, keys, containedBoxes, and initialBoxes arrays, and their candies arrays are C and C' with C[i] <= C'[i] for every 0 <= i < n. -/
theorem spec_13 (status : Slice Std.I64)
    (C C' : Slice Std.I64)
    (keys containedBoxes : Slice (alloc.vec.Vec Std.I64)) (initialBoxes : Slice Std.I64)
    (hvalid : ValidInput status C keys containedBoxes initialBoxes)
    (hvalid' : ValidInput status C' keys containedBoxes initialBoxes)
    (hpos : 1 ≤ status.val.length)
    (hle : ∀ i, i < status.val.length → ivalAt C.val i ≤ ivalAt C'.val i)
    (r r' : Std.I64)
    (h : Aegis.MaxCandies.max_candies status C keys containedBoxes initialBoxes = ok r)
    (h' : Aegis.MaxCandies.max_candies status C' keys containedBoxes initialBoxes = ok r') :
    r.val ≤ r'.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (status : Slice Std.I64)
    (C C' : Slice Std.I64)
    (keys containedBoxes : Slice (alloc.vec.Vec Std.I64)) (initialBoxes : Slice Std.I64)
    (hvalid : ValidInput status C keys containedBoxes initialBoxes)
    (hvalid' : ValidInput status C' keys containedBoxes initialBoxes)
    (hpos : 1 ≤ status.val.length)
    (hle : ∀ i, i < status.val.length → ivalAt C.val i ≤ ivalAt C'.val i)
    (r r' : Std.I64)
    (h : Aegis.MaxCandies.max_candies status C keys containedBoxes initialBoxes = ok r)
    (h' : Aegis.MaxCandies.max_candies status C' keys containedBoxes initialBoxes = ok r'), r.val ≤ r'.val) := by
  sorry

end AegisSpec.MaxCandies

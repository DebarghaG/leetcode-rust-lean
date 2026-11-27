import Aegis.SortByBits.Code.Funs

/-!
# Specifications of `Aegis.SortByBits.sort_by_bits`

LeetCode problem `sort-integers-by-the-number-of-1-bits`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.SortByBits

  open Aegis.SortByBits

  def onesNat (n : Nat) : Nat :=
    if n = 0 then 0 else n % 2 + onesNat (n / 2)
  termination_by n

  def ones (x : Int) : Nat := onesNat x.toNat

  def arrList (arr : Slice Std.I64) : List Int := arr.val.map (fun x => x.val)

  def vecList (r : Aeneas.Std.alloc.vec.Vec Std.I64) : List Int :=
    r.val.map (fun x => x.val)

  def cnt (v : Int) (l : List Int) : Nat := (l.filter (fun x => x = v)).length

  def cntOnes (b : Nat) (l : List Int) : Nat := (l.filter (fun x => ones x = b)).length

  def occurs (v : Int) (l : List Int) : Prop := ∃ i : Fin l.length, l.get i = v

  def listMin : List Int → Int
    | [] => 0
    | a :: l => l.foldl min a

  def listMax : List Int → Int
    | [] => 0
    | a :: l => l.foldl max a

  def SortedByBits (l : List Int) : Prop :=
    ∀ (i j : Nat) (hij : i < j) (hj : j < l.length),
      ones (l[i]'(Nat.lt_trans hij hj)) < ones (l[j]'hj) ∨
        (ones (l[i]'(Nat.lt_trans hij hj)) = ones (l[j]'hj) ∧
          l[i]'(Nat.lt_trans hij hj) ≤ l[j]'hj)

  /-- Let ones(x) be the number of 1 digits in the standard binary representation of the nonnegative integer x (so ones(0) = 0). The function returns a result r such that: (1) len(r) = len(arr); (2) r is a permutation of arr, meaning that for every integer v, the number of indices i with 0 <= i < len(r) and r[i] = v equals the number of indices j with 0 <= j < len(arr) and arr[j] = v; and (3) for all i and j with 0 <= i < j < len(r), either ones(r[i]) < ones(r[j]), or ones(r[i]) = ones(r[j]) and r[i] <= r[j]. Thus r is exactly the sequence obtained by sorting arr in nondecreasing order of the pair (ones(x), x).
    Preconditions: len(arr) >= 1 and, for every i with 0 <= i < len(arr), arr[i] >= 0. -/
  theorem spec_1 (arr : Slice Std.I64) (hlen : 1 ≤ arr.val.length)
      (hnn : ∀ (i : Nat) (h : i < arr.val.length), 0 ≤ (arr.val[i]'h).val) :
      ∃ r : Aeneas.Std.alloc.vec.Vec Std.I64,
        sort_by_bits arr = ok r ∧ r.val.length = arr.val.length ∧
          (∀ v : Int, cnt v (vecList r) = cnt v (arrList arr)) ∧
          SortedByBits (vecList r) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (arr : Slice Std.I64) (hlen : 1 ≤ arr.val.length)
        (hnn : ∀ (i : Nat) (h : i < arr.val.length), 0 ≤ (arr.val[i]'h).val), ∃ r : Aeneas.Std.alloc.vec.Vec Std.I64,
          sort_by_bits arr = ok r ∧ r.val.length = arr.val.length ∧
            (∀ v : Int, cnt v (vecList r) = cnt v (arrList arr)) ∧
            SortedByBits (vecList r)) := by
    sorry

  /-- The function returns a result r for every arr satisfying the preconditions; in particular it does not fail, panic, overflow, or perform an out-of-bounds access.
    Preconditions: len(arr) >= 1 and, for every i with 0 <= i < len(arr), arr[i] >= 0. -/
  theorem spec_2 (arr : Slice Std.I64) (hlen : 1 ≤ arr.val.length)
      (hnn : ∀ (i : Nat) (h : i < arr.val.length), 0 ≤ (arr.val[i]'h).val) :
      ∃ r : Aeneas.Std.alloc.vec.Vec Std.I64, sort_by_bits arr = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (arr : Slice Std.I64) (hlen : 1 ≤ arr.val.length)
        (hnn : ∀ (i : Nat) (h : i < arr.val.length), 0 ≤ (arr.val[i]'h).val), ∃ r : Aeneas.Std.alloc.vec.Vec Std.I64, sort_by_bits arr = ok r) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = len(arr).
    Preconditions: len(arr) >= 1 and, for every i with 0 <= i < len(arr), arr[i] >= 0. -/
  theorem spec_3 (arr : Slice Std.I64) (hlen : 1 ≤ arr.val.length)
      (hnn : ∀ (i : Nat) (h : i < arr.val.length), 0 ≤ (arr.val[i]'h).val) :
      ∀ r : Aeneas.Std.alloc.vec.Vec Std.I64,
        sort_by_bits arr = ok r → r.val.length = arr.val.length := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (arr : Slice Std.I64) (hlen : 1 ≤ arr.val.length)
        (hnn : ∀ (i : Nat) (h : i < arr.val.length), 0 ≤ (arr.val[i]'h).val), ∀ r : Aeneas.Std.alloc.vec.Vec Std.I64,
          sort_by_bits arr = ok r → r.val.length = arr.val.length) := by
    sorry

  /-- Whenever the function returns a result r, for every integer v, the number of indices i with 0 <= i < len(r) and r[i] = v equals the number of indices j with 0 <= j < len(arr) and arr[j] = v.
    Preconditions: len(arr) >= 1 and, for every i with 0 <= i < len(arr), arr[i] >= 0. -/
  theorem spec_4 (arr : Slice Std.I64) (hlen : 1 ≤ arr.val.length)
      (hnn : ∀ (i : Nat) (h : i < arr.val.length), 0 ≤ (arr.val[i]'h).val) :
      ∀ r : Aeneas.Std.alloc.vec.Vec Std.I64,
        sort_by_bits arr = ok r →
          ∀ v : Int, cnt v (vecList r) = cnt v (arrList arr) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (arr : Slice Std.I64) (hlen : 1 ≤ arr.val.length)
        (hnn : ∀ (i : Nat) (h : i < arr.val.length), 0 ≤ (arr.val[i]'h).val), ∀ r : Aeneas.Std.alloc.vec.Vec Std.I64,
          sort_by_bits arr = ok r →
            ∀ v : Int, cnt v (vecList r) = cnt v (arrList arr)) := by
    sorry

  /-- Whenever the function returns a result r, for every integer b >= 0, the number of indices i with 0 <= i < len(r) and ones(r[i]) = b equals the number of indices j with 0 <= j < len(arr) and ones(arr[j]) = b, where ones(x) is the number of 1 digits in the binary representation of the nonnegative integer x.
    Preconditions: len(arr) >= 1 and, for every i with 0 <= i < len(arr), arr[i] >= 0. -/
  theorem spec_5 (arr : Slice Std.I64) (hlen : 1 ≤ arr.val.length)
      (hnn : ∀ (i : Nat) (h : i < arr.val.length), 0 ≤ (arr.val[i]'h).val) :
      ∀ r : Aeneas.Std.alloc.vec.Vec Std.I64,
        sort_by_bits arr = ok r →
          ∀ b : Nat, cntOnes b (vecList r) = cntOnes b (arrList arr) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (arr : Slice Std.I64) (hlen : 1 ≤ arr.val.length)
        (hnn : ∀ (i : Nat) (h : i < arr.val.length), 0 ≤ (arr.val[i]'h).val), ∀ r : Aeneas.Std.alloc.vec.Vec Std.I64,
          sort_by_bits arr = ok r →
            ∀ b : Nat, cntOnes b (vecList r) = cntOnes b (arrList arr)) := by
    sorry

  /-- Whenever the function returns a result r, for every k with 0 <= k and k+1 < len(r), ones(r[k]) <= ones(r[k+1]), where ones(x) is the number of 1 digits in the binary representation of the nonnegative integer x.
    Preconditions: len(arr) >= 1 and, for every i with 0 <= i < len(arr), arr[i] >= 0. -/
  theorem spec_6 (arr : Slice Std.I64) (hlen : 1 ≤ arr.val.length)
      (hnn : ∀ (i : Nat) (h : i < arr.val.length), 0 ≤ (arr.val[i]'h).val) :
      ∀ r : Aeneas.Std.alloc.vec.Vec Std.I64,
        sort_by_bits arr = ok r →
          ∀ (k : Nat) (hk : k + 1 < (vecList r).length),
            ones ((vecList r)[k]'(Nat.lt_of_lt_of_le (Nat.lt_succ_self k) (Nat.le_of_lt hk))) ≤
              ones ((vecList r)[k + 1]'hk) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (arr : Slice Std.I64) (hlen : 1 ≤ arr.val.length)
        (hnn : ∀ (i : Nat) (h : i < arr.val.length), 0 ≤ (arr.val[i]'h).val), ∀ r : Aeneas.Std.alloc.vec.Vec Std.I64,
          sort_by_bits arr = ok r →
            ∀ (k : Nat) (hk : k + 1 < (vecList r).length),
              ones ((vecList r)[k]'(Nat.lt_of_lt_of_le (Nat.lt_succ_self k) (Nat.le_of_lt hk))) ≤
                ones ((vecList r)[k + 1]'hk)) := by
    sorry

  /-- Whenever the function returns a result r, for all i and j with 0 <= i < j < len(r), if ones(r[i]) = ones(r[j]) then r[i] <= r[j], where ones(x) is the number of 1 digits in the binary representation of the nonnegative integer x.
    Preconditions: len(arr) >= 1 and, for every i with 0 <= i < len(arr), arr[i] >= 0. -/
  theorem spec_7 (arr : Slice Std.I64) (hlen : 1 ≤ arr.val.length)
      (hnn : ∀ (i : Nat) (h : i < arr.val.length), 0 ≤ (arr.val[i]'h).val) :
      ∀ r : Aeneas.Std.alloc.vec.Vec Std.I64,
        sort_by_bits arr = ok r →
          ∀ (i j : Nat) (hij : i < j) (hj : j < (vecList r).length),
            ones ((vecList r)[i]'(Nat.lt_trans hij hj)) = ones ((vecList r)[j]'hj) →
              (vecList r)[i]'(Nat.lt_trans hij hj) ≤ (vecList r)[j]'hj := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (arr : Slice Std.I64) (hlen : 1 ≤ arr.val.length)
        (hnn : ∀ (i : Nat) (h : i < arr.val.length), 0 ≤ (arr.val[i]'h).val), ∀ r : Aeneas.Std.alloc.vec.Vec Std.I64,
          sort_by_bits arr = ok r →
            ∀ (i j : Nat) (hij : i < j) (hj : j < (vecList r).length),
              ones ((vecList r)[i]'(Nat.lt_trans hij hj)) = ones ((vecList r)[j]'hj) →
                (vecList r)[i]'(Nat.lt_trans hij hj) ≤ (vecList r)[j]'hj) := by
    sorry

  /-- Whenever the function returns a result r, for all i and j with 0 <= i < j < len(r), either ones(r[i]) < ones(r[j]), or ones(r[i]) = ones(r[j]) and r[i] <= r[j], where ones(x) is the number of 1 digits in the binary representation of the nonnegative integer x.
    Preconditions: len(arr) >= 1 and, for every i with 0 <= i < len(arr), arr[i] >= 0. -/
  theorem spec_8 (arr : Slice Std.I64) (hlen : 1 ≤ arr.val.length)
      (hnn : ∀ (i : Nat) (h : i < arr.val.length), 0 ≤ (arr.val[i]'h).val) :
      ∀ r : Aeneas.Std.alloc.vec.Vec Std.I64,
        sort_by_bits arr = ok r →
          ∀ (i j : Nat) (hij : i < j) (hj : j < (vecList r).length),
            ones ((vecList r)[i]'(Nat.lt_trans hij hj)) < ones ((vecList r)[j]'hj) ∨
              (ones ((vecList r)[i]'(Nat.lt_trans hij hj)) = ones ((vecList r)[j]'hj) ∧
                (vecList r)[i]'(Nat.lt_trans hij hj) ≤ (vecList r)[j]'hj) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (arr : Slice Std.I64) (hlen : 1 ≤ arr.val.length)
        (hnn : ∀ (i : Nat) (h : i < arr.val.length), 0 ≤ (arr.val[i]'h).val), ∀ r : Aeneas.Std.alloc.vec.Vec Std.I64,
          sort_by_bits arr = ok r →
            ∀ (i j : Nat) (hij : i < j) (hj : j < (vecList r).length),
              ones ((vecList r)[i]'(Nat.lt_trans hij hj)) < ones ((vecList r)[j]'hj) ∨
                (ones ((vecList r)[i]'(Nat.lt_trans hij hj)) = ones ((vecList r)[j]'hj) ∧
                  (vecList r)[i]'(Nat.lt_trans hij hj) ≤ (vecList r)[j]'hj)) := by
    sorry

  /-- Whenever the function returns a result r, for every k with 0 <= k < len(r), min(arr) <= r[k] <= max(arr), where min(arr) is the least entry of the nonempty array arr and max(arr) is the greatest entry of arr.
    Preconditions: len(arr) >= 1 and, for every i with 0 <= i < len(arr), arr[i] >= 0. -/
  theorem spec_9 (arr : Slice Std.I64) (hlen : 1 ≤ arr.val.length)
      (hnn : ∀ (i : Nat) (h : i < arr.val.length), 0 ≤ (arr.val[i]'h).val) :
      ∀ r : Aeneas.Std.alloc.vec.Vec Std.I64,
        sort_by_bits arr = ok r →
          ∀ (k : Nat) (hk : k < (vecList r).length),
            listMin (arrList arr) ≤ (vecList r)[k]'hk ∧
              (vecList r)[k]'hk ≤ listMax (arrList arr) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (arr : Slice Std.I64) (hlen : 1 ≤ arr.val.length)
        (hnn : ∀ (i : Nat) (h : i < arr.val.length), 0 ≤ (arr.val[i]'h).val), ∀ r : Aeneas.Std.alloc.vec.Vec Std.I64,
          sort_by_bits arr = ok r →
            ∀ (k : Nat) (hk : k < (vecList r).length),
              listMin (arrList arr) ≤ (vecList r)[k]'hk ∧
                (vecList r)[k]'hk ≤ listMax (arrList arr)) := by
    sorry

  /-- Whenever the function returns result r1 for arr1 and result r2 for arr2, r1 = r2.
    Preconditions: len(arr1) >= 1, len(arr2) >= 1, every entry of arr1 and arr2 is nonnegative, and for every integer v the number of occurrences of v in arr1 equals the number of occurrences of v in arr2. -/
  theorem spec_10 (arr1 arr2 : Slice Std.I64) (h1 : 1 ≤ arr1.val.length)
      (h2 : 1 ≤ arr2.val.length)
      (hnn1 : ∀ (i : Nat) (h : i < arr1.val.length), 0 ≤ (arr1.val[i]'h).val)
      (hnn2 : ∀ (i : Nat) (h : i < arr2.val.length), 0 ≤ (arr2.val[i]'h).val)
      (hcnt : ∀ v : Int, cnt v (arrList arr1) = cnt v (arrList arr2)) :
      ∀ r1 r2 : Aeneas.Std.alloc.vec.Vec Std.I64,
        sort_by_bits arr1 = ok r1 → sort_by_bits arr2 = ok r2 → r1 = r2 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (arr1 arr2 : Slice Std.I64) (h1 : 1 ≤ arr1.val.length)
        (h2 : 1 ≤ arr2.val.length)
        (hnn1 : ∀ (i : Nat) (h : i < arr1.val.length), 0 ≤ (arr1.val[i]'h).val)
        (hnn2 : ∀ (i : Nat) (h : i < arr2.val.length), 0 ≤ (arr2.val[i]'h).val)
        (hcnt : ∀ v : Int, cnt v (arrList arr1) = cnt v (arrList arr2)), ∀ r1 r2 : Aeneas.Std.alloc.vec.Vec Std.I64,
          sort_by_bits arr1 = ok r1 → sort_by_bits arr2 = ok r2 → r1 = r2) := by
    sorry

  /-- Whenever the function returns a result r, for every integer v, v occurs in r if and only if v occurs in arr, where v occurs in a sequence s if there exists an index k with 0 <= k < len(s) and s[k] = v.
    Preconditions: len(arr) >= 1 and, for every i with 0 <= i < len(arr), arr[i] >= 0. -/
  theorem spec_11 (arr : Slice Std.I64) (hlen : 1 ≤ arr.val.length)
      (hnn : ∀ (i : Nat) (h : i < arr.val.length), 0 ≤ (arr.val[i]'h).val) :
      ∀ r : Aeneas.Std.alloc.vec.Vec Std.I64,
        sort_by_bits arr = ok r → ∀ v : Int, occurs v (vecList r) ↔ occurs v (arrList arr) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (arr : Slice Std.I64) (hlen : 1 ≤ arr.val.length)
        (hnn : ∀ (i : Nat) (h : i < arr.val.length), 0 ≤ (arr.val[i]'h).val), ∀ r : Aeneas.Std.alloc.vec.Vec Std.I64,
          sort_by_bits arr = ok r → ∀ v : Int, occurs v (vecList r) ↔ occurs v (arrList arr)) := by
    sorry

  /-- Whenever the function returns a result r, for every integer v, the set of indices k with 0 <= k < len(r) and r[k] = v is a contiguous interval of indices: if 0 <= i < j < k < len(r), r[i] = v, and r[k] = v, then r[j] = v.
    Preconditions: len(arr) >= 1 and, for every i with 0 <= i < len(arr), arr[i] >= 0. -/
  theorem spec_12 (arr : Slice Std.I64) (hlen : 1 ≤ arr.val.length)
      (hnn : ∀ (i : Nat) (h : i < arr.val.length), 0 ≤ (arr.val[i]'h).val) :
      ∀ r : Aeneas.Std.alloc.vec.Vec Std.I64,
        sort_by_bits arr = ok r →
          ∀ (v : Int) (i j k : Nat) (hij : i < j) (hjk : j < k)
            (hk : k < (vecList r).length),
            (vecList r)[i]'(Nat.lt_trans hij (Nat.lt_trans hjk hk)) = v →
              (vecList r)[k]'hk = v → (vecList r)[j]'(Nat.lt_trans hjk hk) = v := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (arr : Slice Std.I64) (hlen : 1 ≤ arr.val.length)
        (hnn : ∀ (i : Nat) (h : i < arr.val.length), 0 ≤ (arr.val[i]'h).val), ∀ r : Aeneas.Std.alloc.vec.Vec Std.I64,
          sort_by_bits arr = ok r →
            ∀ (v : Int) (i j k : Nat) (hij : i < j) (hjk : j < k)
              (hk : k < (vecList r).length),
              (vecList r)[i]'(Nat.lt_trans hij (Nat.lt_trans hjk hk)) = v →
                (vecList r)[k]'hk = v → (vecList r)[j]'(Nat.lt_trans hjk hk) = v) := by
    sorry

  end AegisSpec.SortByBits

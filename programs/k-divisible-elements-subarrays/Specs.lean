import Aegis.CountDistinct.Code.Funs

/-!
# Specifications of `Aegis.CountDistinct.count_distinct`

LeetCode problem `k-divisible-elements-subarrays`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CountDistinct

open Aegis.CountDistinct

def len (nums : Slice Std.I64) : Nat := nums.val.length

def vals (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

def elem (nums : Slice Std.I64) (i : Nat) : Int := (vals nums).getD i 0

def sub (nums : Slice Std.I64) (a b : Nat) : List Int := ((vals nums).drop a).take (b - a)

def divCount (nums : Slice Std.I64) (p : Int) (a b : Nat) : Nat :=
  (sub nums a b).countP (fun x => decide (p ∣ x))

def numDivisible (nums : Slice Std.I64) (p : Int) : Nat :=
  ((Finset.range (len nums)).filter (fun i => p ∣ elem nums i)).card

def distinctVals (nums : Slice Std.I64) : Finset Int :=
  (Finset.range (len nums)).image (elem nums)

def numDistinct (nums : Slice Std.I64) : Nat := (distinctVals nums).card

def divPairs (nums : Slice Std.I64) (k p : Std.I64) : Finset (Nat × Nat) :=
  ((Finset.range (len nums + 1)).product (Finset.range (len nums + 1))).filter
    (fun ab => ab.1 < ab.2 ∧ (divCount nums p.val ab.1 ab.2 : Int) ≤ k.val)

def numDivPairs (nums : Slice Std.I64) (k p : Std.I64) : Nat := (divPairs nums k p).card

def D (nums : Slice Std.I64) (k p : Std.I64) : Finset (List Int) :=
  (divPairs nums k p).image (fun ab => sub nums ab.1 ab.2)

def shortPairs (nums : Slice Std.I64) (k : Std.I64) : Finset (Nat × Nat) :=
  ((Finset.range (len nums + 1)).product (Finset.range (len nums + 1))).filter
    (fun ab => ab.1 < ab.2 ∧ ((ab.2 - ab.1 : Nat) : Int) ≤ k.val)

def E (nums : Slice Std.I64) (k : Std.I64) : Finset (List Int) :=
  (shortPairs nums k).image (fun ab => sub nums ab.1 ab.2)

def allPairs (nums : Slice Std.I64) : Finset (Nat × Nat) :=
  ((Finset.range (len nums + 1)).product (Finset.range (len nums + 1))).filter
    (fun ab => ab.1 < ab.2)

def U (nums : Slice Std.I64) : Finset (List Int) :=
  (allPairs nums).image (fun ab => sub nums ab.1 ab.2)

def listNOfList {α : Type} : (l : List α) → Aeneas.Data.ListN.ListN α l.length
  | [] => .nil
  | a :: l => .cons a (listNOfList l)

theorem listNOfList_toList {α : Type} : ∀ l : List α, (listNOfList l).toList = l
  | [] => rfl
  | a :: l => by
    rw [show (listNOfList (a :: l)).toList = a :: (listNOfList l).toList from rfl,
      listNOfList_toList l]

theorem ListN.length_toList {α : Type} {n : Nat} (l : Aeneas.Data.ListN.ListN α n) :
    l.toList.length = n := by
  induction l with
  | nil => rfl
  | cons _ _ ih => simp [Aeneas.Data.ListN.ListN.toList, ih]

theorem Slice.val_length {α : Type} (s : Slice α) : s.val.length = s.leng :=
  ListN.length_toList s.list

def mkSlice (l : List Std.I64) (h : l.length ≤ Usize.max) : Slice Std.I64 :=
  Slice.mk l.length (listNOfList l) h

theorem mkSlice_val (l : List Std.I64) (h : l.length ≤ Usize.max) : (mkSlice l h).val = l := by
  simp only [mkSlice, Slice.val, listNOfList_toList]

def revSlice (nums : Slice Std.I64) : Slice Std.I64 :=
  mkSlice nums.val.reverse (by
    rw [List.length_reverse, Slice.val_length]
    exact nums.bound)

theorem vals_revSlice (nums : Slice Std.I64) :
    vals (revSlice nums) = (vals nums).reverse := by
  simp [vals, revSlice, mkSlice_val, List.map_reverse]

theorem len_eq_Slice_length (nums : Slice Std.I64) : len nums = Slice.length nums := by
  simp [len, Slice.length]

theorem len_revSlice (nums : Slice Std.I64) : len (revSlice nums) = len nums := by
  simp [len, revSlice, mkSlice_val]

/-- Let n = len(nums). For 0 <= a < b <= n, write nums[a..b) for the sequence (nums[a], nums[a+1], ..., nums[b-1]), and let div(a,b) be the number of indices i with a <= i < b such that p divides nums[i]. Let D = { s | there exist integers a,b with 0 <= a < b <= n, s = nums[a..b), and div(a,b) <= k }. Whenever count_distinct(nums,k,p) returns a result r, r is the cardinality of D.
  Preconditions: 1 <= len(nums) <= 200; 1 <= k <= len(nums); 1 <= p <= 200; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 200. -/
theorem spec_1 (nums : Slice Std.I64) (k p : Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 200)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (len nums : Int))
    (hp1 : 1 ≤ p.val) (hp2 : p.val ≤ 200)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 200) :
    ∀ r, count_distinct nums k p = ok r → r.val = ((D nums k p).card : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (k p : Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 200)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (len nums : Int))
    (hp1 : 1 ≤ p.val) (hp2 : p.val ≤ 200)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 200), ∀ r, count_distinct nums k p = ok r → r.val = ((D nums k p).card : Int)) := by
  sorry

/-- For every input satisfying the preconditions, count_distinct(nums,k,p) returns a result r; it does not fail, panic, overflow, or get stuck.
  Preconditions: 1 <= len(nums) <= 200; 1 <= k <= len(nums); 1 <= p <= 200; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 200. -/
theorem spec_2 (nums : Slice Std.I64) (k p : Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 200)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (len nums : Int))
    (hp1 : 1 ≤ p.val) (hp2 : p.val ≤ 200)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 200) :
    ∃ r, count_distinct nums k p = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (k p : Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 200)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (len nums : Int))
    (hp1 : 1 ≤ p.val) (hp2 : p.val ≤ 200)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 200), ∃ r, count_distinct nums k p = ok r) := by
  sorry

/-- Let n = len(nums). Whenever count_distinct(nums,k,p) returns a result r, r <= n*(n+1)/2.
  Preconditions: 1 <= len(nums) <= 200; 1 <= k <= len(nums); 1 <= p <= 200; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 200. -/
theorem spec_3 (nums : Slice Std.I64) (k p : Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 200)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (len nums : Int))
    (hp1 : 1 ≤ p.val) (hp2 : p.val ≤ 200)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 200) :
    ∀ r, count_distinct nums k p = ok r → r.val ≤ ((len nums * (len nums + 1) / 2 : Nat) : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (k p : Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 200)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (len nums : Int))
    (hp1 : 1 ≤ p.val) (hp2 : p.val ≤ 200)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 200), ∀ r, count_distinct nums k p = ok r → r.val ≤ ((len nums * (len nums + 1) / 2 : Nat) : Int)) := by
  sorry

/-- Let m = |{ nums[i] | 0 <= i < len(nums) }| be the number of distinct values appearing in nums. Whenever count_distinct(nums,k,p) returns a result r, r >= m.
  Preconditions: 1 <= len(nums) <= 200; 1 <= k <= len(nums); 1 <= p <= 200; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 200. -/
theorem spec_4 (nums : Slice Std.I64) (k p : Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 200)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (len nums : Int))
    (hp1 : 1 ≤ p.val) (hp2 : p.val ≤ 200)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 200) :
    ∀ r, count_distinct nums k p = ok r → (numDistinct nums : Int) ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (k p : Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 200)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (len nums : Int))
    (hp1 : 1 ≤ p.val) (hp2 : p.val ≤ 200)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 200), ∀ r, count_distinct nums k p = ok r → (numDistinct nums : Int) ≤ r.val) := by
  sorry

/-- Let n = len(nums). Let div(a,b) be the number of i with a <= i < b such that p divides nums[i]. Let A be the number of pairs (a,b) with 0 <= a < b <= n and div(a,b) <= k. Whenever count_distinct(nums,k,p) returns a result r, r <= A.
  Preconditions: 1 <= len(nums) <= 200; 1 <= k <= len(nums); 1 <= p <= 200; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 200. -/
theorem spec_5 (nums : Slice Std.I64) (k p : Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 200)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (len nums : Int))
    (hp1 : 1 ≤ p.val) (hp2 : p.val ≤ 200)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 200) :
    ∀ r, count_distinct nums k p = ok r → r.val ≤ ((numDivPairs nums k p : Nat) : Int) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (k p : Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 200)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (len nums : Int))
    (hp1 : 1 ≤ p.val) (hp2 : p.val ≤ 200)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 200), ∀ r, count_distinct nums k p = ok r → r.val ≤ ((numDivPairs nums k p : Nat) : Int)) := by
  sorry

/-- Whenever count_distinct(nums,k,p) returns a result r, r = 1.
  Preconditions: 1 <= len(nums) <= 200; 1 <= k <= len(nums); 1 <= p <= 200; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 200; len(nums) = 1. -/
theorem spec_6 (nums : Slice Std.I64) (k p : Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 200)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (len nums : Int))
    (hp1 : 1 ≤ p.val) (hp2 : p.val ≤ 200)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 200)
    (hlen : len nums = 1) :
    ∀ r, count_distinct nums k p = ok r → r.val = 1 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (k p : Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 200)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (len nums : Int))
    (hp1 : 1 ≤ p.val) (hp2 : p.val ≤ 200)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 200)
    (hlen : len nums = 1), ∀ r, count_distinct nums k p = ok r → r.val = 1) := by
  sorry

/-- Let E be the set of sequences s for which there exist integers a,b with 0 <= a < b <= len(nums), b-a <= k, and s = (nums[a], ..., nums[b-1]). Whenever count_distinct(nums,k,p) returns a result r, r is the cardinality of E.
  Preconditions: 1 <= len(nums) <= 200; 1 <= k <= len(nums); 1 <= p <= 200; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 200; for every i with 0 <= i < len(nums), p divides nums[i]. -/
theorem spec_7 (nums : Slice Std.I64) (k p : Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 200)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (len nums : Int))
    (hp1 : 1 ≤ p.val) (hp2 : p.val ≤ 200)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 200)
    (hdiv : ∀ i, i < len nums → p.val ∣ elem nums i) :
    ∀ r, count_distinct nums k p = ok r → r.val = ((E nums k).card : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (k p : Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 200)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (len nums : Int))
    (hp1 : 1 ≤ p.val) (hp2 : p.val ≤ 200)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 200)
    (hdiv : ∀ i, i < len nums → p.val ∣ elem nums i), ∀ r, count_distinct nums k p = ok r → r.val = ((E nums k).card : Int)) := by
  sorry

/-- Let T be the set of sequences s for which there exist integers a,b with 0 <= a < b <= len(nums) and s = (nums[a], ..., nums[b-1]). Whenever count_distinct(nums,k,p) returns a result r, r is the cardinality of T.
  Preconditions: 1 <= len(nums) <= 200; 1 <= k <= len(nums); 1 <= p <= 200; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 200; the number of indices i with 0 <= i < len(nums) for which p divides nums[i] is at most k. -/
theorem spec_8 (nums : Slice Std.I64) (k p : Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 200)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (len nums : Int))
    (hp1 : 1 ≤ p.val) (hp2 : p.val ≤ 200)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 200)
    (hcnt : (numDivisible nums p.val : Int) ≤ k.val) :
    ∀ r, count_distinct nums k p = ok r → r.val = ((U nums).card : Int) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (k p : Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 200)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (len nums : Int))
    (hp1 : 1 ≤ p.val) (hp2 : p.val ≤ 200)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 200)
    (hcnt : (numDivisible nums p.val : Int) ≤ k.val), ∀ r, count_distinct nums k p = ok r → r.val = ((U nums).card : Int)) := by
  sorry

/-- Whenever count_distinct(nums,k1,p) returns a result r1 and count_distinct(nums,k2,p) returns a result r2, r1 <= r2.
  Preconditions: 1 <= len(nums) <= 200; 1 <= p <= 200; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 200; 1 <= k1 <= k2 <= len(nums). -/
theorem spec_9 (nums : Slice Std.I64) (k1 k2 p : Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 200)
    (hk1 : 1 ≤ k1.val) (hk12 : k1.val ≤ k2.val) (hk2 : k2.val ≤ (len nums : Int))
    (hp1 : 1 ≤ p.val) (hp2 : p.val ≤ 200)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 200) :
    ∀ r1, count_distinct nums k1 p = ok r1 →
    ∀ r2, count_distinct nums k2 p = ok r2 → r1.val ≤ r2.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (k1 k2 p : Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 200)
    (hk1 : 1 ≤ k1.val) (hk12 : k1.val ≤ k2.val) (hk2 : k2.val ≤ (len nums : Int))
    (hp1 : 1 ≤ p.val) (hp2 : p.val ≤ 200)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 200), ∀ r1, count_distinct nums k1 p = ok r1 →
    ∀ r2, count_distinct nums k2 p = ok r2 → r1.val ≤ r2.val) := by
  sorry

/-- Whenever count_distinct(nums,k,p1) returns a result r1 and count_distinct(nums,k,p2) returns a result r2, r1 <= r2.
  Preconditions: 1 <= len(nums) <= 200; 1 <= k <= len(nums); 1 <= p1 <= 200; 1 <= p2 <= 200; p1 divides p2; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 200. -/
theorem spec_10 (nums : Slice Std.I64) (k p1 p2 : Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 200)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (len nums : Int))
    (hp1a : 1 ≤ p1.val) (hp1b : p1.val ≤ 200)
    (hp2a : 1 ≤ p2.val) (hp2b : p2.val ≤ 200)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 200)
    (hpp : p1.val ∣ p2.val) :
    ∀ r1, count_distinct nums k p1 = ok r1 →
    ∀ r2, count_distinct nums k p2 = ok r2 → r1.val ≤ r2.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64) (k p1 p2 : Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 200)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (len nums : Int))
    (hp1a : 1 ≤ p1.val) (hp1b : p1.val ≤ 200)
    (hp2a : 1 ≤ p2.val) (hp2b : p2.val ≤ 200)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 200)
    (hpp : p1.val ∣ p2.val), ∀ r1, count_distinct nums k p1 = ok r1 →
    ∀ r2, count_distinct nums k p2 = ok r2 → r1.val ≤ r2.val) := by
  sorry

/-- Let rev(nums) be the sequence (nums[len(nums)-1], nums[len(nums)-2], ..., nums[0]). Whenever count_distinct(nums,k,p) returns a result r and count_distinct(rev(nums),k,p) returns a result r', r = r'.
  Preconditions: 1 <= len(nums) <= 200; 1 <= k <= len(nums); 1 <= p <= 200; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 200. -/
theorem spec_11 (nums : Slice Std.I64) (k p : Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 200)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (len nums : Int))
    (hp1 : 1 ≤ p.val) (hp2 : p.val ≤ 200)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 200) :
    ∀ r, count_distinct nums k p = ok r →
    ∀ r', count_distinct (revSlice nums) k p = ok r' → r.val = r'.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (k p : Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 200)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (len nums : Int))
    (hp1 : 1 ≤ p.val) (hp2 : p.val ≤ 200)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 200), ∀ r, count_distinct nums k p = ok r →
    ∀ r', count_distinct (revSlice nums) k p = ok r' → r.val = r'.val) := by
  sorry

/-- Whenever count_distinct(nums,k,p) returns a result r and count_distinct(nums,k,q) returns a result r', r = r'.
  Preconditions: 1 <= len(nums) <= 200; 1 <= k <= len(nums); 1 <= p <= 200; 1 <= q <= 200; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 200; for every i with 0 <= i < len(nums), p divides nums[i] iff q divides nums[i]. -/
theorem spec_12 (nums : Slice Std.I64) (k p q : Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 200)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (len nums : Int))
    (hp1 : 1 ≤ p.val) (hp2 : p.val ≤ 200)
    (hq1 : 1 ≤ q.val) (hq2 : q.val ≤ 200)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 200)
    (hdiv : ∀ i, i < len nums →
      (p.val ∣ elem nums i ↔ q.val ∣ elem nums i)) :
    ∀ r, count_distinct nums k p = ok r →
    ∀ r', count_distinct nums k q = ok r' → r.val = r'.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64) (k p q : Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 200)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (len nums : Int))
    (hp1 : 1 ≤ p.val) (hp2 : p.val ≤ 200)
    (hq1 : 1 ≤ q.val) (hq2 : q.val ≤ 200)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 200)
    (hdiv : ∀ i, i < len nums →
      (p.val ∣ elem nums i ↔ q.val ∣ elem nums i)), ∀ r, count_distinct nums k p = ok r →
    ∀ r', count_distinct nums k q = ok r' → r.val = r'.val) := by
  sorry

/-- Whenever count_distinct(nums,k,p) returns a result r and count_distinct(nums',k,p) returns a result r', r = r'.
  Preconditions: 1 <= len(nums) <= 200; 1 <= k <= len(nums); 1 <= p <= 200; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 200; nums' is an array with len(nums') = len(nums) and 1 <= nums'[i] <= 200 for every i; for all i,j with 0 <= i,j < len(nums), nums[i] = nums[j] iff nums'[i] = nums'[j]; for all i with 0 <= i < len(nums), p divides nums[i] iff p divides nums'[i]. -/
theorem spec_13 (nums nums' : Slice Std.I64) (k p : Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 200)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (len nums : Int))
    (hp1 : 1 ≤ p.val) (hp2 : p.val ≤ 200)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 200)
    (hlen' : len nums' = len nums)
    (hval' : ∀ i, i < len nums' → 1 ≤ elem nums' i ∧ elem nums' i ≤ 200)
    (heq : ∀ i j, i < len nums → j < len nums →
      (elem nums i = elem nums j ↔ elem nums' i = elem nums' j))
    (hdiv : ∀ i, i < len nums →
      (p.val ∣ elem nums i ↔ p.val ∣ elem nums' i)) :
    ∀ r, count_distinct nums k p = ok r →
    ∀ r', count_distinct nums' k p = ok r' → r.val = r'.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (k p : Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 200)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (len nums : Int))
    (hp1 : 1 ≤ p.val) (hp2 : p.val ≤ 200)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 200)
    (hlen' : len nums' = len nums)
    (hval' : ∀ i, i < len nums' → 1 ≤ elem nums' i ∧ elem nums' i ≤ 200)
    (heq : ∀ i j, i < len nums → j < len nums →
      (elem nums i = elem nums j ↔ elem nums' i = elem nums' j))
    (hdiv : ∀ i, i < len nums →
      (p.val ∣ elem nums i ↔ p.val ∣ elem nums' i)), ∀ r, count_distinct nums k p = ok r →
    ∀ r', count_distinct nums' k p = ok r' → r.val = r'.val) := by
  sorry

/-- Let U be the set of all sequences s for which there exist integers a,b with 0 <= a < b <= len(nums) and s = (nums[a], ..., nums[b-1]). Whenever count_distinct(nums,k,p) returns a result r, r <= |U|.
  Preconditions: 1 <= len(nums) <= 200; 1 <= k <= len(nums); 1 <= p <= 200; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 200. -/
theorem spec_14 (nums : Slice Std.I64) (k p : Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 200)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (len nums : Int))
    (hp1 : 1 ≤ p.val) (hp2 : p.val ≤ 200)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 200) :
    ∀ r, count_distinct nums k p = ok r → r.val ≤ ((U nums).card : Int) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums : Slice Std.I64) (k p : Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 200)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (len nums : Int))
    (hp1 : 1 ≤ p.val) (hp2 : p.val ≤ 200)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 200), ∀ r, count_distinct nums k p = ok r → r.val ≤ ((U nums).card : Int)) := by
  sorry

/-- Let n = len(nums). For 0 <= a < b <= n, let div(a,b) be the number of indices i with a <= i < b such that p divides nums[i]. Let A be the number of pairs (a,b) with 0 <= a < b <= n and div(a,b) <= k. Whenever count_distinct(nums,k,p) returns a result r, r = A.
  Preconditions: 1 <= len(nums) <= 200; 1 <= k <= len(nums); 1 <= p <= 200; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 200; for all i,j with 0 <= i < j < len(nums), nums[i] != nums[j]. -/
theorem spec_15 (nums : Slice Std.I64) (k p : Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 200)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (len nums : Int))
    (hp1 : 1 ≤ p.val) (hp2 : p.val ≤ 200)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 200)
    (hnd : ∀ i j, i < j → j < len nums → elem nums i ≠ elem nums j) :
    ∀ r, count_distinct nums k p = ok r → r.val = ((numDivPairs nums k p : Nat) : Int) := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (nums : Slice Std.I64) (k p : Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 200)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (len nums : Int))
    (hp1 : 1 ≤ p.val) (hp2 : p.val ≤ 200)
    (hval : ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 200)
    (hnd : ∀ i j, i < j → j < len nums → elem nums i ≠ elem nums j), ∀ r, count_distinct nums k p = ok r → r.val = ((numDivPairs nums k p : Nat) : Int)) := by
  sorry

end AegisSpec.CountDistinct

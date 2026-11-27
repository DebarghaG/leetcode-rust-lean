import Aegis.BalancedString.Code.Funs

/-!
# Specifications of `Aegis.BalancedString.balanced_string`

LeetCode problem `replace-the-substring-for-balanced-string`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.BalancedString

namespace AegisSpec.BalancedString

def allowedBytes : List Nat := [81, 87, 69, 82]

def listCountIn (l : List Std.U8) (x a b : Nat) : Nat :=
  ((l.drop a).take (b - a)).countP (fun c => decide (c.val = x))

def byteCount (s : Slice Std.U8) (x a b : Nat) : Nat :=
  listCountIn s.val x a b

def ExactCounts (l : List Std.U8) (T : Nat) : Prop :=
  ∀ x, x ∈ allowedBytes → listCountIn l x 0 l.length = T

def WindowOK (s : Slice Std.U8) (T l j : Nat) : Prop :=
  l ≤ j ∧ j ≤ s.val.length ∧
    ∀ x, x ∈ allowedBytes → byteCount s x 0 l + byteCount s x j s.val.length ≤ T

def excessTotal (l : List Std.U8) (T : Nat) : Int :=
  (allowedBytes.map (fun x => max 0 ((listCountIn l x 0 l.length : Int) - (T : Int)))).sum

def replaceRange (l : List Std.U8) (a b : Nat) (t : List Std.U8) : List Std.U8 :=
  l.take a ++ t ++ l.drop b

lemma val_length_le_usizeMax (s : Slice Std.U8) : s.val.length ≤ Usize.max := by
  simpa [Slice.val] using Slice.length_ineq s

def revSlice (s : Slice Std.U8) : Slice Std.U8 :=
  Slice.from s.val.reverse (by
    rw [List.length_reverse]
    exact val_length_le_usizeMax s)

def permuteSlice (pi : Std.U8 → Std.U8) (s : Slice Std.U8) : Slice Std.U8 :=
  Slice.from (s.val.map pi) (by
    rw [List.length_map]
    exact val_length_le_usizeMax s)

@[simp]
lemma revSlice_val (s : Slice Std.U8) : (revSlice s).val = s.val.reverse :=
  Slice.from_val _ _

@[simp]
lemma permuteSlice_val (pi : Std.U8 → Std.U8) (s : Slice Std.U8) :
    (permuteSlice pi s).val = s.val.map pi :=
  Slice.from_val _ _

/-- The function returns a result ans and ans is exactly the minimum integer L for which there exist integers l, j with 0 <= l <= j <= n, j - l = L, and for every x in {81,87,69,82}, if C_x(a,b) denotes the number of indices i with a <= i < b and s[i] = x, then C_x(0,l) + C_x(j,n) <= T. The minimum exists because (l,j) = (0,n) is always allowed.
  Preconditions: Let n = len(s). Assume 4 <= n <= 100000, n is divisible by 4, and for every i with 0 <= i < n, s[i] is one of the bytes 81 ('Q'), 87 ('W'), 69 ('E'), 82 ('R'). Let T = n/4, the exact integer target count for each allowed byte. -/
theorem spec_1 (s : Slice Std.U8)
    (hn_lo : 4 ≤ s.val.length) (hn_hi : s.val.length ≤ 100000)
    (hn_dvd : 4 ∣ s.val.length)
    (hbytes : ∀ c ∈ s.val, c.val ∈ allowedBytes) :
    ∃ ans : Std.I64, balanced_string s = ok ans ∧
      (∃ l j : Nat, WindowOK s (s.val.length / 4) l j ∧ ans.val = (j : Int) - (l : Int)) ∧
      (∀ L : Int,
        (∃ l j : Nat, WindowOK s (s.val.length / 4) l j ∧ (j : Int) - (l : Int) = L) →
        ans.val ≤ L) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hn_lo : 4 ≤ s.val.length) (hn_hi : s.val.length ≤ 100000)
    (hn_dvd : 4 ∣ s.val.length)
    (hbytes : ∀ c ∈ s.val, c.val ∈ allowedBytes), ∃ ans : Std.I64, balanced_string s = ok ans ∧
      (∃ l j : Nat, WindowOK s (s.val.length / 4) l j ∧ ans.val = (j : Int) - (l : Int)) ∧
      (∀ L : Int,
        (∃ l j : Nat, WindowOK s (s.val.length / 4) l j ∧ (j : Int) - (l : Int) = L) →
        ans.val ≤ L)) := by
  sorry

/-- The function returns a result ans; it does not fail, panic, overflow, or access memory out of bounds for any input satisfying the preconditions.
  Preconditions: Let n = len(s). Assume 4 <= n <= 100000, n is divisible by 4, and every s[i] belongs to {81,87,69,82}. -/
theorem spec_2 (s : Slice Std.U8)
    (hn_lo : 4 ≤ s.val.length) (hn_hi : s.val.length ≤ 100000)
    (hn_dvd : 4 ∣ s.val.length)
    (hbytes : ∀ c ∈ s.val, c.val ∈ allowedBytes) :
    ∃ ans : Std.I64, balanced_string s = ok ans := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hn_lo : 4 ≤ s.val.length) (hn_hi : s.val.length ≤ 100000)
    (hn_dvd : 4 ∣ s.val.length)
    (hbytes : ∀ c ∈ s.val, c.val ∈ allowedBytes), ∃ ans : Std.I64, balanced_string s = ok ans) := by
  sorry

/-- Whenever the function returns a result ans, one has 0 <= ans <= 3 * (n / 4). Here n / 4 is the exact integer T because n is divisible by 4.
  Preconditions: Let n = len(s). Assume 4 <= n <= 100000, n is divisible by 4, and every s[i] belongs to {81,87,69,82}. -/
theorem spec_3 (s : Slice Std.U8)
    (hn_lo : 4 ≤ s.val.length) (hn_hi : s.val.length ≤ 100000)
    (hn_dvd : 4 ∣ s.val.length)
    (hbytes : ∀ c ∈ s.val, c.val ∈ allowedBytes)
    (ans : Std.I64) (hans : balanced_string s = ok ans) :
    0 ≤ ans.val ∧ ans.val ≤ (3 : Int) * ((s.val.length / 4 : Nat) : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hn_lo : 4 ≤ s.val.length) (hn_hi : s.val.length ≤ 100000)
    (hn_dvd : 4 ∣ s.val.length)
    (hbytes : ∀ c ∈ s.val, c.val ∈ allowedBytes)
    (ans : Std.I64) (hans : balanced_string s = ok ans), 0 ≤ ans.val ∧ ans.val ≤ (3 : Int) * ((s.val.length / 4 : Nat) : Int)) := by
  sorry

/-- Whenever the function returns a result ans, ans >= sum over x in {81,87,69,82} of max(0, C_x(0,n) - T).
  Preconditions: Let n = len(s). Assume 4 <= n <= 100000, n is divisible by 4, and every s[i] belongs to {81,87,69,82}. Let T = n/4 and let C_x(0,n) be the number of indices i with 0 <= i < n and s[i] = x. -/
theorem spec_4 (s : Slice Std.U8)
    (hn_lo : 4 ≤ s.val.length) (hn_hi : s.val.length ≤ 100000)
    (hn_dvd : 4 ∣ s.val.length)
    (hbytes : ∀ c ∈ s.val, c.val ∈ allowedBytes)
    (ans : Std.I64) (hans : balanced_string s = ok ans) :
    excessTotal s.val (s.val.length / 4) ≤ ans.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hn_lo : 4 ≤ s.val.length) (hn_hi : s.val.length ≤ 100000)
    (hn_dvd : 4 ∣ s.val.length)
    (hbytes : ∀ c ∈ s.val, c.val ∈ allowedBytes)
    (ans : Std.I64) (hans : balanced_string s = ok ans), excessTotal s.val (s.val.length / 4) ≤ ans.val) := by
  sorry

/-- Whenever the function returns a result ans, ans = 0 if and only if for every x in {81,87,69,82}, the byte x occurs exactly T times in s.
  Preconditions: Let n = len(s). Assume 4 <= n <= 100000, n is divisible by 4, and every s[i] belongs to {81,87,69,82}. Let T = n/4. -/
theorem spec_5 (s : Slice Std.U8)
    (hn_lo : 4 ≤ s.val.length) (hn_hi : s.val.length ≤ 100000)
    (hn_dvd : 4 ∣ s.val.length)
    (hbytes : ∀ c ∈ s.val, c.val ∈ allowedBytes)
    (ans : Std.I64) (hans : balanced_string s = ok ans) :
    (ans.val = 0 ↔ ExactCounts s.val (s.val.length / 4)) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hn_lo : 4 ≤ s.val.length) (hn_hi : s.val.length ≤ 100000)
    (hn_dvd : 4 ∣ s.val.length)
    (hbytes : ∀ c ∈ s.val, c.val ∈ allowedBytes)
    (ans : Std.I64) (hans : balanced_string s = ok ans), (ans.val = 0 ↔ ExactCounts s.val (s.val.length / 4))) := by
  sorry

/-- Whenever the function returns a result ans, there exist integers l and j with 0 <= l <= j <= n, j - l = ans, and for every x in {81,87,69,82}, C_x(0,l) + C_x(j,n) <= T.
  Preconditions: Let n = len(s). Assume 4 <= n <= 100000, n is divisible by 4, and every s[i] belongs to {81,87,69,82}. Let T = n/4 and define C_x(a,b) as the number of indices i with a <= i < b and s[i] = x. -/
theorem spec_6 (s : Slice Std.U8)
    (hn_lo : 4 ≤ s.val.length) (hn_hi : s.val.length ≤ 100000)
    (hn_dvd : 4 ∣ s.val.length)
    (hbytes : ∀ c ∈ s.val, c.val ∈ allowedBytes)
    (ans : Std.I64) (hans : balanced_string s = ok ans) :
    ∃ l j : Nat, WindowOK s (s.val.length / 4) l j ∧ ans.val = (j : Int) - (l : Int) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hn_lo : 4 ≤ s.val.length) (hn_hi : s.val.length ≤ 100000)
    (hn_dvd : 4 ∣ s.val.length)
    (hbytes : ∀ c ∈ s.val, c.val ∈ allowedBytes)
    (ans : Std.I64) (hans : balanced_string s = ok ans), ∃ l j : Nat, WindowOK s (s.val.length / 4) l j ∧ ans.val = (j : Int) - (l : Int)) := by
  sorry

/-- Whenever the function returns a result ans, for every pair of integers l and j with 0 <= l <= j <= n, if C_x(0,l) + C_x(j,n) <= T for every x in {81,87,69,82}, then j - l >= ans.
  Preconditions: Let n = len(s). Assume 4 <= n <= 100000, n is divisible by 4, and every s[i] belongs to {81,87,69,82}. Let T = n/4 and define C_x(a,b) as the number of indices i with a <= i < b and s[i] = x. -/
theorem spec_7 (s : Slice Std.U8)
    (hn_lo : 4 ≤ s.val.length) (hn_hi : s.val.length ≤ 100000)
    (hn_dvd : 4 ∣ s.val.length)
    (hbytes : ∀ c ∈ s.val, c.val ∈ allowedBytes)
    (ans : Std.I64) (hans : balanced_string s = ok ans) :
    ∀ l j : Nat, WindowOK s (s.val.length / 4) l j → ans.val ≤ (j : Int) - (l : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hn_lo : 4 ≤ s.val.length) (hn_hi : s.val.length ≤ 100000)
    (hn_dvd : 4 ∣ s.val.length)
    (hbytes : ∀ c ∈ s.val, c.val ∈ allowedBytes)
    (ans : Std.I64) (hans : balanced_string s = ok ans), ∀ l j : Nat, WindowOK s (s.val.length / 4) l j → ans.val ≤ (j : Int) - (l : Int)) := by
  sorry

/-- Whenever the function returns a result ans, there exist integers l and j with 0 <= l <= j <= n, j - l = ans, and a byte array t of length ans whose every entry belongs to {81,87,69,82}, such that replacing s[l..j) by t yields a byte array s' of length n in which each byte in {81,87,69,82} occurs exactly T times.
  Preconditions: Let n = len(s). Assume 4 <= n <= 100000, n is divisible by 4, and every s[i] belongs to {81,87,69,82}. Let T = n/4. -/
theorem spec_8 (s : Slice Std.U8)
    (hn_lo : 4 ≤ s.val.length) (hn_hi : s.val.length ≤ 100000)
    (hn_dvd : 4 ∣ s.val.length)
    (hbytes : ∀ c ∈ s.val, c.val ∈ allowedBytes)
    (ans : Std.I64) (hans : balanced_string s = ok ans) :
    ∃ (l j : Nat) (t : List Std.U8),
      l ≤ j ∧ j ≤ s.val.length ∧ (j : Int) - (l : Int) = ans.val ∧
      (t.length : Int) = ans.val ∧
      (∀ c ∈ t, c.val ∈ allowedBytes) ∧
      ∃ s' : List Std.U8,
        s' = replaceRange s.val l j t ∧ s'.length = s.val.length ∧
          ExactCounts s' (s.val.length / 4) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hn_lo : 4 ≤ s.val.length) (hn_hi : s.val.length ≤ 100000)
    (hn_dvd : 4 ∣ s.val.length)
    (hbytes : ∀ c ∈ s.val, c.val ∈ allowedBytes)
    (ans : Std.I64) (hans : balanced_string s = ok ans), ∃ (l j : Nat) (t : List Std.U8),
      l ≤ j ∧ j ≤ s.val.length ∧ (j : Int) - (l : Int) = ans.val ∧
      (t.length : Int) = ans.val ∧
      (∀ c ∈ t, c.val ∈ allowedBytes) ∧
      ∃ s' : List Std.U8,
        s' = replaceRange s.val l j t ∧ s'.length = s.val.length ∧
          ExactCounts s' (s.val.length / 4)) := by
  sorry

/-- Whenever the function returns a result ans on input s, the same function returns the same result ans on input rev(s).
  Preconditions: Let n = len(s). Assume 4 <= n <= 100000, n is divisible by 4, and every s[i] belongs to {81,87,69,82}. Let rev(s) be the slice of length n with rev(s)[i] = s[n-1-i] for 0 <= i < n; rev(s) also satisfies the preconditions. -/
theorem spec_9 (s : Slice Std.U8)
    (hn_lo : 4 ≤ s.val.length) (hn_hi : s.val.length ≤ 100000)
    (hn_dvd : 4 ∣ s.val.length)
    (hbytes : ∀ c ∈ s.val, c.val ∈ allowedBytes)
    (ans : Std.I64) (hans : balanced_string s = ok ans) :
    balanced_string (revSlice s) = ok ans := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hn_lo : 4 ≤ s.val.length) (hn_hi : s.val.length ≤ 100000)
    (hn_dvd : 4 ∣ s.val.length)
    (hbytes : ∀ c ∈ s.val, c.val ∈ allowedBytes)
    (ans : Std.I64) (hans : balanced_string s = ok ans), balanced_string (revSlice s) = ok ans) := by
  sorry

/-- Whenever the function returns a result ans on input s, the same function returns the same result ans on input pi(s).
  Preconditions: Let n = len(s). Assume 4 <= n <= 100000, n is divisible by 4, and every s[i] belongs to {81,87,69,82}. Let pi be any bijection from {81,87,69,82} to itself, and let pi(s) be the slice of length n with pi(s)[i] = pi(s[i]) for 0 <= i < n; pi(s) also satisfies the preconditions. -/
theorem spec_10 (s : Slice Std.U8)
    (hn_lo : 4 ≤ s.val.length) (hn_hi : s.val.length ≤ 100000)
    (hn_dvd : 4 ∣ s.val.length)
    (hbytes : ∀ c ∈ s.val, c.val ∈ allowedBytes)
    (pi : Std.U8 → Std.U8)
    (hpi_mem : ∀ c : Std.U8, c.val ∈ allowedBytes → (pi c).val ∈ allowedBytes)
    (hpi_inj : ∀ c d : Std.U8, c.val ∈ allowedBytes → d.val ∈ allowedBytes →
      pi c = pi d → c = d)
    (hpi_surj : ∀ d : Std.U8, d.val ∈ allowedBytes → ∃ c : Std.U8, c.val ∈ allowedBytes ∧ pi c = d)
    (ans : Std.I64) (hans : balanced_string s = ok ans) :
    balanced_string (permuteSlice pi s) = ok ans := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hn_lo : 4 ≤ s.val.length) (hn_hi : s.val.length ≤ 100000)
    (hn_dvd : 4 ∣ s.val.length)
    (hbytes : ∀ c ∈ s.val, c.val ∈ allowedBytes)
    (pi : Std.U8 → Std.U8)
    (hpi_mem : ∀ c : Std.U8, c.val ∈ allowedBytes → (pi c).val ∈ allowedBytes)
    (hpi_inj : ∀ c d : Std.U8, c.val ∈ allowedBytes → d.val ∈ allowedBytes →
      pi c = pi d → c = d)
    (hpi_surj : ∀ d : Std.U8, d.val ∈ allowedBytes → ∃ c : Std.U8, c.val ∈ allowedBytes ∧ pi c = d)
    (ans : Std.I64) (hans : balanced_string s = ok ans), balanced_string (permuteSlice pi s) = ok ans) := by
  sorry

end AegisSpec.BalancedString

import Aegis.CountBalancedPermutations.Code.Funs

/-!
# Specifications of `Aegis.CountBalancedPermutations.count_balanced_permutations`

LeetCode problem `count-number-of-balanced-permutations`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CountBalancedPermutations

  def modulus : ℕ := 1000000007

  def modulusInt : ℤ := 1000000007

  def digitOf (b : Aeneas.Std.U8) : ℕ := b.val - 48

  def digits (num : Aeneas.Std.Slice Aeneas.Std.U8) : List ℕ := num.val.map digitOf

  def nthDigit (num : Aeneas.Std.Slice Aeneas.Std.U8) (i : ℕ) : ℕ :=
    digitOf (num.val.getD i default)

  def AllDigits (num : Aeneas.Std.Slice Aeneas.Std.U8) : Prop :=
    ∀ b ∈ num.val, 48 ≤ b.val ∧ b.val ≤ 57

  def totalDigitSum (num : Aeneas.Std.Slice Aeneas.Std.U8) : ℕ := (digits num).sum

  def evenIndexSum : List ℕ → ℕ
    | [] => 0
    | [a] => a
    | a :: _ :: t => a + evenIndexSum t

  def oddIndexSum : List ℕ → ℕ
    | [] => 0
    | [_] => 0
    | _ :: b :: t => b + oddIndexSum t

  def BalancedDigits (ds p : List ℕ) : Prop :=
    p.length = ds.length ∧
      (∀ d : Fin 10, p.count d.val = ds.count d.val) ∧
      evenIndexSum p = oddIndexSum p

  def IsBalancedPermutation (num : Aeneas.Std.Slice Aeneas.Std.U8) (p : List ℕ) : Prop :=
    BalancedDigits (digits num) p

  def IsSubMultiset (q ds : List ℕ) : Prop := ∀ d : ℕ, q.count d ≤ ds.count d

  def HasHalfSubset (ds : List ℕ) : Prop :=
    ∃ q : List ℕ, IsSubMultiset q ds ∧ q.length = (ds.length + 1) / 2 ∧ q.sum = ds.sum / 2

  def fnCount {n : ℕ} (f : Fin n → Fin 10) (d : Fin 10) : ℕ :=
    (Finset.univ.filter (fun i : Fin n => f i = d)).card

  def fnEvenSum {n : ℕ} (f : Fin n → Fin 10) : ℕ :=
    ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val % 2 = 0), (f i).val

  def fnOddSum {n : ℕ} (f : Fin n → Fin 10) : ℕ :=
    ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val % 2 = 1), (f i).val

  def BalancedFn (ds : List ℕ) (f : Fin ds.length → Fin 10) : Prop :=
    (∀ d : Fin 10, fnCount f d = ds.count d.val) ∧ fnEvenSum f = fnOddSum f

  noncomputable def balancedStrings (ds : List ℕ) : Finset (Fin ds.length → Fin 10) := by
    classical exact Finset.univ.filter (fun f => BalancedFn ds f)

  noncomputable def balancedCount (ds : List ℕ) : ℕ := (balancedStrings ds).card

  def permCount (ds : List ℕ) : ℕ :=
    ds.length.factorial / ∏ d ∈ Finset.range 10, (ds.count d).factorial

  /-- The function returns a result r such that 0 <= r < 10^9+7, and r is congruent modulo 10^9+7 to the number of distinct strings p of length n over the digits '0' to '9' satisfying: (a) for each d in {0,1,...,9}, the number of occurrences of digit d in p equals the number of occurrences of digit d in num; (b) the sum of the digit values at even indices of p (indices 0,2,4,...) equals the sum of the digit values at odd indices of p (indices 1,3,5,...). Equivalently, r is the unique integer in [0, 10^9+6] that is the remainder of that number when divided by 10^9+7.
    Preconditions: len(num) = n with 2 <= n <= 80; for every i with 0 <= i < n, num[i] is an ASCII byte in the range '0' (48) to '9' (57). -/
  theorem spec_1 (num : Aeneas.Std.Slice Aeneas.Std.U8) (n : ℕ)
      (hlen : num.val.length = n) (hn2 : 2 ≤ n) (hn80 : n ≤ 80) (hdig : AllDigits num) :
      ∃ r : Aeneas.Std.I64,
        Aegis.CountBalancedPermutations.count_balanced_permutations num =
          Aeneas.Std.Result.ok r ∧
        0 ≤ r.val ∧ r.val < modulusInt ∧
        Int.ModEq modulusInt r.val ((balancedCount (digits num) : ℕ) : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (num : Aeneas.Std.Slice Aeneas.Std.U8) (n : ℕ)
        (hlen : num.val.length = n) (hn2 : 2 ≤ n) (hn80 : n ≤ 80) (hdig : AllDigits num), ∃ r : Aeneas.Std.I64,
          Aegis.CountBalancedPermutations.count_balanced_permutations num =
            Aeneas.Std.Result.ok r ∧
          0 ≤ r.val ∧ r.val < modulusInt ∧
          Int.ModEq modulusInt r.val ((balancedCount (digits num) : ℕ) : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r is an integer satisfying 0 <= r <= 10^9+6.
    Preconditions: len(num) = n with 2 <= n <= 80; for every i with 0 <= i < n, num[i] is an ASCII byte in the range '0' (48) to '9' (57). -/
  theorem spec_2 (num : Aeneas.Std.Slice Aeneas.Std.U8) (n : ℕ)
      (hlen : num.val.length = n) (hn2 : 2 ≤ n) (hn80 : n ≤ 80) (hdig : AllDigits num)
      (r : Aeneas.Std.I64)
      (hres : Aegis.CountBalancedPermutations.count_balanced_permutations num =
        Aeneas.Std.Result.ok r) :
      0 ≤ r.val ∧ r.val ≤ modulusInt - 1 := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (num : Aeneas.Std.Slice Aeneas.Std.U8) (n : ℕ)
        (hlen : num.val.length = n) (hn2 : 2 ≤ n) (hn80 : n ≤ 80) (hdig : AllDigits num)
        (r : Aeneas.Std.I64)
        (hres : Aegis.CountBalancedPermutations.count_balanced_permutations num =
          Aeneas.Std.Result.ok r), 0 ≤ r.val ∧ r.val ≤ modulusInt - 1) := by
    sorry

  /-- The function returns a result r (i.e., it does not fail, panic, or overflow) for every input satisfying the preconditions.
    Preconditions: len(num) = n with 2 <= n <= 80; for every i with 0 <= i < n, num[i] is an ASCII byte in the range '0' (48) to '9' (57). -/
  theorem spec_3 (num : Aeneas.Std.Slice Aeneas.Std.U8) (n : ℕ)
      (hlen : num.val.length = n) (hn2 : 2 ≤ n) (hn80 : n ≤ 80) (hdig : AllDigits num) :
      ∃ r : Aeneas.Std.I64,
        Aegis.CountBalancedPermutations.count_balanced_permutations num =
          Aeneas.Std.Result.ok r := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (num : Aeneas.Std.Slice Aeneas.Std.U8) (n : ℕ)
        (hlen : num.val.length = n) (hn2 : 2 ≤ n) (hn80 : n ≤ 80) (hdig : AllDigits num), ∃ r : Aeneas.Std.I64,
          Aegis.CountBalancedPermutations.count_balanced_permutations num =
            Aeneas.Std.Result.ok r) := by
    sorry

  /-- Let S = sum_{i=0}^{n-1} digit(num[i]). If S is odd, then the function returns 0.
    Preconditions: len(num) = n with 2 <= n <= 80; for every i with 0 <= i < n, num[i] is an ASCII byte in the range '0' (48) to '9' (57). -/
  theorem spec_4 (num : Aeneas.Std.Slice Aeneas.Std.U8) (n : ℕ)
      (hlen : num.val.length = n) (hn2 : 2 ≤ n) (hn80 : n ≤ 80) (hdig : AllDigits num)
      (hodd : totalDigitSum num % 2 = 1) :
      Aegis.CountBalancedPermutations.count_balanced_permutations num =
        Aeneas.Std.Result.ok 0#i64 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (num : Aeneas.Std.Slice Aeneas.Std.U8) (n : ℕ)
        (hlen : num.val.length = n) (hn2 : 2 ≤ n) (hn80 : n ≤ 80) (hdig : AllDigits num)
        (hodd : totalDigitSum num % 2 = 1), Aegis.CountBalancedPermutations.count_balanced_permutations num =
          Aeneas.Std.Result.ok 0#i64) := by
    sorry

  /-- The function returns 1 if digit(num[0]) = digit(num[1]), and returns 0 otherwise.
    Preconditions: len(num) = 2; num[0] and num[1] are ASCII bytes in the range '0' (48) to '9' (57). -/
  theorem spec_5 (num : Aeneas.Std.Slice Aeneas.Std.U8)
      (hlen : num.val.length = 2) (hdig : AllDigits num) :
      (nthDigit num 0 = nthDigit num 1 →
        Aegis.CountBalancedPermutations.count_balanced_permutations num =
          Aeneas.Std.Result.ok 1#i64) ∧
      (nthDigit num 0 ≠ nthDigit num 1 →
        Aegis.CountBalancedPermutations.count_balanced_permutations num =
          Aeneas.Std.Result.ok 0#i64) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (num : Aeneas.Std.Slice Aeneas.Std.U8)
        (hlen : num.val.length = 2) (hdig : AllDigits num), (nthDigit num 0 = nthDigit num 1 →
          Aegis.CountBalancedPermutations.count_balanced_permutations num =
            Aeneas.Std.Result.ok 1#i64) ∧
        (nthDigit num 0 ≠ nthDigit num 1 →
          Aegis.CountBalancedPermutations.count_balanced_permutations num =
            Aeneas.Std.Result.ok 0#i64)) := by
    sorry

  /-- The function returns 1 if (n is even) or (d = 0); otherwise it returns 0.
    Preconditions: len(num) = n with 2 <= n <= 80; for every i with 0 <= i < n, num[i] is an ASCII byte in the range '0' (48) to '9' (57); there exists a digit d in {0,...,9} such that for every i with 0 <= i < n, digit(num[i]) = d. -/
  theorem spec_6 (num : Aeneas.Std.Slice Aeneas.Std.U8) (n d : ℕ)
      (hlen : num.val.length = n) (hn2 : 2 ≤ n) (hn80 : n ≤ 80) (hdig : AllDigits num)
      (hd : d ≤ 9) (huni : ∀ b ∈ num.val, digitOf b = d) :
      (n % 2 = 0 ∨ d = 0 →
        Aegis.CountBalancedPermutations.count_balanced_permutations num =
          Aeneas.Std.Result.ok 1#i64) ∧
      (n % 2 ≠ 0 → d ≠ 0 →
        Aegis.CountBalancedPermutations.count_balanced_permutations num =
          Aeneas.Std.Result.ok 0#i64) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (num : Aeneas.Std.Slice Aeneas.Std.U8) (n d : ℕ)
        (hlen : num.val.length = n) (hn2 : 2 ≤ n) (hn80 : n ≤ 80) (hdig : AllDigits num)
        (hd : d ≤ 9) (huni : ∀ b ∈ num.val, digitOf b = d), (n % 2 = 0 ∨ d = 0 →
          Aegis.CountBalancedPermutations.count_balanced_permutations num =
            Aeneas.Std.Result.ok 1#i64) ∧
        (n % 2 ≠ 0 → d ≠ 0 →
          Aegis.CountBalancedPermutations.count_balanced_permutations num =
            Aeneas.Std.Result.ok 0#i64)) := by
    sorry

  /-- For any two byte slices num1 and num2 satisfying the preconditions, if for every d in {0,...,9} the number of occurrences of digit d in num1 equals the number of occurrences of digit d in num2, then count_balanced_permutations(num1) = count_balanced_permutations(num2) (as results).
    Preconditions: num1 and num2 are byte slices each of length between 2 and 80, and every byte in both slices is an ASCII digit '0' (48) to '9' (57). -/
  theorem spec_7 (num1 num2 : Aeneas.Std.Slice Aeneas.Std.U8)
      (hlen1 : 2 ≤ num1.val.length) (hlen1' : num1.val.length ≤ 80)
      (hlen2 : 2 ≤ num2.val.length) (hlen2' : num2.val.length ≤ 80)
      (hdig1 : AllDigits num1) (hdig2 : AllDigits num2)
      (hcount : ∀ d : Fin 10, (digits num1).count d.val = (digits num2).count d.val) :
      Aegis.CountBalancedPermutations.count_balanced_permutations num1 =
        Aegis.CountBalancedPermutations.count_balanced_permutations num2 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (num1 num2 : Aeneas.Std.Slice Aeneas.Std.U8)
        (hlen1 : 2 ≤ num1.val.length) (hlen1' : num1.val.length ≤ 80)
        (hlen2 : 2 ≤ num2.val.length) (hlen2' : num2.val.length ≤ 80)
        (hdig1 : AllDigits num1) (hdig2 : AllDigits num2)
        (hcount : ∀ d : Fin 10, (digits num1).count d.val = (digits num2).count d.val), Aegis.CountBalancedPermutations.count_balanced_permutations num1 =
          Aegis.CountBalancedPermutations.count_balanced_permutations num2) := by
    sorry

  /-- Whenever the function returns a result r with r > 0, there exists at least one distinct permutation p of num that is balanced (i.e., p has the same digit counts as num and the sum of digits at even indices equals the sum at odd indices).
    Preconditions: len(num) = n with 2 <= n <= 80; for every i with 0 <= i < n, num[i] is an ASCII byte in the range '0' (48) to '9' (57). -/
  theorem spec_8 (num : Aeneas.Std.Slice Aeneas.Std.U8) (n : ℕ)
      (hlen : num.val.length = n) (hn2 : 2 ≤ n) (hn80 : n ≤ 80) (hdig : AllDigits num)
      (r : Aeneas.Std.I64)
      (hres : Aegis.CountBalancedPermutations.count_balanced_permutations num =
        Aeneas.Std.Result.ok r)
      (hpos : 0 < r.val) :
      ∃ p : List ℕ, IsBalancedPermutation num p := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (num : Aeneas.Std.Slice Aeneas.Std.U8) (n : ℕ)
        (hlen : num.val.length = n) (hn2 : 2 ≤ n) (hn80 : n ≤ 80) (hdig : AllDigits num)
        (r : Aeneas.Std.I64)
        (hres : Aegis.CountBalancedPermutations.count_balanced_permutations num =
          Aeneas.Std.Result.ok r)
        (hpos : 0 < r.val), ∃ p : List ℕ, IsBalancedPermutation num p) := by
    sorry

  /-- Let S = sum_{i=0}^{n-1} digit(num[i]). If S is even and there is no sub-multiset of the digits of num of size ceil(n/2) whose sum equals S/2, then the function returns 0.
    Preconditions: len(num) = n with 2 <= n <= 80; for every i with 0 <= i < n, num[i] is an ASCII byte in the range '0' (48) to '9' (57). -/
  theorem spec_9 (num : Aeneas.Std.Slice Aeneas.Std.U8) (n : ℕ)
      (hlen : num.val.length = n) (hn2 : 2 ≤ n) (hn80 : n ≤ 80) (hdig : AllDigits num)
      (heven : totalDigitSum num % 2 = 0) (hno : ¬ HasHalfSubset (digits num)) :
      Aegis.CountBalancedPermutations.count_balanced_permutations num =
        Aeneas.Std.Result.ok 0#i64 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (num : Aeneas.Std.Slice Aeneas.Std.U8) (n : ℕ)
        (hlen : num.val.length = n) (hn2 : 2 ≤ n) (hn80 : n ≤ 80) (hdig : AllDigits num)
        (heven : totalDigitSum num % 2 = 0) (hno : ¬ HasHalfSubset (digits num)), Aegis.CountBalancedPermutations.count_balanced_permutations num =
          Aeneas.Std.Result.ok 0#i64) := by
    sorry

  /-- Let num' be the byte slice obtained from num by replacing each byte corresponding to digit d with the byte corresponding to digit 9-d. Then the function returns the same result for num and num'.
    Preconditions: len(num) = n with 2 <= n <= 80; for every i with 0 <= i < n, num[i] is an ASCII byte in the range '0' (48) to '9' (57); n is even. -/
  theorem spec_10 (num num' : Aeneas.Std.Slice Aeneas.Std.U8) (n : ℕ)
      (hlen : num.val.length = n) (hlen' : num'.val.length = n)
      (hn2 : 2 ≤ n) (hn80 : n ≤ 80) (heven : n % 2 = 0)
      (hdig : AllDigits num) (hdig' : AllDigits num')
      (hcompl : ∀ i, i < n → nthDigit num' i = 9 - nthDigit num i) :
      Aegis.CountBalancedPermutations.count_balanced_permutations num' =
        Aegis.CountBalancedPermutations.count_balanced_permutations num := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (num num' : Aeneas.Std.Slice Aeneas.Std.U8) (n : ℕ)
        (hlen : num.val.length = n) (hlen' : num'.val.length = n)
        (hn2 : 2 ≤ n) (hn80 : n ≤ 80) (heven : n % 2 = 0)
        (hdig : AllDigits num) (hdig' : AllDigits num')
        (hcompl : ∀ i, i < n → nthDigit num' i = 9 - nthDigit num i), Aegis.CountBalancedPermutations.count_balanced_permutations num' =
          Aegis.CountBalancedPermutations.count_balanced_permutations num) := by
    sorry

  /-- If k is even, the function returns (C(ceil(n/2), k/2) * C(floor(n/2), k/2)) mod (10^9+7); if k is odd, the function returns 0. Here C(a,b) denotes the binomial coefficient a choose b, with C(a,b) = 0 if b < 0 or b > a.
    Preconditions: len(num) = n with 2 <= n <= 80; for every i with 0 <= i < n, num[i] is an ASCII byte in the range '0' (48) to '9' (57); the multiset of digits of num consists of k copies of a single digit d (with 1 <= d <= 9) and n-k copies of '0', where k >= 1. -/
  theorem spec_11 (num : Aeneas.Std.Slice Aeneas.Std.U8) (n k d : ℕ)
      (hlen : num.val.length = n) (hn2 : 2 ≤ n) (hn80 : n ≤ 80) (hdig : AllDigits num)
      (hd1 : 1 ≤ d) (hd9 : d ≤ 9) (hk1 : 1 ≤ k)
      (hcnt : (digits num).count d = k) (hzero : (digits num).count 0 = n - k)
      (hother : ∀ e : ℕ, e ≠ 0 → e ≠ d → (digits num).count e = 0) :
      (k % 2 = 0 →
        ∃ r : Aeneas.Std.I64,
          Aegis.CountBalancedPermutations.count_balanced_permutations num =
              Aeneas.Std.Result.ok r ∧
            r.val =
              (((Nat.choose ((n + 1) / 2) (k / 2) * Nat.choose (n / 2) (k / 2)) %
                  modulus : ℕ) : ℤ)) ∧
      (k % 2 = 1 →
        Aegis.CountBalancedPermutations.count_balanced_permutations num =
          Aeneas.Std.Result.ok 0#i64) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (num : Aeneas.Std.Slice Aeneas.Std.U8) (n k d : ℕ)
        (hlen : num.val.length = n) (hn2 : 2 ≤ n) (hn80 : n ≤ 80) (hdig : AllDigits num)
        (hd1 : 1 ≤ d) (hd9 : d ≤ 9) (hk1 : 1 ≤ k)
        (hcnt : (digits num).count d = k) (hzero : (digits num).count 0 = n - k)
        (hother : ∀ e : ℕ, e ≠ 0 → e ≠ d → (digits num).count e = 0), (k % 2 = 0 →
          ∃ r : Aeneas.Std.I64,
            Aegis.CountBalancedPermutations.count_balanced_permutations num =
                Aeneas.Std.Result.ok r ∧
              r.val =
                (((Nat.choose ((n + 1) / 2) (k / 2) * Nat.choose (n / 2) (k / 2)) %
                    modulus : ℕ) : ℤ)) ∧
        (k % 2 = 1 →
          Aegis.CountBalancedPermutations.count_balanced_permutations num =
            Aeneas.Std.Result.ok 0#i64)) := by
    sorry

  /-- The function returns the same result for num and num'.
    Preconditions: len(num) = n with 2 <= n <= 80; for every i with 0 <= i < n, num[i] is an ASCII byte in the range '0' (48) to '9' (57); let c be a positive integer such that for every digit d that appears in num, c*d <= 9; let num' be the byte slice obtained by replacing each byte corresponding to digit d with the byte corresponding to digit c*d (num' also satisfies the basic length and digit-range preconditions). -/
  theorem spec_12 (num num' : Aeneas.Std.Slice Aeneas.Std.U8) (n c : ℕ)
      (hlen : num.val.length = n) (hlen' : num'.val.length = n)
      (hn2 : 2 ≤ n) (hn80 : n ≤ 80)
      (hdig : AllDigits num) (hdig' : AllDigits num')
      (hc : 1 ≤ c) (hc9 : ∀ i, i < n → c * nthDigit num i ≤ 9)
      (hscale : ∀ i, i < n → nthDigit num' i = c * nthDigit num i) :
      Aegis.CountBalancedPermutations.count_balanced_permutations num' =
        Aegis.CountBalancedPermutations.count_balanced_permutations num := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (num num' : Aeneas.Std.Slice Aeneas.Std.U8) (n c : ℕ)
        (hlen : num.val.length = n) (hlen' : num'.val.length = n)
        (hn2 : 2 ≤ n) (hn80 : n ≤ 80)
        (hdig : AllDigits num) (hdig' : AllDigits num')
        (hc : 1 ≤ c) (hc9 : ∀ i, i < n → c * nthDigit num i ≤ 9)
        (hscale : ∀ i, i < n → nthDigit num' i = c * nthDigit num i), Aegis.CountBalancedPermutations.count_balanced_permutations num' =
          Aegis.CountBalancedPermutations.count_balanced_permutations num) := by
    sorry

  /-- Let T be the total number of distinct permutations of num, i.e., T = n! / (prod_{d=0}^9 c_d!), where c_d is the number of occurrences of digit d in num. If T < 10^9+7, then the returned value r satisfies r <= T.
    Preconditions: len(num) = n with 2 <= n <= 80; for every i with 0 <= i < n, num[i] is an ASCII byte in the range '0' (48) to '9' (57). -/
  theorem spec_13 (num : Aeneas.Std.Slice Aeneas.Std.U8) (n : ℕ)
      (hlen : num.val.length = n) (hn2 : 2 ≤ n) (hn80 : n ≤ 80) (hdig : AllDigits num)
      (hT : permCount (digits num) < modulus) (r : Aeneas.Std.I64)
      (hres : Aegis.CountBalancedPermutations.count_balanced_permutations num =
        Aeneas.Std.Result.ok r) :
      r.val ≤ ((permCount (digits num) : ℕ) : ℤ) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (num : Aeneas.Std.Slice Aeneas.Std.U8) (n : ℕ)
        (hlen : num.val.length = n) (hn2 : 2 ≤ n) (hn80 : n ≤ 80) (hdig : AllDigits num)
        (hT : permCount (digits num) < modulus) (r : Aeneas.Std.I64)
        (hres : Aegis.CountBalancedPermutations.count_balanced_permutations num =
          Aeneas.Std.Result.ok r), r.val ≤ ((permCount (digits num) : ℕ) : ℤ)) := by
    sorry

  end AegisSpec.CountBalancedPermutations

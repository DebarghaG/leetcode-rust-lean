import Aegis.NumberOfCombinations.Code.Funs

/-!
# Specifications of `Aegis.NumberOfCombinations.number_of_combinations`

LeetCode problem `number-of-ways-to-separate-numbers`. Each `spec_<n>` theorem states one property of the function.
-/

namespace AegisSpec.NumberOfCombinations

def modulus : Nat := 1000000007

def IsDigitByte (c : Aeneas.Std.U8) : Prop := 48 ≤ c.val ∧ c.val ≤ 57

def digitVal (c : Aeneas.Std.U8) : Nat := c.val - 48

def blockVal (b : List Aeneas.Std.U8) : Nat := b.foldl (fun acc c => acc * 10 + digitVal c) 0

def startsNonzeroB : List Aeneas.Std.U8 → Bool
  | [] => false
  | c :: _ => decide (1 ≤ digitVal c)

def StartsNonzero (b : List Aeneas.Std.U8) : Prop := startsNonzeroB b = true

def blockValsNondecreasingB (blocks : List (List Aeneas.Std.U8)) : Bool :=
  (blocks.zip blocks.tail).all (fun p => decide (blockVal p.1 ≤ blockVal p.2))

def BlockValsNondecreasing (blocks : List (List Aeneas.Std.U8)) : Prop :=
  blockValsNondecreasingB blocks = true

def isAdmissiblePartitionB (num : List Aeneas.Std.U8) (blocks : List (List Aeneas.Std.U8)) : Bool :=
  !blocks.isEmpty &&
    blocks.all (fun b => !b.isEmpty && startsNonzeroB b) &&
    blockValsNondecreasingB blocks &&
    decide (blocks.flatten = num)

def IsAdmissiblePartition (num : List Aeneas.Std.U8)
    (blocks : List (List Aeneas.Std.U8)) : Prop :=
  isAdmissiblePartitionB num blocks = true

def allBlockSplits : List Aeneas.Std.U8 → List (List (List Aeneas.Std.U8))
  | [] => [[]]
  | x :: xs =>
      (allBlockSplits xs).flatMap fun blocks =>
        match blocks with
        | [] => [[[x]]]
        | b :: rest => [(x :: b) :: rest, [x] :: b :: rest]

def numAdmissible (num : List Aeneas.Std.U8) : Nat :=
  ((allBlockSplits num).filter (isAdmissiblePartitionB num)).length

def IsIntegerPartition (n : Nat) (a : List Nat) : Prop :=
  (∀ x ∈ a, 1 ≤ x) ∧ a.Pairwise (· ≤ ·) ∧ a.sum = n

def numIntegerPartitions (n : Nat) : Nat :=
  ((Finset.univ : Finset (Fin n → Fin (n + 1))).filter
    (fun f => (Finset.univ.sum fun i : Fin n => (i.1 + 1) * (f i).1) = n)).card

/-- Let n be the length of num. For every input satisfying the preconditions, the function returns Ok r, where r is the unique integer such that 0 <= r < 1000000007 and r is congruent modulo 1000000007 to C(num), defined as follows. An admissible partition of num consists of an integer k >= 1 and indices 0 = p_0 < p_1 < ... < p_k = n. For 0 <= j < k, block j is the substring num[p_j], num[p_j+1], ..., num[p_{j+1}-1]. The partition is admissible iff (1) for every j with 0 <= j < k, num[p_j] is not the ASCII byte '0' (so each block is a positive integer with no leading zero), and (2) for every j with 0 <= j < k-1, the decimal integer represented by block j is <= the decimal integer represented by block j+1. C(num) is the number of admissible partitions.
  Preconditions: num is a byte slice of length n with 1 <= n <= 3500, and for every i with 0 <= i < n, num[i] is an ASCII decimal digit (48 <= num[i] <= 57). -/
theorem spec_1 (num : Aeneas.Std.Slice Aeneas.Std.U8) (n : Nat)
    (hn : num.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 3500)
    (hdig : ∀ (i : Nat) (_ : i < n), IsDigitByte num.val[i]) :
    ∃ r : Aeneas.Std.I64,
      Aegis.NumberOfCombinations.number_of_combinations num = Aeneas.Std.Result.ok r ∧
        r.val = ((numAdmissible num.val % modulus : Nat) : Int) ∧
        0 ≤ r.val ∧ r.val < (modulus : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (num : Aeneas.Std.Slice Aeneas.Std.U8) (n : Nat)
    (hn : num.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 3500)
    (hdig : ∀ (i : Nat) (_ : i < n), IsDigitByte num.val[i]), ∃ r : Aeneas.Std.I64,
      Aegis.NumberOfCombinations.number_of_combinations num = Aeneas.Std.Result.ok r ∧
        r.val = ((numAdmissible num.val % modulus : Nat) : Int) ∧
        0 ≤ r.val ∧ r.val < (modulus : Int)) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r < 1000000007; equivalently, the returned count is reduced to its canonical residue modulo 1000000007.
  Preconditions: num is a byte slice of length n with 1 <= n <= 3500, and for every i with 0 <= i < n, num[i] is an ASCII decimal digit (48 <= num[i] <= 57). -/
theorem spec_2 (num : Aeneas.Std.Slice Aeneas.Std.U8) (n : Nat)
    (hn : num.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 3500)
    (hdig : ∀ (i : Nat) (_ : i < n), IsDigitByte num.val[i])
    (r : Aeneas.Std.I64)
    (hr : Aegis.NumberOfCombinations.number_of_combinations num = Aeneas.Std.Result.ok r) :
    0 ≤ r.val ∧ r.val < (modulus : Int) := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (num : Aeneas.Std.Slice Aeneas.Std.U8) (n : Nat)
    (hn : num.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 3500)
    (hdig : ∀ (i : Nat) (_ : i < n), IsDigitByte num.val[i])
    (r : Aeneas.Std.I64)
    (hr : Aegis.NumberOfCombinations.number_of_combinations num = Aeneas.Std.Result.ok r), 0 ≤ r.val ∧ r.val < (modulus : Int)) := by
  sorry

/-- The function returns a result r for every input satisfying the preconditions; it does not fail, panic, access memory out of bounds, or overflow 64-bit signed arithmetic.
  Preconditions: num is a byte slice of length n with 1 <= n <= 3500, and for every i with 0 <= i < n, num[i] is an ASCII decimal digit (48 <= num[i] <= 57). -/
theorem spec_3 (num : Aeneas.Std.Slice Aeneas.Std.U8) (n : Nat)
    (hn : num.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 3500)
    (hdig : ∀ (i : Nat) (_ : i < n), IsDigitByte num.val[i]) :
    ∃ r : Aeneas.Std.I64,
      Aegis.NumberOfCombinations.number_of_combinations num = Aeneas.Std.Result.ok r := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (num : Aeneas.Std.Slice Aeneas.Std.U8) (n : Nat)
    (hn : num.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 3500)
    (hdig : ∀ (i : Nat) (_ : i < n), IsDigitByte num.val[i]), ∃ r : Aeneas.Std.I64,
      Aegis.NumberOfCombinations.number_of_combinations num = Aeneas.Std.Result.ok r) := by
  sorry

/-- The function returns r = 0. Equivalently, the exact number of admissible partitions is 0, so the modulo answer is 0.
  Preconditions: num is a byte slice of length n with 1 <= n <= 3500; every num[i] is an ASCII decimal digit; and num[0] is the ASCII byte '0' (48). -/
theorem spec_4 (num : Aeneas.Std.Slice Aeneas.Std.U8) (n : Nat)
    (hn : num.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 3500)
    (hdig : ∀ (i : Nat) (_ : i < n), IsDigitByte num.val[i])
    (hzero : num.val[0] = 48#u8) :
    (∃ r : Aeneas.Std.I64,
        Aegis.NumberOfCombinations.number_of_combinations num = Aeneas.Std.Result.ok r ∧
          r.val = 0) ∧
      numAdmissible num.val = 0 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (num : Aeneas.Std.Slice Aeneas.Std.U8) (n : Nat)
    (hn : num.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 3500)
    (hdig : ∀ (i : Nat) (_ : i < n), IsDigitByte num.val[i])
    (hzero : num.val[0] = 48#u8), (∃ r : Aeneas.Std.I64,
        Aegis.NumberOfCombinations.number_of_combinations num = Aeneas.Std.Result.ok r ∧
          r.val = 0) ∧
      numAdmissible num.val = 0) := by
  sorry

/-- The function returns r = 1; the only admissible partition is the single block containing the one digit.
  Preconditions: num is a byte slice of length n with 1 <= n <= 3500; every num[i] is an ASCII decimal digit; n = 1; and 49 <= num[0] <= 57. -/
theorem spec_5 (num : Aeneas.Std.Slice Aeneas.Std.U8) (n : Nat)
    (hn : num.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 3500)
    (hdig : ∀ (i : Nat) (_ : i < n), IsDigitByte num.val[i])
    (hnone : n = 1) (hfirst : 49 ≤ (num.val[0]).val) :
    ∃ r : Aeneas.Std.I64,
      Aegis.NumberOfCombinations.number_of_combinations num = Aeneas.Std.Result.ok r ∧
        r.val = 1 ∧ numAdmissible num.val = 1 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (num : Aeneas.Std.Slice Aeneas.Std.U8) (n : Nat)
    (hn : num.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 3500)
    (hdig : ∀ (i : Nat) (_ : i < n), IsDigitByte num.val[i])
    (hnone : n = 1) (hfirst : 49 ≤ (num.val[0]).val), ∃ r : Aeneas.Std.I64,
      Aegis.NumberOfCombinations.number_of_combinations num = Aeneas.Std.Result.ok r ∧
        r.val = 1 ∧ numAdmissible num.val = 1) := by
  sorry

/-- The function returns r = 1; the only admissible partition is the single block equal to the whole string num.
  Preconditions: num is a byte slice of length n with 1 <= n <= 3500; every num[i] is an ASCII decimal digit; n >= 2; 49 <= num[0] <= 57; and for every i with 1 <= i < n, num[i] is the ASCII byte '0' (48). -/
theorem spec_6 (num : Aeneas.Std.Slice Aeneas.Std.U8) (n : Nat)
    (hn : num.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 3500)
    (hdig : ∀ (i : Nat) (_ : i < n), IsDigitByte num.val[i])
    (hn2' : 2 ≤ n) (hfirst : 49 ≤ (num.val[0]).val)
    (hrest : ∀ (i : Nat) (_ : 1 ≤ i) (_ : i < n), (num.val[i]).val = 48) :
    ∃ r : Aeneas.Std.I64,
      Aegis.NumberOfCombinations.number_of_combinations num = Aeneas.Std.Result.ok r ∧
        r.val = 1 ∧ numAdmissible num.val = 1 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (num : Aeneas.Std.Slice Aeneas.Std.U8) (n : Nat)
    (hn : num.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 3500)
    (hdig : ∀ (i : Nat) (_ : i < n), IsDigitByte num.val[i])
    (hn2' : 2 ≤ n) (hfirst : 49 ≤ (num.val[0]).val)
    (hrest : ∀ (i : Nat) (_ : 1 ≤ i) (_ : i < n), (num.val[i]).val = 48), ∃ r : Aeneas.Std.I64,
      Aegis.NumberOfCombinations.number_of_combinations num = Aeneas.Std.Result.ok r ∧
        r.val = 1 ∧ numAdmissible num.val = 1) := by
  sorry

/-- Let p(n) be the number of integer partitions of n, i.e. the number of nondecreasing sequences a_1 <= a_2 <= ... <= a_t of positive integers whose sum is n. The function returns r = p(n) mod 1000000007.
  Preconditions: num is a byte slice of length n with 1 <= n <= 3500; every num[i] is an ASCII decimal digit; and there exists d with 49 <= d <= 57 such that num[i] = d for every i with 0 <= i < n. -/
theorem spec_7 (num : Aeneas.Std.Slice Aeneas.Std.U8) (n d : Nat)
    (hn : num.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 3500)
    (hdig : ∀ (i : Nat) (_ : i < n), IsDigitByte num.val[i])
    (hd1 : 49 ≤ d) (hd2 : d ≤ 57)
    (hunif : ∀ (i : Nat) (_ : i < n), (num.val[i]).val = d) :
    ∃ r : Aeneas.Std.I64,
      Aegis.NumberOfCombinations.number_of_combinations num = Aeneas.Std.Result.ok r ∧
        r.val = ((numIntegerPartitions n % modulus : Nat) : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (num : Aeneas.Std.Slice Aeneas.Std.U8) (n d : Nat)
    (hn : num.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 3500)
    (hdig : ∀ (i : Nat) (_ : i < n), IsDigitByte num.val[i])
    (hd1 : 49 ≤ d) (hd2 : d ≤ 57)
    (hunif : ∀ (i : Nat) (_ : i < n), (num.val[i]).val = d), ∃ r : Aeneas.Std.I64,
      Aegis.NumberOfCombinations.number_of_combinations num = Aeneas.Std.Result.ok r ∧
        r.val = ((numIntegerPartitions n % modulus : Nat) : Int)) := by
  sorry

/-- Let a = num[0] - 48 and b = num[1] - 48. The function returns r = 2 if num[1] is not the ASCII byte '0' and a <= b; otherwise the function returns r = 1.
  Preconditions: num is a byte slice of length n with 1 <= n <= 3500; every num[i] is an ASCII decimal digit; n = 2; and num[0] is not the ASCII byte '0' (48). -/
theorem spec_8 (num : Aeneas.Std.Slice Aeneas.Std.U8) (n : Nat)
    (hn : num.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 3500)
    (hdig : ∀ (i : Nat) (_ : i < n), IsDigitByte num.val[i])
    (hn2' : n = 2) (hfirst : num.val[0] ≠ 48#u8) :
    ∃ r : Aeneas.Std.I64,
      Aegis.NumberOfCombinations.number_of_combinations num = Aeneas.Std.Result.ok r ∧
        r.val = (if num.val[1] ≠ 48#u8 ∧ digitVal num.val[0] ≤ digitVal num.val[1] then
            (2 : Int) else 1) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (num : Aeneas.Std.Slice Aeneas.Std.U8) (n : Nat)
    (hn : num.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 3500)
    (hdig : ∀ (i : Nat) (_ : i < n), IsDigitByte num.val[i])
    (hn2' : n = 2) (hfirst : num.val[0] ≠ 48#u8), ∃ r : Aeneas.Std.I64,
      Aegis.NumberOfCombinations.number_of_combinations num = Aeneas.Std.Result.ok r ∧
        r.val = (if num.val[1] ≠ 48#u8 ∧ digitVal num.val[0] ≤ digitVal num.val[1] then
            (2 : Int) else 1)) := by
  sorry

/-- The single-block partition with k = 1, p_0 = 0, and p_1 = n is admissible; hence the exact count C(num) of admissible partitions satisfies C(num) >= 1. Consequently, for the returned r, r is congruent modulo 1000000007 to a positive integer C(num), although r itself can be 0 if C(num) is a positive multiple of 1000000007.
  Preconditions: num is a byte slice of length n with 1 <= n <= 3500; every num[i] is an ASCII decimal digit; and num[0] is not the ASCII byte '0' (48). -/
theorem spec_9 (num : Aeneas.Std.Slice Aeneas.Std.U8) (n : Nat)
    (hn : num.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 3500)
    (hdig : ∀ (i : Nat) (_ : i < n), IsDigitByte num.val[i])
    (hfirst : num.val[0] ≠ 48#u8) :
    IsAdmissiblePartition num.val [num.val] ∧
      1 ≤ numAdmissible num.val ∧
      ∃ r : Aeneas.Std.I64,
        Aegis.NumberOfCombinations.number_of_combinations num = Aeneas.Std.Result.ok r ∧
          0 ≤ r.val ∧ r.val < (modulus : Int) ∧
          r.val = ((numAdmissible num.val % modulus : Nat) : Int) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (num : Aeneas.Std.Slice Aeneas.Std.U8) (n : Nat)
    (hn : num.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 3500)
    (hdig : ∀ (i : Nat) (_ : i < n), IsDigitByte num.val[i])
    (hfirst : num.val[0] ≠ 48#u8), IsAdmissiblePartition num.val [num.val] ∧
      1 ≤ numAdmissible num.val ∧
      ∃ r : Aeneas.Std.I64,
        Aegis.NumberOfCombinations.number_of_combinations num = Aeneas.Std.Result.ok r ∧
          0 ≤ r.val ∧ r.val < (modulus : Int) ∧
          r.val = ((numAdmissible num.val % modulus : Nat) : Int)) := by
  sorry

end AegisSpec.NumberOfCombinations

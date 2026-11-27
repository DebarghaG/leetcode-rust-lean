import Aegis.CountBeautifulPairs.Code.Funs

/-!
# Specifications of `Aegis.CountBeautifulPairs.count_beautiful_pairs`

LeetCode problem `number-of-beautiful-pairs`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CountBeautifulPairs

  abbrev SliceI64 : Type := Aeneas.Std.Slice Aeneas.Std.I64

  def firstDigitNat (n : Nat) : Nat :=
    if _h : n < 10 then n else firstDigitNat (n / 10)
  termination_by n
  decreasing_by exact Nat.div_lt_self (by omega) (by decide)

  def firstDigit (x : Int) : Nat := firstDigitNat x.natAbs

  def lastDigit (x : Int) : Nat := x.natAbs % 10

  def elems (nums : SliceI64) : List Int := nums.val.map (fun x => x.val)

  def elem (nums : SliceI64) (i : Nat) : Int := (elems nums).getD i 0

  def indicator (b : Bool) : Nat := if b then 1 else 0

  def pairBound (n : Nat) : Int := (((n * (n - 1)) / 2 : Nat) : Int)

  def countAfter (l : List Int) (i : Nat) : Nat :=
    (List.range l.length).countP (fun j =>
      decide (i < j) && decide (Nat.Coprime (firstDigit (l.getD i 0)) (lastDigit (l.getD j 0))))

  def pairCount (l : List Int) : Nat :=
    ((List.range l.length).map (fun i => countAfter l i)).sum

  def countFirstCoprime (l : List Int) (d : Nat) : Nat :=
    l.countP (fun x => Nat.gcd (firstDigit x) d == 1)

  def countLastCoprime (l : List Int) (d : Nat) : Nat :=
    l.countP (fun x => Nat.gcd d (lastDigit x) == 1)

  def weightedFirstSum (l : List Int) (d : Nat) : Nat :=
    ((List.range (l.length - 1)).map (fun i =>
      (l.length - 1 - i) * indicator (Nat.gcd (firstDigit (l.getD i 0)) d == 1))).sum

  def weightedLastSum (l : List Int) (a : Nat) : Nat :=
    ((List.range (l.length - 1)).map (fun k =>
      (k + 1) * indicator (Nat.gcd a (lastDigit (l.getD (k + 1) 0)) == 1))).sum

  /-- The function returns a result r and r equals the number of pairs (i,j) with 0 <= i < j < len(nums) such that gcd(firstDigit(nums[i]), lastDigit(nums[j])) = 1.
    Preconditions: len(nums) >= 2 and len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 9999. -/
  theorem spec_1 (nums : SliceI64) (hlen_lo : 2 ≤ nums.val.length)
      (hlen_hi : nums.val.length ≤ 100)
      (hrange : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 9999) :
      ∃ r, Aegis.CountBeautifulPairs.count_beautiful_pairs nums = ok r ∧
        r.val = (pairCount (elems nums) : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : SliceI64) (hlen_lo : 2 ≤ nums.val.length)
        (hlen_hi : nums.val.length ≤ 100)
        (hrange : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 9999), ∃ r, Aegis.CountBeautifulPairs.count_beautiful_pairs nums = ok r ∧
          r.val = (pairCount (elems nums) : Int)) := by
    sorry

  /-- The function returns a result r and 0 <= r <= len(nums)*(len(nums)-1)/2.
    Preconditions: len(nums) >= 2 and len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 9999. -/
  theorem spec_2 (nums : SliceI64) (hlen_lo : 2 ≤ nums.val.length)
      (hlen_hi : nums.val.length ≤ 100)
      (hrange : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 9999) :
      ∃ r, Aegis.CountBeautifulPairs.count_beautiful_pairs nums = ok r ∧
        0 ≤ r.val ∧ r.val ≤ pairBound nums.val.length := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : SliceI64) (hlen_lo : 2 ≤ nums.val.length)
        (hlen_hi : nums.val.length ≤ 100)
        (hrange : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 9999), ∃ r, Aegis.CountBeautifulPairs.count_beautiful_pairs nums = ok r ∧
          0 ≤ r.val ∧ r.val ≤ pairBound nums.val.length) := by
    sorry

  /-- The function returns a result r; in particular, it does not fail by arithmetic overflow, out-of-bounds access, or panic.
    Preconditions: len(nums) >= 2 and len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 9999. -/
  theorem spec_3 (nums : SliceI64) (hlen_lo : 2 ≤ nums.val.length)
      (hlen_hi : nums.val.length ≤ 100)
      (hrange : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 9999) :
      ∃ r, Aegis.CountBeautifulPairs.count_beautiful_pairs nums = ok r := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : SliceI64) (hlen_lo : 2 ≤ nums.val.length)
        (hlen_hi : nums.val.length ≤ 100)
        (hrange : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 9999), ∃ r, Aegis.CountBeautifulPairs.count_beautiful_pairs nums = ok r) := by
    sorry

  /-- The function returns a result r and r = 1 if gcd(firstDigit(nums[0]), lastDigit(nums[1])) = 1, and r = 0 otherwise.
    Preconditions: len(nums) = 2, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 9999. -/
  theorem spec_4 (nums : SliceI64) (hlen : nums.val.length = 2)
      (hrange : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 9999) :
      ∃ r, Aegis.CountBeautifulPairs.count_beautiful_pairs nums = ok r ∧
        r.val =
          (if Nat.Coprime (firstDigit (elem nums 0)) (lastDigit (elem nums 1)) then 1 else 0) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : SliceI64) (hlen : nums.val.length = 2)
        (hrange : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 9999), ∃ r, Aegis.CountBeautifulPairs.count_beautiful_pairs nums = ok r ∧
          r.val =
            (if Nat.Coprime (firstDigit (elem nums 0)) (lastDigit (elem nums 1)) then 1 else 0)) := by
    sorry

  /-- The function returns a result r and r = len(nums)*(len(nums)-1)/2 if and only if for every i,j with 0 <= i < j < len(nums), gcd(firstDigit(nums[i]), lastDigit(nums[j])) = 1.
    Preconditions: len(nums) >= 2 and len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 9999. -/
  theorem spec_5 (nums : SliceI64) (hlen_lo : 2 ≤ nums.val.length)
      (hlen_hi : nums.val.length ≤ 100)
      (hrange : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 9999) :
      ∃ r, Aegis.CountBeautifulPairs.count_beautiful_pairs nums = ok r ∧
        (r.val = pairBound nums.val.length ↔
          ∀ i j, i < j → j < nums.val.length →
            Nat.Coprime (firstDigit (elem nums i)) (lastDigit (elem nums j))) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : SliceI64) (hlen_lo : 2 ≤ nums.val.length)
        (hlen_hi : nums.val.length ≤ 100)
        (hrange : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 9999), ∃ r, Aegis.CountBeautifulPairs.count_beautiful_pairs nums = ok r ∧
          (r.val = pairBound nums.val.length ↔
            ∀ i j, i < j → j < nums.val.length →
              Nat.Coprime (firstDigit (elem nums i)) (lastDigit (elem nums j)))) := by
    sorry

  /-- The function returns a result r and r = 0 if and only if for every i,j with 0 <= i < j < len(nums), gcd(firstDigit(nums[i]), lastDigit(nums[j])) > 1.
    Preconditions: len(nums) >= 2 and len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 9999. -/
  theorem spec_6 (nums : SliceI64) (hlen_lo : 2 ≤ nums.val.length)
      (hlen_hi : nums.val.length ≤ 100)
      (hrange : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 9999) :
      ∃ r, Aegis.CountBeautifulPairs.count_beautiful_pairs nums = ok r ∧
        (r.val = 0 ↔
          ∀ i j, i < j → j < nums.val.length →
            1 < Nat.gcd (firstDigit (elem nums i)) (lastDigit (elem nums j))) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : SliceI64) (hlen_lo : 2 ≤ nums.val.length)
        (hlen_hi : nums.val.length ≤ 100)
        (hrange : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 9999), ∃ r, Aegis.CountBeautifulPairs.count_beautiful_pairs nums = ok r ∧
          (r.val = 0 ↔
            ∀ i j, i < j → j < nums.val.length →
              1 < Nat.gcd (firstDigit (elem nums i)) (lastDigit (elem nums j)))) := by
    sorry

  /-- Let nums' be nums with x appended as its last element. The function returns a result r on nums' and a result r0 on nums, and r = r0 + #{ i : 0 <= i < len(nums) and gcd(firstDigit(nums[i]), lastDigit(x)) = 1 }.
    Preconditions: len(nums) >= 2, len(nums) + 1 <= 100, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 9999, and 1 <= x <= 9999. -/
  theorem spec_7 (nums nums' : SliceI64) (x : Aeneas.Std.I64)
      (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length + 1 ≤ 100)
      (hrange : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 9999)
      (hx : 1 ≤ x.val ∧ x.val ≤ 9999)
      (happend : nums'.val = nums.val ++ [x]) :
      ∃ r r0, Aegis.CountBeautifulPairs.count_beautiful_pairs nums' = ok r ∧
        Aegis.CountBeautifulPairs.count_beautiful_pairs nums = ok r0 ∧
        r.val = r0.val + (countFirstCoprime (elems nums) (lastDigit x.val) : Int) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums nums' : SliceI64) (x : Aeneas.Std.I64)
        (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length + 1 ≤ 100)
        (hrange : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 9999)
        (hx : 1 ≤ x.val ∧ x.val ≤ 9999)
        (happend : nums'.val = nums.val ++ [x]), ∃ r r0, Aegis.CountBeautifulPairs.count_beautiful_pairs nums' = ok r ∧
          Aegis.CountBeautifulPairs.count_beautiful_pairs nums = ok r0 ∧
          r.val = r0.val + (countFirstCoprime (elems nums) (lastDigit x.val) : Int)) := by
    sorry

  /-- Let nums' be x followed by nums. The function returns a result r on nums' and a result r0 on nums, and r = r0 + #{ j : 0 <= j < len(nums) and gcd(firstDigit(x), lastDigit(nums[j])) = 1 }.
    Preconditions: len(nums) >= 2, len(nums) + 1 <= 100, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 9999, and 1 <= x <= 9999. -/
  theorem spec_8 (nums nums' : SliceI64) (x : Aeneas.Std.I64)
      (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length + 1 ≤ 100)
      (hrange : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 9999)
      (hx : 1 ≤ x.val ∧ x.val ≤ 9999)
      (hprepend : nums'.val = x :: nums.val) :
      ∃ r r0, Aegis.CountBeautifulPairs.count_beautiful_pairs nums' = ok r ∧
        Aegis.CountBeautifulPairs.count_beautiful_pairs nums = ok r0 ∧
        r.val = r0.val + (countLastCoprime (elems nums) (firstDigit x.val) : Int) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums nums' : SliceI64) (x : Aeneas.Std.I64)
        (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length + 1 ≤ 100)
        (hrange : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 9999)
        (hx : 1 ≤ x.val ∧ x.val ≤ 9999)
        (hprepend : nums'.val = x :: nums.val), ∃ r r0, Aegis.CountBeautifulPairs.count_beautiful_pairs nums' = ok r ∧
          Aegis.CountBeautifulPairs.count_beautiful_pairs nums = ok r0 ∧
          r.val = r0.val + (countLastCoprime (elems nums) (firstDigit x.val) : Int)) := by
    sorry

  /-- If for every i with 0 <= i < len(nums) we have firstDigit(nums[i]) = firstDigit(m[i]) and lastDigit(nums[i]) = lastDigit(m[i]), then the function returns results r and r' on nums and m respectively and r = r'.
    Preconditions: len(nums) >= 2, len(nums) <= 100, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 9999; len(m) >= 2, len(m) <= 100, for every i with 0 <= i < len(m), 1 <= m[i] <= 9999; and len(nums) = len(m). -/
  theorem spec_9 (nums m : SliceI64) (hlen_lo : 2 ≤ nums.val.length)
      (hlen_hi : nums.val.length ≤ 100)
      (hrange : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 9999)
      (mlen_lo : 2 ≤ m.val.length) (mlen_hi : m.val.length ≤ 100)
      (mrange : ∀ i, i < m.val.length → 1 ≤ elem m i ∧ elem m i ≤ 9999)
      (hlen : nums.val.length = m.val.length)
      (hdigits : ∀ i, i < nums.val.length →
        firstDigit (elem nums i) = firstDigit (elem m i) ∧
          lastDigit (elem nums i) = lastDigit (elem m i)) :
      ∃ r r', Aegis.CountBeautifulPairs.count_beautiful_pairs nums = ok r ∧
        Aegis.CountBeautifulPairs.count_beautiful_pairs m = ok r' ∧ r.val = r'.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums m : SliceI64) (hlen_lo : 2 ≤ nums.val.length)
        (hlen_hi : nums.val.length ≤ 100)
        (hrange : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 9999)
        (mlen_lo : 2 ≤ m.val.length) (mlen_hi : m.val.length ≤ 100)
        (mrange : ∀ i, i < m.val.length → 1 ≤ elem m i ∧ elem m i ≤ 9999)
        (hlen : nums.val.length = m.val.length)
        (hdigits : ∀ i, i < nums.val.length →
          firstDigit (elem nums i) = firstDigit (elem m i) ∧
            lastDigit (elem nums i) = lastDigit (elem m i)), ∃ r r', Aegis.CountBeautifulPairs.count_beautiful_pairs nums = ok r ∧
          Aegis.CountBeautifulPairs.count_beautiful_pairs m = ok r' ∧ r.val = r'.val) := by
    sorry

  /-- The function returns a result r and r = sum_{i=0}^{len(nums)-2} (len(nums)-1-i) * [gcd(firstDigit(nums[i]), d) = 1], where [true]=1 and [false]=0.
    Preconditions: len(nums) >= 2 and len(nums) <= 100, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 9999, and there exists an integer d with 0 <= d <= 9 such that for every j with 0 <= j < len(nums), lastDigit(nums[j]) = d. -/
  theorem spec_10 (nums : SliceI64) (d : Nat) (hlen_lo : 2 ≤ nums.val.length)
      (hlen_hi : nums.val.length ≤ 100)
      (hrange : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 9999)
      (hd : d ≤ 9)
      (hlast : ∀ j, j < nums.val.length → lastDigit (elem nums j) = d) :
      ∃ r, Aegis.CountBeautifulPairs.count_beautiful_pairs nums = ok r ∧
        r.val = (weightedFirstSum (elems nums) d : Int) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : SliceI64) (d : Nat) (hlen_lo : 2 ≤ nums.val.length)
        (hlen_hi : nums.val.length ≤ 100)
        (hrange : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 9999)
        (hd : d ≤ 9)
        (hlast : ∀ j, j < nums.val.length → lastDigit (elem nums j) = d), ∃ r, Aegis.CountBeautifulPairs.count_beautiful_pairs nums = ok r ∧
          r.val = (weightedFirstSum (elems nums) d : Int)) := by
    sorry

  /-- The function returns a result r and r = sum_{j=1}^{len(nums)-1} j * [gcd(a, lastDigit(nums[j])) = 1], where [true]=1 and [false]=0.
    Preconditions: len(nums) >= 2 and len(nums) <= 100, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 9999, and there exists an integer a with 1 <= a <= 9 such that for every i with 0 <= i < len(nums), firstDigit(nums[i]) = a. -/
  theorem spec_11 (nums : SliceI64) (a : Nat) (hlen_lo : 2 ≤ nums.val.length)
      (hlen_hi : nums.val.length ≤ 100)
      (hrange : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 9999)
      (ha_lo : 1 ≤ a) (ha_hi : a ≤ 9)
      (hfirst : ∀ i, i < nums.val.length → firstDigit (elem nums i) = a) :
      ∃ r, Aegis.CountBeautifulPairs.count_beautiful_pairs nums = ok r ∧
        r.val = (weightedLastSum (elems nums) a : Int) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : SliceI64) (a : Nat) (hlen_lo : 2 ≤ nums.val.length)
        (hlen_hi : nums.val.length ≤ 100)
        (hrange : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 9999)
        (ha_lo : 1 ≤ a) (ha_hi : a ≤ 9)
        (hfirst : ∀ i, i < nums.val.length → firstDigit (elem nums i) = a), ∃ r, Aegis.CountBeautifulPairs.count_beautiful_pairs nums = ok r ∧
          r.val = (weightedLastSum (elems nums) a : Int)) := by
    sorry

  /-- The function returns a result r and r = sum_{i=0}^{len(nums)-2} c_i, where for each i, c_i = #{ j : i < j < len(nums) and gcd(firstDigit(nums[i]), lastDigit(nums[j])) = 1 }.
    Preconditions: len(nums) >= 2 and len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 9999. -/
  theorem spec_12 (nums : SliceI64) (hlen_lo : 2 ≤ nums.val.length)
      (hlen_hi : nums.val.length ≤ 100)
      (hrange : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 9999) :
      ∃ r, Aegis.CountBeautifulPairs.count_beautiful_pairs nums = ok r ∧
        r.val = (((List.range (nums.val.length - 1)).map
          (fun i => countAfter (elems nums) i)).sum : Int) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : SliceI64) (hlen_lo : 2 ≤ nums.val.length)
        (hlen_hi : nums.val.length ≤ 100)
        (hrange : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 9999), ∃ r, Aegis.CountBeautifulPairs.count_beautiful_pairs nums = ok r ∧
          r.val = (((List.range (nums.val.length - 1)).map
            (fun i => countAfter (elems nums) i)).sum : Int)) := by
    sorry

  end AegisSpec.CountBeautifulPairs

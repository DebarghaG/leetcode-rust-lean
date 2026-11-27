import Aegis.IsAdditiveNumber.Code.Funs

/-!
# Specifications of `Aegis.IsAdditiveNumber.is_additive_number`

LeetCode problem `additive-number`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.IsAdditiveNumber

  def byteAt (bs : List Aeneas.Std.U8) (j : Nat) : Option Aeneas.Std.U8 := bs[j]?

  def digitVal (b : Aeneas.Std.U8) : Nat := b.val - 48

  def digitAt (bs : List Aeneas.Std.U8) (j : Nat) : Nat :=
    match byteAt bs j with
    | some b => digitVal b
    | none => 0

  def bytesVal (bs : List Aeneas.Std.U8) : Nat :=
    bs.foldl (fun acc b => acc * 10 + digitVal b) 0

  def subBytes (bs : List Aeneas.Std.U8) (s e : Nat) : List Aeneas.Std.U8 :=
    (bs.drop s).take (e - s)

  def firstDigit (bs : List Aeneas.Std.U8) : Option Nat := bs.head?.map digitVal

  def splitPart (bs : List Aeneas.Std.U8) (i : Nat → Nat) (j : Nat) : List Aeneas.Std.U8 :=
    subBytes bs (i j) (i (j + 1))

  def IsAdditiveSplit (bs : List Aeneas.Std.U8) (k : Nat) (i : Nat → Nat) : Prop :=
    3 ≤ k ∧
    i 0 = 0 ∧
    i k = bs.length ∧
    (∀ j, j < k → i j < i (j + 1)) ∧
    (∀ j, j < k → 2 ≤ i (j + 1) - i j → firstDigit (splitPart bs i j) ≠ some 0) ∧
    (∀ j, 2 ≤ j → j < k →
      bytesVal (splitPart bs i j) = bytesVal (splitPart bs i (j - 1))
        + bytesVal (splitPart bs i (j - 2)))

  def HasAdditiveSplit (bs : List Aeneas.Std.U8) : Prop :=
    ∃ (k : Nat) (i : Nat → Nat), IsAdditiveSplit bs k i

  def partValue (ps : List (List Aeneas.Std.U8)) (j : Nat) : Nat := bytesVal (ps.getD j [])

  def IsAdditivePartition (bs : List Aeneas.Std.U8) (ps : List (List Aeneas.Std.U8)) : Prop :=
    3 ≤ ps.length ∧
    ps.flatten = bs ∧
    (∀ p ∈ ps, p ≠ [] ∧ (2 ≤ p.length → firstDigit p ≠ some 0)) ∧
    (∀ j, 2 ≤ j → j < ps.length →
      partValue ps j = partValue ps (j - 1) + partValue ps (j - 2))

  /-- The function returns a result r (it does not fail), and r = true if and only if there exist an integer k >= 3 and indices 0 = i_0 < i_1 < ... < i_k = len(num) such that, for each j with 0 <= j < k, the bytes num[i_j], num[i_j+1], ..., num[i_{j+1}-1] form a nonempty decimal numeral a_j with no leading zero (if i_{j+1}-i_j > 1 then num[i_j] != 48), and for every j with 2 <= j < k, a_j = a_{j-1} + a_{j-2}. Here a_j is the usual base-10 value of that byte substring. Otherwise r = false.
    Preconditions: The input satisfies the problem constraints: 1 <= len(num) <= 35, and for every i with 0 <= i < len(num), num[i] is an ASCII decimal digit, i.e. 48 <= num[i] <= 57. -/
  theorem spec_1 (num : Aeneas.Std.Slice Aeneas.Std.U8)
      (h_len1 : 1 ≤ num.val.length) (h_len35 : num.val.length ≤ 35)
      (h_digits : ∀ b ∈ num.val, 48 ≤ b.val ∧ b.val ≤ 57) :
      ∃ r, Aegis.IsAdditiveNumber.is_additive_number num = ok r ∧
        (r = true ↔ HasAdditiveSplit num.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (num : Aeneas.Std.Slice Aeneas.Std.U8)
        (h_len1 : 1 ≤ num.val.length) (h_len35 : num.val.length ≤ 35)
        (h_digits : ∀ b ∈ num.val, 48 ≤ b.val ∧ b.val ≤ 57), ∃ r, Aegis.IsAdditiveNumber.is_additive_number num = ok r ∧
          (r = true ↔ HasAdditiveSplit num.val)) := by
    sorry

  /-- For every input satisfying the preconditions, is_additive_number num returns Result.ok b for some Boolean b; it does not panic, return an error, or fail because of arithmetic overflow.
    Preconditions: The input satisfies the problem constraints: 1 <= len(num) <= 35, and for every i with 0 <= i < len(num), num[i] is an ASCII decimal digit, i.e. 48 <= num[i] <= 57. -/
  theorem spec_2 (num : Aeneas.Std.Slice Aeneas.Std.U8)
      (h_len1 : 1 ≤ num.val.length) (h_len35 : num.val.length ≤ 35)
      (h_digits : ∀ b ∈ num.val, 48 ≤ b.val ∧ b.val ≤ 57) :
      ∃ b, Aegis.IsAdditiveNumber.is_additive_number num = ok b := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (num : Aeneas.Std.Slice Aeneas.Std.U8)
        (h_len1 : 1 ≤ num.val.length) (h_len35 : num.val.length ≤ 35)
        (h_digits : ∀ b ∈ num.val, 48 ≤ b.val ∧ b.val ≤ 57), ∃ b, Aegis.IsAdditiveNumber.is_additive_number num = ok b) := by
    sorry

  /-- The function returns Result.ok false.
    Preconditions: The input satisfies the problem constraints: 1 <= len(num) <= 35, and for every i with 0 <= i < len(num), num[i] is an ASCII decimal digit, i.e. 48 <= num[i] <= 57. Also len(num) < 3. -/
  theorem spec_3 (num : Aeneas.Std.Slice Aeneas.Std.U8)
      (h_len1 : 1 ≤ num.val.length) (h_len35 : num.val.length ≤ 35)
      (h_digits : ∀ b ∈ num.val, 48 ≤ b.val ∧ b.val ≤ 57)
      (h_len : num.val.length < 3) :
      Aegis.IsAdditiveNumber.is_additive_number num = ok false := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (num : Aeneas.Std.Slice Aeneas.Std.U8)
        (h_len1 : 1 ≤ num.val.length) (h_len35 : num.val.length ≤ 35)
        (h_digits : ∀ b ∈ num.val, 48 ≤ b.val ∧ b.val ≤ 57)
        (h_len : num.val.length < 3), Aegis.IsAdditiveNumber.is_additive_number num = ok false) := by
    sorry

  /-- Let d_0 = num[0] - 48, d_1 = num[1] - 48, and d_2 = num[2] - 48. The function returns Result.ok true if and only if d_0 + d_1 = d_2.
    Preconditions: The input satisfies the problem constraints: 1 <= len(num) <= 35, and for every i with 0 <= i < len(num), num[i] is an ASCII decimal digit, i.e. 48 <= num[i] <= 57. Also len(num) = 3. -/
  theorem spec_4 (num : Aeneas.Std.Slice Aeneas.Std.U8)
      (h_len1 : 1 ≤ num.val.length) (h_len35 : num.val.length ≤ 35)
      (h_digits : ∀ b ∈ num.val, 48 ≤ b.val ∧ b.val ≤ 57)
      (h_len : num.val.length = 3) :
      Aegis.IsAdditiveNumber.is_additive_number num = ok true ↔
        digitAt num.val 0 + digitAt num.val 1 = digitAt num.val 2 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (num : Aeneas.Std.Slice Aeneas.Std.U8)
        (h_len1 : 1 ≤ num.val.length) (h_len35 : num.val.length ≤ 35)
        (h_digits : ∀ b ∈ num.val, 48 ≤ b.val ∧ b.val ≤ 57)
        (h_len : num.val.length = 3), Aegis.IsAdditiveNumber.is_additive_number num = ok true ↔
          digitAt num.val 0 + digitAt num.val 1 = digitAt num.val 2) := by
    sorry

  /-- The function returns Result.ok true.
    Preconditions: The input satisfies the problem constraints: 1 <= len(num) <= 35, and for every i with 0 <= i < len(num), num[i] is an ASCII decimal digit, i.e. 48 <= num[i] <= 57. Also len(num) >= 3, and num[i] = 48 for every i with 0 <= i < len(num). -/
  theorem spec_5 (num : Aeneas.Std.Slice Aeneas.Std.U8)
      (h_len1 : 1 ≤ num.val.length) (h_len35 : num.val.length ≤ 35)
      (h_digits : ∀ b ∈ num.val, 48 ≤ b.val ∧ b.val ≤ 57)
      (h_len : 3 ≤ num.val.length) (h_zeros : ∀ b ∈ num.val, b.val = 48) :
      Aegis.IsAdditiveNumber.is_additive_number num = ok true := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (num : Aeneas.Std.Slice Aeneas.Std.U8)
        (h_len1 : 1 ≤ num.val.length) (h_len35 : num.val.length ≤ 35)
        (h_digits : ∀ b ∈ num.val, 48 ≤ b.val ∧ b.val ≤ 57)
        (h_len : 3 ≤ num.val.length) (h_zeros : ∀ b ∈ num.val, b.val = 48), Aegis.IsAdditiveNumber.is_additive_number num = ok true) := by
    sorry

  /-- Whenever the function returns Result.ok b with b = true, len(num) >= 3.
    Preconditions: The input satisfies the problem constraints: 1 <= len(num) <= 35, and for every i with 0 <= i < len(num), num[i] is an ASCII decimal digit, i.e. 48 <= num[i] <= 57. -/
  theorem spec_6 (num : Aeneas.Std.Slice Aeneas.Std.U8)
      (h_len1 : 1 ≤ num.val.length) (h_len35 : num.val.length ≤ 35)
      (h_digits : ∀ b ∈ num.val, 48 ≤ b.val ∧ b.val ≤ 57) :
      ∀ b, Aegis.IsAdditiveNumber.is_additive_number num = ok b → b = true →
        3 ≤ num.val.length := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (num : Aeneas.Std.Slice Aeneas.Std.U8)
        (h_len1 : 1 ≤ num.val.length) (h_len35 : num.val.length ≤ 35)
        (h_digits : ∀ b ∈ num.val, 48 ≤ b.val ∧ b.val ≤ 57), ∀ b, Aegis.IsAdditiveNumber.is_additive_number num = ok b → b = true →
          3 ≤ num.val.length) := by
    sorry

  /-- Whenever the function returns Result.ok true and num[0] = 48 ('0'), there exists a valid additive partition of num (a split of the whole byte string into at least three nonempty decimal numbers, none with a leading zero except a one-byte 0, with each number from the third equal to the sum of the previous two) whose first number is the one-byte substring num[0..1), i.e. the number 0.
    Preconditions: The input satisfies the problem constraints: 1 <= len(num) <= 35, and for every i with 0 <= i < len(num), num[i] is an ASCII decimal digit, i.e. 48 <= num[i] <= 57. -/
  theorem spec_7 (num : Aeneas.Std.Slice Aeneas.Std.U8)
      (h_len1 : 1 ≤ num.val.length) (h_len35 : num.val.length ≤ 35)
      (h_digits : ∀ b ∈ num.val, 48 ≤ b.val ∧ b.val ≤ 57) :
      Aegis.IsAdditiveNumber.is_additive_number num = ok true →
        byteAt num.val 0 = some 48#u8 →
        ∃ ps, IsAdditivePartition num.val ps ∧ ps.head? = some (subBytes num.val 0 1) ∧
          partValue ps 0 = 0 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (num : Aeneas.Std.Slice Aeneas.Std.U8)
        (h_len1 : 1 ≤ num.val.length) (h_len35 : num.val.length ≤ 35)
        (h_digits : ∀ b ∈ num.val, 48 ≤ b.val ∧ b.val ≤ 57), Aegis.IsAdditiveNumber.is_additive_number num = ok true →
          byteAt num.val 0 = some 48#u8 →
          ∃ ps, IsAdditivePartition num.val ps ∧ ps.head? = some (subBytes num.val 0 1) ∧
            partValue ps 0 = 0) := by
    sorry

  /-- The function returns Result.ok true if and only if num[i] = 48 ('0') for every i with 0 <= i < len(num).
    Preconditions: The input satisfies the problem constraints: 1 <= len(num) <= 35, and for every i with 0 <= i < len(num), num[i] is an ASCII decimal digit, i.e. 48 <= num[i] <= 57. Also len(num) >= 3, num[0] = 48, and num[1] = 48. -/
  theorem spec_8 (num : Aeneas.Std.Slice Aeneas.Std.U8)
      (h_len1 : 1 ≤ num.val.length) (h_len35 : num.val.length ≤ 35)
      (h_digits : ∀ b ∈ num.val, 48 ≤ b.val ∧ b.val ≤ 57)
      (h_len : 3 ≤ num.val.length) (h0 : byteAt num.val 0 = some 48#u8)
      (h1 : byteAt num.val 1 = some 48#u8) :
      Aegis.IsAdditiveNumber.is_additive_number num = ok true ↔
        ∀ b ∈ num.val, b.val = 48 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (num : Aeneas.Std.Slice Aeneas.Std.U8)
        (h_len1 : 1 ≤ num.val.length) (h_len35 : num.val.length ≤ 35)
        (h_digits : ∀ b ∈ num.val, 48 ≤ b.val ∧ b.val ≤ 57)
        (h_len : 3 ≤ num.val.length) (h0 : byteAt num.val 0 = some 48#u8)
        (h1 : byteAt num.val 1 = some 48#u8), Aegis.IsAdditiveNumber.is_additive_number num = ok true ↔
          ∀ b ∈ num.val, b.val = 48) := by
    sorry

  /-- Let d_i = num[i] - 48 for i = 0,1,2,3. The function returns Result.ok true if and only if either (A) d_2 != 0 and d_0 + d_1 = 10*d_2 + d_3, or (B) d_0 + d_1 = d_2 and d_1 + d_2 = d_3.
    Preconditions: The input satisfies the problem constraints: 1 <= len(num) <= 35, and for every i with 0 <= i < len(num), num[i] is an ASCII decimal digit, i.e. 48 <= num[i] <= 57. Also len(num) = 4. -/
  theorem spec_9 (num : Aeneas.Std.Slice Aeneas.Std.U8)
      (h_len1 : 1 ≤ num.val.length) (h_len35 : num.val.length ≤ 35)
      (h_digits : ∀ b ∈ num.val, 48 ≤ b.val ∧ b.val ≤ 57)
      (h_len : num.val.length = 4) :
      Aegis.IsAdditiveNumber.is_additive_number num = ok true ↔
        (digitAt num.val 2 ≠ 0 ∧
            digitAt num.val 0 + digitAt num.val 1 =
              10 * digitAt num.val 2 + digitAt num.val 3) ∨
          (digitAt num.val 0 + digitAt num.val 1 = digitAt num.val 2 ∧
            digitAt num.val 1 + digitAt num.val 2 = digitAt num.val 3) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (num : Aeneas.Std.Slice Aeneas.Std.U8)
        (h_len1 : 1 ≤ num.val.length) (h_len35 : num.val.length ≤ 35)
        (h_digits : ∀ b ∈ num.val, 48 ≤ b.val ∧ b.val ≤ 57)
        (h_len : num.val.length = 4), Aegis.IsAdditiveNumber.is_additive_number num = ok true ↔
          (digitAt num.val 2 ≠ 0 ∧
              digitAt num.val 0 + digitAt num.val 1 =
                10 * digitAt num.val 2 + digitAt num.val 3) ∨
            (digitAt num.val 0 + digitAt num.val 1 = digitAt num.val 2 ∧
              digitAt num.val 1 + digitAt num.val 2 = digitAt num.val 3)) := by
    sorry

  /-- Whenever the function returns Result.ok true and num[0] = 48 ('0'), there exists a valid additive partition of num (as described in spec_7) whose second and third numbers are equal.
    Preconditions: The input satisfies the problem constraints: 1 <= len(num) <= 35, and for every i with 0 <= i < len(num), num[i] is an ASCII decimal digit, i.e. 48 <= num[i] <= 57. -/
  theorem spec_10 (num : Aeneas.Std.Slice Aeneas.Std.U8)
      (h_len1 : 1 ≤ num.val.length) (h_len35 : num.val.length ≤ 35)
      (h_digits : ∀ b ∈ num.val, 48 ≤ b.val ∧ b.val ≤ 57) :
      Aegis.IsAdditiveNumber.is_additive_number num = ok true →
        byteAt num.val 0 = some 48#u8 →
        ∃ ps, IsAdditivePartition num.val ps ∧ partValue ps 1 = partValue ps 2 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (num : Aeneas.Std.Slice Aeneas.Std.U8)
        (h_len1 : 1 ≤ num.val.length) (h_len35 : num.val.length ≤ 35)
        (h_digits : ∀ b ∈ num.val, 48 ≤ b.val ∧ b.val ≤ 57), Aegis.IsAdditiveNumber.is_additive_number num = ok true →
          byteAt num.val 0 = some 48#u8 →
          ∃ ps, IsAdditivePartition num.val ps ∧ partValue ps 1 = partValue ps 2) := by
    sorry

  /-- Whenever the function returns Result.ok true, there exists a valid additive partition of num with at least three numbers such that its last number equals the sum of its two immediately preceding numbers.
    Preconditions: The input satisfies the problem constraints: 1 <= len(num) <= 35, and for every i with 0 <= i < len(num), num[i] is an ASCII decimal digit, i.e. 48 <= num[i] <= 57. -/
  theorem spec_11 (num : Aeneas.Std.Slice Aeneas.Std.U8)
      (h_len1 : 1 ≤ num.val.length) (h_len35 : num.val.length ≤ 35)
      (h_digits : ∀ b ∈ num.val, 48 ≤ b.val ∧ b.val ≤ 57) :
      Aegis.IsAdditiveNumber.is_additive_number num = ok true →
        ∃ ps, IsAdditivePartition num.val ps ∧ 3 ≤ ps.length ∧
          partValue ps (ps.length - 1) = partValue ps (ps.length - 2) +
            partValue ps (ps.length - 3) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (num : Aeneas.Std.Slice Aeneas.Std.U8)
        (h_len1 : 1 ≤ num.val.length) (h_len35 : num.val.length ≤ 35)
        (h_digits : ∀ b ∈ num.val, 48 ≤ b.val ∧ b.val ≤ 57), Aegis.IsAdditiveNumber.is_additive_number num = ok true →
          ∃ ps, IsAdditivePartition num.val ps ∧ 3 ≤ ps.length ∧
            partValue ps (ps.length - 1) = partValue ps (ps.length - 2) +
              partValue ps (ps.length - 3)) := by
    sorry

  /-- Whenever the function returns Result.ok true, there exists a valid additive partition of num whose numeric values a_0, a_1, ..., a_{k-1} (with k >= 3) satisfy a_2 <= a_3 <= ... <= a_{k-1}.
    Preconditions: The input satisfies the problem constraints: 1 <= len(num) <= 35, and for every i with 0 <= i < len(num), num[i] is an ASCII decimal digit, i.e. 48 <= num[i] <= 57. -/
  theorem spec_12 (num : Aeneas.Std.Slice Aeneas.Std.U8)
      (h_len1 : 1 ≤ num.val.length) (h_len35 : num.val.length ≤ 35)
      (h_digits : ∀ b ∈ num.val, 48 ≤ b.val ∧ b.val ≤ 57) :
      Aegis.IsAdditiveNumber.is_additive_number num = ok true →
        ∃ ps, IsAdditivePartition num.val ps ∧
          ∀ j, 2 ≤ j → j + 1 < ps.length → partValue ps j ≤ partValue ps (j + 1) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (num : Aeneas.Std.Slice Aeneas.Std.U8)
        (h_len1 : 1 ≤ num.val.length) (h_len35 : num.val.length ≤ 35)
        (h_digits : ∀ b ∈ num.val, 48 ≤ b.val ∧ b.val ≤ 57), Aegis.IsAdditiveNumber.is_additive_number num = ok true →
          ∃ ps, IsAdditivePartition num.val ps ∧
            ∀ j, 2 ≤ j → j + 1 < ps.length → partValue ps j ≤ partValue ps (j + 1)) := by
    sorry

  /-- Whenever the function returns Result.ok true, there exist integers k and i_0, i_1, ..., i_k such that k >= 3, 0 = i_0 < i_1 < ... < i_k = len(num), and each part length i_{j+1} - i_j (for 0 <= j < k) is at least 1 and at most len(num) - 2.
    Preconditions: The input satisfies the problem constraints: 1 <= len(num) <= 35, and for every i with 0 <= i < len(num), num[i] is an ASCII decimal digit, i.e. 48 <= num[i] <= 57. -/
  theorem spec_13 (num : Aeneas.Std.Slice Aeneas.Std.U8)
      (h_len1 : 1 ≤ num.val.length) (h_len35 : num.val.length ≤ 35)
      (h_digits : ∀ b ∈ num.val, 48 ≤ b.val ∧ b.val ≤ 57) :
      Aegis.IsAdditiveNumber.is_additive_number num = ok true →
        ∃ (k : Nat) (i : Nat → Nat), 3 ≤ k ∧ i 0 = 0 ∧ i k = num.val.length ∧
          (∀ j, j < k → i j < i (j + 1)) ∧
          (∀ j, j < k → 1 ≤ i (j + 1) - i j ∧ i (j + 1) - i j ≤ num.val.length - 2) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (num : Aeneas.Std.Slice Aeneas.Std.U8)
        (h_len1 : 1 ≤ num.val.length) (h_len35 : num.val.length ≤ 35)
        (h_digits : ∀ b ∈ num.val, 48 ≤ b.val ∧ b.val ≤ 57), Aegis.IsAdditiveNumber.is_additive_number num = ok true →
          ∃ (k : Nat) (i : Nat → Nat), 3 ≤ k ∧ i 0 = 0 ∧ i k = num.val.length ∧
            (∀ j, j < k → i j < i (j + 1)) ∧
            (∀ j, j < k → 1 ≤ i (j + 1) - i j ∧ i (j + 1) - i j ≤ num.val.length - 2)) := by
    sorry

  end AegisSpec.IsAdditiveNumber

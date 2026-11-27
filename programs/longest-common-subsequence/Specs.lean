import Aegis.LongestCommonSubsequence.Code.Funs

/-!
# Specifications of `Aegis.LongestCommonSubsequence.longest_common_subsequence`

LeetCode problem `longest-common-subsequence`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.LongestCommonSubsequence

  open Aegis.LongestCommonSubsequence (longest_common_subsequence)

  def ByteInAZ (b : Std.U8) : Prop := 97 ≤ b.val ∧ b.val ≤ 122

  def AllBytesInAZ (xs : List Std.U8) : Prop := ∀ b ∈ xs, ByteInAZ b

  def ValidInput (text1 text2 : Slice Std.U8) : Prop :=
    1 ≤ text1.val.length ∧ 1 ≤ text2.val.length ∧
      text1.val.length ≤ 1000 ∧ text2.val.length ≤ 1000 ∧
        AllBytesInAZ text1.val ∧ AllBytesInAZ text2.val

  def HasCommonSubsequence {α : Type} (xs ys : List α) (k : ℕ) : Prop :=
    ∃ i : Fin k → Fin xs.length, ∃ j : Fin k → Fin ys.length,
      (∀ a b : Fin k, a < b → i a < i b) ∧
        (∀ a b : Fin k, a < b → j a < j b) ∧
          (∀ a : Fin k, xs.get (i a) = ys.get (j a))

  def IsLCSLength {α : Type} (xs ys : List α) (k : ℕ) : Prop :=
    HasCommonSubsequence xs ys k ∧ ∀ k' : ℕ, HasCommonSubsequence xs ys k' → k' ≤ k

  noncomputable def lcsLength {α : Type} (xs ys : List α) : ℕ :=
    @Nat.findGreatest (fun k => HasCommonSubsequence xs ys k) (Classical.decPred _)
      (min xs.length ys.length)

  def IsSubsequenceOf {α : Type} (xs ys : List α) : Prop :=
    ∃ i : Fin xs.length → Fin ys.length,
      (∀ a b : Fin xs.length, a < b → i a < i b) ∧
        ∀ a : Fin xs.length, ys.get (i a) = xs.get a

  def removeAt {α : Type} (xs : List α) (p : ℕ) : List α := xs.take p ++ xs.drop (p + 1)

  def countOcc (xs : List Std.U8) (b : Std.U8) : ℕ := (xs.filter (fun x => x = b)).length

  /-- Whenever the function returns a result r, r equals the length of the longest common subsequence of text1 and text2. Formally, define LCS(X,Y) for sequences X and Y as the maximum k such that there exist strictly increasing indices 0 <= i_0 < i_1 < ... < i_{k-1} < len(X) and 0 <= j_0 < j_1 < ... < j_{k-1} < len(Y) with X[i_t] = Y[j_t] for every t with 0 <= t < k. The case k = 0 is allowed with empty index sequences, so LCS(X,Y) >= 0. Then r = LCS(text1, text2).
    Preconditions: len(text1) >= 1, len(text2) >= 1, len(text1) <= 1000, len(text2) <= 1000, and every element of text1 and text2 is in the range 97..122 inclusive (ASCII 'a'..'z'). -/
  theorem spec_1 (text1 text2 : Slice Std.U8) (hpre : ValidInput text1 text2) (r : Std.I64)
      (hres : longest_common_subsequence text1 text2 = ok r) :
      r.val = (lcsLength text1.val text2.val : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (text1 text2 : Slice Std.U8) (hpre : ValidInput text1 text2) (r : Std.I64)
        (hres : longest_common_subsequence text1 text2 = ok r), r.val = (lcsLength text1.val text2.val : ℤ)) := by
    sorry

  /-- Whenever text1 and text2 satisfy the preconditions, the function returns a result r (it does not fail, panic, or overflow).
    Preconditions: len(text1) >= 1, len(text2) >= 1, len(text1) <= 1000, len(text2) <= 1000, and every element of text1 and text2 is in the range 97..122 inclusive (ASCII 'a'..'z'). -/
  theorem spec_2 (text1 text2 : Slice Std.U8) (hpre : ValidInput text1 text2) :
      ∃ r : Std.I64, longest_common_subsequence text1 text2 = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (text1 text2 : Slice Std.U8) (hpre : ValidInput text1 text2), ∃ r : Std.I64, longest_common_subsequence text1 text2 = ok r) := by
    sorry

  /-- Whenever the function returns r, 0 <= r <= min(len(text1), len(text2)).
    Preconditions: len(text1) >= 1, len(text2) >= 1, len(text1) <= 1000, len(text2) <= 1000, and every element of text1 and text2 is in the range 97..122 inclusive (ASCII 'a'..'z'). -/
  theorem spec_3 (text1 text2 : Slice Std.U8) (hpre : ValidInput text1 text2) (r : Std.I64)
      (hres : longest_common_subsequence text1 text2 = ok r) :
      0 ≤ r.val ∧ r.val ≤ ((min text1.val.length text2.val.length : ℕ) : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (text1 text2 : Slice Std.U8) (hpre : ValidInput text1 text2) (r : Std.I64)
        (hres : longest_common_subsequence text1 text2 = ok r), 0 ≤ r.val ∧ r.val ≤ ((min text1.val.length text2.val.length : ℕ) : ℤ)) := by
    sorry

  /-- Whenever the function returns r, there exist strictly increasing indices 0 <= i_0 < ... < i_{r-1} < len(text1) and 0 <= j_0 < ... < j_{r-1} < len(text2) such that text1[i_t] = text2[j_t] for every t with 0 <= t < r. (If r = 0, both index sequences are empty.)
    Preconditions: len(text1) >= 1, len(text2) >= 1, len(text1) <= 1000, len(text2) <= 1000, and every element of text1 and text2 is in the range 97..122 inclusive (ASCII 'a'..'z'). -/
  theorem spec_4 (text1 text2 : Slice Std.U8) (hpre : ValidInput text1 text2) (r : Std.I64)
      (hres : longest_common_subsequence text1 text2 = ok r) :
      ∃ k : ℕ, (k : ℤ) = r.val ∧ HasCommonSubsequence text1.val text2.val k := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (text1 text2 : Slice Std.U8) (hpre : ValidInput text1 text2) (r : Std.I64)
        (hres : longest_common_subsequence text1 text2 = ok r), ∃ k : ℕ, (k : ℤ) = r.val ∧ HasCommonSubsequence text1.val text2.val k) := by
    sorry

  /-- Whenever the function returns r, for every k >= 0 and every pair of strictly increasing index sequences 0 <= i_0 < ... < i_{k-1} < len(text1) and 0 <= j_0 < ... < j_{k-1} < len(text2) satisfying text1[i_t] = text2[j_t] for all 0 <= t < k, we have k <= r.
    Preconditions: len(text1) >= 1, len(text2) >= 1, len(text1) <= 1000, len(text2) <= 1000, and every element of text1 and text2 is in the range 97..122 inclusive (ASCII 'a'..'z'). -/
  theorem spec_5 (text1 text2 : Slice Std.U8) (hpre : ValidInput text1 text2) (r : Std.I64)
      (hres : longest_common_subsequence text1 text2 = ok r) :
      ∀ k : ℕ, HasCommonSubsequence text1.val text2.val k → (k : ℤ) ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (text1 text2 : Slice Std.U8) (hpre : ValidInput text1 text2) (r : Std.I64)
        (hres : longest_common_subsequence text1 text2 = ok r), ∀ k : ℕ, HasCommonSubsequence text1.val text2.val k → (k : ℤ) ≤ r.val) := by
    sorry

  /-- Whenever the function returns r, r = 0 if and only if there is no pair of indices (i,j) with 0 <= i < len(text1) and 0 <= j < len(text2) such that text1[i] = text2[j].
    Preconditions: len(text1) >= 1, len(text2) >= 1, len(text1) <= 1000, len(text2) <= 1000, and every element of text1 and text2 is in the range 97..122 inclusive (ASCII 'a'..'z'). -/
  theorem spec_6 (text1 text2 : Slice Std.U8) (hpre : ValidInput text1 text2) (r : Std.I64)
      (hres : longest_common_subsequence text1 text2 = ok r) :
      (r.val = 0 ↔ ¬ ∃ (i : Fin text1.val.length) (j : Fin text2.val.length),
        text1.val.get i = text2.val.get j) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (text1 text2 : Slice Std.U8) (hpre : ValidInput text1 text2) (r : Std.I64)
        (hres : longest_common_subsequence text1 text2 = ok r), (r.val = 0 ↔ ¬ ∃ (i : Fin text1.val.length) (j : Fin text2.val.length),
          text1.val.get i = text2.val.get j)) := by
    sorry

  /-- Whenever the function returns r and the set C = { b | b occurs in text1 and b occurs in text2 } has exactly one element c, then r = min( #{ i | 0 <= i < len(text1) and text1[i] = c }, #{ j | 0 <= j < len(text2) and text2[j] = c } ), where #{ ... } denotes the number of indices satisfying the condition.
    Preconditions: len(text1) >= 1, len(text2) >= 1, len(text1) <= 1000, len(text2) <= 1000, and every element of text1 and text2 is in the range 97..122 inclusive (ASCII 'a'..'z'). -/
  theorem spec_7 (text1 text2 : Slice Std.U8) (hpre : ValidInput text1 text2) (r : Std.I64)
      (hres : longest_common_subsequence text1 text2 = ok r) (c : Std.U8)
      (hset : ∀ b : Std.U8, (b ∈ text1.val ∧ b ∈ text2.val) ↔ b = c) :
      r.val = ((min (countOcc text1.val c) (countOcc text2.val c) : ℕ) : ℤ) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (text1 text2 : Slice Std.U8) (hpre : ValidInput text1 text2) (r : Std.I64)
        (hres : longest_common_subsequence text1 text2 = ok r) (c : Std.U8)
        (hset : ∀ b : Std.U8, (b ∈ text1.val ∧ b ∈ text2.val) ↔ b = c), r.val = ((min (countOcc text1.val c) (countOcc text2.val c) : ℕ) : ℤ)) := by
    sorry

  /-- Whenever the function returns r, r = min(len(text1), len(text2)) if and only if the following holds: if len(text1) <= len(text2) then text1 is a subsequence of text2 (there exist 0 <= j_0 < ... < j_{len(text1)-1} < len(text2) with text2[j_t] = text1[t] for all 0 <= t < len(text1)); otherwise text2 is a subsequence of text1 (there exist 0 <= i_0 < ... < i_{len(text2)-1} < len(text1) with text1[i_t] = text2[t] for all 0 <= t < len(text2)).
    Preconditions: len(text1) >= 1, len(text2) >= 1, len(text1) <= 1000, len(text2) <= 1000, and every element of text1 and text2 is in the range 97..122 inclusive (ASCII 'a'..'z'). -/
  theorem spec_8 (text1 text2 : Slice Std.U8) (hpre : ValidInput text1 text2) (r : Std.I64)
      (hres : longest_common_subsequence text1 text2 = ok r) :
      (r.val = ((min text1.val.length text2.val.length : ℕ) : ℤ) ↔
        ((text1.val.length ≤ text2.val.length → IsSubsequenceOf text1.val text2.val) ∧
          (text2.val.length < text1.val.length → IsSubsequenceOf text2.val text1.val))) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (text1 text2 : Slice Std.U8) (hpre : ValidInput text1 text2) (r : Std.I64)
        (hres : longest_common_subsequence text1 text2 = ok r), (r.val = ((min text1.val.length text2.val.length : ℕ) : ℤ) ↔
          ((text1.val.length ≤ text2.val.length → IsSubsequenceOf text1.val text2.val) ∧
            (text2.val.length < text1.val.length → IsSubsequenceOf text2.val text1.val)))) := by
    sorry

  /-- Whenever the function returns r, r also equals the length of the longest common subsequence of text2 and text1, where the roles of the two sequences are exchanged: the maximal k such that there exist strictly increasing indices 0 <= j_0 < ... < j_{k-1} < len(text2) and 0 <= i_0 < ... < i_{k-1} < len(text1) with text2[j_t] = text1[i_t] for every 0 <= t < k.
    Preconditions: len(text1) >= 1, len(text2) >= 1, len(text1) <= 1000, len(text2) <= 1000, and every element of text1 and text2 is in the range 97..122 inclusive (ASCII 'a'..'z'). -/
  theorem spec_9 (text1 text2 : Slice Std.U8) (hpre : ValidInput text1 text2) (r : Std.I64)
      (hres : longest_common_subsequence text1 text2 = ok r) :
      r.val = (lcsLength text2.val text1.val : ℤ) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (text1 text2 : Slice Std.U8) (hpre : ValidInput text1 text2) (r : Std.I64)
        (hres : longest_common_subsequence text1 text2 = ok r), r.val = (lcsLength text2.val text1.val : ℤ)) := by
    sorry

  /-- Whenever the function returns r, for every index p with 0 <= p < len(text1), let u be the sequence of length len(text1)-1 defined by u[t] = text1[t] for 0 <= t < p and u[t] = text1[t+1] for p <= t < len(text1)-1. Then the longest common subsequence of u and text2 has length r' with r - 1 <= r' <= r.
    Preconditions: len(text1) >= 1, len(text2) >= 1, len(text1) <= 1000, len(text2) <= 1000, and every element of text1 and text2 is in the range 97..122 inclusive (ASCII 'a'..'z'). -/
  theorem spec_10 (text1 text2 : Slice Std.U8) (hpre : ValidInput text1 text2) (r : Std.I64)
      (hres : longest_common_subsequence text1 text2 = ok r) :
      ∀ p : Fin text1.val.length,
        r.val - 1 ≤ (lcsLength (removeAt text1.val p.val) text2.val : ℤ) ∧
          (lcsLength (removeAt text1.val p.val) text2.val : ℤ) ≤ r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (text1 text2 : Slice Std.U8) (hpre : ValidInput text1 text2) (r : Std.I64)
        (hres : longest_common_subsequence text1 text2 = ok r), ∀ p : Fin text1.val.length,
          r.val - 1 ≤ (lcsLength (removeAt text1.val p.val) text2.val : ℤ) ∧
            (lcsLength (removeAt text1.val p.val) text2.val : ℤ) ≤ r.val) := by
    sorry

  /-- Whenever the function returns r, for every byte b with 0 <= b <= 255, let v be the sequence of length len(text1)+1 defined by v[t] = text1[t] for 0 <= t < len(text1) and v[len(text1)] = b. Then the longest common subsequence of v and text2 has length r'' with r <= r'' <= r + 1.
    Preconditions: len(text1) >= 1, len(text2) >= 1, len(text1) <= 1000, len(text2) <= 1000, and every element of text1 and text2 is in the range 97..122 inclusive (ASCII 'a'..'z'). -/
  theorem spec_11 (text1 text2 : Slice Std.U8) (hpre : ValidInput text1 text2) (r : Std.I64)
      (hres : longest_common_subsequence text1 text2 = ok r) :
      ∀ b : Std.U8,
        r.val ≤ (lcsLength (text1.val ++ [b]) text2.val : ℤ) ∧
          (lcsLength (text1.val ++ [b]) text2.val : ℤ) ≤ r.val + 1 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (text1 text2 : Slice Std.U8) (hpre : ValidInput text1 text2) (r : Std.I64)
        (hres : longest_common_subsequence text1 text2 = ok r), ∀ b : Std.U8,
          r.val ≤ (lcsLength (text1.val ++ [b]) text2.val : ℤ) ∧
            (lcsLength (text1.val ++ [b]) text2.val : ℤ) ≤ r.val + 1) := by
    sorry

  /-- Whenever the function returns r, let rev(text1) be the sequence of length len(text1) with rev(text1)[i] = text1[len(text1)-1-i] for 0 <= i < len(text1), and define rev(text2) analogously. Then r equals the length of the longest common subsequence of rev(text1) and rev(text2).
    Preconditions: len(text1) >= 1, len(text2) >= 1, len(text1) <= 1000, len(text2) <= 1000, and every element of text1 and text2 is in the range 97..122 inclusive (ASCII 'a'..'z'). -/
  theorem spec_12 (text1 text2 : Slice Std.U8) (hpre : ValidInput text1 text2) (r : Std.I64)
      (hres : longest_common_subsequence text1 text2 = ok r) :
      r.val = (lcsLength text1.val.reverse text2.val.reverse : ℤ) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (text1 text2 : Slice Std.U8) (hpre : ValidInput text1 text2) (r : Std.I64)
        (hres : longest_common_subsequence text1 text2 = ok r), r.val = (lcsLength text1.val.reverse text2.val.reverse : ℤ)) := by
    sorry

  /-- Whenever the function returns r, if there exists an index p with 0 <= p < len(text1) such that text1[p] does not occur in text2 (i.e., text2[j] != text1[p] for all 0 <= j < len(text2)), then let u be the sequence of length len(text1)-1 obtained from text1 by deleting position p (u[t] = text1[t] for 0 <= t < p, and u[t] = text1[t+1] for p <= t < len(text1)-1). Then the longest common subsequence of u and text2 also has length r.
    Preconditions: len(text1) >= 1, len(text2) >= 1, len(text1) <= 1000, len(text2) <= 1000, and every element of text1 and text2 is in the range 97..122 inclusive (ASCII 'a'..'z'). -/
  theorem spec_13 (text1 text2 : Slice Std.U8) (hpre : ValidInput text1 text2) (r : Std.I64)
      (hres : longest_common_subsequence text1 text2 = ok r) :
      ∀ p : Fin text1.val.length,
        (∀ j : Fin text2.val.length, text2.val.get j ≠ text1.val.get p) →
          (lcsLength (removeAt text1.val p.val) text2.val : ℤ) = r.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (text1 text2 : Slice Std.U8) (hpre : ValidInput text1 text2) (r : Std.I64)
        (hres : longest_common_subsequence text1 text2 = ok r), ∀ p : Fin text1.val.length,
          (∀ j : Fin text2.val.length, text2.val.get j ≠ text1.val.get p) →
            (lcsLength (removeAt text1.val p.val) text2.val : ℤ) = r.val) := by
    sorry

  /-- Whenever the function returns r, for every k with 0 <= k <= r there exist strictly increasing indices 0 <= i_0 < ... < i_{k-1} < len(text1) and 0 <= j_0 < ... < j_{k-1} < len(text2) such that text1[i_t] = text2[j_t] for every t with 0 <= t < k.
    Preconditions: len(text1) >= 1, len(text2) >= 1, len(text1) <= 1000, len(text2) <= 1000, and every element of text1 and text2 is in the range 97..122 inclusive (ASCII 'a'..'z'). -/
  theorem spec_14 (text1 text2 : Slice Std.U8) (hpre : ValidInput text1 text2) (r : Std.I64)
      (hres : longest_common_subsequence text1 text2 = ok r) :
      ∀ k : ℕ, (k : ℤ) ≤ r.val → HasCommonSubsequence text1.val text2.val k := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (text1 text2 : Slice Std.U8) (hpre : ValidInput text1 text2) (r : Std.I64)
        (hres : longest_common_subsequence text1 text2 = ok r), ∀ k : ℕ, (k : ℤ) ≤ r.val → HasCommonSubsequence text1.val text2.val k) := by
    sorry

  end AegisSpec.LongestCommonSubsequence

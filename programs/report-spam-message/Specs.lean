import Aegis.ReportSpam.Code.Funs

/-!
# Specifications of `Aegis.ReportSpam.report_spam`

LeetCode problem `report-spam-message`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.ReportSpam

def ByteEq (w₁ w₂ : alloc.vec.Vec Std.U8) : Prop :=
  w₁.val.map (fun b => b.val) = w₂.val.map (fun b => b.val)

def ValidWord (w : alloc.vec.Vec Std.U8) : Prop :=
  1 ≤ w.val.length ∧ w.val.length ≤ 15 ∧ ∀ b ∈ w.val, 97 ≤ b.val ∧ b.val ≤ 122

def ValidSlice (s : Slice (alloc.vec.Vec Std.U8)) : Prop :=
  1 ≤ s.val.length ∧ s.val.length ≤ 100000 ∧ ∀ w ∈ s.val, ValidWord w

def Inputs (message bannedWords : Slice (alloc.vec.Vec Std.U8)) : Prop :=
  ValidSlice message ∧ ValidSlice bannedWords

def BannedMatch (bannedWords : Slice (alloc.vec.Vec Std.U8)) (w : alloc.vec.Vec Std.U8) : Prop :=
  ∃ (j : Nat) (hj : j < bannedWords.val.length),
    ByteEq w (bannedWords.val.get ⟨j, hj⟩)

def BannedAt (bannedWords message : Slice (alloc.vec.Vec Std.U8)) (i : Nat) : Prop :=
  ∃ (hi : i < message.val.length), BannedMatch bannedWords (message.val.get ⟨i, hi⟩)

noncomputable def matchingWords (message bannedWords : Slice (alloc.vec.Vec Std.U8)) :
    List (alloc.vec.Vec Std.U8) := by
  classical
  exact message.val.filter (fun w => decide (BannedMatch bannedWords w))

noncomputable def matchCount (message bannedWords : Slice (alloc.vec.Vec Std.U8)) : Nat := by
  classical
  exact (message.val.filter (fun w => decide (BannedMatch bannedWords w))).length

def PermByByteEq (l₁ l₂ : List (alloc.vec.Vec Std.U8)) : Prop :=
  List.Perm (l₁.map (fun w => w.val.map (fun b => b.val)))
    (l₂.map (fun w => w.val.map (fun b => b.val)))

def SubseqByByteEq (l₁ l₂ : List (alloc.vec.Vec Std.U8)) : Prop :=
  List.Sublist (l₁.map (fun w => w.val.map (fun b => b.val)))
    (l₂.map (fun w => w.val.map (fun b => b.val)))

/-- The function returns a result r and does not fail. Let C be the number of indices i with 0 <= i < len(message) such that there exists an index j with 0 <= j < len(bannedWords) for which message[i] is byte-equal to bannedWords[j], where byte-equal means same length and same byte at every index. Then r = true if and only if C >= 2; otherwise r = false.
  Preconditions: The problem constraints hold: 1 <= len(message) <= 100000 and 1 <= len(bannedWords) <= 100000; every word in message and bannedWords has length between 1 and 15 and consists only of lowercase ASCII letters (bytes 97 through 122). -/
theorem spec_1 (message bannedWords : Slice (alloc.vec.Vec Std.U8))
    (h : Inputs message bannedWords) :
    ∃ r : Bool, Aegis.ReportSpam.report_spam message bannedWords = ok r ∧
      (r = true ↔ 2 ≤ matchCount message bannedWords) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (message bannedWords : Slice (alloc.vec.Vec Std.U8))
    (h : Inputs message bannedWords), ∃ r : Bool, Aegis.ReportSpam.report_spam message bannedWords = ok r ∧
      (r = true ↔ 2 ≤ matchCount message bannedWords)) := by
  sorry

/-- The function returns a Boolean result and does not fail: no arithmetic overflow, no out-of-bounds access, and no panic occurs.
  Preconditions: The problem constraints hold: 1 <= len(message) <= 100000 and 1 <= len(bannedWords) <= 100000; every word in message and bannedWords has length between 1 and 15 and consists only of lowercase ASCII letters (bytes 97 through 122). -/
theorem spec_2 (message bannedWords : Slice (alloc.vec.Vec Std.U8))
    (h : Inputs message bannedWords) :
    ∃ r : Bool, Aegis.ReportSpam.report_spam message bannedWords = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (message bannedWords : Slice (alloc.vec.Vec Std.U8))
    (h : Inputs message bannedWords), ∃ r : Bool, Aegis.ReportSpam.report_spam message bannedWords = ok r) := by
  sorry

/-- Whenever the function returns a result r with r = true, we have len(message) >= 2.
  Preconditions: The problem constraints hold: 1 <= len(message) <= 100000 and 1 <= len(bannedWords) <= 100000; every word in message and bannedWords has length between 1 and 15 and consists only of lowercase ASCII letters (bytes 97 through 122). -/
theorem spec_3 (message bannedWords : Slice (alloc.vec.Vec Std.U8))
    (h : Inputs message bannedWords) (r : Bool)
    (hr : Aegis.ReportSpam.report_spam message bannedWords = ok r) (hr_true : r = true) :
    2 ≤ message.val.length := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (message bannedWords : Slice (alloc.vec.Vec Std.U8))
    (h : Inputs message bannedWords) (r : Bool)
    (hr : Aegis.ReportSpam.report_spam message bannedWords = ok r) (hr_true : r = true), 2 ≤ message.val.length) := by
  sorry

/-- Whenever the function returns a result r with r = true, there exist two distinct indices i and k with 0 <= i < k < len(message) and indices p and q with 0 <= p < len(bannedWords) and 0 <= q < len(bannedWords) such that message[i] is byte-equal to bannedWords[p] and message[k] is byte-equal to bannedWords[q].
  Preconditions: The problem constraints hold: 1 <= len(message) <= 100000 and 1 <= len(bannedWords) <= 100000; every word in message and bannedWords has length between 1 and 15 and consists only of lowercase ASCII letters (bytes 97 through 122). -/
theorem spec_4 (message bannedWords : Slice (alloc.vec.Vec Std.U8))
    (h : Inputs message bannedWords) (r : Bool)
    (hr : Aegis.ReportSpam.report_spam message bannedWords = ok r) (hr_true : r = true) :
    ∃ (i k p q : Nat) (hi : i < message.val.length) (hk : k < message.val.length)
      (hp : p < bannedWords.val.length) (hq : q < bannedWords.val.length),
      i < k ∧
      ByteEq (message.val.get ⟨i, hi⟩) (bannedWords.val.get ⟨p, hp⟩) ∧
      ByteEq (message.val.get ⟨k, hk⟩) (bannedWords.val.get ⟨q, hq⟩) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (message bannedWords : Slice (alloc.vec.Vec Std.U8))
    (h : Inputs message bannedWords) (r : Bool)
    (hr : Aegis.ReportSpam.report_spam message bannedWords = ok r) (hr_true : r = true), ∃ (i k p q : Nat) (hi : i < message.val.length) (hk : k < message.val.length)
      (hp : p < bannedWords.val.length) (hq : q < bannedWords.val.length),
      i < k ∧
      ByteEq (message.val.get ⟨i, hi⟩) (bannedWords.val.get ⟨p, hp⟩) ∧
      ByteEq (message.val.get ⟨k, hk⟩) (bannedWords.val.get ⟨q, hq⟩)) := by
  sorry

/-- Whenever the function returns a result r with r = false, for every pair of distinct indices i and k with 0 <= i < k < len(message), it is not the case that both message[i] matches some word of bannedWords and message[k] matches some word of bannedWords. Equivalently, at most one message position is banned-matching.
  Preconditions: The problem constraints hold: 1 <= len(message) <= 100000 and 1 <= len(bannedWords) <= 100000; every word in message and bannedWords has length between 1 and 15 and consists only of lowercase ASCII letters (bytes 97 through 122). -/
theorem spec_5 (message bannedWords : Slice (alloc.vec.Vec Std.U8))
    (h : Inputs message bannedWords) (r : Bool)
    (hr : Aegis.ReportSpam.report_spam message bannedWords = ok r) (hr_false : r = false) :
    ∀ (i k : Nat), i < k → k < message.val.length →
      ¬ (BannedAt bannedWords message i ∧ BannedAt bannedWords message k) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (message bannedWords : Slice (alloc.vec.Vec Std.U8))
    (h : Inputs message bannedWords) (r : Bool)
    (hr : Aegis.ReportSpam.report_spam message bannedWords = ok r) (hr_false : r = false), ∀ (i k : Nat), i < k → k < message.val.length →
      ¬ (BannedAt bannedWords message i ∧ BannedAt bannedWords message k)) := by
  sorry

/-- The Boolean result of the function on (message, b2) is the same as the Boolean result on (message, bannedWords).
  Preconditions: The problem constraints hold for message and bannedWords; let b2 be any slice of byte-vectors satisfying the same constraints as bannedWords and being a permutation of bannedWords (same length and the same multiset of byte-equal words). -/
theorem spec_6 (message bannedWords b2 : Slice (alloc.vec.Vec Std.U8))
    (h : Inputs message bannedWords) (h2 : ValidSlice b2)
    (hperm : PermByByteEq bannedWords.val b2.val) (r r2 : Bool)
    (hr : Aegis.ReportSpam.report_spam message bannedWords = ok r)
    (hr2 : Aegis.ReportSpam.report_spam message b2 = ok r2) :
    r = r2 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (message bannedWords b2 : Slice (alloc.vec.Vec Std.U8))
    (h : Inputs message bannedWords) (h2 : ValidSlice b2)
    (hperm : PermByByteEq bannedWords.val b2.val) (r r2 : Bool)
    (hr : Aegis.ReportSpam.report_spam message bannedWords = ok r)
    (hr2 : Aegis.ReportSpam.report_spam message b2 = ok r2), r = r2) := by
  sorry

/-- The Boolean result of the function on (m2, bannedWords) is the same as the Boolean result on (message, bannedWords).
  Preconditions: The problem constraints hold for message and bannedWords; let m2 be any slice of byte-vectors satisfying the same constraints as message and being a permutation of message (same length and the same multiset of byte-equal words). -/
theorem spec_7 (message m2 bannedWords : Slice (alloc.vec.Vec Std.U8))
    (h : Inputs message bannedWords) (h2 : ValidSlice m2)
    (hperm : PermByByteEq message.val m2.val) (r r2 : Bool)
    (hr : Aegis.ReportSpam.report_spam message bannedWords = ok r)
    (hr2 : Aegis.ReportSpam.report_spam m2 bannedWords = ok r2) :
    r = r2 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (message m2 bannedWords : Slice (alloc.vec.Vec Std.U8))
    (h : Inputs message bannedWords) (h2 : ValidSlice m2)
    (hperm : PermByByteEq message.val m2.val) (r r2 : Bool)
    (hr : Aegis.ReportSpam.report_spam message bannedWords = ok r)
    (hr2 : Aegis.ReportSpam.report_spam m2 bannedWords = ok r2), r = r2) := by
  sorry

/-- If the function on (message, bannedWords) returns true, then the function on (message, b2) returns true.
  Preconditions: The problem constraints hold for message, bannedWords, and b2, and b2 contains every word of bannedWords up to byte-equality: for every j with 0 <= j < len(bannedWords), there exists q with 0 <= q < len(b2) such that bannedWords[j] is byte-equal to b2[q]. -/
theorem spec_8 (message bannedWords b2 : Slice (alloc.vec.Vec Std.U8))
    (h : Inputs message bannedWords) (h2 : ValidSlice b2)
    (hcov : ∀ (j : Nat) (hj : j < bannedWords.val.length),
      ∃ (q : Nat) (hq : q < b2.val.length),
        ByteEq (bannedWords.val.get ⟨j, hj⟩) (b2.val.get ⟨q, hq⟩))
    (r : Bool) (hr : Aegis.ReportSpam.report_spam message bannedWords = ok r)
    (hr_true : r = true) :
    ∃ r2 : Bool, Aegis.ReportSpam.report_spam message b2 = ok r2 ∧ r2 = true := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (message bannedWords b2 : Slice (alloc.vec.Vec Std.U8))
    (h : Inputs message bannedWords) (h2 : ValidSlice b2)
    (hcov : ∀ (j : Nat) (hj : j < bannedWords.val.length),
      ∃ (q : Nat) (hq : q < b2.val.length),
        ByteEq (bannedWords.val.get ⟨j, hj⟩) (b2.val.get ⟨q, hq⟩))
    (r : Bool) (hr : Aegis.ReportSpam.report_spam message bannedWords = ok r)
    (hr_true : r = true), ∃ r2 : Bool, Aegis.ReportSpam.report_spam message b2 = ok r2 ∧ r2 = true) := by
  sorry

/-- Whenever both function calls return results, the Boolean result on (message, bannedWords) equals the Boolean result on (m2, bannedWords).
  Preconditions: The problem constraints hold. Let m2 be the subsequence of message consisting exactly of those entries message[i] for which there exists j with 0 <= j < len(bannedWords) and message[i] byte-equal to bannedWords[j], kept in their original order. -/
theorem spec_9 (message m2 bannedWords : Slice (alloc.vec.Vec Std.U8))
    (h : Inputs message bannedWords)
    (hm2 : m2.val = matchingWords message bannedWords) (r r2 : Bool)
    (hr : Aegis.ReportSpam.report_spam message bannedWords = ok r)
    (hr2 : Aegis.ReportSpam.report_spam m2 bannedWords = ok r2) :
    r = r2 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (message m2 bannedWords : Slice (alloc.vec.Vec Std.U8))
    (h : Inputs message bannedWords)
    (hm2 : m2.val = matchingWords message bannedWords) (r r2 : Bool)
    (hr : Aegis.ReportSpam.report_spam message bannedWords = ok r)
    (hr2 : Aegis.ReportSpam.report_spam m2 bannedWords = ok r2), r = r2) := by
  sorry

/-- If the function on (message, bannedWords) returns true, then the function on (m2, bannedWords) returns true.
  Preconditions: The problem constraints hold for message and m2, and message is a subsequence of m2 (m2 is obtained from message by inserting additional words). -/
theorem spec_10 (message m2 bannedWords : Slice (alloc.vec.Vec Std.U8))
    (h : Inputs message bannedWords) (h2 : ValidSlice m2)
    (hsub : SubseqByByteEq message.val m2.val)
    (r : Bool) (hr : Aegis.ReportSpam.report_spam message bannedWords = ok r)
    (hr_true : r = true) :
    ∃ r2 : Bool, Aegis.ReportSpam.report_spam m2 bannedWords = ok r2 ∧ r2 = true := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (message m2 bannedWords : Slice (alloc.vec.Vec Std.U8))
    (h : Inputs message bannedWords) (h2 : ValidSlice m2)
    (hsub : SubseqByByteEq message.val m2.val)
    (r : Bool) (hr : Aegis.ReportSpam.report_spam message bannedWords = ok r)
    (hr_true : r = true), ∃ r2 : Bool, Aegis.ReportSpam.report_spam m2 bannedWords = ok r2 ∧ r2 = true) := by
  sorry

end AegisSpec.ReportSpam

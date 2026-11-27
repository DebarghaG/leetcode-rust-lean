import Aegis.ReorderLogFiles.Code.Funs

/-!
# Specifications of `Aegis.ReorderLogFiles.reorder_log_files`

LeetCode problem `reorder-data-in-log-files`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.ReorderLogFiles

def spaceByte : Nat := 32

def isLowerByte (c : Nat) : Prop := 97 ≤ c ∧ c ≤ 122

def isDigitByte (c : Nat) : Prop := 48 ≤ c ∧ c ≤ 57

def IsToken (w : List Nat) : Prop := w ≠ [] ∧ ∀ c ∈ w, c ≠ spaceByte

def IsTokenSeq (ws : List (List Nat)) : Prop := ws ≠ [] ∧ ∀ w ∈ ws, IsToken w

def IsLowerWordSeq (ws : List (List Nat)) : Prop :=
  ws ≠ [] ∧ ∀ w ∈ ws, IsToken w ∧ ∀ c ∈ w, isLowerByte c

def IsDigitWordSeq (ws : List (List Nat)) : Prop :=
  ws ≠ [] ∧ ∀ w ∈ ws, IsToken w ∧ ∀ c ∈ w, isDigitByte c

def joinWithSpace : List (List Nat) → List Nat
  | [] => []
  | [w] => w
  | w :: w' :: ws => w ++ spaceByte :: joinWithSpace (w' :: ws)

def IsWellFormedLog (l : List Nat) : Prop :=
  ∃ (id : List Nat) (ws : List (List Nat)),
    IsToken id ∧ IsTokenSeq ws ∧
      (∀ w ∈ ws, (∀ c ∈ w, isLowerByte c) ∨ (∀ c ∈ w, isDigitByte c)) ∧
      ((∀ w ∈ ws, ∀ c ∈ w, isLowerByte c) ∨ (∀ w ∈ ws, ∀ c ∈ w, isDigitByte c)) ∧
      l = id ++ spaceByte :: joinWithSpace ws

def IsLetterLog (l : List Nat) : Prop :=
  ∃ (id : List Nat) (ws : List (List Nat)),
    IsToken id ∧ IsLowerWordSeq ws ∧ l = id ++ spaceByte :: joinWithSpace ws

def IsDigitLog (l : List Nat) : Prop :=
  ∃ (id : List Nat) (ws : List (List Nat)),
    IsToken id ∧ IsDigitWordSeq ws ∧ l = id ++ spaceByte :: joinWithSpace ws

def bytes (x : alloc.vec.Vec Std.U8) : List Nat := x.val.map (fun b => b.val)

def idBytes (l : List Nat) : List Nat := l.takeWhile (fun c => decide (c ≠ spaceByte))

def bodyBytes (l : List Nat) : List Nat :=
  (l.dropWhile (fun c => decide (c ≠ spaceByte))).drop 1

def entryBytes : List (alloc.vec.Vec Std.U8) → Nat → List Nat
  | [], _ => []
  | x :: _, 0 => bytes x
  | _ :: rest, k + 1 => entryBytes rest k

def lexLt : List Nat → List Nat → Prop
  | [], [] => False
  | [], _ :: _ => True
  | _ :: _, [] => False
  | a :: al, b :: bl => a < b ∨ (a = b ∧ lexLt al bl)

def lexLe (a b : List Nat) : Prop := lexLt a b ∨ a = b

def countOcc (x : List Nat) : List (List Nat) → Nat
  | [] => 0
  | y :: rest => (if y = x then 1 else 0) + countOcc x rest

def SameMultiset (l₁ l₂ : List (List Nat)) : Prop := ∀ x, countOcc x l₁ = countOcc x l₂

noncomputable def filterProp (p : alloc.vec.Vec Std.U8 → Prop) :
    List (alloc.vec.Vec Std.U8) → List (alloc.vec.Vec Std.U8)
  | [] => []
  | x :: rest =>
    match Classical.dec (p x) with
    | isTrue _ => x :: filterProp p rest
    | isFalse _ => filterProp p rest

noncomputable def letterLogs (l : List (alloc.vec.Vec Std.U8)) : List (alloc.vec.Vec Std.U8) :=
  filterProp (fun x => IsLetterLog (bytes x)) l

noncomputable def digitLogs (l : List (alloc.vec.Vec Std.U8)) : List (alloc.vec.Vec Std.U8) :=
  filterProp (fun x => IsDigitLog (bytes x)) l

/-- Whenever reorder_log_files returns a result r, it satisfies the following. Let n = len(logs). For a log x, let id(x) be the byte string before its first space and body(x) be the byte string after its first space. Let L be the number of indices i with 0 <= i < n such that logs[i] is a letter-log. Then len(r) = n; the multiset of entries r[0],...,r[L-1] is exactly the multiset of all letter-logs in logs; for every k with 0 <= k < L, r[k] is a letter-log; for every k with L <= k < n, r[k] is a digit-log; for all i,j with 0 <= i < j < L, either body(r[i]) <_lex body(r[j]), or body(r[i]) = body(r[j]) and id(r[i]) <=_lex id(r[j]); and the sequence r[L],...,r[n-1] is exactly the sequence of digit-logs of logs in their original order, i.e. logs[j] for j in increasing order such that logs[j] is a digit-log. Here <_lex and <=_lex denote standard byte-wise lexicographic order.
  Preconditions: logs is a non-empty slice of byte-vector strings with 1 <= len(logs) <= 100; each log has length between 3 and 100; each log consists of an identifier followed by a single space and at least one word, with tokens separated by single spaces; for each log, every non-identifier word consists entirely of lowercase English letters (a-z) or entirely of digits (0-9), and all non-identifier words of that log are of the same kind. Thus each log is either a letter-log or a digit-log. -/
theorem spec_1
    (logs : Slice (alloc.vec.Vec Std.U8))
    (h_nonempty : 1 ≤ logs.val.length)
    (h_max : logs.val.length ≤ 100)
    (h_size : ∀ x ∈ logs.val, 3 ≤ x.val.length ∧ x.val.length ≤ 100)
    (h_wf : ∀ x ∈ logs.val, IsWellFormedLog (bytes x)) :
    ∀ r, Aegis.ReorderLogFiles.reorder_log_files logs = ok r →
      let n := logs.val.length
      let L := (letterLogs logs.val).length
      r.val.length = n ∧
      SameMultiset ((r.val.take L).map bytes) ((letterLogs logs.val).map bytes) ∧
      (∀ k, k < L → IsLetterLog (entryBytes r.val k)) ∧
      (∀ k, L ≤ k → k < n → IsDigitLog (entryBytes r.val k)) ∧
      (∀ i j, i < j → j < L →
        lexLt (bodyBytes (entryBytes r.val i)) (bodyBytes (entryBytes r.val j)) ∨
          (bodyBytes (entryBytes r.val i) = bodyBytes (entryBytes r.val j) ∧
            lexLe (idBytes (entryBytes r.val i)) (idBytes (entryBytes r.val j)))) ∧
      (∀ k, k < (digitLogs logs.val).length →
        entryBytes r.val (L + k) = entryBytes (digitLogs logs.val) k) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (logs : Slice (alloc.vec.Vec Std.U8))
    (h_nonempty : 1 ≤ logs.val.length)
    (h_max : logs.val.length ≤ 100)
    (h_size : ∀ x ∈ logs.val, 3 ≤ x.val.length ∧ x.val.length ≤ 100)
    (h_wf : ∀ x ∈ logs.val, IsWellFormedLog (bytes x)), ∀ r, Aegis.ReorderLogFiles.reorder_log_files logs = ok r →
      let n := logs.val.length
      let L := (letterLogs logs.val).length
      r.val.length = n ∧
      SameMultiset ((r.val.take L).map bytes) ((letterLogs logs.val).map bytes) ∧
      (∀ k, k < L → IsLetterLog (entryBytes r.val k)) ∧
      (∀ k, L ≤ k → k < n → IsDigitLog (entryBytes r.val k)) ∧
      (∀ i j, i < j → j < L →
        lexLt (bodyBytes (entryBytes r.val i)) (bodyBytes (entryBytes r.val j)) ∨
          (bodyBytes (entryBytes r.val i) = bodyBytes (entryBytes r.val j) ∧
            lexLe (idBytes (entryBytes r.val i)) (idBytes (entryBytes r.val j)))) ∧
      (∀ k, k < (digitLogs logs.val).length →
        entryBytes r.val (L + k) = entryBytes (digitLogs logs.val) k)) := by
  sorry

/-- Under the preconditions, the function returns a result r and does not fail: there is no panic, out-of-bounds access, arithmetic overflow, or error result.
  Preconditions: logs is a non-empty slice of byte-vector strings with 1 <= len(logs) <= 100; each log has length between 3 and 100; each log consists of an identifier followed by a single space and at least one word, with tokens separated by single spaces; for each log, every non-identifier word consists entirely of lowercase English letters (a-z) or entirely of digits (0-9), and all non-identifier words of that log are of the same kind. Thus each log is either a letter-log or a digit-log. -/
theorem spec_2
    (logs : Slice (alloc.vec.Vec Std.U8))
    (h_nonempty : 1 ≤ logs.val.length)
    (h_max : logs.val.length ≤ 100)
    (h_size : ∀ x ∈ logs.val, 3 ≤ x.val.length ∧ x.val.length ≤ 100)
    (h_wf : ∀ x ∈ logs.val, IsWellFormedLog (bytes x)) :
    ∃ r, Aegis.ReorderLogFiles.reorder_log_files logs = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (logs : Slice (alloc.vec.Vec Std.U8))
    (h_nonempty : 1 ≤ logs.val.length)
    (h_max : logs.val.length ≤ 100)
    (h_size : ∀ x ∈ logs.val, 3 ≤ x.val.length ∧ x.val.length ≤ 100)
    (h_wf : ∀ x ∈ logs.val, IsWellFormedLog (bytes x)), ∃ r, Aegis.ReorderLogFiles.reorder_log_files logs = ok r) := by
  sorry

/-- Whenever reorder_log_files returns a result r, len(r) = len(logs).
  Preconditions: logs is a non-empty slice of byte-vector strings with 1 <= len(logs) <= 100; each log has length between 3 and 100; each log consists of an identifier followed by a single space and at least one word, with tokens separated by single spaces; for each log, every non-identifier word consists entirely of lowercase English letters (a-z) or entirely of digits (0-9), and all non-identifier words of that log are of the same kind. Thus each log is either a letter-log or a digit-log. -/
theorem spec_3
    (logs : Slice (alloc.vec.Vec Std.U8))
    (h_nonempty : 1 ≤ logs.val.length)
    (h_max : logs.val.length ≤ 100)
    (h_size : ∀ x ∈ logs.val, 3 ≤ x.val.length ∧ x.val.length ≤ 100)
    (h_wf : ∀ x ∈ logs.val, IsWellFormedLog (bytes x)) :
    ∀ r, Aegis.ReorderLogFiles.reorder_log_files logs = ok r →
      r.val.length = logs.val.length := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (logs : Slice (alloc.vec.Vec Std.U8))
    (h_nonempty : 1 ≤ logs.val.length)
    (h_max : logs.val.length ≤ 100)
    (h_size : ∀ x ∈ logs.val, 3 ≤ x.val.length ∧ x.val.length ≤ 100)
    (h_wf : ∀ x ∈ logs.val, IsWellFormedLog (bytes x)), ∀ r, Aegis.ReorderLogFiles.reorder_log_files logs = ok r →
      r.val.length = logs.val.length) := by
  sorry

/-- Whenever reorder_log_files returns a result r, for every byte-vector x, the number of indices i with 0 <= i < len(r) and r[i] = x equals the number of indices j with 0 <= j < len(logs) and logs[j] = x. Equivalently, r is a permutation of logs as a multiset.
  Preconditions: logs is a non-empty slice of byte-vector strings with 1 <= len(logs) <= 100; each log has length between 3 and 100; each log consists of an identifier followed by a single space and at least one word, with tokens separated by single spaces; for each log, every non-identifier word consists entirely of lowercase English letters (a-z) or entirely of digits (0-9), and all non-identifier words of that log are of the same kind. Thus each log is either a letter-log or a digit-log. -/
theorem spec_4
    (logs : Slice (alloc.vec.Vec Std.U8))
    (h_nonempty : 1 ≤ logs.val.length)
    (h_max : logs.val.length ≤ 100)
    (h_size : ∀ x ∈ logs.val, 3 ≤ x.val.length ∧ x.val.length ≤ 100)
    (h_wf : ∀ x ∈ logs.val, IsWellFormedLog (bytes x)) :
    ∀ r, Aegis.ReorderLogFiles.reorder_log_files logs = ok r →
      ∀ x : alloc.vec.Vec Std.U8,
        countOcc (bytes x) (r.val.map bytes) = countOcc (bytes x) (logs.val.map bytes) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (logs : Slice (alloc.vec.Vec Std.U8))
    (h_nonempty : 1 ≤ logs.val.length)
    (h_max : logs.val.length ≤ 100)
    (h_size : ∀ x ∈ logs.val, 3 ≤ x.val.length ∧ x.val.length ≤ 100)
    (h_wf : ∀ x ∈ logs.val, IsWellFormedLog (bytes x)), ∀ r, Aegis.ReorderLogFiles.reorder_log_files logs = ok r →
      ∀ x : alloc.vec.Vec Std.U8,
        countOcc (bytes x) (r.val.map bytes) = countOcc (bytes x) (logs.val.map bytes)) := by
  sorry

/-- Whenever reorder_log_files returns a result r, let L be the number of letter-logs in logs. Then len(r) = len(logs), and for every index i: if 0 <= i < L then r[i] is a letter-log; if L <= i < len(r) then r[i] is a digit-log.
  Preconditions: logs is a non-empty slice of byte-vector strings with 1 <= len(logs) <= 100; each log has length between 3 and 100; each log consists of an identifier followed by a single space and at least one word, with tokens separated by single spaces; for each log, every non-identifier word consists entirely of lowercase English letters (a-z) or entirely of digits (0-9), and all non-identifier words of that log are of the same kind. Thus each log is either a letter-log or a digit-log. -/
theorem spec_5
    (logs : Slice (alloc.vec.Vec Std.U8))
    (h_nonempty : 1 ≤ logs.val.length)
    (h_max : logs.val.length ≤ 100)
    (h_size : ∀ x ∈ logs.val, 3 ≤ x.val.length ∧ x.val.length ≤ 100)
    (h_wf : ∀ x ∈ logs.val, IsWellFormedLog (bytes x)) :
    ∀ r, Aegis.ReorderLogFiles.reorder_log_files logs = ok r →
      let L := (letterLogs logs.val).length
      r.val.length = logs.val.length ∧
      (∀ i, i < L → IsLetterLog (entryBytes r.val i)) ∧
      (∀ i, L ≤ i → i < r.val.length → IsDigitLog (entryBytes r.val i)) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (logs : Slice (alloc.vec.Vec Std.U8))
    (h_nonempty : 1 ≤ logs.val.length)
    (h_max : logs.val.length ≤ 100)
    (h_size : ∀ x ∈ logs.val, 3 ≤ x.val.length ∧ x.val.length ≤ 100)
    (h_wf : ∀ x ∈ logs.val, IsWellFormedLog (bytes x)), ∀ r, Aegis.ReorderLogFiles.reorder_log_files logs = ok r →
      let L := (letterLogs logs.val).length
      r.val.length = logs.val.length ∧
      (∀ i, i < L → IsLetterLog (entryBytes r.val i)) ∧
      (∀ i, L ≤ i → i < r.val.length → IsDigitLog (entryBytes r.val i))) := by
  sorry

/-- Whenever reorder_log_files returns a result r, let L be the number of letter-logs in logs. For every byte-vector x that is a letter-log, the number of indices i with 0 <= i < L and r[i] = x equals the number of indices j with 0 <= j < len(logs) and logs[j] = x.
  Preconditions: logs is a non-empty slice of byte-vector strings with 1 <= len(logs) <= 100; each log has length between 3 and 100; each log consists of an identifier followed by a single space and at least one word, with tokens separated by single spaces; for each log, every non-identifier word consists entirely of lowercase English letters (a-z) or entirely of digits (0-9), and all non-identifier words of that log are of the same kind. Thus each log is either a letter-log or a digit-log. -/
theorem spec_6
    (logs : Slice (alloc.vec.Vec Std.U8))
    (h_nonempty : 1 ≤ logs.val.length)
    (h_max : logs.val.length ≤ 100)
    (h_size : ∀ x ∈ logs.val, 3 ≤ x.val.length ∧ x.val.length ≤ 100)
    (h_wf : ∀ x ∈ logs.val, IsWellFormedLog (bytes x)) :
    ∀ r, Aegis.ReorderLogFiles.reorder_log_files logs = ok r →
      let L := (letterLogs logs.val).length
      ∀ x : alloc.vec.Vec Std.U8, IsLetterLog (bytes x) →
        countOcc (bytes x) ((r.val.take L).map bytes) =
          countOcc (bytes x) (logs.val.map bytes) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (logs : Slice (alloc.vec.Vec Std.U8))
    (h_nonempty : 1 ≤ logs.val.length)
    (h_max : logs.val.length ≤ 100)
    (h_size : ∀ x ∈ logs.val, 3 ≤ x.val.length ∧ x.val.length ≤ 100)
    (h_wf : ∀ x ∈ logs.val, IsWellFormedLog (bytes x)), ∀ r, Aegis.ReorderLogFiles.reorder_log_files logs = ok r →
      let L := (letterLogs logs.val).length
      ∀ x : alloc.vec.Vec Std.U8, IsLetterLog (bytes x) →
        countOcc (bytes x) ((r.val.take L).map bytes) =
          countOcc (bytes x) (logs.val.map bytes)) := by
  sorry

/-- Whenever reorder_log_files returns a result r, let D be the list of digit-logs of logs in their original order: D = [logs[j] for j in increasing order with 0 <= j < len(logs) and logs[j] is a digit-log]. Let L be the number of letter-logs in logs. Then len(r) = len(logs) and for every k with 0 <= k < len(D), r[L + k] = D[k].
  Preconditions: logs is a non-empty slice of byte-vector strings with 1 <= len(logs) <= 100; each log has length between 3 and 100; each log consists of an identifier followed by a single space and at least one word, with tokens separated by single spaces; for each log, every non-identifier word consists entirely of lowercase English letters (a-z) or entirely of digits (0-9), and all non-identifier words of that log are of the same kind. Thus each log is either a letter-log or a digit-log. -/
theorem spec_7
    (logs : Slice (alloc.vec.Vec Std.U8))
    (h_nonempty : 1 ≤ logs.val.length)
    (h_max : logs.val.length ≤ 100)
    (h_size : ∀ x ∈ logs.val, 3 ≤ x.val.length ∧ x.val.length ≤ 100)
    (h_wf : ∀ x ∈ logs.val, IsWellFormedLog (bytes x)) :
    ∀ r, Aegis.ReorderLogFiles.reorder_log_files logs = ok r →
      let L := (letterLogs logs.val).length
      r.val.length = logs.val.length ∧
      (∀ k, k < (digitLogs logs.val).length →
        entryBytes r.val (L + k) = entryBytes (digitLogs logs.val) k) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (logs : Slice (alloc.vec.Vec Std.U8))
    (h_nonempty : 1 ≤ logs.val.length)
    (h_max : logs.val.length ≤ 100)
    (h_size : ∀ x ∈ logs.val, 3 ≤ x.val.length ∧ x.val.length ≤ 100)
    (h_wf : ∀ x ∈ logs.val, IsWellFormedLog (bytes x)), ∀ r, Aegis.ReorderLogFiles.reorder_log_files logs = ok r →
      let L := (letterLogs logs.val).length
      r.val.length = logs.val.length ∧
      (∀ k, k < (digitLogs logs.val).length →
        entryBytes r.val (L + k) = entryBytes (digitLogs logs.val) k)) := by
  sorry

/-- Whenever reorder_log_files returns a result r, let L be the number of letter-logs in logs. For all i,j with 0 <= i < j < L, body(r[i]) <=_lex body(r[j]), where body(x) is the byte string after the first space of x and <=_lex is standard byte-wise lexicographic order.
  Preconditions: logs is a non-empty slice of byte-vector strings with 1 <= len(logs) <= 100; each log has length between 3 and 100; each log consists of an identifier followed by a single space and at least one word, with tokens separated by single spaces; for each log, every non-identifier word consists entirely of lowercase English letters (a-z) or entirely of digits (0-9), and all non-identifier words of that log are of the same kind. Thus each log is either a letter-log or a digit-log. -/
theorem spec_8
    (logs : Slice (alloc.vec.Vec Std.U8))
    (h_nonempty : 1 ≤ logs.val.length)
    (h_max : logs.val.length ≤ 100)
    (h_size : ∀ x ∈ logs.val, 3 ≤ x.val.length ∧ x.val.length ≤ 100)
    (h_wf : ∀ x ∈ logs.val, IsWellFormedLog (bytes x)) :
    ∀ r, Aegis.ReorderLogFiles.reorder_log_files logs = ok r →
      let L := (letterLogs logs.val).length
      ∀ i j, i < j → j < L →
        lexLe (bodyBytes (entryBytes r.val i)) (bodyBytes (entryBytes r.val j)) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (logs : Slice (alloc.vec.Vec Std.U8))
    (h_nonempty : 1 ≤ logs.val.length)
    (h_max : logs.val.length ≤ 100)
    (h_size : ∀ x ∈ logs.val, 3 ≤ x.val.length ∧ x.val.length ≤ 100)
    (h_wf : ∀ x ∈ logs.val, IsWellFormedLog (bytes x)), ∀ r, Aegis.ReorderLogFiles.reorder_log_files logs = ok r →
      let L := (letterLogs logs.val).length
      ∀ i j, i < j → j < L →
        lexLe (bodyBytes (entryBytes r.val i)) (bodyBytes (entryBytes r.val j))) := by
  sorry

/-- Whenever reorder_log_files returns a result r, let L be the number of letter-logs in logs. For all i,j with 0 <= i < j < L, if body(r[i]) = body(r[j]), then id(r[i]) <=_lex id(r[j]), where body(x) is the byte string after the first space of x, id(x) is the byte string before the first space of x, and <=_lex is standard byte-wise lexicographic order.
  Preconditions: logs is a non-empty slice of byte-vector strings with 1 <= len(logs) <= 100; each log has length between 3 and 100; each log consists of an identifier followed by a single space and at least one word, with tokens separated by single spaces; for each log, every non-identifier word consists entirely of lowercase English letters (a-z) or entirely of digits (0-9), and all non-identifier words of that log are of the same kind. Thus each log is either a letter-log or a digit-log. -/
theorem spec_9
    (logs : Slice (alloc.vec.Vec Std.U8))
    (h_nonempty : 1 ≤ logs.val.length)
    (h_max : logs.val.length ≤ 100)
    (h_size : ∀ x ∈ logs.val, 3 ≤ x.val.length ∧ x.val.length ≤ 100)
    (h_wf : ∀ x ∈ logs.val, IsWellFormedLog (bytes x)) :
    ∀ r, Aegis.ReorderLogFiles.reorder_log_files logs = ok r →
      let L := (letterLogs logs.val).length
      ∀ i j, i < j → j < L →
        bodyBytes (entryBytes r.val i) = bodyBytes (entryBytes r.val j) →
          lexLe (idBytes (entryBytes r.val i)) (idBytes (entryBytes r.val j)) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (logs : Slice (alloc.vec.Vec Std.U8))
    (h_nonempty : 1 ≤ logs.val.length)
    (h_max : logs.val.length ≤ 100)
    (h_size : ∀ x ∈ logs.val, 3 ≤ x.val.length ∧ x.val.length ≤ 100)
    (h_wf : ∀ x ∈ logs.val, IsWellFormedLog (bytes x)), ∀ r, Aegis.ReorderLogFiles.reorder_log_files logs = ok r →
      let L := (letterLogs logs.val).length
      ∀ i j, i < j → j < L →
        bodyBytes (entryBytes r.val i) = bodyBytes (entryBytes r.val j) →
          lexLe (idBytes (entryBytes r.val i)) (idBytes (entryBytes r.val j))) := by
  sorry

end AegisSpec.ReorderLogFiles

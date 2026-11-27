import Aegis.NumUniqueEmails.Code.Funs

/-!
# Specifications of `Aegis.NumUniqueEmails.num_unique_emails`

LeetCode problem `unique-email-addresses`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std
open Aeneas.Std.alloc.vec
open Aegis.NumUniqueEmails

namespace AegisSpec.NumUniqueEmails

def isAtB (b : U8) : Bool := b.val == 64

def isPlusB (b : U8) : Bool := b.val == 43

def isDotB (b : U8) : Bool := b.val == 46

def IsAt (b : U8) : Prop := b.val = 64

def IsPlus (b : U8) : Prop := b.val = 43

def IsDot (b : U8) : Prop := b.val = 46

def IsLower (b : U8) : Prop := 97 ≤ b.val ∧ b.val ≤ 122

def AllowedByte (b : U8) : Prop := IsLower b ∨ IsPlus b ∨ IsDot b ∨ IsAt b

def splitAtFirstAt : List U8 → List U8 × List U8
  | [] => ([], [])
  | b :: rest =>
    if isAtB b then ([], rest)
    else (b :: (splitAtFirstAt rest).1, (splitAtFirstAt rest).2)

def localPart (l : List U8) : List U8 := (splitAtFirstAt l).1

def domainPart (l : List U8) : List U8 := (splitAtFirstAt l).2

def takeBeforePlus : List U8 → List U8
  | [] => []
  | b :: rest => if isPlusB b then [] else b :: takeBeforePlus rest

def deleteDots (l : List U8) : List U8 := l.filter (fun b => !isDotB b)

def normLocal (l : List U8) : List U8 := deleteDots (takeBeforePlus l)

def norm (l : List U8) : List U8 :=
  normLocal (localPart l) ++ [64#u8] ++ domainPart l

def normVec (e : Vec U8) : List U8 := norm e.val

def normLocalVec (e : Vec U8) : List U8 := normLocal (localPart e.val)

def domainVec (e : Vec U8) : List U8 := domainPart e.val

def byteVals (l : List U8) : List ℕ := l.map (fun b => b.val)

def endsWithDotCom (l : List U8) : Prop :=
  (byteVals l).drop ((byteVals l).length - 4) = [46, 99, 111, 109]

def ValidEmail (e : Vec U8) : Prop :=
  let l := e.val
  1 ≤ l.length ∧ l.length ≤ 100 ∧
    (∀ b ∈ l, AllowedByte b) ∧
    (l.filter isAtB).length = 1 ∧
    1 ≤ (localPart l).length ∧
    1 ≤ (domainPart l).length ∧
    (∀ (b : U8) (t : List U8), localPart l = b :: t → ¬ IsPlus b) ∧
    endsWithDotCom (domainPart l) ∧
    5 ≤ (domainPart l).length

def ValidInput (emails : Slice (Vec U8)) : Prop :=
  1 ≤ emails.val.length ∧ emails.val.length ≤ 100 ∧ ∀ e ∈ emails.val, ValidEmail e

def addrs (emails : Slice (Vec U8)) : List (List U8) := emails.val.map normVec

def domains (emails : Slice (Vec U8)) : List (List U8) := emails.val.map domainVec

def normLocals (emails : Slice (Vec U8)) : List (List U8) :=
  emails.val.map normLocalVec

def SameLocalUpToDots (e e' : Vec U8) : Prop :=
  deleteDots (localPart e'.val) = deleteDots (localPart e.val) ∧
    domainPart e'.val = domainPart e.val

/-- For every input emails satisfying the preconditions, the function returns a result r and r equals, as an i64, the number of distinct byte strings in the set { norm(emails[i]) | 0 <= i < len(emails) }, where: at(e) is the unique index with e[at(e)] = '@'; local(e) = e[0..at(e)-1]; domain(e) = e[at(e)+1..len(e)-1]; prefix(e) is local(e) if local(e) contains no '+' byte, otherwise local(e)[0..p-1] where p is the first index with local(e)[p] = '+'; norm_local(e) is prefix(e) with every '.' byte deleted; and norm(e) is the byte string norm_local(e) followed by the byte '@' followed by domain(e). Thus r is exactly the number of different addresses that actually receive mail after applying the local-name dot and plus rules and leaving the domain unchanged.
  Preconditions: Let a valid input mean: len(emails) is between 1 and 100 inclusive; for every i with 0 <= i < len(emails), e = emails[i] has 1 <= len(e) <= 100; every byte of e is one of 'a'..'z', '+', '.', '@'; e contains exactly one byte '@'; the local part (bytes before '@') and domain part (bytes after '@') are both non-empty; local[0] != '+'; the domain ends with the four bytes '.', 'c', 'o', 'm'; and len(domain) >= 5 so at least one byte precedes the .com suffix. The input emails is a valid input. -/
theorem spec_1 (emails : Slice (Vec U8)) (h : ValidInput emails) :
    ∃ r : I64,
      num_unique_emails emails = Result.ok r ∧
        r.val = ((addrs emails).dedup.length : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (emails : Slice (Vec U8)) (h : ValidInput emails), ∃ r : I64,
      num_unique_emails emails = Result.ok r ∧
        r.val = ((addrs emails).dedup.length : ℤ)) := by
  sorry

/-- For every input emails satisfying the preconditions, the function returns a result r; it does not fail due to overflow, out-of-bounds access, or panic. The value of r is not constrained by this specification.
  Preconditions: Let a valid input mean: len(emails) is between 1 and 100 inclusive; for every i with 0 <= i < len(emails), e = emails[i] has 1 <= len(e) <= 100; every byte of e is one of 'a'..'z', '+', '.', '@'; e contains exactly one byte '@'; the local part (bytes before '@') and domain part (bytes after '@') are both non-empty; local[0] != '+'; the domain ends with the four bytes '.', 'c', 'o', 'm'; and len(domain) >= 5. The input emails is a valid input. -/
theorem spec_2 (emails : Slice (Vec U8)) (h : ValidInput emails) :
    ∃ r : I64, num_unique_emails emails = Result.ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (emails : Slice (Vec U8)) (h : ValidInput emails), ∃ r : I64, num_unique_emails emails = Result.ok r) := by
  sorry

/-- For every input emails satisfying the preconditions, whenever the function returns a result r, 1 <= r <= len(emails).
  Preconditions: Let a valid input mean: len(emails) is between 1 and 100 inclusive; for every i with 0 <= i < len(emails), e = emails[i] has 1 <= len(e) <= 100; every byte of e is one of 'a'..'z', '+', '.', '@'; e contains exactly one byte '@'; the local part and domain part are both non-empty; local[0] != '+'; the domain ends with the four bytes '.', 'c', 'o', 'm'; and len(domain) >= 5. The input emails is a valid input. -/
theorem spec_3 (emails : Slice (Vec U8)) (h : ValidInput emails) (r : I64)
    (hr : num_unique_emails emails = Result.ok r) :
    1 ≤ r.val ∧ r.val ≤ ((emails.val.length : ℕ) : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (emails : Slice (Vec U8)) (h : ValidInput emails) (r : I64)
    (hr : num_unique_emails emails = Result.ok r), 1 ≤ r.val ∧ r.val ≤ ((emails.val.length : ℕ) : ℤ)) := by
  sorry

/-- For every such pair emails and emails', whenever the function returns r for emails and r' for emails', r = r'.
  Preconditions: Let a valid input mean: len(emails) is between 1 and 100 inclusive; for every i with 0 <= i < len(emails), e = emails[i] has 1 <= len(e) <= 100; every byte of e is one of 'a'..'z', '+', '.', '@'; e contains exactly one byte '@'; the local part and domain part are both non-empty; local[0] != '+'; the domain ends with the four bytes '.', 'c', 'o', 'm'; and len(domain) >= 5. Both emails and emails' are valid inputs. They have the same length, and for every i with 0 <= i < len(emails), emails'[i] is obtained from emails[i] by inserting or deleting any number of '.' bytes inside the local part (the bytes before the unique '@'), with no other byte changed, so the '@' and the whole domain are unchanged. -/
theorem spec_4 (emails emails' : Slice (Vec U8)) (h : ValidInput emails)
    (h' : ValidInput emails') (hlen : emails'.val.length = emails.val.length)
    (hdots : ∀ i (hi : i < emails.val.length),
      SameLocalUpToDots (emails.val[i]) (emails'.val[i]'(by omega)))
    (r r' : I64) (hr : num_unique_emails emails = Result.ok r)
    (hr' : num_unique_emails emails' = Result.ok r') : r = r' := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (emails emails' : Slice (Vec U8)) (h : ValidInput emails)
    (h' : ValidInput emails') (hlen : emails'.val.length = emails.val.length)
    (hdots : ∀ i (hi : i < emails.val.length),
      SameLocalUpToDots (emails.val[i]) (emails'.val[i]'(by omega)))
    (r r' : I64) (hr : num_unique_emails emails = Result.ok r)
    (hr' : num_unique_emails emails' = Result.ok r'), r = r') := by
  sorry

/-- For every such emails and e, whenever the function returns r for emails and r' for emails', r = r'.
  Preconditions: Let a valid input mean: len(emails) is between 1 and 100 inclusive; for every i with 0 <= i < len(emails), e = emails[i] has 1 <= len(e) <= 100; every byte of e is one of 'a'..'z', '+', '.', '@'; e contains exactly one byte '@'; the local part and domain part are both non-empty; local[0] != '+'; the domain ends with the four bytes '.', 'c', 'o', 'm'; and len(domain) >= 5. emails is a valid input with len(emails) < 100. e is a valid email byte array, and e has the same forwarded address as some emails[i]: after deleting all '.' bytes in its local part and ignoring everything from the first '+' onward in its local part if any, its local part equals the similarly treated local part of emails[i], and its domain part equals the domain part of emails[i]. Let emails' be emails with e appended. -/
theorem spec_5 (emails : Slice (Vec U8)) (e : Vec U8) (h : ValidInput emails)
    (hlen : emails.val.length < 100) (he : ValidEmail e)
    (hsame : ∃ i : Fin emails.val.length, normVec e = normVec (emails.val[i]))
    (emails' : Slice (Vec U8)) (hemails' : emails'.val = emails.val ++ [e])
    (r r' : I64) (hr : num_unique_emails emails = Result.ok r)
    (hr' : num_unique_emails emails' = Result.ok r') : r = r' := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (emails : Slice (Vec U8)) (e : Vec U8) (h : ValidInput emails)
    (hlen : emails.val.length < 100) (he : ValidEmail e)
    (hsame : ∃ i : Fin emails.val.length, normVec e = normVec (emails.val[i]))
    (emails' : Slice (Vec U8)) (hemails' : emails'.val = emails.val ++ [e])
    (r r' : I64) (hr : num_unique_emails emails = Result.ok r)
    (hr' : num_unique_emails emails' = Result.ok r'), r = r') := by
  sorry

/-- For every such input emails, whenever the function returns r, r = 1.
  Preconditions: Let a valid input mean: len(emails) is between 1 and 100 inclusive; for every i with 0 <= i < len(emails), e = emails[i] has 1 <= len(e) <= 100; every byte of e is one of 'a'..'z', '+', '.', '@'; e contains exactly one byte '@'; the local part and domain part are both non-empty; local[0] != '+'; the domain ends with the four bytes '.', 'c', 'o', 'm'; and len(domain) >= 5. emails is a valid input, and all emails forward to the same address: for every i,j with 0 <= i,j < len(emails), after deleting all '.' bytes in the local part and ignoring everything from the first '+' onward in the local part if any, the local parts are equal, and the domain parts are equal. -/
theorem spec_6 (emails : Slice (Vec U8)) (h : ValidInput emails)
    (hall : ∀ x ∈ addrs emails, ∀ y ∈ addrs emails, x = y) (r : I64)
    (hr : num_unique_emails emails = Result.ok r) : r.val = 1 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (emails : Slice (Vec U8)) (h : ValidInput emails)
    (hall : ∀ x ∈ addrs emails, ∀ y ∈ addrs emails, x = y) (r : I64)
    (hr : num_unique_emails emails = Result.ok r), r.val = 1) := by
  sorry

/-- For every such input emails, whenever the function returns r, r = len(emails).
  Preconditions: Let a valid input mean: len(emails) is between 1 and 100 inclusive; for every i with 0 <= i < len(emails), e = emails[i] has 1 <= len(e) <= 100; every byte of e is one of 'a'..'z', '+', '.', '@'; e contains exactly one byte '@'; the local part and domain part are both non-empty; local[0] != '+'; the domain ends with the four bytes '.', 'c', 'o', 'm'; and len(domain) >= 5. emails is a valid input, and no two emails forward to the same address: for every i,j with 0 <= i < j < len(emails), after deleting all '.' bytes in the local part and ignoring everything from the first '+' onward in the local part if any, either the local parts differ or the domain parts differ. -/
theorem spec_7 (emails : Slice (Vec U8)) (h : ValidInput emails)
    (hnd : ∀ i j (hi : i < emails.val.length) (hj : j < emails.val.length), i < j →
      normVec (emails.val[i]) ≠ normVec (emails.val[j]))
    (r : I64) (hr : num_unique_emails emails = Result.ok r) :
    r.val = ((emails.val.length : ℕ) : ℤ) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (emails : Slice (Vec U8)) (h : ValidInput emails)
    (hnd : ∀ i j (hi : i < emails.val.length) (hj : j < emails.val.length), i < j →
      normVec (emails.val[i]) ≠ normVec (emails.val[j]))
    (r : I64) (hr : num_unique_emails emails = Result.ok r), r.val = ((emails.val.length : ℕ) : ℤ)) := by
  sorry

/-- For every such emails, k, and emails', whenever the function returns r for emails and r' for emails', if there exists j != k with 0 <= j < len(emails) such that emails[j] and emails[k] forward to the same address under the local-name rules (delete all '.' in the local part, ignore everything from the first '+' onward in the local part, leave the domain unchanged), then r' = r; otherwise r' = r - 1.
  Preconditions: Let a valid input mean: len(emails) is between 1 and 100 inclusive; for every i with 0 <= i < len(emails), e = emails[i] has 1 <= len(e) <= 100; every byte of e is one of 'a'..'z', '+', '.', '@'; e contains exactly one byte '@'; the local part and domain part are both non-empty; local[0] != '+'; the domain ends with the four bytes '.', 'c', 'o', 'm'; and len(domain) >= 5. emails is a valid input with len(emails) >= 2, and k is an index with 0 <= k < len(emails). Let emails' be emails with the element at index k removed. -/
theorem spec_8 (emails : Slice (Vec U8)) (h : ValidInput emails)
    (hlen : 2 ≤ emails.val.length) (k : ℕ) (hk : k < emails.val.length)
    (emails' : Slice (Vec U8)) (hemails' : emails'.val = emails.val.eraseIdx k)
    (r r' : I64) (hr : num_unique_emails emails = Result.ok r)
    (hr' : num_unique_emails emails' = Result.ok r') :
    ((∃ j : Fin emails.val.length, j ≠ ⟨k, hk⟩ ∧
        normVec (emails.val[j]) = normVec (emails.val[k])) →
      r'.val = r.val) ∧
      ((¬ ∃ j : Fin emails.val.length, j ≠ ⟨k, hk⟩ ∧
          normVec (emails.val[j]) = normVec (emails.val[k])) →
        r'.val = r.val - 1) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (emails : Slice (Vec U8)) (h : ValidInput emails)
    (hlen : 2 ≤ emails.val.length) (k : ℕ) (hk : k < emails.val.length)
    (emails' : Slice (Vec U8)) (hemails' : emails'.val = emails.val.eraseIdx k)
    (r r' : I64) (hr : num_unique_emails emails = Result.ok r)
    (hr' : num_unique_emails emails' = Result.ok r'), ((∃ j : Fin emails.val.length, j ≠ ⟨k, hk⟩ ∧
        normVec (emails.val[j]) = normVec (emails.val[k])) →
      r'.val = r.val) ∧
      ((¬ ∃ j : Fin emails.val.length, j ≠ ⟨k, hk⟩ ∧
          normVec (emails.val[j]) = normVec (emails.val[k])) →
        r'.val = r.val - 1)) := by
  sorry

/-- For every input emails satisfying the preconditions, whenever the function returns r, the number of distinct domain parts domain(emails[i]) for 0 <= i < len(emails), where domain(e) is the non-empty byte string after the unique '@' in e, is at most r.
  Preconditions: Let a valid input mean: len(emails) is between 1 and 100 inclusive; for every i with 0 <= i < len(emails), e = emails[i] has 1 <= len(e) <= 100; every byte of e is one of 'a'..'z', '+', '.', '@'; e contains exactly one byte '@'; the local part and domain part are both non-empty; local[0] != '+'; the domain ends with the four bytes '.', 'c', 'o', 'm'; and len(domain) >= 5. The input emails is a valid input. -/
theorem spec_9 (emails : Slice (Vec U8)) (h : ValidInput emails) (r : I64)
    (hr : num_unique_emails emails = Result.ok r) :
    ((domains emails).dedup.length : ℤ) ≤ r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (emails : Slice (Vec U8)) (h : ValidInput emails) (r : I64)
    (hr : num_unique_emails emails = Result.ok r), ((domains emails).dedup.length : ℤ) ≤ r.val) := by
  sorry

/-- For every input emails satisfying the preconditions, whenever the function returns r, the number of distinct byte strings obtained from emails[i] by taking the part of its local name before the first '+' (or the whole local name if it has no '+') and deleting every '.' byte, for 0 <= i < len(emails), is at most r.
  Preconditions: Let a valid input mean: len(emails) is between 1 and 100 inclusive; for every i with 0 <= i < len(emails), e = emails[i] has 1 <= len(e) <= 100; every byte of e is one of 'a'..'z', '+', '.', '@'; e contains exactly one byte '@'; the local part and domain part are both non-empty; local[0] != '+'; the domain ends with the four bytes '.', 'c', 'o', 'm'; and len(domain) >= 5. The input emails is a valid input. -/
theorem spec_10 (emails : Slice (Vec U8)) (h : ValidInput emails) (r : I64)
    (hr : num_unique_emails emails = Result.ok r) :
    ((normLocals emails).dedup.length : ℤ) ≤ r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (emails : Slice (Vec U8)) (h : ValidInput emails) (r : I64)
    (hr : num_unique_emails emails = Result.ok r), ((normLocals emails).dedup.length : ℤ) ≤ r.val) := by
  sorry

/-- For every input emails satisfying the preconditions, whenever the function returns r, there exist r indices i_1, ..., i_r with 0 <= i_1 < ... < i_r < len(emails) such that their forwarded addresses (after deleting all '.' bytes in the local part, ignoring everything from the first '+' onward in that local part if any, and leaving the domain unchanged) are pairwise distinct, and for every index j with 0 <= j < len(emails), the forwarded address of emails[j] equals the forwarded address of emails[i_m] for some m in {1,...,r}.
  Preconditions: Let a valid input mean: len(emails) is between 1 and 100 inclusive; for every i with 0 <= i < len(emails), e = emails[i] has 1 <= len(e) <= 100; every byte of e is one of 'a'..'z', '+', '.', '@'; e contains exactly one byte '@'; the local part and domain part are both non-empty; local[0] != '+'; the domain ends with the four bytes '.', 'c', 'o', 'm'; and len(domain) >= 5. The input emails is a valid input. -/
theorem spec_11 (emails : Slice (Vec U8)) (h : ValidInput emails) (r : I64)
    (hr : num_unique_emails emails = Result.ok r) :
    ∃ is : List (Fin (addrs emails).length),
      r.val = ((is.length : ℕ) : ℤ) ∧
        is.Pairwise (· < ·) ∧
        (is.map (fun i => (addrs emails).get i)).Nodup ∧
        (∀ j : Fin (addrs emails).length,
          (addrs emails).get j ∈ is.map (fun i => (addrs emails).get i)) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (emails : Slice (Vec U8)) (h : ValidInput emails) (r : I64)
    (hr : num_unique_emails emails = Result.ok r), ∃ is : List (Fin (addrs emails).length),
      r.val = ((is.length : ℕ) : ℤ) ∧
        is.Pairwise (· < ·) ∧
        (is.map (fun i => (addrs emails).get i)).Nodup ∧
        (∀ j : Fin (addrs emails).length,
          (addrs emails).get j ∈ is.map (fun i => (addrs emails).get i))) := by
  sorry

/-- For every such emails and e, whenever the function returns r for emails and r' for emails', r <= r' <= r + 1.
  Preconditions: Let a valid input mean: len(emails) is between 1 and 100 inclusive; for every i with 0 <= i < len(emails), e = emails[i] has 1 <= len(e) <= 100; every byte of e is one of 'a'..'z', '+', '.', '@'; e contains exactly one byte '@'; the local part and domain part are both non-empty; local[0] != '+'; the domain ends with the four bytes '.', 'c', 'o', 'm'; and len(domain) >= 5. emails is a valid input with len(emails) < 100; e is a valid email byte array satisfying the same per-email constraints as an element of a valid input (1 <= len(e) <= 100, bytes in 'a'..'z', '+', '.', '@', exactly one '@', non-empty local and domain, local[0] != '+', domain ends with '.com', len(domain) >= 5); emails' is emails with e appended. -/
theorem spec_12 (emails : Slice (Vec U8)) (e : Vec U8) (h : ValidInput emails)
    (hlen : emails.val.length < 100) (he : ValidEmail e)
    (emails' : Slice (Vec U8)) (hemails' : emails'.val = emails.val ++ [e])
    (r r' : I64) (hr : num_unique_emails emails = Result.ok r)
    (hr' : num_unique_emails emails' = Result.ok r') :
    r.val ≤ r'.val ∧ r'.val ≤ r.val + 1 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (emails : Slice (Vec U8)) (e : Vec U8) (h : ValidInput emails)
    (hlen : emails.val.length < 100) (he : ValidEmail e)
    (emails' : Slice (Vec U8)) (hemails' : emails'.val = emails.val ++ [e])
    (r r' : I64) (hr : num_unique_emails emails = Result.ok r)
    (hr' : num_unique_emails emails' = Result.ok r'), r.val ≤ r'.val ∧ r'.val ≤ r.val + 1) := by
  sorry

/-- Whenever the function returns r for emails and r' for emails', r = r'.
  Preconditions: Let a valid input mean: len(emails) is between 1 and 100 inclusive; for every i with 0 <= i < len(emails), e = emails[i] has 1 <= len(e) <= 100; every byte of e is one of 'a'..'z', '+', '.', '@'; e contains exactly one byte '@'; the local part and domain part are both non-empty; local[0] != '+'; the domain ends with the four bytes '.', 'c', 'o', 'm'; and len(domain) >= 5. Both emails and emails' are valid inputs and have the same length. For every i with 0 <= i < len(emails), norm(emails[i]) = norm(emails'[i]), where norm(e) is defined as in the main specification: local(e) is the bytes before the unique '@', domain(e) is the bytes after it, take the prefix of local(e) before the first '+' if any (or all of local(e) if there is no '+'), delete every '.' byte from that prefix, and append '@' followed by domain(e). -/
theorem spec_13 (emails emails' : Slice (Vec U8)) (h : ValidInput emails)
    (h' : ValidInput emails') (hlen : emails'.val.length = emails.val.length)
    (hnorm : ∀ i (hi : i < emails.val.length),
      normVec (emails.val[i]) = normVec (emails'.val[i]'(by omega)))
    (r r' : I64) (hr : num_unique_emails emails = Result.ok r)
    (hr' : num_unique_emails emails' = Result.ok r') : r.val = r'.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (emails emails' : Slice (Vec U8)) (h : ValidInput emails)
    (h' : ValidInput emails') (hlen : emails'.val.length = emails.val.length)
    (hnorm : ∀ i (hi : i < emails.val.length),
      normVec (emails.val[i]) = normVec (emails'.val[i]'(by omega)))
    (r r' : I64) (hr : num_unique_emails emails = Result.ok r)
    (hr' : num_unique_emails emails' = Result.ok r'), r.val = r'.val) := by
  sorry

end AegisSpec.NumUniqueEmails

import Aegis.IsInterleave.Code.Funs

/-!
# Specifications of `Aegis.IsInterleave.is_interleave`

LeetCode problem `interleaving-string`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.IsInterleave

  def listNOfList : (l : List α) → Aeneas.Data.ListN.ListN α l.length
    | [] => .nil
    | a :: l => .cons (n := l.length) a (listNOfList l)

  def sliceOfList (l : List U8) : Slice U8 :=
    if h : l.length ≤ Usize.max then ⟨l.length, listNOfList l, h⟩
    else ⟨0, .nil, Nat.zero_le _⟩

  theorem listNOfList_toList (l : List α) : (listNOfList l).toList = l := by
    induction l with
    | nil => rfl
    | cons a l ih =>
      show (Aeneas.Data.ListN.ListN.cons a (listNOfList l)).toList = a :: l
      rw [show (Aeneas.Data.ListN.ListN.cons a (listNOfList l)).toList
            = a :: (listNOfList l).toList from rfl, ih]

  theorem sliceOfList_val (l : List U8) (h : l.length ≤ Usize.max) :
      (sliceOfList l).val = l := by
    simp only [sliceOfList]
    split
    · show (listNOfList l).toList = l
      exact listNOfList_toList l
    · rename_i h'
      exact absurd h h'

  def rev (s : Slice U8) : Slice U8 := sliceOfList s.val.reverse

  def snoc (s : Slice U8) (c : U8) : Slice U8 := sliceOfList (s.val ++ [c])

  def byteAt (l : List U8) (i : ℕ) : Option U8 := l[i]?

  def prefixOf (s : Slice U8) (t : ℕ) : List U8 := s.val.take t

  def suffixOf (s : Slice U8) (t : ℕ) : List U8 := s.val.drop (s.length - t)

  def countByte (c : U8) (l : List U8) : ℕ := (l.filter (fun b => b = c)).length

  def pick {α : Type} : List Bool → List α → List α
    | [], _ => []
    | _ :: _, [] => []
    | b :: d, x :: c => if b then pick d c else x :: pick d c

  def IsShuffle (a b c : List U8) : Prop :=
    ∃ d : List Bool, d.length = c.length ∧ pick d c = a ∧ pick (d.map (fun b => !b)) c = b

  def Valid (s1 s2 s3 : Slice U8) : Prop :=
    s1.length ≤ 100 ∧ s2.length ≤ 100 ∧ s3.length ≤ 200 ∧
      (∀ b ∈ s1.val, 97 ≤ b.val ∧ b.val ≤ 122) ∧
      (∀ b ∈ s2.val, 97 ≤ b.val ∧ b.val ≤ 122) ∧
      (∀ b ∈ s3.val, 97 ≤ b.val ∧ b.val ≤ 122)

  def interleaveBlocks : List (List U8) → List (List U8) → List (List U8)
    | [], v => v
    | u :: us, [] => u :: us
    | u :: us, v :: vs => u :: v :: interleaveBlocks us vs

  /-- For every Valid s1,s2,s3, whenever is_interleave(s1,s2,s3) returns a result r, r = true if and only if there exists a sequence d of length len(s3) with each d[t] in {0,1}, exactly len(s1) entries equal to 0, and exactly len(s2) entries equal to 1, such that reading s3 from left to right and assigning s3[t] to s1 when d[t]=0 and to s2 when d[t]=1, the bytes assigned to s1 in their order of appearance form exactly s1 and the bytes assigned to s2 in their order of appearance form exactly s2. Equivalently, the subsequence of s3 at positions t with d[t]=0 equals s1, and the complementary subsequence at positions with d[t]=1 equals s2. This is the usual interleaving/shuffle preserving the internal left-to-right order of s1 and s2.
    Preconditions: Let Valid mean s1, s2, s3 are byte slices with 0 <= len(s1), len(s2) <= 100, 0 <= len(s3) <= 200, and every byte of s1, s2, s3 is in 97..122. -/
  theorem spec_1
    (s1 s2 s3 : Slice U8) (hValid : Valid s1 s2 s3) (r : Bool)
    (hres : Aegis.IsInterleave.is_interleave s1 s2 s3 = ok r) :
    (r = true ↔ IsShuffle s1.val s2.val s3.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s1 s2 s3 : Slice U8) (hValid : Valid s1 s2 s3) (r : Bool)
      (hres : Aegis.IsInterleave.is_interleave s1 s2 s3 = ok r), (r = true ↔ IsShuffle s1.val s2.val s3.val)) := by
    sorry

  /-- For every Valid s1,s2,s3 with len(s3) != len(s1) + len(s2), whenever is_interleave(s1,s2,s3) returns a result r, r = false.
    Preconditions: Let Valid be as in spec_1. -/
  theorem spec_2
    (s1 s2 s3 : Slice U8) (hValid : Valid s1 s2 s3)
    (hlen : s3.length ≠ s1.length + s2.length) (r : Bool)
    (hres : Aegis.IsInterleave.is_interleave s1 s2 s3 = ok r) :
    r = false := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s1 s2 s3 : Slice U8) (hValid : Valid s1 s2 s3)
      (hlen : s3.length ≠ s1.length + s2.length) (r : Bool)
      (hres : Aegis.IsInterleave.is_interleave s1 s2 s3 = ok r), r = false) := by
    sorry

  /-- For every Valid s1,s2,s3 such that s3 is exactly the concatenation s1 followed by s2 (len(s3)=len(s1)+len(s2), s3[i]=s1[i] for 0 <= i < len(s1), and s3[len(s1)+j]=s2[j] for 0 <= j < len(s2)), whenever is_interleave(s1,s2,s3) returns a result r, r = true.
    Preconditions: Let Valid be as in spec_1. -/
  theorem spec_3
    (s1 s2 s3 : Slice U8) (hValid : Valid s1 s2 s3)
    (hcat : s3.val = s1.val ++ s2.val) (r : Bool)
    (hres : Aegis.IsInterleave.is_interleave s1 s2 s3 = ok r) :
    r = true := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s1 s2 s3 : Slice U8) (hValid : Valid s1 s2 s3)
      (hcat : s3.val = s1.val ++ s2.val) (r : Bool)
      (hres : Aegis.IsInterleave.is_interleave s1 s2 s3 = ok r), r = true) := by
    sorry

  /-- For every Valid s1,s2,s3, whenever is_interleave(s1,s2,s3) returns r and is_interleave(s2,s1,s3) returns r', we have r = r'.
    Preconditions: Let Valid be as in spec_1. -/
  theorem spec_4
    (s1 s2 s3 : Slice U8) (hValid : Valid s1 s2 s3) (r r' : Bool)
    (hres : Aegis.IsInterleave.is_interleave s1 s2 s3 = ok r)
    (hres' : Aegis.IsInterleave.is_interleave s2 s1 s3 = ok r') :
    r = r' := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s1 s2 s3 : Slice U8) (hValid : Valid s1 s2 s3) (r r' : Bool)
      (hres : Aegis.IsInterleave.is_interleave s1 s2 s3 = ok r)
      (hres' : Aegis.IsInterleave.is_interleave s2 s1 s3 = ok r'), r = r') := by
    sorry

  /-- For every Valid s1,s2,s3, whenever is_interleave(s1,s2,s3) returns r and is_interleave(rev(s1),rev(s2),rev(s3)) returns r', we have r = r'.
    Preconditions: Let Valid be as in spec_1. For a byte slice a, define rev(a) by len(rev(a))=len(a) and rev(a)[i] = a[len(a)-1-i] for 0 <= i < len(a). -/
  theorem spec_5
    (s1 s2 s3 : Slice U8) (hValid : Valid s1 s2 s3) (r r' : Bool)
    (hres : Aegis.IsInterleave.is_interleave s1 s2 s3 = ok r)
    (hres' : Aegis.IsInterleave.is_interleave (rev s1) (rev s2) (rev s3) = ok r') :
    r = r' := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s1 s2 s3 : Slice U8) (hValid : Valid s1 s2 s3) (r r' : Bool)
      (hres : Aegis.IsInterleave.is_interleave s1 s2 s3 = ok r)
      (hres' : Aegis.IsInterleave.is_interleave (rev s1) (rev s2) (rev s3) = ok r'), r = r') := by
    sorry

  /-- For every Valid s1,s2,s3, whenever is_interleave(s1,s2,s3) returns true, for every byte c with 97 <= c <= 122 the number of indices i with 0 <= i < len(s3) and s3[i]=c equals the number of indices i with 0 <= i < len(s1) and s1[i]=c plus the number of indices j with 0 <= j < len(s2) and s2[j]=c.
    Preconditions: Let Valid be as in spec_1. -/
  theorem spec_6
    (s1 s2 s3 : Slice U8) (hValid : Valid s1 s2 s3) (c : U8)
    (hc : 97 ≤ c.val ∧ c.val ≤ 122)
    (hres : Aegis.IsInterleave.is_interleave s1 s2 s3 = ok true) :
    countByte c s3.val = countByte c s1.val + countByte c s2.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s1 s2 s3 : Slice U8) (hValid : Valid s1 s2 s3) (c : U8)
      (hc : 97 ≤ c.val ∧ c.val ≤ 122)
      (hres : Aegis.IsInterleave.is_interleave s1 s2 s3 = ok true), countByte c s3.val = countByte c s1.val + countByte c s2.val) := by
    sorry

  /-- For every Valid s1,s2,s3, whenever is_interleave(s1,s2,s3) returns true and len(s3) > 0, either (len(s1) > 0 and s3[0] = s1[0]) or (len(s2) > 0 and s3[0] = s2[0]).
    Preconditions: Let Valid be as in spec_1. -/
  theorem spec_7
    (s1 s2 s3 : Slice U8) (hValid : Valid s1 s2 s3)
    (hres : Aegis.IsInterleave.is_interleave s1 s2 s3 = ok true) (hpos : 0 < s3.length) :
    (0 < s1.length ∧ byteAt s3.val 0 = byteAt s1.val 0) ∨
      (0 < s2.length ∧ byteAt s3.val 0 = byteAt s2.val 0) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s1 s2 s3 : Slice U8) (hValid : Valid s1 s2 s3)
      (hres : Aegis.IsInterleave.is_interleave s1 s2 s3 = ok true) (hpos : 0 < s3.length), (0 < s1.length ∧ byteAt s3.val 0 = byteAt s1.val 0) ∨
        (0 < s2.length ∧ byteAt s3.val 0 = byteAt s2.val 0)) := by
    sorry

  /-- For every Valid s1,s2,s3, whenever is_interleave(s1,s2,s3) returns true and len(s3) > 0, either (len(s1) > 0 and s3[len(s3)-1] = s1[len(s1)-1]) or (len(s2) > 0 and s3[len(s3)-1] = s2[len(s2)-1]).
    Preconditions: Let Valid be as in spec_1. -/
  theorem spec_8
    (s1 s2 s3 : Slice U8) (hValid : Valid s1 s2 s3)
    (hres : Aegis.IsInterleave.is_interleave s1 s2 s3 = ok true) (hpos : 0 < s3.length) :
    (0 < s1.length ∧ byteAt s3.val (s3.length - 1) = byteAt s1.val (s1.length - 1)) ∨
      (0 < s2.length ∧ byteAt s3.val (s3.length - 1) = byteAt s2.val (s2.length - 1)) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s1 s2 s3 : Slice U8) (hValid : Valid s1 s2 s3)
      (hres : Aegis.IsInterleave.is_interleave s1 s2 s3 = ok true) (hpos : 0 < s3.length), (0 < s1.length ∧ byteAt s3.val (s3.length - 1) = byteAt s1.val (s1.length - 1)) ∨
        (0 < s2.length ∧ byteAt s3.val (s3.length - 1) = byteAt s2.val (s2.length - 1))) := by
    sorry

  /-- Let s1' be s1 with c appended (len(s1')=len(s1)+1, s1'[i]=s1[i] for 0 <= i < len(s1), and s1'[len(s1)]=c), and let s3' be s3 with c appended similarly. For every such Valid s1,s2,s3, if is_interleave(s1,s2,s3) returns true, then is_interleave(s1',s2,s3') returns true.
    Preconditions: Let Valid be as in spec_1, let c be a byte with 97 <= c <= 122, and suppose len(s1) < 100 and len(s3) < 200. -/
  theorem spec_9
    (s1 s2 s3 : Slice U8) (hValid : Valid s1 s2 s3) (c : U8)
    (hc : 97 ≤ c.val ∧ c.val ≤ 122) (h1 : s1.length < 100) (h3 : s3.length < 200)
    (hres : Aegis.IsInterleave.is_interleave s1 s2 s3 = ok true) :
    Aegis.IsInterleave.is_interleave (snoc s1 c) s2 (snoc s3 c) = ok true := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s1 s2 s3 : Slice U8) (hValid : Valid s1 s2 s3) (c : U8)
      (hc : 97 ≤ c.val ∧ c.val ≤ 122) (h1 : s1.length < 100) (h3 : s3.length < 200)
      (hres : Aegis.IsInterleave.is_interleave s1 s2 s3 = ok true), Aegis.IsInterleave.is_interleave (snoc s1 c) s2 (snoc s3 c) = ok true) := by
    sorry

  /-- Let s2' be s2 with c appended (len(s2')=len(s2)+1, s2'[i]=s2[i] for 0 <= i < len(s2), and s2'[len(s2)]=c), and let s3' be s3 with c appended similarly. For every such Valid s1,s2,s3, if is_interleave(s1,s2,s3) returns true, then is_interleave(s1,s2',s3') returns true.
    Preconditions: Let Valid be as in spec_1, let c be a byte with 97 <= c <= 122, and suppose len(s2) < 100 and len(s3) < 200. -/
  theorem spec_10
    (s1 s2 s3 : Slice U8) (hValid : Valid s1 s2 s3) (c : U8)
    (hc : 97 ≤ c.val ∧ c.val ≤ 122) (h2 : s2.length < 100) (h3 : s3.length < 200)
    (hres : Aegis.IsInterleave.is_interleave s1 s2 s3 = ok true) :
    Aegis.IsInterleave.is_interleave s1 (snoc s2 c) (snoc s3 c) = ok true := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s1 s2 s3 : Slice U8) (hValid : Valid s1 s2 s3) (c : U8)
      (hc : 97 ≤ c.val ∧ c.val ≤ 122) (h2 : s2.length < 100) (h3 : s3.length < 200)
      (hres : Aegis.IsInterleave.is_interleave s1 s2 s3 = ok true), Aegis.IsInterleave.is_interleave s1 (snoc s2 c) (snoc s3 c) = ok true) := by
    sorry

  /-- For every Valid s1,s2,s3, whenever is_interleave(s1,s2,s3) returns true, for every k with 0 <= k <= len(s3) there exist i,j with 0 <= i <= len(s1), 0 <= j <= len(s2), and i+j=k, such that Inter(prefix(s1,i), prefix(s2,j), prefix(s3,k)) holds.
    Preconditions: Let Valid be as in spec_1, and let Inter(a,b,c) denote the interleaving predicate from S1 (c is a shuffle of a and b preserving internal order). Let prefix(a,t) be the byte slice of the first t bytes of a. -/
  theorem spec_11
    (s1 s2 s3 : Slice U8) (hValid : Valid s1 s2 s3)
    (hres : Aegis.IsInterleave.is_interleave s1 s2 s3 = ok true) (k : ℕ) (hk : k ≤ s3.length) :
    ∃ i j : ℕ, i ≤ s1.length ∧ j ≤ s2.length ∧ i + j = k ∧
      IsShuffle (prefixOf s1 i) (prefixOf s2 j) (prefixOf s3 k) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (s1 s2 s3 : Slice U8) (hValid : Valid s1 s2 s3)
      (hres : Aegis.IsInterleave.is_interleave s1 s2 s3 = ok true) (k : ℕ) (hk : k ≤ s3.length), ∃ i j : ℕ, i ≤ s1.length ∧ j ≤ s2.length ∧ i + j = k ∧
        IsShuffle (prefixOf s1 i) (prefixOf s2 j) (prefixOf s3 k)) := by
    sorry

  /-- For every Valid s1,s2,s3, whenever is_interleave(s1,s2,s3) returns true, for every k with 0 <= k <= len(s3) there exist i,j with 0 <= i <= len(s1), 0 <= j <= len(s2), and i+j=k, such that Inter(suffix(s1,i), suffix(s2,j), suffix(s3,k)) holds.
    Preconditions: Let Valid be as in spec_1, let Inter be as in spec_11, and let suffix(a,t) be the byte slice of the last t bytes of a, so suffix(a,t)[u] = a[len(a)-t+u] for 0 <= u < t. -/
  theorem spec_12
    (s1 s2 s3 : Slice U8) (hValid : Valid s1 s2 s3)
    (hres : Aegis.IsInterleave.is_interleave s1 s2 s3 = ok true) (k : ℕ) (hk : k ≤ s3.length) :
    ∃ i j : ℕ, i ≤ s1.length ∧ j ≤ s2.length ∧ i + j = k ∧
      IsShuffle (suffixOf s1 i) (suffixOf s2 j) (suffixOf s3 k) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (s1 s2 s3 : Slice U8) (hValid : Valid s1 s2 s3)
      (hres : Aegis.IsInterleave.is_interleave s1 s2 s3 = ok true) (k : ℕ) (hk : k ≤ s3.length), ∃ i j : ℕ, i ≤ s1.length ∧ j ≤ s2.length ∧ i + j = k ∧
        IsShuffle (suffixOf s1 i) (suffixOf s2 j) (suffixOf s3 k)) := by
    sorry

  /-- For every Valid s1,s2,s3, whenever is_interleave(s1,s2,s3) returns true, there exist integers n >= 0 and m >= 0 with |n-m| <= 1 and byte substrings u_0,...,u_{n-1} (if n > 0) and v_0,...,v_{m-1} (if m > 0) such that: s1 is the concatenation u_0+...+u_{n-1}; s2 is the concatenation v_0+...+v_{m-1}; every u_i and v_j is nonempty, except that if s1 is empty then n=0 and if s2 is empty then m=0; and s3 is one of the two alternating concatenations u_0+v_0+u_1+v_1+... or v_0+u_0+v_1+u_1+..., where missing parts at the end are omitted and the expression stops when all existing parts have been used.
    Preconditions: Let Valid be as in spec_1. -/
  theorem spec_13
    (s1 s2 s3 : Slice U8) (hValid : Valid s1 s2 s3)
    (hres : Aegis.IsInterleave.is_interleave s1 s2 s3 = ok true) :
    ∃ u v : List (List U8),
      u.length ≤ v.length + 1 ∧ v.length ≤ u.length + 1 ∧
        (∀ x ∈ u, x ≠ []) ∧ (∀ y ∈ v, y ≠ []) ∧
        (s1.val = [] → u = []) ∧ (s2.val = [] → v = []) ∧
        u.flatten = s1.val ∧ v.flatten = s2.val ∧
        (s3.val = (interleaveBlocks u v).flatten ∨
          s3.val = (interleaveBlocks v u).flatten) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (s1 s2 s3 : Slice U8) (hValid : Valid s1 s2 s3)
      (hres : Aegis.IsInterleave.is_interleave s1 s2 s3 = ok true), ∃ u v : List (List U8),
        u.length ≤ v.length + 1 ∧ v.length ≤ u.length + 1 ∧
          (∀ x ∈ u, x ≠ []) ∧ (∀ y ∈ v, y ≠ []) ∧
          (s1.val = [] → u = []) ∧ (s2.val = [] → v = []) ∧
          u.flatten = s1.val ∧ v.flatten = s2.val ∧
          (s3.val = (interleaveBlocks u v).flatten ∨
            s3.val = (interleaveBlocks v u).flatten)) := by
    sorry

  /-- For every Valid s1,s2,s3, is_interleave(s1,s2,s3) returns a result (either true or false) and does not fail: no overflow, out-of-bounds access, panic, or other failure occurs.
    Preconditions: Let Valid be as in spec_1. -/
  theorem spec_14
    (s1 s2 s3 : Slice U8) (hValid : Valid s1 s2 s3) :
    ∃ r : Bool, Aegis.IsInterleave.is_interleave s1 s2 s3 = ok r := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (s1 s2 s3 : Slice U8) (hValid : Valid s1 s2 s3), ∃ r : Bool, Aegis.IsInterleave.is_interleave s1 s2 s3 = ok r) := by
    sorry

  end AegisSpec.IsInterleave

import Aegis.CanMakePaliQueries.Code.Funs

/-!
# Specifications of `Aegis.CanMakePaliQueries.can_make_pali_queries`

LeetCode problem `can-make-palindrome-from-substring`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CanMakePaliQueries

  open Aegis.CanMakePaliQueries

  def IsLowerByte (b : Std.U8) : Prop := 97 ≤ b.val ∧ b.val ≤ 122

  def queryInts (v : alloc.vec.Vec Std.I64) : List ℤ := v.val.map (fun x => x.val)

  def subLetters (s : Slice Std.U8) (l r : ℕ) : List ℕ :=
    ((s.val.drop l).take (r + 1 - l)).map (fun b => b.val)

  def countIn (t : List ℕ) (c : ℕ) : ℕ := t.countP (fun d => d = c)

  def freqIn (s : Slice Std.U8) (l r c : ℕ) : ℕ := countIn (subLetters s l r) c

  def oddCount (s : Slice Std.U8) (l r : ℕ) : ℕ :=
    (List.range 26).countP (fun i => (freqIn s l r (97 + i)) % 2 == 1)

  def IsLowerLetters (t : List ℕ) : Prop := ∀ c ∈ t, 97 ≤ c ∧ c ≤ 122

  def replaceCost (src t : List ℕ) : ℕ :=
    ((List.range 26).map (fun i => max 0 (countIn t (97 + i) - countIn src (97 + i)))).sum

  /-- Whenever the function returns a result answer, answer has length len(queries); and for every j with 0 <= j < len(queries), if l=queries[j][0], r=queries[j][1], k=queries[j][2], then answer[j] is true if and only if odd(l,r) <= 2*k + 1, where odd(l,r) is the number of letters c in {'a',...,'z'} whose frequency among s[l], s[l+1], ..., s[r] is odd.
    Preconditions: len(s) and len(queries) are each between 1 and 100000. Every byte s[i] is the ASCII code of a lowercase English letter ('a' through 'z'). For every j with 0 <= j < len(queries), queries[j] has exactly three components; writing l=queries[j][0], r=queries[j][1], k=queries[j][2], we have 0 <= l <= r < len(s) and 0 <= k <= len(s). Indices are 0-based and s[l..r] includes both endpoints. -/
  theorem spec_1 (s : Slice Std.U8) (queries : Slice (alloc.vec.Vec Std.I64))
      (h_s_len : 1 ≤ s.val.length ∧ s.val.length ≤ 100000)
      (h_q_len : 1 ≤ queries.val.length ∧ queries.val.length ≤ 100000)
      (h_s_letters : ∀ i (hi : i < s.val.length), IsLowerByte s.val[i])
      (h_q_wellformed : ∀ j (hj : j < queries.val.length), ∃ l r k : ℤ,
        queryInts queries.val[j] = [l, r, k] ∧
          0 ≤ l ∧ l ≤ r ∧ r < (s.val.length : ℤ) ∧ 0 ≤ k ∧ k ≤ (s.val.length : ℤ))
      (answer : alloc.vec.Vec Bool)
      (h_run : can_make_pali_queries s queries = ok answer) :
      answer.val.length = queries.val.length ∧
        ∀ j (hj : j < queries.val.length) (l r k : ℤ),
          queryInts queries.val[j] = [l, r, k] →
          0 ≤ l → l ≤ r → r < (s.val.length : ℤ) →
          0 ≤ k → k ≤ (s.val.length : ℤ) →
          (answer.val.getD j false = true ↔
            (oddCount s l.toNat r.toNat : ℤ) ≤ 2 * k + 1) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice Std.U8) (queries : Slice (alloc.vec.Vec Std.I64))
        (h_s_len : 1 ≤ s.val.length ∧ s.val.length ≤ 100000)
        (h_q_len : 1 ≤ queries.val.length ∧ queries.val.length ≤ 100000)
        (h_s_letters : ∀ i (hi : i < s.val.length), IsLowerByte s.val[i])
        (h_q_wellformed : ∀ j (hj : j < queries.val.length), ∃ l r k : ℤ,
          queryInts queries.val[j] = [l, r, k] ∧
            0 ≤ l ∧ l ≤ r ∧ r < (s.val.length : ℤ) ∧ 0 ≤ k ∧ k ≤ (s.val.length : ℤ))
        (answer : alloc.vec.Vec Bool)
        (h_run : can_make_pali_queries s queries = ok answer), answer.val.length = queries.val.length ∧
          ∀ j (hj : j < queries.val.length) (l r k : ℤ),
            queryInts queries.val[j] = [l, r, k] →
            0 ≤ l → l ≤ r → r < (s.val.length : ℤ) →
            0 ≤ k → k ≤ (s.val.length : ℤ) →
            (answer.val.getD j false = true ↔
              (oddCount s l.toNat r.toNat : ℤ) ≤ 2 * k + 1)) := by
    sorry

  /-- Under the preconditions, the function returns a result answer; in particular it does not panic, access out of bounds, or fail from integer overflow.
    Preconditions: len(s) and len(queries) are each between 1 and 100000. Every byte s[i] is the ASCII code of a lowercase English letter ('a' through 'z'). For every j with 0 <= j < len(queries), queries[j] has exactly three components; writing l=queries[j][0], r=queries[j][1], k=queries[j][2], we have 0 <= l <= r < len(s) and 0 <= k <= len(s). Indices are 0-based and s[l..r] includes both endpoints. -/
  theorem spec_2 (s : Slice Std.U8) (queries : Slice (alloc.vec.Vec Std.I64))
      (h_s_len : 1 ≤ s.val.length ∧ s.val.length ≤ 100000)
      (h_q_len : 1 ≤ queries.val.length ∧ queries.val.length ≤ 100000)
      (h_s_letters : ∀ i (hi : i < s.val.length), IsLowerByte s.val[i])
      (h_q_wellformed : ∀ j (hj : j < queries.val.length), ∃ l r k : ℤ,
        queryInts queries.val[j] = [l, r, k] ∧
          0 ≤ l ∧ l ≤ r ∧ r < (s.val.length : ℤ) ∧ 0 ≤ k ∧ k ≤ (s.val.length : ℤ)) :
      ∃ answer : alloc.vec.Vec Bool, can_make_pali_queries s queries = ok answer := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice Std.U8) (queries : Slice (alloc.vec.Vec Std.I64))
        (h_s_len : 1 ≤ s.val.length ∧ s.val.length ≤ 100000)
        (h_q_len : 1 ≤ queries.val.length ∧ queries.val.length ≤ 100000)
        (h_s_letters : ∀ i (hi : i < s.val.length), IsLowerByte s.val[i])
        (h_q_wellformed : ∀ j (hj : j < queries.val.length), ∃ l r k : ℤ,
          queryInts queries.val[j] = [l, r, k] ∧
            0 ≤ l ∧ l ≤ r ∧ r < (s.val.length : ℤ) ∧ 0 ≤ k ∧ k ≤ (s.val.length : ℤ)), ∃ answer : alloc.vec.Vec Bool, can_make_pali_queries s queries = ok answer) := by
    sorry

  /-- Whenever the function returns a result answer, for every j with 0 <= j < len(queries) such that answer[j] is true, let l=queries[j][0], r=queries[j][1], k=queries[j][2] and L=r-l+1. There exists a palindrome t of length L over lowercase English letters such that the minimum number of single-character replacements needed to change the multiset of letters in s[l..r] into the multiset of letters in t is at most k; equivalently, sum_{c in {'a',...,'z'}} max(0, freq_t(c) - freq_s(c;l,r)) <= k.
    Preconditions: len(s) and len(queries) are each between 1 and 100000. Every byte s[i] is the ASCII code of a lowercase English letter ('a' through 'z'). For every j with 0 <= j < len(queries), queries[j] has exactly three components; writing l=queries[j][0], r=queries[j][1], k=queries[j][2], we have 0 <= l <= r < len(s) and 0 <= k <= len(s). Indices are 0-based and s[l..r] includes both endpoints. -/
  theorem spec_3 (s : Slice Std.U8) (queries : Slice (alloc.vec.Vec Std.I64))
      (h_s_len : 1 ≤ s.val.length ∧ s.val.length ≤ 100000)
      (h_q_len : 1 ≤ queries.val.length ∧ queries.val.length ≤ 100000)
      (h_s_letters : ∀ i (hi : i < s.val.length), IsLowerByte s.val[i])
      (h_q_wellformed : ∀ j (hj : j < queries.val.length), ∃ l r k : ℤ,
        queryInts queries.val[j] = [l, r, k] ∧
          0 ≤ l ∧ l ≤ r ∧ r < (s.val.length : ℤ) ∧ 0 ≤ k ∧ k ≤ (s.val.length : ℤ))
      (answer : alloc.vec.Vec Bool)
      (h_run : can_make_pali_queries s queries = ok answer) :
      ∀ j (hj : j < queries.val.length) (l r k : ℤ),
        queryInts queries.val[j] = [l, r, k] →
        0 ≤ l → l ≤ r → r < (s.val.length : ℤ) →
        0 ≤ k → k ≤ (s.val.length : ℤ) →
        answer.val.getD j false = true →
        ∃ t : List ℕ, IsLowerLetters t ∧ t.length = (r - l + 1).toNat ∧ t.reverse = t ∧
          (replaceCost (subLetters s l.toNat r.toNat) t : ℤ) ≤ k := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice Std.U8) (queries : Slice (alloc.vec.Vec Std.I64))
        (h_s_len : 1 ≤ s.val.length ∧ s.val.length ≤ 100000)
        (h_q_len : 1 ≤ queries.val.length ∧ queries.val.length ≤ 100000)
        (h_s_letters : ∀ i (hi : i < s.val.length), IsLowerByte s.val[i])
        (h_q_wellformed : ∀ j (hj : j < queries.val.length), ∃ l r k : ℤ,
          queryInts queries.val[j] = [l, r, k] ∧
            0 ≤ l ∧ l ≤ r ∧ r < (s.val.length : ℤ) ∧ 0 ≤ k ∧ k ≤ (s.val.length : ℤ))
        (answer : alloc.vec.Vec Bool)
        (h_run : can_make_pali_queries s queries = ok answer), ∀ j (hj : j < queries.val.length) (l r k : ℤ),
          queryInts queries.val[j] = [l, r, k] →
          0 ≤ l → l ≤ r → r < (s.val.length : ℤ) →
          0 ≤ k → k ≤ (s.val.length : ℤ) →
          answer.val.getD j false = true →
          ∃ t : List ℕ, IsLowerLetters t ∧ t.length = (r - l + 1).toNat ∧ t.reverse = t ∧
            (replaceCost (subLetters s l.toNat r.toNat) t : ℤ) ≤ k) := by
    sorry

  /-- Whenever the function returns a result answer, for any indices p,q with 0<=p,q<len(queries), if queries[p][0]=queries[q][0], queries[p][1]=queries[q][1], and queries[p][2] <= queries[q][2], then answer[p]=true implies answer[q]=true.
    Preconditions: len(s) and len(queries) are each between 1 and 100000. Every byte s[i] is the ASCII code of a lowercase English letter ('a' through 'z'). For every j with 0 <= j < len(queries), queries[j] has exactly three components; writing l=queries[j][0], r=queries[j][1], k=queries[j][2], we have 0 <= l <= r < len(s) and 0 <= k <= len(s). Indices are 0-based and s[l..r] includes both endpoints. -/
  theorem spec_4 (s : Slice Std.U8) (queries : Slice (alloc.vec.Vec Std.I64))
      (h_s_len : 1 ≤ s.val.length ∧ s.val.length ≤ 100000)
      (h_q_len : 1 ≤ queries.val.length ∧ queries.val.length ≤ 100000)
      (h_s_letters : ∀ i (hi : i < s.val.length), IsLowerByte s.val[i])
      (h_q_wellformed : ∀ j (hj : j < queries.val.length), ∃ l r k : ℤ,
        queryInts queries.val[j] = [l, r, k] ∧
          0 ≤ l ∧ l ≤ r ∧ r < (s.val.length : ℤ) ∧ 0 ≤ k ∧ k ≤ (s.val.length : ℤ))
      (answer : alloc.vec.Vec Bool)
      (h_run : can_make_pali_queries s queries = ok answer) :
      ∀ p (hp : p < queries.val.length) (q : ℕ) (hq : q < queries.val.length)
        (l r kp kq : ℤ),
        queryInts queries.val[p] = [l, r, kp] →
        queryInts queries.val[q] = [l, r, kq] →
        kp ≤ kq →
        answer.val.getD p false = true → answer.val.getD q false = true := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice Std.U8) (queries : Slice (alloc.vec.Vec Std.I64))
        (h_s_len : 1 ≤ s.val.length ∧ s.val.length ≤ 100000)
        (h_q_len : 1 ≤ queries.val.length ∧ queries.val.length ≤ 100000)
        (h_s_letters : ∀ i (hi : i < s.val.length), IsLowerByte s.val[i])
        (h_q_wellformed : ∀ j (hj : j < queries.val.length), ∃ l r k : ℤ,
          queryInts queries.val[j] = [l, r, k] ∧
            0 ≤ l ∧ l ≤ r ∧ r < (s.val.length : ℤ) ∧ 0 ≤ k ∧ k ≤ (s.val.length : ℤ))
        (answer : alloc.vec.Vec Bool)
        (h_run : can_make_pali_queries s queries = ok answer), ∀ p (hp : p < queries.val.length) (q : ℕ) (hq : q < queries.val.length)
          (l r kp kq : ℤ),
          queryInts queries.val[p] = [l, r, kp] →
          queryInts queries.val[q] = [l, r, kq] →
          kp ≤ kq →
          answer.val.getD p false = true → answer.val.getD q false = true) := by
    sorry

  /-- Whenever the function returns a result answer, for every j with 0<=j<len(queries), let l=queries[j][0], r=queries[j][1], k=queries[j][2], L=r-l+1. If k >= floor(L/2), then answer[j] is true.
    Preconditions: len(s) and len(queries) are each between 1 and 100000. Every byte s[i] is the ASCII code of a lowercase English letter ('a' through 'z'). For every j with 0 <= j < len(queries), queries[j] has exactly three components; writing l=queries[j][0], r=queries[j][1], k=queries[j][2], we have 0 <= l <= r < len(s) and 0 <= k <= len(s). Indices are 0-based and s[l..r] includes both endpoints. -/
  theorem spec_5 (s : Slice Std.U8) (queries : Slice (alloc.vec.Vec Std.I64))
      (h_s_len : 1 ≤ s.val.length ∧ s.val.length ≤ 100000)
      (h_q_len : 1 ≤ queries.val.length ∧ queries.val.length ≤ 100000)
      (h_s_letters : ∀ i (hi : i < s.val.length), IsLowerByte s.val[i])
      (h_q_wellformed : ∀ j (hj : j < queries.val.length), ∃ l r k : ℤ,
        queryInts queries.val[j] = [l, r, k] ∧
          0 ≤ l ∧ l ≤ r ∧ r < (s.val.length : ℤ) ∧ 0 ≤ k ∧ k ≤ (s.val.length : ℤ))
      (answer : alloc.vec.Vec Bool)
      (h_run : can_make_pali_queries s queries = ok answer) :
      ∀ j (hj : j < queries.val.length) (l r k : ℤ),
        queryInts queries.val[j] = [l, r, k] →
        0 ≤ l → l ≤ r → r < (s.val.length : ℤ) →
        0 ≤ k → k ≤ (s.val.length : ℤ) →
        (r - l + 1) / 2 ≤ k →
        answer.val.getD j false = true := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice Std.U8) (queries : Slice (alloc.vec.Vec Std.I64))
        (h_s_len : 1 ≤ s.val.length ∧ s.val.length ≤ 100000)
        (h_q_len : 1 ≤ queries.val.length ∧ queries.val.length ≤ 100000)
        (h_s_letters : ∀ i (hi : i < s.val.length), IsLowerByte s.val[i])
        (h_q_wellformed : ∀ j (hj : j < queries.val.length), ∃ l r k : ℤ,
          queryInts queries.val[j] = [l, r, k] ∧
            0 ≤ l ∧ l ≤ r ∧ r < (s.val.length : ℤ) ∧ 0 ≤ k ∧ k ≤ (s.val.length : ℤ))
        (answer : alloc.vec.Vec Bool)
        (h_run : can_make_pali_queries s queries = ok answer), ∀ j (hj : j < queries.val.length) (l r k : ℤ),
          queryInts queries.val[j] = [l, r, k] →
          0 ≤ l → l ≤ r → r < (s.val.length : ℤ) →
          0 ≤ k → k ≤ (s.val.length : ℤ) →
          (r - l + 1) / 2 ≤ k →
          answer.val.getD j false = true) := by
    sorry

  /-- Whenever the function returns results for (s,queries) and for (s',queries), for every j with 0<=j<len(queries), if for every letter c in {'a',...,'z'} the count of c in s[l..r] equals the count of c in s'[l..r], where l=queries[j][0], r=queries[j][1], then the j-th entry of the first answer equals the j-th entry of the second answer.
    Preconditions: len(s) and len(queries) are each between 1 and 100000. Every byte s[i] is the ASCII code of a lowercase English letter ('a' through 'z'). For every j with 0 <= j < len(queries), queries[j] has exactly three components; writing l=queries[j][0], r=queries[j][1], k=queries[j][2], we have 0 <= l <= r < len(s) and 0 <= k <= len(s). The slice s' is another byte slice of the same length as s, also consisting of ASCII lowercase English letters. -/
  theorem spec_6 (s s' : Slice Std.U8) (queries : Slice (alloc.vec.Vec Std.I64))
      (h_s_len : 1 ≤ s.val.length ∧ s.val.length ≤ 100000)
      (h_q_len : 1 ≤ queries.val.length ∧ queries.val.length ≤ 100000)
      (h_s_letters : ∀ i (hi : i < s.val.length), IsLowerByte s.val[i])
      (h_s'_len : s'.val.length = s.val.length)
      (h_s'_letters : ∀ i (hi : i < s'.val.length), IsLowerByte s'.val[i])
      (h_q_wellformed : ∀ j (hj : j < queries.val.length), ∃ l r k : ℤ,
        queryInts queries.val[j] = [l, r, k] ∧
          0 ≤ l ∧ l ≤ r ∧ r < (s.val.length : ℤ) ∧ 0 ≤ k ∧ k ≤ (s.val.length : ℤ))
      (answer answer' : alloc.vec.Vec Bool)
      (h_run : can_make_pali_queries s queries = ok answer)
      (h_run' : can_make_pali_queries s' queries = ok answer') :
      ∀ j (hj : j < queries.val.length) (l r k : ℤ),
        queryInts queries.val[j] = [l, r, k] →
        0 ≤ l → l ≤ r → r < (s.val.length : ℤ) →
        0 ≤ k → k ≤ (s.val.length : ℤ) →
        (∀ c : ℕ, c < 26 →
          freqIn s l.toNat r.toNat (97 + c) = freqIn s' l.toNat r.toNat (97 + c)) →
        answer.val.getD j false = answer'.val.getD j false := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s s' : Slice Std.U8) (queries : Slice (alloc.vec.Vec Std.I64))
        (h_s_len : 1 ≤ s.val.length ∧ s.val.length ≤ 100000)
        (h_q_len : 1 ≤ queries.val.length ∧ queries.val.length ≤ 100000)
        (h_s_letters : ∀ i (hi : i < s.val.length), IsLowerByte s.val[i])
        (h_s'_len : s'.val.length = s.val.length)
        (h_s'_letters : ∀ i (hi : i < s'.val.length), IsLowerByte s'.val[i])
        (h_q_wellformed : ∀ j (hj : j < queries.val.length), ∃ l r k : ℤ,
          queryInts queries.val[j] = [l, r, k] ∧
            0 ≤ l ∧ l ≤ r ∧ r < (s.val.length : ℤ) ∧ 0 ≤ k ∧ k ≤ (s.val.length : ℤ))
        (answer answer' : alloc.vec.Vec Bool)
        (h_run : can_make_pali_queries s queries = ok answer)
        (h_run' : can_make_pali_queries s' queries = ok answer'), ∀ j (hj : j < queries.val.length) (l r k : ℤ),
          queryInts queries.val[j] = [l, r, k] →
          0 ≤ l → l ≤ r → r < (s.val.length : ℤ) →
          0 ≤ k → k ≤ (s.val.length : ℤ) →
          (∀ c : ℕ, c < 26 →
            freqIn s l.toNat r.toNat (97 + c) = freqIn s' l.toNat r.toNat (97 + c)) →
          answer.val.getD j false = answer'.val.getD j false) := by
    sorry

  /-- Whenever the function returns results for (s,Q) and for (s,Q'), for every j with 0<=j<len(Q) (and len(Q)=len(Q')), if Q[j] and Q'[j] are the same triple, then the j-th entry of the first answer equals the j-th entry of the second answer.
    Preconditions: len(s) is between 1 and 100000. Every byte s[i] is the ASCII code of a lowercase English letter ('a' through 'z'). Q and Q' are two query vectors of the same length satisfying the query preconditions for s: each entry has exactly three components, and for every j, writing l=Q[j][0], r=Q[j][1], k=Q[j][2], we have 0 <= l <= r < len(s) and 0 <= k <= len(s); the same holds for Q'. -/
  theorem spec_7 (s : Slice Std.U8) (Q Q' : Slice (alloc.vec.Vec Std.I64))
      (h_s_len : 1 ≤ s.val.length ∧ s.val.length ≤ 100000)
      (h_s_letters : ∀ i (hi : i < s.val.length), IsLowerByte s.val[i])
      (h_Q_len : Q.val.length = Q'.val.length)
      (h_Q_wellformed : ∀ j (hj : j < Q.val.length), ∃ l r k : ℤ,
        queryInts Q.val[j] = [l, r, k] ∧
          0 ≤ l ∧ l ≤ r ∧ r < (s.val.length : ℤ) ∧ 0 ≤ k ∧ k ≤ (s.val.length : ℤ))
      (h_Q'_wellformed : ∀ j (hj : j < Q'.val.length), ∃ l r k : ℤ,
        queryInts Q'.val[j] = [l, r, k] ∧
          0 ≤ l ∧ l ≤ r ∧ r < (s.val.length : ℤ) ∧ 0 ≤ k ∧ k ≤ (s.val.length : ℤ))
      (answer answer' : alloc.vec.Vec Bool)
      (h_run : can_make_pali_queries s Q = ok answer)
      (h_run' : can_make_pali_queries s Q' = ok answer') :
      ∀ j (hj : j < Q.val.length) (hj' : j < Q'.val.length) (l r k : ℤ),
        queryInts Q.val[j] = [l, r, k] →
        queryInts Q'.val[j] = [l, r, k] →
        answer.val.getD j false = answer'.val.getD j false := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s : Slice Std.U8) (Q Q' : Slice (alloc.vec.Vec Std.I64))
        (h_s_len : 1 ≤ s.val.length ∧ s.val.length ≤ 100000)
        (h_s_letters : ∀ i (hi : i < s.val.length), IsLowerByte s.val[i])
        (h_Q_len : Q.val.length = Q'.val.length)
        (h_Q_wellformed : ∀ j (hj : j < Q.val.length), ∃ l r k : ℤ,
          queryInts Q.val[j] = [l, r, k] ∧
            0 ≤ l ∧ l ≤ r ∧ r < (s.val.length : ℤ) ∧ 0 ≤ k ∧ k ≤ (s.val.length : ℤ))
        (h_Q'_wellformed : ∀ j (hj : j < Q'.val.length), ∃ l r k : ℤ,
          queryInts Q'.val[j] = [l, r, k] ∧
            0 ≤ l ∧ l ≤ r ∧ r < (s.val.length : ℤ) ∧ 0 ≤ k ∧ k ≤ (s.val.length : ℤ))
        (answer answer' : alloc.vec.Vec Bool)
        (h_run : can_make_pali_queries s Q = ok answer)
        (h_run' : can_make_pali_queries s Q' = ok answer'), ∀ j (hj : j < Q.val.length) (hj' : j < Q'.val.length) (l r k : ℤ),
          queryInts Q.val[j] = [l, r, k] →
          queryInts Q'.val[j] = [l, r, k] →
          answer.val.getD j false = answer'.val.getD j false) := by
    sorry

  /-- Whenever the function returns a result answer, for every j with 0<=j<len(queries), if queries[j][2] >= 13, then answer[j] is true.
    Preconditions: len(s) and len(queries) are each between 1 and 100000. Every byte s[i] is the ASCII code of a lowercase English letter ('a' through 'z'). For every j with 0 <= j < len(queries), queries[j] has exactly three components; writing l=queries[j][0], r=queries[j][1], k=queries[j][2], we have 0 <= l <= r < len(s) and 0 <= k <= len(s). Indices are 0-based and s[l..r] includes both endpoints. -/
  theorem spec_8 (s : Slice Std.U8) (queries : Slice (alloc.vec.Vec Std.I64))
      (h_s_len : 1 ≤ s.val.length ∧ s.val.length ≤ 100000)
      (h_q_len : 1 ≤ queries.val.length ∧ queries.val.length ≤ 100000)
      (h_s_letters : ∀ i (hi : i < s.val.length), IsLowerByte s.val[i])
      (h_q_wellformed : ∀ j (hj : j < queries.val.length), ∃ l r k : ℤ,
        queryInts queries.val[j] = [l, r, k] ∧
          0 ≤ l ∧ l ≤ r ∧ r < (s.val.length : ℤ) ∧ 0 ≤ k ∧ k ≤ (s.val.length : ℤ))
      (answer : alloc.vec.Vec Bool)
      (h_run : can_make_pali_queries s queries = ok answer) :
      ∀ j (hj : j < queries.val.length) (l r k : ℤ),
        queryInts queries.val[j] = [l, r, k] →
        0 ≤ l → l ≤ r → r < (s.val.length : ℤ) →
        0 ≤ k → k ≤ (s.val.length : ℤ) →
        13 ≤ k →
        answer.val.getD j false = true := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s : Slice Std.U8) (queries : Slice (alloc.vec.Vec Std.I64))
        (h_s_len : 1 ≤ s.val.length ∧ s.val.length ≤ 100000)
        (h_q_len : 1 ≤ queries.val.length ∧ queries.val.length ≤ 100000)
        (h_s_letters : ∀ i (hi : i < s.val.length), IsLowerByte s.val[i])
        (h_q_wellformed : ∀ j (hj : j < queries.val.length), ∃ l r k : ℤ,
          queryInts queries.val[j] = [l, r, k] ∧
            0 ≤ l ∧ l ≤ r ∧ r < (s.val.length : ℤ) ∧ 0 ≤ k ∧ k ≤ (s.val.length : ℤ))
        (answer : alloc.vec.Vec Bool)
        (h_run : can_make_pali_queries s queries = ok answer), ∀ j (hj : j < queries.val.length) (l r k : ℤ),
          queryInts queries.val[j] = [l, r, k] →
          0 ≤ l → l ≤ r → r < (s.val.length : ℤ) →
          0 ≤ k → k ≤ (s.val.length : ℤ) →
          13 ≤ k →
          answer.val.getD j false = true) := by
    sorry

  /-- Whenever the function returns a result answer, for any p,q with 0<=p,q<len(queries), let odd_p be the number of letters c in {'a',...,'z'} whose count in s[queries[p][0]..queries[p][1]] is odd, and let odd_q be the analogous number for q. If queries[p][2]=queries[q][2] and odd_p <= odd_q and answer[q] is true, then answer[p] is true.
    Preconditions: len(s) and len(queries) are each between 1 and 100000. Every byte s[i] is the ASCII code of a lowercase English letter ('a' through 'z'). For every j with 0 <= j < len(queries), queries[j] has exactly three components; writing l=queries[j][0], r=queries[j][1], k=queries[j][2], we have 0 <= l <= r < len(s) and 0 <= k <= len(s). Indices are 0-based and s[l..r] includes both endpoints. -/
  theorem spec_9 (s : Slice Std.U8) (queries : Slice (alloc.vec.Vec Std.I64))
      (h_s_len : 1 ≤ s.val.length ∧ s.val.length ≤ 100000)
      (h_q_len : 1 ≤ queries.val.length ∧ queries.val.length ≤ 100000)
      (h_s_letters : ∀ i (hi : i < s.val.length), IsLowerByte s.val[i])
      (h_q_wellformed : ∀ j (hj : j < queries.val.length), ∃ l r k : ℤ,
        queryInts queries.val[j] = [l, r, k] ∧
          0 ≤ l ∧ l ≤ r ∧ r < (s.val.length : ℤ) ∧ 0 ≤ k ∧ k ≤ (s.val.length : ℤ))
      (answer : alloc.vec.Vec Bool)
      (h_run : can_make_pali_queries s queries = ok answer) :
      ∀ p (hp : p < queries.val.length) (q : ℕ) (hq : q < queries.val.length)
        (lp rp kp lq rq kq : ℤ),
        queryInts queries.val[p] = [lp, rp, kp] →
        queryInts queries.val[q] = [lq, rq, kq] →
        kp = kq →
        oddCount s lp.toNat rp.toNat ≤ oddCount s lq.toNat rq.toNat →
        answer.val.getD q false = true → answer.val.getD p false = true := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s : Slice Std.U8) (queries : Slice (alloc.vec.Vec Std.I64))
        (h_s_len : 1 ≤ s.val.length ∧ s.val.length ≤ 100000)
        (h_q_len : 1 ≤ queries.val.length ∧ queries.val.length ≤ 100000)
        (h_s_letters : ∀ i (hi : i < s.val.length), IsLowerByte s.val[i])
        (h_q_wellformed : ∀ j (hj : j < queries.val.length), ∃ l r k : ℤ,
          queryInts queries.val[j] = [l, r, k] ∧
            0 ≤ l ∧ l ≤ r ∧ r < (s.val.length : ℤ) ∧ 0 ≤ k ∧ k ≤ (s.val.length : ℤ))
        (answer : alloc.vec.Vec Bool)
        (h_run : can_make_pali_queries s queries = ok answer), ∀ p (hp : p < queries.val.length) (q : ℕ) (hq : q < queries.val.length)
          (lp rp kp lq rq kq : ℤ),
          queryInts queries.val[p] = [lp, rp, kp] →
          queryInts queries.val[q] = [lq, rq, kq] →
          kp = kq →
          oddCount s lp.toNat rp.toNat ≤ oddCount s lq.toNat rq.toNat →
          answer.val.getD q false = true → answer.val.getD p false = true) := by
    sorry

  /-- Whenever the function returns a result answer, for every j with 0<=j<len(queries) such that answer[j] is false, let l=queries[j][0], r=queries[j][1], k=queries[j][2] and L=r-l+1. For every palindrome t of length L over lowercase English letters, the minimum number of single-character replacements needed to change the multiset of letters in s[l..r] into the multiset of letters in t is greater than k; equivalently, sum_{c in {'a',...,'z'}} max(0, freq_t(c) - freq_s(c;l,r)) > k.
    Preconditions: len(s) and len(queries) are each between 1 and 100000. Every byte s[i] is the ASCII code of a lowercase English letter ('a' through 'z'). For every j with 0 <= j < len(queries), queries[j] has exactly three components; writing l=queries[j][0], r=queries[j][1], k=queries[j][2], we have 0 <= l <= r < len(s) and 0 <= k <= len(s). Indices are 0-based and s[l..r] includes both endpoints. -/
  theorem spec_10 (s : Slice Std.U8) (queries : Slice (alloc.vec.Vec Std.I64))
      (h_s_len : 1 ≤ s.val.length ∧ s.val.length ≤ 100000)
      (h_q_len : 1 ≤ queries.val.length ∧ queries.val.length ≤ 100000)
      (h_s_letters : ∀ i (hi : i < s.val.length), IsLowerByte s.val[i])
      (h_q_wellformed : ∀ j (hj : j < queries.val.length), ∃ l r k : ℤ,
        queryInts queries.val[j] = [l, r, k] ∧
          0 ≤ l ∧ l ≤ r ∧ r < (s.val.length : ℤ) ∧ 0 ≤ k ∧ k ≤ (s.val.length : ℤ))
      (answer : alloc.vec.Vec Bool)
      (h_run : can_make_pali_queries s queries = ok answer) :
      ∀ j (hj : j < queries.val.length) (l r k : ℤ),
        queryInts queries.val[j] = [l, r, k] →
        0 ≤ l → l ≤ r → r < (s.val.length : ℤ) →
        0 ≤ k → k ≤ (s.val.length : ℤ) →
        answer.val.getD j false = false →
        ∀ t : List ℕ, IsLowerLetters t → t.length = (r - l + 1).toNat → t.reverse = t →
          k < (replaceCost (subLetters s l.toNat r.toNat) t : ℤ) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s : Slice Std.U8) (queries : Slice (alloc.vec.Vec Std.I64))
        (h_s_len : 1 ≤ s.val.length ∧ s.val.length ≤ 100000)
        (h_q_len : 1 ≤ queries.val.length ∧ queries.val.length ≤ 100000)
        (h_s_letters : ∀ i (hi : i < s.val.length), IsLowerByte s.val[i])
        (h_q_wellformed : ∀ j (hj : j < queries.val.length), ∃ l r k : ℤ,
          queryInts queries.val[j] = [l, r, k] ∧
            0 ≤ l ∧ l ≤ r ∧ r < (s.val.length : ℤ) ∧ 0 ≤ k ∧ k ≤ (s.val.length : ℤ))
        (answer : alloc.vec.Vec Bool)
        (h_run : can_make_pali_queries s queries = ok answer), ∀ j (hj : j < queries.val.length) (l r k : ℤ),
          queryInts queries.val[j] = [l, r, k] →
          0 ≤ l → l ≤ r → r < (s.val.length : ℤ) →
          0 ≤ k → k ≤ (s.val.length : ℤ) →
          answer.val.getD j false = false →
          ∀ t : List ℕ, IsLowerLetters t → t.length = (r - l + 1).toNat → t.reverse = t →
            k < (replaceCost (subLetters s l.toNat r.toNat) t : ℤ)) := by
    sorry

  end AegisSpec.CanMakePaliQueries

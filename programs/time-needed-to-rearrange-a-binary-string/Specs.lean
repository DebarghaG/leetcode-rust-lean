import Aegis.SecondsToRemoveOccurrences.Code.Funs

/-!
# Specifications of `Aegis.SecondsToRemoveOccurrences.seconds_to_remove_occurrences`

LeetCode problem `time-needed-to-rearrange-a-binary-string`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.SecondsToRemoveOccurrences

  abbrev byte0 : Std.U8 := 48#u8

  abbrev byte1 : Std.U8 := 49#u8

  def byteAt (l : List Std.U8) (i : ℕ) : Std.U8 := l.getD i byte0

  def IsBinary (l : List Std.U8) : Prop :=
    ∀ i, i < l.length → byteAt l i = byte0 ∨ byteAt l i = byte1

  def IsOccurrence (l : List Std.U8) (i : ℕ) : Prop :=
    i + 1 < l.length ∧ byteAt l i = byte0 ∧ byteAt l (i + 1) = byte1

  def HasOccurrence (l : List Std.U8) : Prop := ∃ i, IsOccurrence l i

  def IsStep (x y : List Std.U8) : Prop :=
    y.length = x.length ∧
    (∀ i, IsOccurrence x i → byteAt y i = byte1 ∧ byteAt y (i + 1) = byte0) ∧
    (∀ j, j < x.length → (∀ i, IsOccurrence x i → j ≠ i ∧ j ≠ i + 1) →
      byteAt y j = byteAt x j)

  noncomputable def stepList (x : List Std.U8) : List Std.U8 :=
    by
      classical
      exact if h : ∃ y, IsStep x y then Classical.choose h else x

  noncomputable def orbit (x : List Std.U8) : ℕ → List Std.U8
    | 0 => x
    | t + 1 => stepList (orbit x t)

  noncomputable def IsFirstStable (x : List Std.U8) (t : ℕ) : Prop :=
    ¬ HasOccurrence (orbit x t) ∧ ∀ u, u < t → HasOccurrence (orbit x u)

  def zerosBefore (l : List Std.U8) (i : ℕ) : ℕ :=
    (l.take i).countP (fun b => b = byte0)

  def oneIdxWithZeros (l : List Std.U8) : List ℕ :=
    (List.range l.length).filter
      (fun i => decide (byteAt l i = byte1 ∧ 0 < zerosBefore l i))

  def oneZerosAfter (l : List Std.U8) (i : ℕ) : ℕ :=
    ((List.range l.length).filter
      (fun j => decide (i < j ∧ byteAt l j = byte1 ∧ 0 < zerosBefore l j))).length

  def imaxList (l : List ℤ) : ℤ := l.foldr max 0

  /-- Define the one-second update U(x) of a binary byte slice x to be the unique binary slice of the same length such that, for every i with i+1 < len(x), if x[i]=48 and x[i+1]=49 then U(x)[i]=49 and U(x)[i+1]=48, and for every index j that is not one of the positions i or i+1 of any such occurrence, U(x)[j]=x[j]. Starting from s_0=s and s_{t+1}=U(s_t), let T be the least t >= 0 such that s_t has no index i with i+1 < len(s_t), s_t[i]=48, and s_t[i+1]=49. The function returns Ok r and r, interpreted as a mathematical integer, equals T.
    Preconditions: 1 <= len(s) <= 1000, and for every i with 0 <= i < len(s), s[i] is either 48 (ASCII '0') or 49 (ASCII '1'). -/
  theorem spec_1 (s : Slice Std.U8)
      (hlen : 1 ≤ s.val.length) (hlen_max : s.val.length ≤ 1000)
      (hbin : IsBinary s.val) :
      ∃ r : Std.I64,
        Aegis.SecondsToRemoveOccurrences.seconds_to_remove_occurrences s = ok r ∧
        ∃ T : ℕ, IsFirstStable s.val T ∧ r.val = (T : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen : 1 ≤ s.val.length) (hlen_max : s.val.length ≤ 1000)
        (hbin : IsBinary s.val), ∃ r : Std.I64,
          Aegis.SecondsToRemoveOccurrences.seconds_to_remove_occurrences s = ok r ∧
          ∃ T : ℕ, IsFirstStable s.val T ∧ r.val = (T : ℤ)) := by
    sorry

  /-- For every s satisfying the preconditions, the function returns an Ok value (some r : I64); it does not return Err, panic, access out of bounds, or overflow.
    Preconditions: 1 <= len(s) <= 1000, and for every i with 0 <= i < len(s), s[i] is either 48 (ASCII '0') or 49 (ASCII '1'). -/
  theorem spec_2 (s : Slice Std.U8)
      (hlen : 1 ≤ s.val.length) (hlen_max : s.val.length ≤ 1000)
      (hbin : IsBinary s.val) :
      ∃ r : Std.I64,
        Aegis.SecondsToRemoveOccurrences.seconds_to_remove_occurrences s = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen : 1 ≤ s.val.length) (hlen_max : s.val.length ≤ 1000)
        (hbin : IsBinary s.val), ∃ r : Std.I64,
          Aegis.SecondsToRemoveOccurrences.seconds_to_remove_occurrences s = ok r) := by
    sorry

  /-- Whenever the function returns Ok r, the mathematical integer value of r satisfies 0 <= r <= len(s) - 1.
    Preconditions: 1 <= len(s) <= 1000, and for every i with 0 <= i < len(s), s[i] is either 48 (ASCII '0') or 49 (ASCII '1'). -/
  theorem spec_3 (s : Slice Std.U8)
      (hlen : 1 ≤ s.val.length) (hlen_max : s.val.length ≤ 1000)
      (hbin : IsBinary s.val) :
      ∀ r : Std.I64,
        Aegis.SecondsToRemoveOccurrences.seconds_to_remove_occurrences s = ok r →
        0 ≤ r.val ∧ r.val ≤ (s.val.length : ℤ) - 1 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen : 1 ≤ s.val.length) (hlen_max : s.val.length ≤ 1000)
        (hbin : IsBinary s.val), ∀ r : Std.I64,
          Aegis.SecondsToRemoveOccurrences.seconds_to_remove_occurrences s = ok r →
          0 ≤ r.val ∧ r.val ≤ (s.val.length : ℤ) - 1) := by
    sorry

  /-- Whenever the function returns Ok r, r = 0 if and only if there is no index i with 0 <= i < len(s)-1, s[i]=48, and s[i+1]=49. Equivalently, r = 0 exactly when s is of the form 1^a0^b for some a,b >= 0 (all ones before all zeros).
    Preconditions: 1 <= len(s) <= 1000, and for every i with 0 <= i < len(s), s[i] is either 48 (ASCII '0') or 49 (ASCII '1'). -/
  theorem spec_4 (s : Slice Std.U8)
      (hlen : 1 ≤ s.val.length) (hlen_max : s.val.length ≤ 1000)
      (hbin : IsBinary s.val) :
      ∀ r : Std.I64,
        Aegis.SecondsToRemoveOccurrences.seconds_to_remove_occurrences s = ok r →
        (r.val = 0 ↔ ¬ HasOccurrence s.val) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen : 1 ≤ s.val.length) (hlen_max : s.val.length ≤ 1000)
        (hbin : IsBinary s.val), ∀ r : Std.I64,
          Aegis.SecondsToRemoveOccurrences.seconds_to_remove_occurrences s = ok r →
          (r.val = 0 ↔ ¬ HasOccurrence s.val)) := by
    sorry

  /-- Whenever the function returns Ok r, if there exist integers a >= 0 and b >= 0 with a+b = len(s) such that the first a bytes of s are all 48 and the remaining b bytes are all 49, then r = 0 when a=0 or b=0, and r = a+b-1 when a>0 and b>0.
    Preconditions: 1 <= len(s) <= 1000, and for every i with 0 <= i < len(s), s[i] is either 48 (ASCII '0') or 49 (ASCII '1'). -/
  theorem spec_5 (s : Slice Std.U8)
      (hlen : 1 ≤ s.val.length) (hlen_max : s.val.length ≤ 1000)
      (hbin : IsBinary s.val) :
      ∀ r : Std.I64,
        Aegis.SecondsToRemoveOccurrences.seconds_to_remove_occurrences s = ok r →
        ∀ a b : ℕ, a + b = s.val.length →
          (∀ i, i < a → byteAt s.val i = byte0) →
          (∀ i, a ≤ i → i < s.val.length → byteAt s.val i = byte1) →
          (a = 0 ∨ b = 0 → r.val = 0) ∧
          (0 < a → 0 < b → r.val = (a : ℤ) + (b : ℤ) - 1) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen : 1 ≤ s.val.length) (hlen_max : s.val.length ≤ 1000)
        (hbin : IsBinary s.val), ∀ r : Std.I64,
          Aegis.SecondsToRemoveOccurrences.seconds_to_remove_occurrences s = ok r →
          ∀ a b : ℕ, a + b = s.val.length →
            (∀ i, i < a → byteAt s.val i = byte0) →
            (∀ i, a ≤ i → i < s.val.length → byteAt s.val i = byte1) →
            (a = 0 ∨ b = 0 → r.val = 0) ∧
            (0 < a → 0 < b → r.val = (a : ℤ) + (b : ℤ) - 1)) := by
    sorry

  /-- For every such s, let t be the binary byte slice of length len(s)+1 with t[0]=49 and t[i+1]=s[i] for every 0 <= i < len(s). Then whenever the call on s returns Ok r_s and the call on t returns Ok r_t, r_t = r_s.
    Preconditions: 1 <= len(s) <= 999, and for every i with 0 <= i < len(s), s[i] is either 48 (ASCII '0') or 49 (ASCII '1'). -/
  theorem spec_6 (s : Slice Std.U8)
      (hlen : 1 ≤ s.val.length) (hlen_max : s.val.length ≤ 999)
      (hbin : IsBinary s.val) :
      ∀ t : Slice Std.U8, t.val = byte1 :: s.val →
        ∀ r_s r_t : Std.I64,
          Aegis.SecondsToRemoveOccurrences.seconds_to_remove_occurrences s = ok r_s →
          Aegis.SecondsToRemoveOccurrences.seconds_to_remove_occurrences t = ok r_t →
          r_t.val = r_s.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen : 1 ≤ s.val.length) (hlen_max : s.val.length ≤ 999)
        (hbin : IsBinary s.val), ∀ t : Slice Std.U8, t.val = byte1 :: s.val →
          ∀ r_s r_t : Std.I64,
            Aegis.SecondsToRemoveOccurrences.seconds_to_remove_occurrences s = ok r_s →
            Aegis.SecondsToRemoveOccurrences.seconds_to_remove_occurrences t = ok r_t →
            r_t.val = r_s.val) := by
    sorry

  /-- For every such s, let t be the binary byte slice of length len(s)+1 with t[i]=s[i] for 0 <= i < len(s) and t[len(s)]=48. Then whenever the calls on s and t return Ok r_s and Ok r_t, r_t = r_s.
    Preconditions: 1 <= len(s) <= 999, and for every i with 0 <= i < len(s), s[i] is either 48 (ASCII '0') or 49 (ASCII '1'). -/
  theorem spec_7 (s : Slice Std.U8)
      (hlen : 1 ≤ s.val.length) (hlen_max : s.val.length ≤ 999)
      (hbin : IsBinary s.val) :
      ∀ t : Slice Std.U8, t.val = s.val ++ [byte0] →
        ∀ r_s r_t : Std.I64,
          Aegis.SecondsToRemoveOccurrences.seconds_to_remove_occurrences s = ok r_s →
          Aegis.SecondsToRemoveOccurrences.seconds_to_remove_occurrences t = ok r_t →
          r_t.val = r_s.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen : 1 ≤ s.val.length) (hlen_max : s.val.length ≤ 999)
        (hbin : IsBinary s.val), ∀ t : Slice Std.U8, t.val = s.val ++ [byte0] →
          ∀ r_s r_t : Std.I64,
            Aegis.SecondsToRemoveOccurrences.seconds_to_remove_occurrences s = ok r_s →
            Aegis.SecondsToRemoveOccurrences.seconds_to_remove_occurrences t = ok r_t →
            r_t.val = r_s.val) := by
    sorry

  /-- Define u by len(u)=len(s) and, for every 0 <= i < len(s), u[i]=49 if s[len(s)-1-i]=48, and u[i]=48 if s[len(s)-1-i]=49. Then whenever the calls on s and u return Ok r_s and Ok r_u, r_u = r_s.
    Preconditions: 1 <= len(s) <= 1000, and for every i with 0 <= i < len(s), s[i] is either 48 (ASCII '0') or 49 (ASCII '1'). -/
  theorem spec_8 (s : Slice Std.U8)
      (hlen : 1 ≤ s.val.length) (hlen_max : s.val.length ≤ 1000)
      (hbin : IsBinary s.val) :
      ∀ u : Slice Std.U8, u.val.length = s.val.length →
        (∀ i, i < s.val.length →
          (byteAt s.val (s.val.length - 1 - i) = byte0 ∧ byteAt u.val i = byte1) ∨
          (byteAt s.val (s.val.length - 1 - i) = byte1 ∧ byteAt u.val i = byte0)) →
        ∀ r_s r_u : Std.I64,
          Aegis.SecondsToRemoveOccurrences.seconds_to_remove_occurrences s = ok r_s →
          Aegis.SecondsToRemoveOccurrences.seconds_to_remove_occurrences u = ok r_u →
          r_u.val = r_s.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen : 1 ≤ s.val.length) (hlen_max : s.val.length ≤ 1000)
        (hbin : IsBinary s.val), ∀ u : Slice Std.U8, u.val.length = s.val.length →
          (∀ i, i < s.val.length →
            (byteAt s.val (s.val.length - 1 - i) = byte0 ∧ byteAt u.val i = byte1) ∨
            (byteAt s.val (s.val.length - 1 - i) = byte1 ∧ byteAt u.val i = byte0)) →
          ∀ r_s r_u : Std.I64,
            Aegis.SecondsToRemoveOccurrences.seconds_to_remove_occurrences s = ok r_s →
            Aegis.SecondsToRemoveOccurrences.seconds_to_remove_occurrences u = ok r_u →
            r_u.val = r_s.val) := by
    sorry

  /-- Using the simultaneous 01 -> 10 update, let s_0=s and s_{t+1} be the result after one second from s_t. Whenever the function returns Ok r, the slice s_r (after exactly r updates) has the form 1^k0^(len(s)-k) for some integer k with 0 <= k <= len(s); equivalently, s_r has no index i with s_r[i]=48 and s_r[i+1]=49.
    Preconditions: 1 <= len(s) <= 1000, and for every i with 0 <= i < len(s), s[i] is either 48 (ASCII '0') or 49 (ASCII '1'). -/
  theorem spec_9 (s : Slice Std.U8)
      (hlen : 1 ≤ s.val.length) (hlen_max : s.val.length ≤ 1000)
      (hbin : IsBinary s.val) :
      ∀ r : Std.I64,
        Aegis.SecondsToRemoveOccurrences.seconds_to_remove_occurrences s = ok r →
        ∃ k : ℕ, k ≤ s.val.length ∧
          orbit s.val r.val.toNat =
            List.replicate k byte1 ++ List.replicate (s.val.length - k) byte0 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen : 1 ≤ s.val.length) (hlen_max : s.val.length ≤ 1000)
        (hbin : IsBinary s.val), ∀ r : Std.I64,
          Aegis.SecondsToRemoveOccurrences.seconds_to_remove_occurrences s = ok r →
          ∃ k : ℕ, k ≤ s.val.length ∧
            orbit s.val r.val.toNat =
              List.replicate k byte1 ++ List.replicate (s.val.length - k) byte0) := by
    sorry

  /-- Using the simultaneous 01 -> 10 update, let s_0=s and s_{t+1} be the result after one second from s_t. Whenever the function returns Ok r, for every integer t with 0 <= t < r, the slice s_t contains at least one index i with i+1 < len(s_t), s_t[i]=48, and s_t[i+1]=49.
    Preconditions: 1 <= len(s) <= 1000, and for every i with 0 <= i < len(s), s[i] is either 48 (ASCII '0') or 49 (ASCII '1'). -/
  theorem spec_10 (s : Slice Std.U8)
      (hlen : 1 ≤ s.val.length) (hlen_max : s.val.length ≤ 1000)
      (hbin : IsBinary s.val) :
      ∀ r : Std.I64,
        Aegis.SecondsToRemoveOccurrences.seconds_to_remove_occurrences s = ok r →
        ∀ t : ℕ, t < r.val.toNat → HasOccurrence (orbit s.val t) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen : 1 ≤ s.val.length) (hlen_max : s.val.length ≤ 1000)
        (hbin : IsBinary s.val), ∀ r : Std.I64,
          Aegis.SecondsToRemoveOccurrences.seconds_to_remove_occurrences s = ok r →
          ∀ t : ℕ, t < r.val.toNat → HasOccurrence (orbit s.val t)) := by
    sorry

  /-- For an index i, define z(i) = the number of j with 0 <= j < i and s[j]=48. Let i_0 < i_1 < ... < i_{m-1} be all indices i with s[i]=49 and z(i)>0, and let m be their number. Whenever the function returns Ok r, if m=0 then r=0, and if m>0 then r = max over 0 <= k < m of ( z(i_k) + (m-1-k) ).
    Preconditions: 1 <= len(s) <= 1000, and for every i with 0 <= i < len(s), s[i] is either 48 (ASCII '0') or 49 (ASCII '1'). -/
  theorem spec_11 (s : Slice Std.U8)
      (hlen : 1 ≤ s.val.length) (hlen_max : s.val.length ≤ 1000)
      (hbin : IsBinary s.val) :
      ∀ r : Std.I64,
        Aegis.SecondsToRemoveOccurrences.seconds_to_remove_occurrences s = ok r →
        let idx := oneIdxWithZeros s.val
        (idx.length = 0 → r.val = 0) ∧
        (0 < idx.length →
          r.val = imaxList ((List.range idx.length).map
            (fun k => (zerosBefore s.val (idx.getD k 0) : ℤ) +
              (((idx.length - 1) - k : ℕ) : ℤ)))) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen : 1 ≤ s.val.length) (hlen_max : s.val.length ≤ 1000)
        (hbin : IsBinary s.val), ∀ r : Std.I64,
          Aegis.SecondsToRemoveOccurrences.seconds_to_remove_occurrences s = ok r →
          let idx := oneIdxWithZeros s.val
          (idx.length = 0 → r.val = 0) ∧
          (0 < idx.length →
            r.val = imaxList ((List.range idx.length).map
              (fun k => (zerosBefore s.val (idx.getD k 0) : ℤ) +
                (((idx.length - 1) - k : ℕ) : ℤ))))) := by
    sorry

  /-- For an index i, define z(i) = the number of j with 0 <= j < i and s[j]=48. Whenever the function returns Ok r, for every i with 0 <= i < len(s), s[i]=49, and z(i)>0, we have r >= z(i).
    Preconditions: 1 <= len(s) <= 1000, and for every i with 0 <= i < len(s), s[i] is either 48 (ASCII '0') or 49 (ASCII '1'). -/
  theorem spec_12 (s : Slice Std.U8)
      (hlen : 1 ≤ s.val.length) (hlen_max : s.val.length ≤ 1000)
      (hbin : IsBinary s.val) :
      ∀ r : Std.I64,
        Aegis.SecondsToRemoveOccurrences.seconds_to_remove_occurrences s = ok r →
        ∀ i : ℕ, i < s.val.length → byteAt s.val i = byte1 →
          0 < zerosBefore s.val i → (zerosBefore s.val i : ℤ) ≤ r.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen : 1 ≤ s.val.length) (hlen_max : s.val.length ≤ 1000)
        (hbin : IsBinary s.val), ∀ r : Std.I64,
          Aegis.SecondsToRemoveOccurrences.seconds_to_remove_occurrences s = ok r →
          ∀ i : ℕ, i < s.val.length → byteAt s.val i = byte1 →
            0 < zerosBefore s.val i → (zerosBefore s.val i : ℤ) ≤ r.val) := by
    sorry

  /-- For an index i, define z(i)=the number of j with 0 <= j < i and s[j]=48, and c(i)=the number of j with i < j < len(s), s[j]=49, and z(j)>0. Whenever the function returns Ok r, either r=0 and there is no index i with s[i]=49 and z(i)>0, or there exists an index i with s[i]=49, z(i)>0, and r = z(i) + c(i).
    Preconditions: 1 <= len(s) <= 1000, and for every i with 0 <= i < len(s), s[i] is either 48 (ASCII '0') or 49 (ASCII '1'). -/
  theorem spec_13 (s : Slice Std.U8)
      (hlen : 1 ≤ s.val.length) (hlen_max : s.val.length ≤ 1000)
      (hbin : IsBinary s.val) :
      ∀ r : Std.I64,
        Aegis.SecondsToRemoveOccurrences.seconds_to_remove_occurrences s = ok r →
        (r.val = 0 ∧
          ¬ ∃ i, i < s.val.length ∧ byteAt s.val i = byte1 ∧ 0 < zerosBefore s.val i) ∨
        (∃ i, i < s.val.length ∧ byteAt s.val i = byte1 ∧ 0 < zerosBefore s.val i ∧
          r.val = (zerosBefore s.val i : ℤ) + (oneZerosAfter s.val i : ℤ)) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen : 1 ≤ s.val.length) (hlen_max : s.val.length ≤ 1000)
        (hbin : IsBinary s.val), ∀ r : Std.I64,
          Aegis.SecondsToRemoveOccurrences.seconds_to_remove_occurrences s = ok r →
          (r.val = 0 ∧
            ¬ ∃ i, i < s.val.length ∧ byteAt s.val i = byte1 ∧ 0 < zerosBefore s.val i) ∨
          (∃ i, i < s.val.length ∧ byteAt s.val i = byte1 ∧ 0 < zerosBefore s.val i ∧
            r.val = (zerosBefore s.val i : ℤ) + (oneZerosAfter s.val i : ℤ))) := by
    sorry

  /-- Let t be the binary byte slice of length len(s)+1 with t[0]=48 and t[i+1]=s[i] for every 0 <= i < len(s). Then whenever the calls on s and t return Ok r_s and Ok r_t, r_t = r_s + 1.
    Preconditions: 1 <= len(s) <= 999, for every i with 0 <= i < len(s), s[i] is either 48 (ASCII '0') or 49 (ASCII '1'), s[0]=48, and there exists i with 0 <= i < len(s) and s[i]=49. -/
  theorem spec_14 (s : Slice Std.U8)
      (hlen : 1 ≤ s.val.length) (hlen_max : s.val.length ≤ 999)
      (hbin : IsBinary s.val)
      (h0 : byteAt s.val 0 = byte0)
      (h1 : ∃ i, i < s.val.length ∧ byteAt s.val i = byte1) :
      ∀ t : Slice Std.U8, t.val = byte0 :: s.val →
        ∀ r_s r_t : Std.I64,
          Aegis.SecondsToRemoveOccurrences.seconds_to_remove_occurrences s = ok r_s →
          Aegis.SecondsToRemoveOccurrences.seconds_to_remove_occurrences t = ok r_t →
          r_t.val = r_s.val + 1 := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen : 1 ≤ s.val.length) (hlen_max : s.val.length ≤ 999)
        (hbin : IsBinary s.val)
        (h0 : byteAt s.val 0 = byte0)
        (h1 : ∃ i, i < s.val.length ∧ byteAt s.val i = byte1), ∀ t : Slice Std.U8, t.val = byte0 :: s.val →
          ∀ r_s r_t : Std.I64,
            Aegis.SecondsToRemoveOccurrences.seconds_to_remove_occurrences s = ok r_s →
            Aegis.SecondsToRemoveOccurrences.seconds_to_remove_occurrences t = ok r_t →
            r_t.val = r_s.val + 1) := by
    sorry

  end AegisSpec.SecondsToRemoveOccurrences

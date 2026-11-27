import Aegis.DeleteString.Code.Funs

/-!
# Specifications of `Aegis.DeleteString.delete_string`

LeetCode problem `maximum-deletions-on-a-string`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.DeleteString (delete_string)

  namespace AegisSpec.DeleteString

  def bytes (s : Slice Std.U8) : List Nat := s.val.map (fun b => b.val)

  def byte (s : Slice Std.U8) (i : Nat) : Nat := (bytes s).getD i 0

  def blockEq (s : Slice Std.U8) (i j : Nat) : Prop :=
    ∀ a, a < j → byte s (i + a) = byte s (i + j + a)

  def stepOk (s : Slice Std.U8) (n i j : Nat) : Prop :=
    1 ≤ j ∧ 2 * j ≤ n - i ∧ blockEq s i j

  def IsPlanFrom (s : Slice Std.U8) (n i k : Nat) (p : Nat → Nat) : Prop :=
    1 ≤ k ∧ p 0 = i ∧ p k = n ∧
      (∀ t, t < k → p t < p (t + 1)) ∧
      (∀ t, t + 2 ≤ k → stepOk s n (p t) (p (t + 1) - p t))

  def IsPlan (s : Slice Std.U8) (n k : Nat) (p : Nat → Nat) : Prop :=
    IsPlanFrom s n 0 k p

  def allBytesEq (s : Slice Std.U8) (n : Nat) : Prop :=
    ∀ a b, a < n → b < n → byte s a = byte s b

  noncomputable def G (s : Slice Std.U8) (n i : Nat) : Nat := by
    classical
    exact ((Finset.range (n + 1)).filter
      (fun k => ∃ p : Nat → Nat, IsPlanFrom s n i k p)).sup (fun k => k)

  noncomputable def jumps (s : Slice Std.U8) (n i : Nat) : Finset Nat := by
    classical
    exact (Finset.range (n - i + 1)).filter (fun j => stepOk s n i j)

  noncomputable def bestJump (s : Slice Std.U8) (n i : Nat) : Nat :=
    (jumps s n i).sup (fun j => 1 + G s n (i + j))

  /-- Whenever the function returns a result r, r equals the maximum, over all deletion plans of s, of the plan's number of operations. A deletion plan of s is a sequence 0 = p_0 < p_1 < ... < p_k = n with k >= 1 such that for every t with 0 <= t <= k-2, setting j = p_{t+1} - p_t, we have 1 <= j, 2*j <= n - p_t, and s[p_t + a] = s[p_t + j + a] for every a with 0 <= a < j; the plan's number of operations is k.
    Preconditions: n = len(s); 1 <= n <= 4000; for every t with 0 <= t < n, 97 <= s[t] <= 122 (each byte is an ASCII lowercase letter). -/
  theorem spec_1 (s : Slice Std.U8) (n : Nat)
      (hn : n = s.val.length) (hn1 : 1 ≤ n) (hn4000 : n ≤ 4000)
      (hlow : ∀ t, t < n → 97 ≤ byte s t ∧ byte s t ≤ 122) :
      ∀ r : I64, delete_string s = ok r →
        (∀ (k : Nat) (p : Nat → Nat), IsPlan s n k p → (k : Int) ≤ r.val) ∧
          (∃ (k : Nat) (p : Nat → Nat), IsPlan s n k p ∧ r.val = (k : Int)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice Std.U8) (n : Nat)
        (hn : n = s.val.length) (hn1 : 1 ≤ n) (hn4000 : n ≤ 4000)
        (hlow : ∀ t, t < n → 97 ≤ byte s t ∧ byte s t ≤ 122), ∀ r : I64, delete_string s = ok r →
          (∀ (k : Nat) (p : Nat → Nat), IsPlan s n k p → (k : Int) ≤ r.val) ∧
            (∃ (k : Nat) (p : Nat → Nat), IsPlan s n k p ∧ r.val = (k : Int))) := by
    sorry

  /-- The function returns a result r and does not fail (no arithmetic overflow, no out-of-bounds access, no panic) for every input satisfying the preconditions.
    Preconditions: n = len(s); 1 <= n <= 4000; for every t with 0 <= t < n, 97 <= s[t] <= 122. -/
  theorem spec_2 (s : Slice Std.U8) (n : Nat)
      (hn : n = s.val.length) (hn1 : 1 ≤ n) (hn4000 : n ≤ 4000)
      (hlow : ∀ t, t < n → 97 ≤ byte s t ∧ byte s t ≤ 122) :
      ∃ r : I64, delete_string s = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice Std.U8) (n : Nat)
        (hn : n = s.val.length) (hn1 : 1 ≤ n) (hn4000 : n ≤ 4000)
        (hlow : ∀ t, t < n → 97 ≤ byte s t ∧ byte s t ≤ 122), ∃ r : I64, delete_string s = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 1 <= r <= n.
    Preconditions: n = len(s); 1 <= n <= 4000; for every t with 0 <= t < n, 97 <= s[t] <= 122. -/
  theorem spec_3 (s : Slice Std.U8) (n : Nat)
      (hn : n = s.val.length) (hn1 : 1 ≤ n) (hn4000 : n ≤ 4000)
      (hlow : ∀ t, t < n → 97 ≤ byte s t ∧ byte s t ≤ 122) :
      ∀ r : I64, delete_string s = ok r → 1 ≤ r.val ∧ r.val ≤ (n : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice Std.U8) (n : Nat)
        (hn : n = s.val.length) (hn1 : 1 ≤ n) (hn4000 : n ≤ 4000)
        (hlow : ∀ t, t < n → 97 ≤ byte s t ∧ byte s t ≤ 122), ∀ r : I64, delete_string s = ok r → 1 ≤ r.val ∧ r.val ≤ (n : Int)) := by
    sorry

  /-- Whenever the function returns a result r, r = n if and only if all bytes of s are equal, i.e. s[0] = s[1] = ... = s[n-1].
    Preconditions: n = len(s); 1 <= n <= 4000; for every t with 0 <= t < n, 97 <= s[t] <= 122. -/
  theorem spec_4 (s : Slice Std.U8) (n : Nat)
      (hn : n = s.val.length) (hn1 : 1 ≤ n) (hn4000 : n ≤ 4000)
      (hlow : ∀ t, t < n → 97 ≤ byte s t ∧ byte s t ≤ 122) :
      ∀ r : I64, delete_string s = ok r → (r.val = (n : Int) ↔ allBytesEq s n) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice Std.U8) (n : Nat)
        (hn : n = s.val.length) (hn1 : 1 ≤ n) (hn4000 : n ≤ 4000)
        (hlow : ∀ t, t < n → 97 ≤ byte s t ∧ byte s t ≤ 122), ∀ r : I64, delete_string s = ok r → (r.val = (n : Int) ↔ allBytesEq s n)) := by
    sorry

  /-- Whenever the function returns a result r, r = 1 if and only if there is no integer j such that 1 <= j, 2*j <= n, and s[a] = s[j + a] for every a with 0 <= a < j.
    Preconditions: n = len(s); 1 <= n <= 4000; for every t with 0 <= t < n, 97 <= s[t] <= 122. -/
  theorem spec_5 (s : Slice Std.U8) (n : Nat)
      (hn : n = s.val.length) (hn1 : 1 ≤ n) (hn4000 : n ≤ 4000)
      (hlow : ∀ t, t < n → 97 ≤ byte s t ∧ byte s t ≤ 122) :
      ∀ r : I64, delete_string s = ok r →
        (r.val = 1 ↔ ¬ ∃ j : Nat, 1 ≤ j ∧ 2 * j ≤ n ∧
          ∀ a, a < j → byte s a = byte s (j + a)) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice Std.U8) (n : Nat)
        (hn : n = s.val.length) (hn1 : 1 ≤ n) (hn4000 : n ≤ 4000)
        (hlow : ∀ t, t < n → 97 ≤ byte s t ∧ byte s t ≤ 122), ∀ r : I64, delete_string s = ok r →
          (r.val = 1 ↔ ¬ ∃ j : Nat, 1 ≤ j ∧ 2 * j ≤ n ∧
            ∀ a, a < j → byte s a = byte s (j + a))) := by
    sorry

  /-- Whenever the function returns a result r, there is a sequence 0 = p_0 < p_1 < ... < p_r = n such that for every t with 0 <= t <= r-2, setting j = p_{t+1} - p_t, we have 1 <= j, 2*j <= n - p_t, and s[p_t + a] = s[p_t + j + a] for every a with 0 <= a < j; that is, s can be deleted in exactly r legal operations.
    Preconditions: n = len(s); 1 <= n <= 4000; for every t with 0 <= t < n, 97 <= s[t] <= 122. -/
  theorem spec_6 (s : Slice Std.U8) (n : Nat)
      (hn : n = s.val.length) (hn1 : 1 ≤ n) (hn4000 : n ≤ 4000)
      (hlow : ∀ t, t < n → 97 ≤ byte s t ∧ byte s t ≤ 122) :
      ∀ r : I64, delete_string s = ok r →
        ∃ (k : Nat) (p : Nat → Nat), IsPlan s n k p ∧ r.val = (k : Int) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Slice Std.U8) (n : Nat)
        (hn : n = s.val.length) (hn1 : 1 ≤ n) (hn4000 : n ≤ 4000)
        (hlow : ∀ t, t < n → 97 ≤ byte s t ∧ byte s t ≤ 122), ∀ r : I64, delete_string s = ok r →
          ∃ (k : Nat) (p : Nat → Nat), IsPlan s n k p ∧ r.val = (k : Int)) := by
    sorry

  /-- Whenever the function returns a result r, every sequence 0 = p_0 < p_1 < ... < p_k = n with k >= 1 such that for every t with 0 <= t <= k-2, setting j = p_{t+1} - p_t, one has 1 <= j, 2*j <= n - p_t, and s[p_t + a] = s[p_t + j + a] for all a with 0 <= a < j, satisfies k <= r.
    Preconditions: n = len(s); 1 <= n <= 4000; for every t with 0 <= t < n, 97 <= s[t] <= 122. -/
  theorem spec_7 (s : Slice Std.U8) (n : Nat)
      (hn : n = s.val.length) (hn1 : 1 ≤ n) (hn4000 : n ≤ 4000)
      (hlow : ∀ t, t < n → 97 ≤ byte s t ∧ byte s t ≤ 122) :
      ∀ r : I64, delete_string s = ok r →
        ∀ (k : Nat) (p : Nat → Nat), IsPlan s n k p → (k : Int) ≤ r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s : Slice Std.U8) (n : Nat)
        (hn : n = s.val.length) (hn1 : 1 ≤ n) (hn4000 : n ≤ 4000)
        (hlow : ∀ t, t < n → 97 ≤ byte s t ∧ byte s t ≤ 122), ∀ r : I64, delete_string s = ok r →
          ∀ (k : Nat) (p : Nat → Nat), IsPlan s n k p → (k : Int) ≤ r.val) := by
    sorry

  /-- For any byte slice t of length n whose bytes are all in 97..122 and which has the same equality pattern as s (for all a, b with 0 <= a < n and 0 <= b < n, s[a] = s[b] if and only if t[a] = t[b]), if the function returns r_s on s and r_t on t, then r_s = r_t.
    Preconditions: n = len(s); 1 <= n <= 4000; for every t with 0 <= t < n, 97 <= s[t] <= 122. -/
  theorem spec_8 (s : Slice Std.U8) (n : Nat)
      (hn : n = s.val.length) (hn1 : 1 ≤ n) (hn4000 : n ≤ 4000)
      (hlow : ∀ t, t < n → 97 ≤ byte s t ∧ byte s t ≤ 122) :
      ∀ (t : Slice Std.U8), t.val.length = n →
        (∀ i, i < n → 97 ≤ byte t i ∧ byte t i ≤ 122) →
        (∀ a b, a < n → b < n → (byte s a = byte s b ↔ byte t a = byte t b)) →
        ∀ rs rt : I64, delete_string s = ok rs → delete_string t = ok rt →
          rs.val = rt.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s : Slice Std.U8) (n : Nat)
        (hn : n = s.val.length) (hn1 : 1 ≤ n) (hn4000 : n ≤ 4000)
        (hlow : ∀ t, t < n → 97 ≤ byte s t ∧ byte s t ≤ 122), ∀ (t : Slice Std.U8), t.val.length = n →
          (∀ i, i < n → 97 ≤ byte t i ∧ byte t i ≤ 122) →
          (∀ a b, a < n → b < n → (byte s a = byte s b ↔ byte t a = byte t b)) →
          ∀ rs rt : I64, delete_string s = ok rs → delete_string t = ok rt →
            rs.val = rt.val) := by
    sorry

  /-- Whenever the function returns a result r with r >= 2, there exists an integer j such that 1 <= j, 2*j <= n, s[a] = s[j + a] for every a with 0 <= a < j, and r = 1 + G(j), where for 0 <= j <= n, G(j) denotes the maximum number of operations over all deletion plans of the suffix s[j..n-1] (regarded as a byte string of length n-j), with G(n) = 0.
    Preconditions: n = len(s); 1 <= n <= 4000; for every t with 0 <= t < n, 97 <= s[t] <= 122. -/
  theorem spec_9 (s : Slice Std.U8) (n : Nat)
      (hn : n = s.val.length) (hn1 : 1 ≤ n) (hn4000 : n ≤ 4000)
      (hlow : ∀ t, t < n → 97 ≤ byte s t ∧ byte s t ≤ 122) :
      ∀ r : I64, delete_string s = ok r → 2 ≤ r.val →
        ∃ j : Nat, 1 ≤ j ∧ 2 * j ≤ n ∧
          (∀ a, a < j → byte s a = byte s (j + a)) ∧
          r.val = 1 + (G s n j : Int) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s : Slice Std.U8) (n : Nat)
        (hn : n = s.val.length) (hn1 : 1 ≤ n) (hn4000 : n ≤ 4000)
        (hlow : ∀ t, t < n → 97 ≤ byte s t ∧ byte s t ≤ 122), ∀ r : I64, delete_string s = ok r → 2 ≤ r.val →
          ∃ j : Nat, 1 ≤ j ∧ 2 * j ≤ n ∧
            (∀ a, a < j → byte s a = byte s (j + a)) ∧
            r.val = 1 + (G s n j : Int)) := by
    sorry

  /-- Whenever the function returns a result r, for every integer j such that 1 <= j, 2*j <= n, and s[a] = s[j + a] for every a with 0 <= a < j, we have r >= 1 + G(j), where for 0 <= j <= n, G(j) denotes the maximum number of operations over all deletion plans of the suffix s[j..n-1] (regarded as a byte string of length n-j), with G(n) = 0.
    Preconditions: n = len(s); 1 <= n <= 4000; for every t with 0 <= t < n, 97 <= s[t] <= 122. -/
  theorem spec_10 (s : Slice Std.U8) (n : Nat)
      (hn : n = s.val.length) (hn1 : 1 ≤ n) (hn4000 : n ≤ 4000)
      (hlow : ∀ t, t < n → 97 ≤ byte s t ∧ byte s t ≤ 122) :
      ∀ r : I64, delete_string s = ok r →
        ∀ j : Nat, 1 ≤ j → 2 * j ≤ n →
          (∀ a, a < j → byte s a = byte s (j + a)) →
          1 + (G s n j : Int) ≤ r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s : Slice Std.U8) (n : Nat)
        (hn : n = s.val.length) (hn1 : 1 ≤ n) (hn4000 : n ≤ 4000)
        (hlow : ∀ t, t < n → 97 ≤ byte s t ∧ byte s t ≤ 122), ∀ r : I64, delete_string s = ok r →
          ∀ j : Nat, 1 ≤ j → 2 * j ≤ n →
            (∀ a, a < j → byte s a = byte s (j + a)) →
            1 + (G s n j : Int) ≤ r.val) := by
    sorry

  end AegisSpec.DeleteString

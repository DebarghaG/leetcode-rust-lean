import Aegis.MinimumOperationsToMakeKPeriodic.Code.Funs

/-!
# Specifications of `Aegis.MinimumOperationsToMakeKPeriodic.minimum_operations_to_make_k_periodic`

LeetCode problem `minimum-number-of-operations-to-make-word-k-periodic`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinimumOperationsToMakeKPeriodic

  def blockAt (w : List U8) (k b : Nat) : List U8 := (w.drop (b * k)).take k

  def BlocksAgree (w : List U8) (k b c : Nat) : Prop :=
    ∀ t, t < k → w[b * k + t]? = w[c * k + t]?

  def BlocksDiffer (w : List U8) (k b c : Nat) : Prop :=
    ∃ t, t < k ∧ w[b * k + t]? ≠ w[c * k + t]?

  def sameCount (w : List U8) (k m j : Nat) : Nat :=
    ((List.range m).filter (fun b => blockAt w k b == blockAt w k j)).length

  def maxSame (w : List U8) (k m : Nat) : Nat :=
    ((List.range m).map (fun j => sameCount w k m j)).foldr max 0

  def uniformBlocks (m : Nat) (blk : List U8) : List U8 :=
    List.flatten (List.replicate m blk)

  def AllBlocksEqual (w : List U8) (k m : Nat) : Prop :=
    ∀ b c, b < m → c < m → blockAt w k b = blockAt w k c

  def replaceBlock (w : List U8) (k m b c : Nat) : List U8 :=
    List.flatten ((List.range m).map (fun i =>
      if i = b then blockAt w k c else blockAt w k i))

  def Step (k m : Nat) (w w' : List U8) : Prop :=
    ∃ b c, b < m ∧ c < m ∧ w' = replaceBlock w k m b c

  inductive ReachN (k m : Nat) : Nat → List U8 → List U8 → Prop
    | zero (w : List U8) : ReachN k m 0 w w
    | succ {t : Nat} {w₁ w₂ w₃ : List U8} :
        ReachN k m t w₁ w₂ → Step k m w₂ w₃ → ReachN k m (t + 1) w₁ w₃

  inductive Reach (k m : Nat) : List U8 → List U8 → Prop
    | refl (w : List U8) : Reach k m w w
    | step {w₁ w₂ w₃ : List U8} : Reach k m w₁ w₂ → Step k m w₂ w₃ → Reach k m w₁ w₃

  def byteCount (w : List U8) (c : Nat) : Nat := (w.filter (fun x => x.val == c)).length

  def presentMaxCount (w : List U8) : Nat :=
    (w.map (fun x => byteCount w x.val)).foldr max 0

  /-- Let m = n/k. For each block index b with 0 <= b < m, define block B_b by B_b[t] = word[b*k + t] for 0 <= t < k. For 0 <= j < m, let same(j) be the number of b in [0,m) with B_b = B_j, i.e. for all t with 0 <= t < k, word[b*k+t] = word[j*k+t]. Let F = max { same(j) | 0 <= j < m }. The function returns a result r and r = m - F.
    Preconditions: Let n = len(word). The input satisfies 1 <= n <= 100000, 1 <= k <= n, k divides n (so n = m*k for the positive integer m = n/k), and every byte of word is an ASCII lowercase letter (97 through 122). -/
  theorem spec_1 (word : Slice U8) (k : I64)
      (hn1 : 1 ≤ word.val.length) (hn2 : word.val.length ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (word.val.length : Int))
      (hdiv : k.val.toNat ∣ word.val.length)
      (hbytes : ∀ (i : Nat) (hi : i < word.val.length),
        97 ≤ (word.val[i]).val ∧ (word.val[i]).val ≤ 122) :
      ∃ r : I64,
        Aegis.MinimumOperationsToMakeKPeriodic.minimum_operations_to_make_k_periodic
            word k = ok r ∧
          r.val = ((word.val.length / k.val.toNat : Nat) : Int) -
            (maxSame word.val k.val.toNat (word.val.length / k.val.toNat) : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (word : Slice U8) (k : I64)
        (hn1 : 1 ≤ word.val.length) (hn2 : word.val.length ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (word.val.length : Int))
        (hdiv : k.val.toNat ∣ word.val.length)
        (hbytes : ∀ (i : Nat) (hi : i < word.val.length),
          97 ≤ (word.val[i]).val ∧ (word.val[i]).val ≤ 122), ∃ r : I64,
          Aegis.MinimumOperationsToMakeKPeriodic.minimum_operations_to_make_k_periodic
              word k = ok r ∧
            r.val = ((word.val.length / k.val.toNat : Nat) : Int) -
              (maxSame word.val k.val.toNat (word.val.length / k.val.toNat) : Int)) := by
    sorry

  /-- Whenever the preconditions hold, the function returns a result r; it does not panic, overflow, underflow, or access an out-of-bounds index.
    Preconditions: Let n = len(word). The input satisfies 1 <= n <= 100000, 1 <= k <= n, k divides n, and every byte of word is an ASCII lowercase letter. -/
  theorem spec_2 (word : Slice U8) (k : I64)
      (hn1 : 1 ≤ word.val.length) (hn2 : word.val.length ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (word.val.length : Int))
      (hdiv : k.val.toNat ∣ word.val.length)
      (hbytes : ∀ (i : Nat) (hi : i < word.val.length),
        97 ≤ (word.val[i]).val ∧ (word.val[i]).val ≤ 122) :
      ∃ r : I64,
        Aegis.MinimumOperationsToMakeKPeriodic.minimum_operations_to_make_k_periodic
          word k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (word : Slice U8) (k : I64)
        (hn1 : 1 ≤ word.val.length) (hn2 : word.val.length ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (word.val.length : Int))
        (hdiv : k.val.toNat ∣ word.val.length)
        (hbytes : ∀ (i : Nat) (hi : i < word.val.length),
          97 ≤ (word.val[i]).val ∧ (word.val[i]).val ≤ 122), ∃ r : I64,
          Aegis.MinimumOperationsToMakeKPeriodic.minimum_operations_to_make_k_periodic
            word k = ok r) := by
    sorry

  /-- Let m = n/k. For each block index j with 0 <= j < m, let same(j) be the number of b in [0,m) such that for all t with 0 <= t < k, word[b*k+t] = word[j*k+t]. Whenever the function returns a result r, for every j with 0 <= j < m we have r <= m - same(j).
    Preconditions: Let n = len(word). The input satisfies 1 <= n <= 100000, 1 <= k <= n, k divides n, and every byte of word is an ASCII lowercase letter. -/
  theorem spec_3 (word : Slice U8) (k : I64)
      (hn1 : 1 ≤ word.val.length) (hn2 : word.val.length ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (word.val.length : Int))
      (hdiv : k.val.toNat ∣ word.val.length)
      (hbytes : ∀ (i : Nat) (hi : i < word.val.length),
        97 ≤ (word.val[i]).val ∧ (word.val[i]).val ≤ 122) :
      ∀ r : I64,
        Aegis.MinimumOperationsToMakeKPeriodic.minimum_operations_to_make_k_periodic
            word k = ok r →
          ∀ j, j < word.val.length / k.val.toNat →
            r.val ≤ ((word.val.length / k.val.toNat : Nat) : Int) -
              (sameCount word.val k.val.toNat (word.val.length / k.val.toNat) j : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (word : Slice U8) (k : I64)
        (hn1 : 1 ≤ word.val.length) (hn2 : word.val.length ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (word.val.length : Int))
        (hdiv : k.val.toNat ∣ word.val.length)
        (hbytes : ∀ (i : Nat) (hi : i < word.val.length),
          97 ≤ (word.val[i]).val ∧ (word.val[i]).val ≤ 122), ∀ r : I64,
          Aegis.MinimumOperationsToMakeKPeriodic.minimum_operations_to_make_k_periodic
              word k = ok r →
            ∀ j, j < word.val.length / k.val.toNat →
              r.val ≤ ((word.val.length / k.val.toNat : Nat) : Int) -
                (sameCount word.val k.val.toNat (word.val.length / k.val.toNat) j : Int)) := by
    sorry

  /-- Let m = n/k. Whenever the function returns a result r, r = 0 if and only if word is already k-periodic, that is, if and only if all m blocks of length k are equal: for all b and c with 0 <= b < m and 0 <= c < m and all t with 0 <= t < k, word[b*k+t] = word[c*k+t].
    Preconditions: Let n = len(word). The input satisfies 1 <= n <= 100000, 1 <= k <= n, k divides n, and every byte of word is an ASCII lowercase letter. -/
  theorem spec_4 (word : Slice U8) (k : I64)
      (hn1 : 1 ≤ word.val.length) (hn2 : word.val.length ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (word.val.length : Int))
      (hdiv : k.val.toNat ∣ word.val.length)
      (hbytes : ∀ (i : Nat) (hi : i < word.val.length),
        97 ≤ (word.val[i]).val ∧ (word.val[i]).val ≤ 122) :
      ∀ r : I64,
        Aegis.MinimumOperationsToMakeKPeriodic.minimum_operations_to_make_k_periodic
            word k = ok r →
          (r.val = 0 ↔
            ∀ b c, b < word.val.length / k.val.toNat → c < word.val.length / k.val.toNat →
              ∀ t, t < k.val.toNat →
                word.val[b * k.val.toNat + t]? = word.val[c * k.val.toNat + t]?) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (word : Slice U8) (k : I64)
        (hn1 : 1 ≤ word.val.length) (hn2 : word.val.length ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (word.val.length : Int))
        (hdiv : k.val.toNat ∣ word.val.length)
        (hbytes : ∀ (i : Nat) (hi : i < word.val.length),
          97 ≤ (word.val[i]).val ∧ (word.val[i]).val ≤ 122), ∀ r : I64,
          Aegis.MinimumOperationsToMakeKPeriodic.minimum_operations_to_make_k_periodic
              word k = ok r →
            (r.val = 0 ↔
              ∀ b c, b < word.val.length / k.val.toNat → c < word.val.length / k.val.toNat →
                ∀ t, t < k.val.toNat →
                  word.val[b * k.val.toNat + t]? = word.val[c * k.val.toNat + t]?)) := by
    sorry

  /-- Let n = len(word). For each byte value c, let count(c) be the number of indices i with 0 <= i < n and word[i] = c. Let C = max { count(c) | c is a byte value appearing in word }. Whenever the function returns a result r, r = n - C.
    Preconditions: Let n = len(word). The input satisfies 1 <= n <= 100000, k = 1, k divides n, and every byte of word is an ASCII lowercase letter. -/
  theorem spec_5 (word : Slice U8) (k : I64)
      (hn1 : 1 ≤ word.val.length) (hn2 : word.val.length ≤ 100000)
      (hk : k.val = 1)
      (hbytes : ∀ (i : Nat) (hi : i < word.val.length),
        97 ≤ (word.val[i]).val ∧ (word.val[i]).val ≤ 122) :
      ∀ r : I64,
        Aegis.MinimumOperationsToMakeKPeriodic.minimum_operations_to_make_k_periodic
            word k = ok r →
          r.val = (word.val.length : Int) - (presentMaxCount word.val : Int) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (word : Slice U8) (k : I64)
        (hn1 : 1 ≤ word.val.length) (hn2 : word.val.length ≤ 100000)
        (hk : k.val = 1)
        (hbytes : ∀ (i : Nat) (hi : i < word.val.length),
          97 ≤ (word.val[i]).val ∧ (word.val[i]).val ≤ 122), ∀ r : I64,
          Aegis.MinimumOperationsToMakeKPeriodic.minimum_operations_to_make_k_periodic
              word k = ok r →
            r.val = (word.val.length : Int) - (presentMaxCount word.val : Int)) := by
    sorry

  /-- Let m = n/k. Suppose the m blocks of length k are pairwise distinct, meaning for all b and c with 0 <= b < m, 0 <= c < m, and b != c, there exists t with 0 <= t < k and word[b*k+t] != word[c*k+t]. Whenever the function returns a result r, r = m - 1.
    Preconditions: Let n = len(word). The input satisfies 1 <= n <= 100000, 1 <= k <= n, k divides n, and every byte of word is an ASCII lowercase letter. -/
  theorem spec_6 (word : Slice U8) (k : I64)
      (hn1 : 1 ≤ word.val.length) (hn2 : word.val.length ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (word.val.length : Int))
      (hdiv : k.val.toNat ∣ word.val.length)
      (hbytes : ∀ (i : Nat) (hi : i < word.val.length),
        97 ≤ (word.val[i]).val ∧ (word.val[i]).val ≤ 122)
      (hdistinct : ∀ b c, b < word.val.length / k.val.toNat →
        c < word.val.length / k.val.toNat → b ≠ c →
          BlocksDiffer word.val k.val.toNat b c) :
      ∀ r : I64,
        Aegis.MinimumOperationsToMakeKPeriodic.minimum_operations_to_make_k_periodic
            word k = ok r →
          r.val = ((word.val.length / k.val.toNat : Nat) : Int) - 1 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (word : Slice U8) (k : I64)
        (hn1 : 1 ≤ word.val.length) (hn2 : word.val.length ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (word.val.length : Int))
        (hdiv : k.val.toNat ∣ word.val.length)
        (hbytes : ∀ (i : Nat) (hi : i < word.val.length),
          97 ≤ (word.val[i]).val ∧ (word.val[i]).val ≤ 122)
        (hdistinct : ∀ b c, b < word.val.length / k.val.toNat →
          c < word.val.length / k.val.toNat → b ≠ c →
            BlocksDiffer word.val k.val.toNat b c), ∀ r : I64,
          Aegis.MinimumOperationsToMakeKPeriodic.minimum_operations_to_make_k_periodic
              word k = ok r →
            r.val = ((word.val.length / k.val.toNat : Nat) : Int) - 1) := by
    sorry

  /-- Let B0 be word[0..k-1] and B1 be word[k..2k-1]. Whenever the function returns a result r, either B0 = B1 and r = 0, or B0 != B1 and r = 1.
    Preconditions: Let n = len(word). The input satisfies 1 <= n <= 100000, 1 <= k <= n, k divides n, every byte of word is an ASCII lowercase letter, and n = 2*k. -/
  theorem spec_7 (word : Slice U8) (k : I64)
      (hn1 : 1 ≤ word.val.length) (hn2 : word.val.length ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (word.val.length : Int))
      (hdiv : k.val.toNat ∣ word.val.length)
      (hbytes : ∀ (i : Nat) (hi : i < word.val.length),
        97 ≤ (word.val[i]).val ∧ (word.val[i]).val ≤ 122)
      (h2k : word.val.length = 2 * k.val.toNat) :
      ∀ r : I64,
        Aegis.MinimumOperationsToMakeKPeriodic.minimum_operations_to_make_k_periodic
            word k = ok r →
          (blockAt word.val k.val.toNat 0 = blockAt word.val k.val.toNat 1 ∧
            r.val = 0) ∨
          (blockAt word.val k.val.toNat 0 ≠ blockAt word.val k.val.toNat 1 ∧
            r.val = 1) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (word : Slice U8) (k : I64)
        (hn1 : 1 ≤ word.val.length) (hn2 : word.val.length ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (word.val.length : Int))
        (hdiv : k.val.toNat ∣ word.val.length)
        (hbytes : ∀ (i : Nat) (hi : i < word.val.length),
          97 ≤ (word.val[i]).val ∧ (word.val[i]).val ≤ 122)
        (h2k : word.val.length = 2 * k.val.toNat), ∀ r : I64,
          Aegis.MinimumOperationsToMakeKPeriodic.minimum_operations_to_make_k_periodic
              word k = ok r →
            (blockAt word.val k.val.toNat 0 = blockAt word.val k.val.toNat 1 ∧
              r.val = 0) ∨
            (blockAt word.val k.val.toNat 0 ≠ blockAt word.val k.val.toNat 1 ∧
              r.val = 1)) := by
    sorry

  /-- Let m = n/k. For 0 <= j < m, define same(j) as the number of b in [0,m) with word[b*k+t] = word[j*k+t] for all t in [0,k). Whenever the function returns a result r, there exists a block index j with 0 <= j < m and same(j) = m - r, and consequently the word can be made k-periodic in exactly r allowed operations by copying B_j onto every block not equal to B_j.
    Preconditions: Let n = len(word). The input satisfies 1 <= n <= 100000, 1 <= k <= n, k divides n, and every byte of word is an ASCII lowercase letter. -/
  theorem spec_8 (word : Slice U8) (k : I64)
      (hn1 : 1 ≤ word.val.length) (hn2 : word.val.length ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (word.val.length : Int))
      (hdiv : k.val.toNat ∣ word.val.length)
      (hbytes : ∀ (i : Nat) (hi : i < word.val.length),
        97 ≤ (word.val[i]).val ∧ (word.val[i]).val ≤ 122) :
      ∀ r : I64,
        Aegis.MinimumOperationsToMakeKPeriodic.minimum_operations_to_make_k_periodic
            word k = ok r →
          ∃ j, j < word.val.length / k.val.toNat ∧
            (sameCount word.val k.val.toNat (word.val.length / k.val.toNat) j : Int) =
              ((word.val.length / k.val.toNat : Nat) : Int) - r.val ∧
            ReachN k.val.toNat (word.val.length / k.val.toNat) r.val.toNat word.val
              (uniformBlocks (word.val.length / k.val.toNat)
                (blockAt word.val k.val.toNat j)) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (word : Slice U8) (k : I64)
        (hn1 : 1 ≤ word.val.length) (hn2 : word.val.length ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (word.val.length : Int))
        (hdiv : k.val.toNat ∣ word.val.length)
        (hbytes : ∀ (i : Nat) (hi : i < word.val.length),
          97 ≤ (word.val[i]).val ∧ (word.val[i]).val ≤ 122), ∀ r : I64,
          Aegis.MinimumOperationsToMakeKPeriodic.minimum_operations_to_make_k_periodic
              word k = ok r →
            ∃ j, j < word.val.length / k.val.toNat ∧
              (sameCount word.val k.val.toNat (word.val.length / k.val.toNat) j : Int) =
                ((word.val.length / k.val.toNat : Nat) : Int) - r.val ∧
              ReachN k.val.toNat (word.val.length / k.val.toNat) r.val.toNat word.val
                (uniformBlocks (word.val.length / k.val.toNat)
                  (blockAt word.val k.val.toNat j))) := by
    sorry

  /-- Let m = n/k. Whenever the function returns a result r, no sequence of fewer than r allowed operations transforms word into a k-periodic word, where an allowed operation replaces a length-k substring starting at an index divisible by k with another length-k substring starting at an index divisible by k.
    Preconditions: Let n = len(word). The input satisfies 1 <= n <= 100000, 1 <= k <= n, k divides n, and every byte of word is an ASCII lowercase letter. -/
  theorem spec_9 (word : Slice U8) (k : I64)
      (hn1 : 1 ≤ word.val.length) (hn2 : word.val.length ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (word.val.length : Int))
      (hdiv : k.val.toNat ∣ word.val.length)
      (hbytes : ∀ (i : Nat) (hi : i < word.val.length),
        97 ≤ (word.val[i]).val ∧ (word.val[i]).val ≤ 122) :
      ∀ r : I64,
        Aegis.MinimumOperationsToMakeKPeriodic.minimum_operations_to_make_k_periodic
            word k = ok r →
          ∀ t : Nat, (t : Int) < r.val →
            ∀ w' : List U8,
              ReachN k.val.toNat (word.val.length / k.val.toNat) t word.val w' →
                ¬ AllBlocksEqual w' k.val.toNat (word.val.length / k.val.toNat) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (word : Slice U8) (k : I64)
        (hn1 : 1 ≤ word.val.length) (hn2 : word.val.length ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (word.val.length : Int))
        (hdiv : k.val.toNat ∣ word.val.length)
        (hbytes : ∀ (i : Nat) (hi : i < word.val.length),
          97 ≤ (word.val[i]).val ∧ (word.val[i]).val ≤ 122), ∀ r : I64,
          Aegis.MinimumOperationsToMakeKPeriodic.minimum_operations_to_make_k_periodic
              word k = ok r →
            ∀ t : Nat, (t : Int) < r.val →
              ∀ w' : List U8,
                ReachN k.val.toNat (word.val.length / k.val.toNat) t word.val w' →
                  ¬ AllBlocksEqual w' k.val.toNat (word.val.length / k.val.toNat)) := by
    sorry

  /-- Whenever the function returns r on input word and r2 on input word2, r = r2.
    Preconditions: Let n = len(word). The input word satisfies 1 <= n <= 100000, 1 <= k <= n, k divides n, and all bytes are ASCII lowercase. Let word2 be any other byte string of length n satisfying the same conditions for the same n and k, and suppose there is a bijection pi from {0,...,m-1} to itself, where m=n/k, such that word2[b*k+t] = word[pi(b)*k+t] for every b in [0,m) and t in [0,k). -/
  theorem spec_10 (word word2 : Slice U8) (k : I64)
      (hn1 : 1 ≤ word.val.length) (hn2 : word.val.length ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (word.val.length : Int))
      (hdiv : k.val.toNat ∣ word.val.length)
      (hbytes : ∀ (i : Nat) (hi : i < word.val.length),
        97 ≤ (word.val[i]).val ∧ (word.val[i]).val ≤ 122)
      (h2len : word2.val.length = word.val.length)
      (h2bytes : ∀ (i : Nat) (hi : i < word2.val.length),
        97 ≤ (word2.val[i]).val ∧ (word2.val[i]).val ≤ 122)
      (hperm : ∃ pi : Equiv.Perm (Fin (word.val.length / k.val.toNat)),
        ∀ (b : Nat) (hb : b < word.val.length / k.val.toNat) (t : Nat),
          t < k.val.toNat →
            word2.val[b * k.val.toNat + t]? =
              word.val[(pi ⟨b, hb⟩).val * k.val.toNat + t]?) :
      ∀ r r2 : I64,
        Aegis.MinimumOperationsToMakeKPeriodic.minimum_operations_to_make_k_periodic
            word k = ok r →
          Aegis.MinimumOperationsToMakeKPeriodic.minimum_operations_to_make_k_periodic
            word2 k = ok r2 → r.val = r2.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (word word2 : Slice U8) (k : I64)
        (hn1 : 1 ≤ word.val.length) (hn2 : word.val.length ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (word.val.length : Int))
        (hdiv : k.val.toNat ∣ word.val.length)
        (hbytes : ∀ (i : Nat) (hi : i < word.val.length),
          97 ≤ (word.val[i]).val ∧ (word.val[i]).val ≤ 122)
        (h2len : word2.val.length = word.val.length)
        (h2bytes : ∀ (i : Nat) (hi : i < word2.val.length),
          97 ≤ (word2.val[i]).val ∧ (word2.val[i]).val ≤ 122)
        (hperm : ∃ pi : Equiv.Perm (Fin (word.val.length / k.val.toNat)),
          ∀ (b : Nat) (hb : b < word.val.length / k.val.toNat) (t : Nat),
            t < k.val.toNat →
              word2.val[b * k.val.toNat + t]? =
                word.val[(pi ⟨b, hb⟩).val * k.val.toNat + t]?), ∀ r r2 : I64,
          Aegis.MinimumOperationsToMakeKPeriodic.minimum_operations_to_make_k_periodic
              word k = ok r →
            Aegis.MinimumOperationsToMakeKPeriodic.minimum_operations_to_make_k_periodic
              word2 k = ok r2 → r.val = r2.val) := by
    sorry

  /-- Let m = n/k. Whenever the function returns a result r, 0 <= r <= m - 1. Moreover, r = m - 1 if and only if the m length-k blocks B_0, ..., B_{m-1} are pairwise distinct.
    Preconditions: Let n = len(word). The input satisfies 1 <= n <= 100000, 1 <= k <= n, k divides n, and every byte of word is an ASCII lowercase letter. -/
  theorem spec_11 (word : Slice U8) (k : I64)
      (hn1 : 1 ≤ word.val.length) (hn2 : word.val.length ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (word.val.length : Int))
      (hdiv : k.val.toNat ∣ word.val.length)
      (hbytes : ∀ (i : Nat) (hi : i < word.val.length),
        97 ≤ (word.val[i]).val ∧ (word.val[i]).val ≤ 122) :
      ∀ r : I64,
        Aegis.MinimumOperationsToMakeKPeriodic.minimum_operations_to_make_k_periodic
            word k = ok r →
          (0 ≤ r.val ∧ r.val ≤ ((word.val.length / k.val.toNat : Nat) : Int) - 1) ∧
          (r.val = ((word.val.length / k.val.toNat : Nat) : Int) - 1 ↔
            ∀ b c, b < word.val.length / k.val.toNat → c < word.val.length / k.val.toNat →
              b ≠ c → BlocksDiffer word.val k.val.toNat b c) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (word : Slice U8) (k : I64)
        (hn1 : 1 ≤ word.val.length) (hn2 : word.val.length ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (word.val.length : Int))
        (hdiv : k.val.toNat ∣ word.val.length)
        (hbytes : ∀ (i : Nat) (hi : i < word.val.length),
          97 ≤ (word.val[i]).val ∧ (word.val[i]).val ≤ 122), ∀ r : I64,
          Aegis.MinimumOperationsToMakeKPeriodic.minimum_operations_to_make_k_periodic
              word k = ok r →
            (0 ≤ r.val ∧ r.val ≤ ((word.val.length / k.val.toNat : Nat) : Int) - 1) ∧
            (r.val = ((word.val.length / k.val.toNat : Nat) : Int) - 1 ↔
              ∀ b c, b < word.val.length / k.val.toNat → c < word.val.length / k.val.toNat →
                b ≠ c → BlocksDiffer word.val k.val.toNat b c)) := by
    sorry

  end AegisSpec.MinimumOperationsToMakeKPeriodic

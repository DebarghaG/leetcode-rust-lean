import Aegis.CountCompleteSubstrings.Code.Funs

/-!
# Specifications of `Aegis.CountCompleteSubstrings.count_complete_substrings`

LeetCode problem `count-complete-substrings`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  set_option autoImplicit false

  namespace AegisSpec.CountCompleteSubstrings

  open Aegis.CountCompleteSubstrings

  def byteAt (word : Slice U8) (i : ℕ) : ℕ := (word.val.getD i ⟨0⟩).val

  def closeBytes (x y : ℕ) : Prop := x ≤ y + 2 ∧ y ≤ x + 2

  def byteCount (word : Slice U8) (a b c : ℕ) : ℕ :=
    ((Finset.Ico a b).filter (fun i => byteAt word i = c)).card

  def ChainClose (word : Slice U8) (a b : ℕ) : Prop :=
    ∀ i : ℕ, a ≤ i → i + 1 < b → closeBytes (byteAt word i) (byteAt word (i + 1))

  def NoRepeat (word : Slice U8) (a b : ℕ) : Prop :=
    ∀ i j : ℕ, a ≤ i → i < j → j < b → byteAt word i ≠ byteAt word j

  def IsComplete (word : Slice U8) (k a b : ℕ) : Prop :=
    (∀ c : ℕ, byteCount word a b c = 0 ∨ byteCount word a b c = k) ∧ ChainClose word a b

  noncomputable def numPairs (n : ℕ) (P : ℕ → ℕ → Prop) : ℕ := by
    classical
    exact (((Finset.range (n + 1)).product (Finset.range (n + 1))).filter
      (fun p : ℕ × ℕ => p.1 < p.2 ∧ P p.1 p.2)).card

  noncomputable def numComplete (word : Slice U8) (k : ℕ) : ℕ :=
    numPairs word.val.length (fun a b => IsComplete word k a b)

  noncomputable def numLenMultiple (n k : ℕ) : ℕ :=
    numPairs n (fun a b => ∃ d : ℕ, 1 ≤ d ∧ d ≤ 26 ∧ b - a = d * k)

  noncomputable def numMonoBlocks (word : Slice U8) (k : ℕ) : ℕ := by
    classical
    exact ((Finset.range (word.val.length - k + 1)).filter
      (fun a : ℕ => ∀ t : ℕ, t < k → byteAt word (a + t) = byteAt word a)).card

  noncomputable def numNoRepeat (word : Slice U8) : ℕ :=
    numPairs word.val.length (fun a b => NoRepeat word a b)

  noncomputable def numChainClose (word : Slice U8) : ℕ :=
    numPairs word.val.length (fun a b => ChainClose word a b)

  noncomputable def numNoRepeatChainClose (word : Slice U8) : ℕ :=
    numPairs word.val.length (fun a b => NoRepeat word a b ∧ ChainClose word a b)

  def flipByte (x : ℕ) : U8 := ⟨BitVec.ofNat 8 (219 - x)⟩

  def shiftByte (x : ℕ) : U8 := ⟨BitVec.ofNat 8 (x + 1)⟩

  /-- Whenever the function returns a result ans, ans equals the number of pairs (a,b) with 0 <= a < b <= n such that the substring word[a..b) = word[a], word[a+1], ..., word[b-1] is complete for k, where complete for k means: (1) for every byte c, the number of indices i with a <= i < b and word[i] = c is either 0 or k; and (2) for every i with a <= i < b-1, |word[i+1] - word[i]| <= 2.
    Preconditions: Let n = len(word). 1 <= n <= 100000; for every i with 0 <= i < n, 97 <= word[i] <= 122; 1 <= k <= n. -/
  theorem spec_1 (word : Slice U8) (k : I64) (ans : I64)
      (hn_pos : 1 ≤ word.val.length) (hn_le : word.val.length ≤ 100000)
      (hletters : ∀ i : ℕ, i < word.val.length → 97 ≤ byteAt word i ∧ byteAt word i ≤ 122)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (word.val.length : ℤ))
      (hres : count_complete_substrings word k = ok ans) :
      ans.val = (numComplete word k.val.toNat : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (word : Slice U8) (k : I64) (ans : I64)
        (hn_pos : 1 ≤ word.val.length) (hn_le : word.val.length ≤ 100000)
        (hletters : ∀ i : ℕ, i < word.val.length → 97 ≤ byteAt word i ∧ byteAt word i ≤ 122)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (word.val.length : ℤ))
        (hres : count_complete_substrings word k = ok ans), ans.val = (numComplete word k.val.toNat : ℤ)) := by
    sorry

  /-- The function returns a result ans (it does not fail) for every input satisfying the preconditions.
    Preconditions: Let n = len(word). 1 <= n <= 100000; for every i with 0 <= i < n, 97 <= word[i] <= 122; 1 <= k <= n. -/
  theorem spec_2 (word : Slice U8) (k : I64)
      (hn_pos : 1 ≤ word.val.length) (hn_le : word.val.length ≤ 100000)
      (hletters : ∀ i : ℕ, i < word.val.length → 97 ≤ byteAt word i ∧ byteAt word i ≤ 122)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (word.val.length : ℤ)) :
      ∃ ans : I64, count_complete_substrings word k = ok ans := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (word : Slice U8) (k : I64)
        (hn_pos : 1 ≤ word.val.length) (hn_le : word.val.length ≤ 100000)
        (hletters : ∀ i : ℕ, i < word.val.length → 97 ≤ byteAt word i ∧ byteAt word i ≤ 122)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (word.val.length : ℤ)), ∃ ans : I64, count_complete_substrings word k = ok ans) := by
    sorry

  /-- Whenever the function returns a result ans, ans is at most the number of pairs (a,b) with 0 <= a < b <= n for which b-a = d*k for some integer d with 1 <= d <= 26.
    Preconditions: Let n = len(word). 1 <= n <= 100000; for every i with 0 <= i < n, 97 <= word[i] <= 122; 1 <= k <= n. -/
  theorem spec_3 (word : Slice U8) (k : I64) (ans : I64)
      (hn_pos : 1 ≤ word.val.length) (hn_le : word.val.length ≤ 100000)
      (hletters : ∀ i : ℕ, i < word.val.length → 97 ≤ byteAt word i ∧ byteAt word i ≤ 122)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (word.val.length : ℤ))
      (hres : count_complete_substrings word k = ok ans) :
      ans.val ≤ (numLenMultiple word.val.length k.val.toNat : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (word : Slice U8) (k : I64) (ans : I64)
        (hn_pos : 1 ≤ word.val.length) (hn_le : word.val.length ≤ 100000)
        (hletters : ∀ i : ℕ, i < word.val.length → 97 ≤ byteAt word i ∧ byteAt word i ≤ 122)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (word.val.length : ℤ))
        (hres : count_complete_substrings word k = ok ans), ans.val ≤ (numLenMultiple word.val.length k.val.toNat : ℤ)) := by
    sorry

  /-- Whenever the function returns a result ans, ans = n - k + 1.
    Preconditions: Let n = len(word). 1 <= n <= 100000; for every i with 0 <= i < n, 97 <= word[i] <= 122; 1 <= k <= n; and there is a byte c such that word[i] = c for every i with 0 <= i < n. -/
  theorem spec_4 (word : Slice U8) (k : I64) (ans : I64)
      (hn_pos : 1 ≤ word.val.length) (hn_le : word.val.length ≤ 100000)
      (hletters : ∀ i : ℕ, i < word.val.length → 97 ≤ byteAt word i ∧ byteAt word i ≤ 122)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (word.val.length : ℤ))
      (hconstant : ∃ c : ℕ, ∀ i : ℕ, i < word.val.length → byteAt word i = c)
      (hres : count_complete_substrings word k = ok ans) :
      ans.val = (word.val.length : ℤ) - k.val + 1 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (word : Slice U8) (k : I64) (ans : I64)
        (hn_pos : 1 ≤ word.val.length) (hn_le : word.val.length ≤ 100000)
        (hletters : ∀ i : ℕ, i < word.val.length → 97 ≤ byteAt word i ∧ byteAt word i ≤ 122)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (word.val.length : ℤ))
        (hconstant : ∃ c : ℕ, ∀ i : ℕ, i < word.val.length → byteAt word i = c)
        (hres : count_complete_substrings word k = ok ans), ans.val = (word.val.length : ℤ) - k.val + 1) := by
    sorry

  /-- Whenever the function returns a result ans, ans = n.
    Preconditions: Let n = len(word). 1 <= n <= 100000; for every i with 0 <= i < n, 97 <= word[i] <= 122; k = 1; and for every i with 0 <= i < n-1, |word[i+1] - word[i]| > 2. -/
  theorem spec_5 (word : Slice U8) (k : I64) (ans : I64)
      (hn_pos : 1 ≤ word.val.length) (hn_le : word.val.length ≤ 100000)
      (hletters : ∀ i : ℕ, i < word.val.length → 97 ≤ byteAt word i ∧ byteAt word i ≤ 122)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (word.val.length : ℤ))
      (hk_one : k.val = 1)
      (hseparated : ∀ i : ℕ, i + 1 < word.val.length →
        ¬ closeBytes (byteAt word i) (byteAt word (i + 1)))
      (hres : count_complete_substrings word k = ok ans) :
      ans.val = (word.val.length : ℤ) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (word : Slice U8) (k : I64) (ans : I64)
        (hn_pos : 1 ≤ word.val.length) (hn_le : word.val.length ≤ 100000)
        (hletters : ∀ i : ℕ, i < word.val.length → 97 ≤ byteAt word i ∧ byteAt word i ≤ 122)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (word.val.length : ℤ))
        (hk_one : k.val = 1)
        (hseparated : ∀ i : ℕ, i + 1 < word.val.length →
          ¬ closeBytes (byteAt word i) (byteAt word (i + 1)))
        (hres : count_complete_substrings word k = ok ans), ans.val = (word.val.length : ℤ)) := by
    sorry

  /-- Whenever the function returns a result ans, ans equals the number of indices a with 0 <= a <= n-k such that all k bytes word[a], word[a+1], ..., word[a+k-1] are equal to each other.
    Preconditions: Let n = len(word). 1 <= n <= 100000; for every i with 0 <= i < n, 97 <= word[i] <= 122; 1 <= k <= n; and 2*k > n. -/
  theorem spec_6 (word : Slice U8) (k : I64) (ans : I64)
      (hn_pos : 1 ≤ word.val.length) (hn_le : word.val.length ≤ 100000)
      (hletters : ∀ i : ℕ, i < word.val.length → 97 ≤ byteAt word i ∧ byteAt word i ≤ 122)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (word.val.length : ℤ))
      (hk_large : 2 * k.val > (word.val.length : ℤ))
      (hres : count_complete_substrings word k = ok ans) :
      ans.val = (numMonoBlocks word k.val.toNat : ℤ) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (word : Slice U8) (k : I64) (ans : I64)
        (hn_pos : 1 ≤ word.val.length) (hn_le : word.val.length ≤ 100000)
        (hletters : ∀ i : ℕ, i < word.val.length → 97 ≤ byteAt word i ∧ byteAt word i ≤ 122)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (word.val.length : ℤ))
        (hk_large : 2 * k.val > (word.val.length : ℤ))
        (hres : count_complete_substrings word k = ok ans), ans.val = (numMonoBlocks word k.val.toNat : ℤ)) := by
    sorry

  /-- Let word_rev be the byte array of length n with word_rev[i] = word[n-1-i] for every i with 0 <= i < n. If the function returns ans on (word,k) and ans_rev on (word_rev,k), then ans = ans_rev.
    Preconditions: Let n = len(word). 1 <= n <= 100000; for every i with 0 <= i < n, 97 <= word[i] <= 122; 1 <= k <= n. -/
  theorem spec_7 (word word_rev : Slice U8) (k ans ans_rev : I64)
      (hn_pos : 1 ≤ word.val.length) (hn_le : word.val.length ≤ 100000)
      (hletters : ∀ i : ℕ, i < word.val.length → 97 ≤ byteAt word i ∧ byteAt word i ≤ 122)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (word.val.length : ℤ))
      (hrev : word_rev.val = word.val.reverse)
      (hres : count_complete_substrings word k = ok ans)
      (hres_rev : count_complete_substrings word_rev k = ok ans_rev) :
      ans.val = ans_rev.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (word word_rev : Slice U8) (k ans ans_rev : I64)
        (hn_pos : 1 ≤ word.val.length) (hn_le : word.val.length ≤ 100000)
        (hletters : ∀ i : ℕ, i < word.val.length → 97 ≤ byteAt word i ∧ byteAt word i ≤ 122)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (word.val.length : ℤ))
        (hrev : word_rev.val = word.val.reverse)
        (hres : count_complete_substrings word k = ok ans)
        (hres_rev : count_complete_substrings word_rev k = ok ans_rev), ans.val = ans_rev.val) := by
    sorry

  /-- Let word_flip be the byte array of length n with word_flip[i] = 219 - word[i] for every i with 0 <= i < n (this maps 'a' to 'z', 'b' to 'y', etc.). If the function returns ans on (word,k) and ans_flip on (word_flip,k), then ans = ans_flip.
    Preconditions: Let n = len(word). 1 <= n <= 100000; for every i with 0 <= i < n, 97 <= word[i] <= 122; 1 <= k <= n. -/
  theorem spec_8 (word word_flip : Slice U8) (k ans ans_flip : I64)
      (hn_pos : 1 ≤ word.val.length) (hn_le : word.val.length ≤ 100000)
      (hletters : ∀ i : ℕ, i < word.val.length → 97 ≤ byteAt word i ∧ byteAt word i ≤ 122)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (word.val.length : ℤ))
      (hflip : word_flip.val = word.val.map (fun b : U8 => flipByte b.val))
      (hres : count_complete_substrings word k = ok ans)
      (hres_flip : count_complete_substrings word_flip k = ok ans_flip) :
      ans.val = ans_flip.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (word word_flip : Slice U8) (k ans ans_flip : I64)
        (hn_pos : 1 ≤ word.val.length) (hn_le : word.val.length ≤ 100000)
        (hletters : ∀ i : ℕ, i < word.val.length → 97 ≤ byteAt word i ∧ byteAt word i ≤ 122)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (word.val.length : ℤ))
        (hflip : word_flip.val = word.val.map (fun b : U8 => flipByte b.val))
        (hres : count_complete_substrings word k = ok ans)
        (hres_flip : count_complete_substrings word_flip k = ok ans_flip), ans.val = ans_flip.val) := by
    sorry

  /-- Let word_shift be the byte array of length n with word_shift[i] = word[i] + 1 for every i with 0 <= i < n. If the function returns ans on (word,k) and ans_shift on (word_shift,k), then ans = ans_shift.
    Preconditions: Let n = len(word). 1 <= n <= 100000; for every i with 0 <= i < n, 97 <= word[i] <= 122; 1 <= k <= n; and for every i with 0 <= i < n, word[i] <= 121. -/
  theorem spec_9 (word word_shift : Slice U8) (k ans ans_shift : I64)
      (hn_pos : 1 ≤ word.val.length) (hn_le : word.val.length ≤ 100000)
      (hletters : ∀ i : ℕ, i < word.val.length → 97 ≤ byteAt word i ∧ byteAt word i ≤ 122)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (word.val.length : ℤ))
      (hbelow_z : ∀ i : ℕ, i < word.val.length → byteAt word i ≤ 121)
      (hshift : word_shift.val = word.val.map (fun b : U8 => shiftByte b.val))
      (hres : count_complete_substrings word k = ok ans)
      (hres_shift : count_complete_substrings word_shift k = ok ans_shift) :
      ans.val = ans_shift.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (word word_shift : Slice U8) (k ans ans_shift : I64)
        (hn_pos : 1 ≤ word.val.length) (hn_le : word.val.length ≤ 100000)
        (hletters : ∀ i : ℕ, i < word.val.length → 97 ≤ byteAt word i ∧ byteAt word i ≤ 122)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (word.val.length : ℤ))
        (hbelow_z : ∀ i : ℕ, i < word.val.length → byteAt word i ≤ 121)
        (hshift : word_shift.val = word.val.map (fun b : U8 => shiftByte b.val))
        (hres : count_complete_substrings word k = ok ans)
        (hres_shift : count_complete_substrings word_shift k = ok ans_shift), ans.val = ans_shift.val) := by
    sorry

  /-- Whenever the function returns a result ans, ans is at least the number of indices a with 0 <= a <= n-k such that all k bytes word[a], word[a+1], ..., word[a+k-1] are equal to each other.
    Preconditions: Let n = len(word). 1 <= n <= 100000; for every i with 0 <= i < n, 97 <= word[i] <= 122; 1 <= k <= n. -/
  theorem spec_10 (word : Slice U8) (k : I64) (ans : I64)
      (hn_pos : 1 ≤ word.val.length) (hn_le : word.val.length ≤ 100000)
      (hletters : ∀ i : ℕ, i < word.val.length → 97 ≤ byteAt word i ∧ byteAt word i ≤ 122)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (word.val.length : ℤ))
      (hres : count_complete_substrings word k = ok ans) :
      (numMonoBlocks word k.val.toNat : ℤ) ≤ ans.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (word : Slice U8) (k : I64) (ans : I64)
        (hn_pos : 1 ≤ word.val.length) (hn_le : word.val.length ≤ 100000)
        (hletters : ∀ i : ℕ, i < word.val.length → 97 ≤ byteAt word i ∧ byteAt word i ≤ 122)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (word.val.length : ℤ))
        (hres : count_complete_substrings word k = ok ans), (numMonoBlocks word k.val.toNat : ℤ) ≤ ans.val) := by
    sorry

  /-- Whenever the function returns a result ans, ans equals the number of pairs (a,b) with 0 <= a < b <= n such that word[a..b) has no repeated character, i.e., for all i,j with a <= i < j < b, word[i] != word[j].
    Preconditions: Let n = len(word). 1 <= n <= 100000; for every i with 0 <= i < n, 97 <= word[i] <= 122; k = 1; and for every i with 0 <= i < n-1, |word[i+1] - word[i]| <= 2. -/
  theorem spec_11 (word : Slice U8) (k : I64) (ans : I64)
      (hn_pos : 1 ≤ word.val.length) (hn_le : word.val.length ≤ 100000)
      (hletters : ∀ i : ℕ, i < word.val.length → 97 ≤ byteAt word i ∧ byteAt word i ≤ 122)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (word.val.length : ℤ))
      (hk_one : k.val = 1)
      (hclose : ∀ i : ℕ, i + 1 < word.val.length →
        closeBytes (byteAt word i) (byteAt word (i + 1)))
      (hres : count_complete_substrings word k = ok ans) :
      ans.val = (numNoRepeat word : ℤ) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (word : Slice U8) (k : I64) (ans : I64)
        (hn_pos : 1 ≤ word.val.length) (hn_le : word.val.length ≤ 100000)
        (hletters : ∀ i : ℕ, i < word.val.length → 97 ≤ byteAt word i ∧ byteAt word i ≤ 122)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (word.val.length : ℤ))
        (hk_one : k.val = 1)
        (hclose : ∀ i : ℕ, i + 1 < word.val.length →
          closeBytes (byteAt word i) (byteAt word (i + 1)))
        (hres : count_complete_substrings word k = ok ans), ans.val = (numNoRepeat word : ℤ)) := by
    sorry

  /-- Whenever the function returns a result ans, ans equals the number of pairs (a,b) with 0 <= a < b <= n such that for every i with a <= i < b-1, |word[i+1] - word[i]| <= 2.
    Preconditions: Let n = len(word). 1 <= n <= 100000; for every i with 0 <= i < n, 97 <= word[i] <= 122; k = 1; and for all i,j with 0 <= i < j < n, word[i] != word[j]. -/
  theorem spec_12 (word : Slice U8) (k : I64) (ans : I64)
      (hn_pos : 1 ≤ word.val.length) (hn_le : word.val.length ≤ 100000)
      (hletters : ∀ i : ℕ, i < word.val.length → 97 ≤ byteAt word i ∧ byteAt word i ≤ 122)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (word.val.length : ℤ))
      (hk_one : k.val = 1)
      (hdistinct : ∀ i j : ℕ, i < j → j < word.val.length → byteAt word i ≠ byteAt word j)
      (hres : count_complete_substrings word k = ok ans) :
      ans.val = (numChainClose word : ℤ) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (word : Slice U8) (k : I64) (ans : I64)
        (hn_pos : 1 ≤ word.val.length) (hn_le : word.val.length ≤ 100000)
        (hletters : ∀ i : ℕ, i < word.val.length → 97 ≤ byteAt word i ∧ byteAt word i ≤ 122)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (word.val.length : ℤ))
        (hk_one : k.val = 1)
        (hdistinct : ∀ i j : ℕ, i < j → j < word.val.length → byteAt word i ≠ byteAt word j)
        (hres : count_complete_substrings word k = ok ans), ans.val = (numChainClose word : ℤ)) := by
    sorry

  /-- Whenever the function returns a result ans, ans equals the number of pairs (a,b) with 0 <= a < b <= n such that (i) for all i,j with a <= i < j < b, word[i] != word[j], and (ii) for every i with a <= i < b-1, |word[i+1] - word[i]| <= 2.
    Preconditions: Let n = len(word). 1 <= n <= 100000; for every i with 0 <= i < n, 97 <= word[i] <= 122; k = 1. -/
  theorem spec_13 (word : Slice U8) (k : I64) (ans : I64)
      (hn_pos : 1 ≤ word.val.length) (hn_le : word.val.length ≤ 100000)
      (hletters : ∀ i : ℕ, i < word.val.length → 97 ≤ byteAt word i ∧ byteAt word i ≤ 122)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (word.val.length : ℤ))
      (hk_one : k.val = 1)
      (hres : count_complete_substrings word k = ok ans) :
      ans.val = (numNoRepeatChainClose word : ℤ) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (word : Slice U8) (k : I64) (ans : I64)
        (hn_pos : 1 ≤ word.val.length) (hn_le : word.val.length ≤ 100000)
        (hletters : ∀ i : ℕ, i < word.val.length → 97 ≤ byteAt word i ∧ byteAt word i ≤ 122)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (word.val.length : ℤ))
        (hk_one : k.val = 1)
        (hres : count_complete_substrings word k = ok ans), ans.val = (numNoRepeatChainClose word : ℤ)) := by
    sorry

  end AegisSpec.CountCompleteSubstrings

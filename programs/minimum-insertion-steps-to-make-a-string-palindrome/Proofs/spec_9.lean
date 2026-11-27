import Aegis.MinInsertions.Code.Funs

/-
Proof of `AegisSpec.MinInsertions.spec_9` (minimum-insertion-steps-to-make-a-string-palindrome).
Contributor: by-eureka
-/

open Aeneas Aeneas.Std Result

  set_option autoImplicit false

  namespace AegisSpec.MinInsertions

  /-!
  ### Conventions

  `min_insertions` takes an Aeneas slice `s : Slice U8`.  The byte string held by the slice is
  `s.val : List U8`, and `len(s)` of the informal specification is `s.val.length`
  (see `slice_length_eq_val`); the ASCII code of a byte `b` is `b.val : Nat` and the numeric
  result of a call is `r.val : Int` for a returned `r : I64`.
  -/

  /-! ### Helper notions used by the specifications -/

  /-- `s.length` is the length of the list underlying the slice `s`. -/
  theorem slice_length_eq_val {α : Type} (s : Slice α) : s.length = s.val.length := by
    simp [Slice.length]

  /-- `b` is the ASCII code of a lowercase English letter, i.e. `97 ≤ b ≤ 122`. -/
  def isLowerAscii (b : U8) : Prop := 97 ≤ b.val ∧ b.val ≤ 122

  /-- `l` is a palindrome: `l[j] = l[len(l) - 1 - j]` for every index `j` in range. -/
  def isPalindrome (l : List U8) : Prop :=
    ∀ (j : Nat), (hj : j < l.length) → l[j] = l[l.length - 1 - j]

  /-- `s` occurs in `t` as a subsequence: there are indices
  `idx 0 < idx 1 < … < idx (len s - 1)` inside `t` carrying the bytes of `s` in order. -/
  def isSubsequence (s t : List U8) : Prop :=
    ∃ idx : Nat → Nat,
      (∀ (a : Nat), a < s.length → idx a < t.length) ∧
        (∀ (a b : Nat), a < b → b < s.length → idx a < idx b) ∧
          (∀ (a : Nat), a < s.length → t[idx a]? = s[a]?)

  /-- `s` has a palindromic supersequence of length `len s + k`: there is a byte string `t`
  with `len t = len s + k`, `t` palindromic and `s` a subsequence of `t`. -/
  def hasPalindromicSupersequence (s : List U8) (k : Nat) : Prop :=
    ∃ t : List U8, t.length = s.length + k ∧ isPalindrome t ∧ isSubsequence s t

  /-- `s` has a palindromic subsequence of size `m`, witnessed by indices
  `i_0 < i_1 < … < i_(m-1)` with `s[i_a] = s[i_(m-1-a)]` for every `a < m`. -/
  def isPalindromicSubseqSize (s : List U8) (m : Nat) : Prop :=
    ∃ i : Nat → Nat,
      (∀ (a : Nat), a < m → i a < s.length) ∧
        (∀ (a b : Nat), a < b → b < m → i a < i b) ∧
          (∀ (a : Nat), a < m → s[i a]? = s[i (m - 1 - a)]?)

  /-- `s` has a common subsequence with its reversal of size `m`, witnessed by indices
  `i_0 < i_1 < … < i_(m-1)` and `j_0 < j_1 < … < j_(m-1)` with
  `s[i_a] = s[len(s) - 1 - j_a]` for every `a < m`. -/
  def isCommonSubseqSize (s : List U8) (m : Nat) : Prop :=
    ∃ i j : Nat → Nat,
      (∀ (a : Nat), a < m → i a < s.length) ∧
        (∀ (a b : Nat), a < b → b < m → i a < i b) ∧
          (∀ (a : Nat), a < m → j a < s.length) ∧
            (∀ (a b : Nat), a < b → b < m → j a < j b) ∧
              (∀ (a : Nat), a < m → s[i a]? = s[s.length - 1 - j a]?)

  /-! ### Auxiliary definitions used in the proof of `spec_S12` -/

  /-- `dpv l lo hi` is the value of the classic interval DP for the sub-list `l[lo..hi]`
  (the minimum number of insertions making that sub-list a palindrome); it is `0` for an
  empty or out-of-bounds interval. -/
  def dpv (l : List U8) (lo hi : Nat) : Nat :=
    if h : lo ≤ hi ∧ hi < l.length then
      (if lo = hi then 0
       else if l[lo]? = l[hi]? then dpv l (lo + 1) (hi - 1)
       else 1 + min (dpv l (lo + 1) hi) (dpv l lo (hi - 1)))
    else 0
  termination_by hi - lo
  decreasing_by all_goals omega

  /-- `lpsOf l lo hi` is the length of the longest palindromic subsequence of the sub-list
  `l[lo..hi]`; it is `0` for an empty or out-of-bounds interval. -/
  def lpsOf (l : List U8) (lo hi : Nat) : Nat :=
    if h : lo ≤ hi ∧ hi < l.length then
      (if lo = hi then 1
       else if l[lo]? = l[hi]? then 2 + lpsOf l (lo + 1) (hi - 1)
       else max (lpsOf l (lo + 1) hi) (lpsOf l lo (hi - 1)))
    else 0
  termination_by hi - lo
  decreasing_by all_goals omega

  /-- `p` enumerates a palindromic subsequence of `l` whose indices all lie in `[lo,hi]`. -/
  def IsPalinIn (l : List U8) (lo hi m : Nat) : Prop :=
    ∃ p : Nat → Nat,
      (∀ x, x < m → lo ≤ p x ∧ p x ≤ hi) ∧
        (∀ x y, x < y → y < m → p x < p y) ∧
          (∀ x, x < m → l[p x]? = l[p (m - 1 - x)]?)

  /-- `i` and `j` enumerate a common subsequence of `u` and `v` of size `m`
  (index-based, in the same style as `isCommonSubseqSize`). -/
  def IsCSS (u v : List U8) (m : Nat) : Prop :=
    ∃ i j : Nat → Nat,
      (∀ x, x < m → i x < u.length) ∧
        (∀ x y, x < y → y < m → i x < i y) ∧
          (∀ x, x < m → j x < v.length) ∧
            (∀ x y, x < y → y < m → j x < j y) ∧
              (∀ x, x < m → u[i x]? = v[j x]?)

  /-- An "aligned family" inside `[lo,hi]`: an increasing index sequence `i` and a decreasing
  index sequence `k` carrying equal letters.  It is the combinatorial core of a common
  subsequence of `l` with its reversal. -/
  def IsFamily (l : List U8) (lo hi m : Nat) : Prop :=
    ∃ i k : Nat → Nat,
      (∀ x, x < m → lo ≤ i x ∧ i x ≤ hi) ∧
        (∀ x y, x < y → y < m → i x < i y) ∧
          (∀ x, x < m → lo ≤ k x ∧ k x ≤ hi) ∧
            (∀ x y, x < y → y < m → k y < k x) ∧
              (∀ x, x < m → l[i x]? = l[k x]?)

  /-! ### Auxiliary lemmas used in the proof of `spec_S12` -/

  /-- An index sequence that is strictly increasing inside `[lo,hi]` has at most `hi-lo+1`
  entries. -/
  theorem lt_of_strictMono_range {p : Nat → Nat} {lo hi m : Nat}
      (hlo : ∀ x, x < m → lo ≤ p x) (hhi : ∀ x, x < m → p x ≤ hi)
      (hmono : ∀ x y, x < y → y < m → p x < p y) : m ≤ hi - lo + 1 := by
    have key : ∀ x, x < m → lo + x ≤ p x := by
      intro x
      induction x with
      | zero => intro hx; simpa using hlo 0 hx
      | succ k ih =>
        intro hk
        have h1 : lo + k ≤ p k := ih (by omega)
        have h2 := hmono k (k + 1) (by omega) hk
        omega
    rcases Nat.eq_zero_or_pos m with hm | hm
    · omega
    · have h3 := key (m - 1) (by omega)
      have h4 := hhi (m - 1) (by omega)
      omega

  /-- `IsPalinIn` is monotone in the ambient interval. -/
  theorem IsPalinIn.mono {l : List U8} {lo hi lo' hi' m : Nat}
      (h : IsPalinIn l lo hi m) (h1 : lo' ≤ lo) (h2 : hi ≤ hi') :
      IsPalinIn l lo' hi' m := by
    obtain ⟨p, hb, hm, hp⟩ := h
    exact ⟨p, fun x hx => ⟨le_trans h1 (hb x hx).1, le_trans (hb x hx).2 h2⟩, hm, hp⟩

  /-- The empty palindromic subsequence, in any interval. -/
  lemma mA_palinIn_zero (l : List U8) (lo hi : Nat) : IsPalinIn l lo hi 0 :=
    ⟨fun _ => lo, by intro x hx; omega, by intro x y hx hy; omega, by intro x hx; omega⟩

  /-- Wrapping a palindromic subsequence of `[lo+1,hi-1]` with the two equal end indices
  `lo < hi` gives a palindromic subsequence of `[lo,hi]` two longer. -/
  lemma mA_wrap {l : List U8} {lo hi M : Nat} (h : IsPalinIn l (lo + 1) (hi - 1) M)
      (hlt : lo < hi) (heq : l[lo]? = l[hi]?) : IsPalinIn l lo hi (M + 2) := by
    obtain ⟨q, hqb, hqm, hqp⟩ := h
    set p : Nat → Nat :=
      fun x => if x = 0 then lo else if x = M + 1 then hi else q (x - 1) with hp
    have hp0 : p 0 = lo := by rw [hp]; simp
    have hpL : p (M + 1) = hi := by rw [hp]; simp
    have hpE : ∀ x, x ≠ 0 → x ≠ M + 1 → p x = q (x - 1) := by
      intro x h0 hM
      rw [hp]
      simp only [if_neg h0, if_neg hM]
    refine ⟨p, ?_, ?_, ?_⟩
    · intro x hx
      rcases Nat.eq_zero_or_pos x with h0 | hpos
      · subst h0
        rw [hp0]; omega
      · by_cases hM : x = M + 1
        · subst hM
          rw [hpL]; omega
        · rw [hpE x (by omega) hM]
          have hk : x - 1 < M := by omega
          have hb := hqb (x - 1) hk
          omega
    · intro x y hx hy
      rcases Nat.eq_zero_or_pos x with h0 | hpos
      · subst h0
        rw [hp0]
        by_cases hM : y = M + 1
        · subst hM
          rw [hpL]; omega
        · rw [hpE y (by omega) hM]
          have hy1 : y - 1 < M := by omega
          have hb := (hqb (y - 1) hy1).1
          omega
      · have hxM : x ≠ M + 1 := by omega
        rw [hpE x (by omega) hxM]
        have hx1 : x - 1 < M := by omega
        have hxb := (hqb (x - 1) hx1).2
        by_cases hM : y = M + 1
        · subst hM
          rw [hpL]; omega
        · rw [hpE y (by omega) hM]
          have hy1 : y - 1 < M := by omega
          have hm := hqm (x - 1) (y - 1) (by omega) hy1
          omega
    · intro x hx
      rcases Nat.eq_zero_or_pos x with h0 | hpos
      · subst h0
        have hidx : M + 2 - 1 - 0 = M + 1 := by omega
        rw [hidx, hp0, hpL]
        exact heq
      · by_cases hM : x = M + 1
        · subst hM
          have hidx : M + 2 - 1 - (M + 1) = 0 := by omega
          rw [hidx, hpL, hp0]
          exact heq.symm
        · rw [hpE x (by omega) hM]
          have hk : x - 1 < M := by omega
          have hm0 : M + 2 - 1 - x ≠ 0 := by omega
          have hmM : M + 2 - 1 - x ≠ M + 1 := by omega
          rw [hpE (M + 2 - 1 - x) hm0 hmM]
          have hidx : M + 2 - 1 - x - 1 = M - 1 - (x - 1) := by omega
          rw [hidx]
          exact hqp (x - 1) hk

  /-- Arithmetic core of the unequal-ends case of `dpv_add_lpsOf`. -/
  lemma mA_minmax_key {a b c d K : Nat} (h1 : a + c = K) (h2 : b + d = K) :
      1 + min a b + max c d = K + 1 := by
    rcases Nat.le_total a b with h | h
    · have hc : d ≤ c := by omega
      have hmc : max c d = c := le_antisymm (max_le (le_refl c) hc) (le_max_left c d)
      rw [min_eq_left h, hmc]
      omega
    · have hd : c ≤ d := by omega
      have hmd : max c d = d := le_antisymm (max_le hd (le_refl d)) (le_max_right c d)
      rw [min_eq_right h, hmd]
      omega

  /-- `lpsOf` is attained (helper version, stated before the theorem of the same name so that
  the name `lpsOf` still denotes the definition inside its proof). -/
  lemma mA_lpsOf_attained {l : List U8} {lo hi : Nat} (h1 : lo ≤ hi) (h2 : hi < l.length) :
      IsPalinIn l lo hi (lpsOf l lo hi) := by
    suffices H : ∀ d lo hi, hi - lo = d → lo ≤ hi → hi < l.length →
        IsPalinIn l lo hi (lpsOf l lo hi) from H _ lo hi rfl h1 h2
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro lo hi hd h1 h2
      rw [lpsOf]
      rw [dif_pos (show lo ≤ hi ∧ hi < l.length from ⟨h1, h2⟩)]
      by_cases hEq : lo = hi
      · rw [if_pos hEq]
        refine ⟨fun _ => lo, ?_, ?_, ?_⟩
        · intro x hx
          have hval : (fun _ => lo) x = lo := rfl
          rw [hval]
          exact ⟨le_refl lo, by omega⟩
        · intro x y hx hy; omega
        · intro x hx
          have hx0 : 1 - 1 - x = 0 := by omega
          rw [hx0]
      · rw [if_neg hEq]
        by_cases hEnds : l[lo]? = l[hi]?
        · rw [if_pos hEnds]
          have hInner : IsPalinIn l (lo + 1) (hi - 1) (lpsOf l (lo + 1) (hi - 1)) := by
            by_cases hin : lo + 1 ≤ hi - 1 ∧ hi - 1 < l.length
            · exact ih _ (by omega) (lo + 1) (hi - 1) rfl hin.1 hin.2
            · have hz : lpsOf l (lo + 1) (hi - 1) = 0 := by
                rw [lpsOf]
                rw [dif_neg hin]
              rw [hz]
              exact mA_palinIn_zero l (lo + 1) (hi - 1)
          have hw : IsPalinIn l lo hi (lpsOf l (lo + 1) (hi - 1) + 2) :=
            mA_wrap hInner (by omega) hEnds
          have he : 2 + lpsOf l (lo + 1) (hi - 1) = lpsOf l (lo + 1) (hi - 1) + 2 := by omega
          rw [he]
          exact hw
        · rw [if_neg hEnds]
          have hA : IsPalinIn l (lo + 1) hi (lpsOf l (lo + 1) hi) :=
            ih _ (by omega) (lo + 1) hi rfl (by omega) h2
          have hB : IsPalinIn l lo (hi - 1) (lpsOf l lo (hi - 1)) :=
            ih _ (by omega) lo (hi - 1) rfl (by omega) (by omega)
          have hA' : IsPalinIn l lo hi (lpsOf l (lo + 1) hi) := hA.mono (by omega) (by omega)
          have hB' : IsPalinIn l lo hi (lpsOf l lo (hi - 1)) := hB.mono (by omega) (by omega)
          by_cases hle : lpsOf l (lo + 1) hi ≤ lpsOf l lo (hi - 1)
          · rw [max_eq_right hle]
            exact hB'
          · rw [max_eq_left (by omega)]
            exact hA'

  /-- A palindromic subsequence of size `m` bounds `lpsOf` from below (for a genuine
  interval, i.e. `hi < l.length`). -/
  theorem IsPalinIn.le_lpsOf {l : List U8} {lo hi m : Nat} (h : IsPalinIn l lo hi m)
      (h2 : hi < l.length) : m ≤ lpsOf l lo hi := by
    have H : ∀ d lo hi m, hi - lo = d → IsPalinIn l lo hi m → hi < l.length →
        m ≤ lpsOf l lo hi := by
      intro d
      induction d using Nat.strong_induction_on with
      | _ d ih =>
        intro lo hi m hd hwit h2
        by_cases hle : lo ≤ hi
        · rw [lpsOf]
          rw [dif_pos (show lo ≤ hi ∧ hi < l.length from ⟨hle, h2⟩)]
          by_cases hEq : lo = hi
          · rw [if_pos hEq]
            obtain ⟨p, hb, hmono, hp⟩ := hwit
            have hb1 : ∀ x, x < m → lo ≤ p x := fun x hx => (hb x hx).1
            have hb2 : ∀ x, x < m → p x ≤ hi := fun x hx => (hb x hx).2
            have hr := lt_of_strictMono_range hb1 hb2 hmono
            omega
          · rw [if_neg hEq]
            by_cases hEnds : l[lo]? = l[hi]?
            · rw [if_pos hEnds]
              obtain ⟨p, hb, hmono, hp⟩ := hwit
              rcases Nat.lt_or_ge m 2 with hm2 | hm2
              · omega
              · have hinner : IsPalinIn l (lo + 1) (hi - 1) (m - 2) := by
                  refine ⟨fun x => p (x + 1), ?_, ?_, ?_⟩
                  · intro x hx
                    show lo + 1 ≤ p (x + 1) ∧ p (x + 1) ≤ hi - 1
                    have hA : lo ≤ p 0 := (hb 0 (by omega)).1
                    have hB : p 0 < p (x + 1) := hmono 0 (x + 1) (by omega) (by omega)
                    have hC : p (x + 1) < p (m - 1) := hmono (x + 1) (m - 1) (by omega) (by omega)
                    have hD : p (m - 1) ≤ hi := (hb (m - 1) (by omega)).2
                    omega
                  · intro x y hx hy
                    exact hmono (x + 1) (y + 1) (by omega) (by omega)
                  · intro x hx
                    show l[p (x + 1)]? = l[p ((m - 2) - 1 - x + 1)]?
                    have h1 := hp (x + 1) (by omega)
                    have hidx : (m - 2) - 1 - x + 1 = m - 1 - (x + 1) := by omega
                    rw [hidx]
                    exact h1
                have hrec := ih ((hi - 1) - (lo + 1)) (by omega) (lo + 1) (hi - 1) (m - 2)
                  rfl hinner (by omega)
                omega
            · rw [if_neg hEnds]
              obtain ⟨p, hb, hmono, hp⟩ := hwit
              rcases Nat.eq_zero_or_pos m with hm0 | hmpos
              · omega
              · by_cases h0 : p 0 = lo
                · by_cases hlast : p (m - 1) = hi
                  · exfalso
                    have heq0 := hp 0 (by omega)
                    have hidx : m - 1 - 0 = m - 1 := by omega
                    rw [hidx, h0, hlast] at heq0
                    exact hEnds heq0
                  · have hB : IsPalinIn l lo (hi - 1) m := by
                      refine ⟨p, ?_, hmono, hp⟩
                      intro x hx
                      refine ⟨(hb x hx).1, ?_⟩
                      have hlastle : p (m - 1) ≤ hi := (hb (m - 1) (by omega)).2
                      have hpx : p x ≤ p (m - 1) := by
                        rcases Nat.lt_or_eq_of_le (show x ≤ m - 1 by omega) with hlt' | heq'
                        · exact Nat.le_of_lt (hmono x (m - 1) hlt' (by omega))
                        · rw [heq']
                      omega
                    have hrec := ih ((hi - 1) - lo) (by omega) lo (hi - 1) m rfl hB (by omega)
                    exact le_trans hrec (le_max_right _ _)
                · have hA : IsPalinIn l (lo + 1) hi m := by
                    refine ⟨p, ?_, hmono, hp⟩
                    intro x hx
                    refine ⟨?_, (hb x hx).2⟩
                    show lo + 1 ≤ p x
                    have h0le : lo ≤ p 0 := (hb 0 (by omega)).1
                    have h0ne : p 0 ≠ lo := h0
                    rcases Nat.eq_zero_or_pos x with hx0 | hxpos
                    · subst hx0
                      omega
                    · have hstep := hmono 0 x hxpos hx
                      omega
                  have hrec := ih (hi - (lo + 1)) (by omega) (lo + 1) hi m rfl hA h2
                  exact le_trans hrec (le_max_left _ _)
        · rw [lpsOf]
          rw [dif_neg (show ¬ (lo ≤ hi ∧ hi < l.length) by omega)]
          obtain ⟨p, hb, hmono, hp⟩ := hwit
          have hm0 : m = 0 := by
            by_contra hne
            have h1 := (hb 0 (by omega)).1
            have h1b := (hb 0 (by omega)).2
            omega
          omega
    exact H _ lo hi m rfl h h2

  /-- `lpsOf` is attained. -/
  theorem IsPalinIn.lpsOf {l : List U8} {lo hi : Nat} (h1 : lo ≤ hi) (h2 : hi < l.length) :
      IsPalinIn l lo hi (lpsOf l lo hi) := by
    exact mA_lpsOf_attained h1 h2

  /-- The DP value plus the longest palindromic subsequence length is the interval length. -/
  theorem dpv_add_lpsOf {l : List U8} {lo hi : Nat} (h1 : lo ≤ hi) (h2 : hi < l.length) :
      dpv l lo hi + lpsOf l lo hi = hi - lo + 1 := by
    suffices H : ∀ d lo hi, hi - lo = d → lo ≤ hi → hi < l.length →
        dpv l lo hi + lpsOf l lo hi = hi - lo + 1 from H _ lo hi rfl h1 h2
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro lo hi hd h1 h2
      rw [dpv, lpsOf]
      rw [dif_pos (show lo ≤ hi ∧ hi < l.length from ⟨h1, h2⟩)]
      rw [dif_pos (show lo ≤ hi ∧ hi < l.length from ⟨h1, h2⟩)]
      by_cases hEq : lo = hi
      · simp only [if_pos hEq]
        omega
      · simp only [if_neg hEq]
        by_cases hEnds : l[lo]? = l[hi]?
        · simp only [if_pos hEnds]
          by_cases hin : lo + 1 ≤ hi - 1 ∧ hi - 1 < l.length
          · have hrec := ih _ (by omega) (lo + 1) (hi - 1) rfl hin.1 hin.2
            omega
          · have hp0 : dpv l (lo + 1) (hi - 1) = 0 := by
              rw [dpv]; rw [dif_neg hin]
            have hq0 : lpsOf l (lo + 1) (hi - 1) = 0 := by
              rw [lpsOf]; rw [dif_neg hin]
            rw [hp0, hq0]
            omega
        · simp only [if_neg hEnds]
          have hA : dpv l (lo + 1) hi + lpsOf l (lo + 1) hi = hi - (lo + 1) + 1 :=
            ih _ (by omega) (lo + 1) hi rfl (by omega) h2
          have hB : dpv l lo (hi - 1) + lpsOf l lo (hi - 1) = hi - 1 - lo + 1 :=
            ih _ (by omega) lo (hi - 1) rfl (by omega) (by omega)
          have hA' : dpv l (lo + 1) hi + lpsOf l (lo + 1) hi = hi - lo := by omega
          have hB' : dpv l lo (hi - 1) + lpsOf l lo (hi - 1) = hi - lo := by omega
          have key := mA_minmax_key (a := dpv l (lo + 1) hi) (b := dpv l lo (hi - 1))
            (c := lpsOf l (lo + 1) hi) (d := lpsOf l lo (hi - 1)) (K := hi - lo) hA' hB'
          exact key

  /-- `isCommonSubseqSize` is the same as a common subsequence with the reversal. -/
  theorem isCommonSubseqSize_iff_IsCSS (s : List U8) (m : Nat) :
      isCommonSubseqSize s m ↔ IsCSS s s.reverse m := by
    constructor
    · rintro ⟨i, j, h1, h2, h3, h4, h5⟩
      refine ⟨i, j, h1, h2, ?_, ?_, ?_⟩
      · intro x hx
        simpa using h3 x hx
      · intro x y hxy hy
        exact h4 x y hxy hy
      · intro x hx
        have hlt : j x < s.length := h3 x hx
        rw [List.getElem?_reverse (by simpa using hlt)]
        exact h5 x hx
    · rintro ⟨i, j, h1, h2, h3, h4, h5⟩
      refine ⟨i, j, h1, h2, ?_, ?_, ?_⟩
      · intro x hx
        simpa using h3 x hx
      · intro x y hxy hy
        exact h4 x y hxy hy
      · intro x hx
        have hlt : j x < s.length := by simpa using h3 x hx
        rw [← List.getElem?_reverse hlt]
        exact h5 x hx

  /-- Subtracting a larger index from the same number gives a smaller value. -/
  theorem mB_sub_lt_sub_left {a u v : Nat} (h1 : u < v) (h2 : v ≤ a) : a - v < a - u :=
    Nat.sub_lt_sub_left (k := u) (m := a) (n := v) (by omega) h1

  /-- A palindromic subsequence of the whole list is a common subsequence with the
  reversal (for a nonempty list; for the empty list both `IsPalinIn [] 0 0 m` and
  `IsCSS [] [] m` degenerate at `m ≤ 1`). -/
  theorem IsCSS.of_isPalinIn {l : List U8} {m : Nat} (hne : 1 ≤ l.length)
      (h : IsPalinIn l 0 (l.length - 1) m) : IsCSS l l.reverse m := by
    obtain ⟨p, hb, hmono, hpal⟩ := h
    refine ⟨p, fun x => l.length - 1 - p (m - 1 - x), ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      have h1 := (hb x hx).2
      omega
    · intro x y hxy hy
      exact hmono x y hxy hy
    · intro x hx
      have h1 : p (m - 1 - x) < l.length := by
        have h2 := hb (m - 1 - x) (by omega)
        omega
      rw [List.length_reverse]
      dsimp only
      omega
    · intro x y hxy hy
      have h2 : m - 1 - x < m := by omega
      have h1 : m - 1 - y < m - 1 - x := by omega
      have h3 : p (m - 1 - y) < p (m - 1 - x) := hmono (m - 1 - y) (m - 1 - x) h1 h2
      have h4 : p (m - 1 - x) < l.length := by
        have h5 := hb (m - 1 - x) h2
        omega
      show l.length - 1 - p (m - 1 - x) < l.length - 1 - p (m - 1 - y)
      omega
    · intro x hx
      have hlt : l.length - 1 - p (m - 1 - x) < l.length := by
        have h1 := hb (m - 1 - x) (by omega)
        omega
      show l[p x]? = l.reverse[l.length - 1 - p (m - 1 - x)]?
      rw [List.getElem?_reverse (l := l) hlt]
      have hsub : l.length - 1 - (l.length - 1 - p (m - 1 - x)) = p (m - 1 - x) := by
        have h1 := hb (m - 1 - x) (by omega)
        omega
      rw [hsub]
      exact hpal x hx

  /-- A common subsequence with the reversal yields an aligned family. -/
  theorem IsFamily.of_IsCSS {l : List U8} {m : Nat} (h : IsCSS l l.reverse m) :
      IsFamily l 0 (l.length - 1) m := by
    obtain ⟨i, j, h1, h2, h3, h4, h5⟩ := h
    refine ⟨i, fun x => l.length - 1 - j x, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      have := h1 x hx
      omega
    · intro x y hxy hy
      exact h2 x y hxy hy
    · intro x hx
      have hb := h3 x hx
      rw [List.length_reverse] at hb
      show 0 ≤ l.length - 1 - j x ∧ l.length - 1 - j x ≤ l.length - 1
      omega
    · intro x y hxy hy
      have hb : j x < j y := h4 x y hxy hy
      have hc : 1 + j y ≤ l.length := by
        have h0 := h3 y hy
        rw [List.length_reverse] at h0
        omega
      have hh : l.length - (1 + j y) < l.length - (1 + j x) :=
        Nat.sub_lt_sub_left (m := l.length) (by omega) (by omega)
      simpa [Nat.sub_sub] using hh
    · intro x hx
      have hlt : j x < l.reverse.length := h3 x hx
      show l[i x]? = l[l.length - 1 - j x]?
      rw [← List.getElem?_reverse (l := l) (by simpa using hlt)]
      exact h5 x hx

  /-- Construction (a): if `i t < k t` for all `t < s`, the nested pairs
  `i_0,…,i_(s-1),k_(s-1),…,k_0` form an increasing palindromic index sequence of length `2*s`. -/
  lemma mA_palin_left {l : List U8} {lo hi m s : Nat} {i k : Nat → Nat}
      (hi_b : ∀ x, x < m → lo ≤ i x ∧ i x ≤ hi)
      (hi_mono : ∀ x y, x < y → y < m → i x < i y)
      (hk_b : ∀ x, x < m → lo ≤ k x ∧ k x ≤ hi)
      (hk_mono : ∀ x y, x < y → y < m → k y < k x)
      (heq : ∀ x, x < m → l[i x]? = l[k x]?)
      (hs : s ≤ m) (hall : ∀ t, t < s → i t < k t) :
      IsPalinIn l lo hi (2 * s) := by
    set p : Nat → Nat :=
      fun x => if x < s then i x else k (2 * s - 1 - x) with hp
    have hpL : ∀ x, x < s → p x = i x := by
      intro x hx
      simp only [hp, if_pos hx]
    have hpG : ∀ x, ¬ x < s → p x = k (2 * s - 1 - x) := by
      intro x hx
      simp only [hp, if_neg hx]
    refine ⟨p, ?_, ?_, ?_⟩
    · intro x hx
      by_cases hxs : x < s
      · rw [hpL x hxs]
        exact hi_b x (by omega)
      · rw [hpG x hxs]
        exact hk_b _ (by omega)
    · intro x y hxy hy
      by_cases hxs : x < s
      · by_cases hys : y < s
        · rw [hpL x hxs, hpL y hys]
          exact hi_mono x y hxy (by omega)
        · rw [hpL x hxs, hpG y hys]
          have h1 : i x ≤ i (s - 1) := by
            rcases Nat.eq_or_lt_of_le (by omega : x ≤ s - 1) with h | h
            · rw [h]
            · exact Nat.le_of_lt (hi_mono x (s - 1) h (by omega))
          have h2 : i (s - 1) < k (s - 1) := hall (s - 1) (by omega)
          have h3 : k (s - 1) ≤ k (2 * s - 1 - y) := by
            rcases Nat.lt_or_ge (2 * s - 1 - y) (s - 1) with h | h
            · exact Nat.le_of_lt (hk_mono (2 * s - 1 - y) (s - 1) h (by omega))
            · rw [show 2 * s - 1 - y = s - 1 from by omega]
          omega
      · rw [hpG x hxs, hpG y (by omega)]
        exact hk_mono (2 * s - 1 - y) (2 * s - 1 - x) (by omega) (by omega)
    · intro x hx
      by_cases hxs : x < s
      · rw [hpL x hxs, hpG (2 * s - 1 - x) (by omega)]
        rw [show 2 * s - 1 - (2 * s - 1 - x) = x from by omega]
        exact heq x (by omega)
      · rw [hpG x hxs, hpL (2 * s - 1 - x) (by omega)]
        exact (heq (2 * s - 1 - x) (by omega)).symm

  /-- Construction (b), strict case: if `k s < i s`, the crossed pairs
  `k_(m-1),…,k_s,i_s,…,i_(m-1)` form an increasing palindromic index sequence of length
  `2*(m-s)`. -/
  lemma mA_palin_right {l : List U8} {lo hi m s : Nat} {i k : Nat → Nat}
      (hi_b : ∀ x, x < m → lo ≤ i x ∧ i x ≤ hi)
      (hi_mono : ∀ x y, x < y → y < m → i x < i y)
      (hk_b : ∀ x, x < m → lo ≤ k x ∧ k x ≤ hi)
      (hk_mono : ∀ x y, x < y → y < m → k y < k x)
      (heq : ∀ x, x < m → l[i x]? = l[k x]?)
      (hsm : s < m) (hjun : k s < i s) :
      IsPalinIn l lo hi (2 * (m - s)) := by
    set p : Nat → Nat :=
      fun x => if x < m - s then k (m - 1 - x) else i (s + (x - (m - s))) with hp
    have hpL : ∀ x, x < m - s → p x = k (m - 1 - x) := by
      intro x hx
      simp only [hp, if_pos hx]
    have hpG : ∀ x, ¬ x < m - s → p x = i (s + (x - (m - s))) := by
      intro x hx
      simp only [hp, if_neg hx]
    have hks_le : ∀ x, x < m - s → k (m - 1 - x) ≤ k s := by
      intro x hx
      rcases Nat.eq_or_lt_of_le (by omega : s ≤ m - 1 - x) with h | h
      · rw [← h]
      · exact Nat.le_of_lt (hk_mono s (m - 1 - x) h (by omega))
    have his_le : ∀ x, ¬ x < m - s → x < 2 * (m - s) → i s ≤ i (s + (x - (m - s))) := by
      intro x hx hx2
      rcases Nat.eq_or_lt_of_le (by omega : s ≤ s + (x - (m - s))) with h | h
      · rw [← h]
      · exact Nat.le_of_lt (hi_mono s _ h (by omega))
    refine ⟨p, ?_, ?_, ?_⟩
    · intro x hx
      by_cases hxs : x < m - s
      · rw [hpL x hxs]
        exact hk_b _ (by omega)
      · rw [hpG x hxs]
        exact hi_b _ (by omega)
    · intro x y hxy hy
      by_cases hxs : x < m - s
      · by_cases hys : y < m - s
        · rw [hpL x hxs, hpL y hys]
          exact hk_mono (m - 1 - y) (m - 1 - x) (by omega) (by omega)
        · rw [hpL x hxs, hpG y hys]
          have h1 := hks_le x hxs
          have h2 := his_le y hys hy
          omega
      · rw [hpG x hxs, hpG y (by omega)]
        exact hi_mono _ _ (by omega) (by omega)
    · intro x hx
      by_cases hxs : x < m - s
      · rw [hpL x hxs, hpG (2 * (m - s) - 1 - x) (by omega)]
        rw [show s + (2 * (m - s) - 1 - x - (m - s)) = m - 1 - x from by omega]
        exact (heq (m - 1 - x) (by omega)).symm
      · rw [hpG x hxs, hpL (2 * (m - s) - 1 - x) (by omega)]
        rw [show m - 1 - (2 * (m - s) - 1 - x) = s + (x - (m - s)) from by omega]
        exact heq _ (by omega)

  /-- Construction (b), equality case: if `k s = i s`, the crossed pairs with `i s` as the
  centre form an increasing palindromic index sequence of length `2*(m-s)-1`. -/
  lemma mA_palin_center {l : List U8} {lo hi m s : Nat} {i k : Nat → Nat}
      (hi_b : ∀ x, x < m → lo ≤ i x ∧ i x ≤ hi)
      (hi_mono : ∀ x y, x < y → y < m → i x < i y)
      (hk_b : ∀ x, x < m → lo ≤ k x ∧ k x ≤ hi)
      (hk_mono : ∀ x y, x < y → y < m → k y < k x)
      (heq : ∀ x, x < m → l[i x]? = l[k x]?)
      (hsm : s < m) (heqs : k s = i s) :
      IsPalinIn l lo hi (2 * (m - s) - 1) := by
    set p : Nat → Nat :=
      fun x => if x < m - s - 1 then k (m - 1 - x) else i (s + (x - (m - s - 1))) with hp
    have hpL : ∀ x, x < m - s - 1 → p x = k (m - 1 - x) := by
      intro x hx
      simp only [hp, if_pos hx]
    have hpG : ∀ x, ¬ x < m - s - 1 → p x = i (s + (x - (m - s - 1))) := by
      intro x hx
      simp only [hp, if_neg hx]
    have hks_le : ∀ x, x < m - s - 1 → k (m - 1 - x) < i s := by
      intro x hx
      have h1 : k (m - 1 - x) < k s := hk_mono s (m - 1 - x) (by omega) (by omega)
      rw [heqs] at h1
      exact h1
    have his_le : ∀ x, ¬ x < m - s - 1 → x < 2 * (m - s) - 1 →
        i s ≤ i (s + (x - (m - s - 1))) := by
      intro x hx hx2
      rcases Nat.eq_or_lt_of_le (by omega : s ≤ s + (x - (m - s - 1))) with h | h
      · rw [← h]
      · exact Nat.le_of_lt (hi_mono s _ h (by omega))
    refine ⟨p, ?_, ?_, ?_⟩
    · intro x hx
      by_cases hxs : x < m - s - 1
      · rw [hpL x hxs]
        exact hk_b _ (by omega)
      · rw [hpG x hxs]
        exact hi_b _ (by omega)
    · intro x y hxy hy
      by_cases hxs : x < m - s - 1
      · by_cases hys : y < m - s - 1
        · rw [hpL x hxs, hpL y hys]
          exact hk_mono (m - 1 - y) (m - 1 - x) (by omega) (by omega)
        · rw [hpL x hxs, hpG y hys]
          have h1 := hks_le x hxs
          have h2 := his_le y hys hy
          omega
      · rw [hpG x hxs, hpG y (by omega)]
        exact hi_mono _ _ (by omega) (by omega)
    · intro x hx
      by_cases hxs : x < m - s - 1
      · rw [hpL x hxs, hpG (2 * (m - s) - 1 - 1 - x) (by omega)]
        rw [show s + (2 * (m - s) - 1 - 1 - x - (m - s - 1)) = m - 1 - x from by omega]
        exact (heq (m - 1 - x) (by omega)).symm
      · rcases Nat.eq_or_lt_of_le (by omega : m - s - 1 ≤ x) with heq' | hgt
        · have hy : 2 * (m - s) - 1 - 1 - x = x := by omega
          rw [hy]
        · rw [hpG x hxs, hpL (2 * (m - s) - 1 - 1 - x) (by omega)]
          rw [show m - 1 - (2 * (m - s) - 1 - 1 - x) = s + (x - (m - s - 1)) from by omega]
          exact heq _ (by omega)

  /-- A long enough palindromic index sequence is a subsequence of an aligned family. -/
  theorem IsFamily.to_isPalinIn {l : List U8} {lo hi m : Nat} (h : IsFamily l lo hi m) :
      ∃ M, m ≤ M ∧ IsPalinIn l lo hi M := by
    obtain ⟨i, k, hi_b, hi_mono, hk_b, hk_mono, heq⟩ := h
    -- there is a threshold `s`: nested for `t < s`, crossed from `s` on
    have key : ∃ s : Nat, (∀ t, t < s → i t < k t) ∧ s ≤ m ∧
        (∀ t, s ≤ t → t < m → k t ≤ i t) := by
      by_cases hex : ∃ t, t < m ∧ k t ≤ i t
      · refine ⟨Nat.find hex, ?_, ?_, ?_⟩
        · intro t ht
          have hspec := Nat.find_spec hex
          by_contra hcon
          have hmem : t < m ∧ k t ≤ i t := ⟨by omega, Nat.le_of_not_lt hcon⟩
          have := Nat.find_min' hex hmem
          omega
        · have := (Nat.find_spec hex).1
          omega
        · intro t hst htm
          rcases Nat.eq_or_lt_of_le hst with hh | hh
          · rw [← hh]
            exact (Nat.find_spec hex).2
          · have h1 : k t < k (Nat.find hex) := hk_mono _ t hh htm
            have h2 : i (Nat.find hex) < i t := hi_mono _ t hh htm
            have h3 := (Nat.find_spec hex).2
            exact le_of_lt (lt_trans h1 (lt_of_le_of_lt h3 h2))
      · push_neg at hex
        refine ⟨m, fun t ht => ?_, le_refl m, fun t hst htm => by omega⟩
        have := hex t (by omega)
        omega
    obtain ⟨s, hall, hsle, hcross⟩ := key
    by_cases hbig : m ≤ 2 * s
    · exact ⟨2 * s, hbig, mA_palin_left hi_b hi_mono hk_b hk_mono heq hsle hall⟩
    · have hslt : s < m := by omega
      rcases Nat.lt_or_ge (k s) (i s) with hjun | hge
      · exact ⟨2 * (m - s), by omega,
          mA_palin_right hi_b hi_mono hk_b hk_mono heq hslt hjun⟩
      · have heqs : k s = i s := le_antisymm (hcross s le_rfl hslt) hge
        exact ⟨2 * (m - s) - 1, by omega,
          mA_palin_center hi_b hi_mono hk_b hk_mono heq hslt heqs⟩

  /-! ### Specifications -/

  /-- **S1 (main, functional).** When `min_insertions s` returns `r`, `r` is the least
  nonnegative `k` such that `s` can be extended to a palindrome by inserting `k` bytes. -/
  theorem spec_S1 (s : Slice U8)
      (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 500)
      (hlower : ∀ (i : Nat), (hi : i < s.val.length) → isLowerAscii (s.val[i])) :
      ∀ r, Aegis.MinInsertions.min_insertions s = ok r →
        0 ≤ r.val ∧
          hasPalindromicSupersequence s.val r.val.toNat ∧
            (∀ k, hasPalindromicSupersequence s.val k → r.val.toNat ≤ k) := by
    sorry

  /-- **S2 (no failure).** `min_insertions` never fails on a nonempty lowercase input. -/
  theorem spec_S2 (s : Slice U8)
      (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 500)
      (hlower : ∀ (i : Nat), (hi : i < s.val.length) → isLowerAscii (s.val[i])) :
      ∃ r, Aegis.MinInsertions.min_insertions s = ok r := by
    sorry

  /-- **S3 (bounds).** The returned number of insertions lies in `[0, len(s) - 1]`. -/
  theorem spec_S3 (s : Slice U8)
      (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 500)
      (hlower : ∀ (i : Nat), (hi : i < s.val.length) → isLowerAscii (s.val[i])) :
      ∀ r, Aegis.MinInsertions.min_insertions s = ok r →
        0 ≤ r.val ∧ r.val ≤ (s.val.length : Int) - 1 := by
    sorry

  /-- **S4 (edge case).** The result is `0` exactly when `s` is already a palindrome. -/
  theorem spec_S4 (s : Slice U8)
      (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 500)
      (hlower : ∀ (i : Nat), (hi : i < s.val.length) → isLowerAscii (s.val[i])) :
      ∀ r, Aegis.MinInsertions.min_insertions s = ok r → (r.val = 0 ↔ isPalindrome s.val) := by
    sorry

  /-- **S5 (relational, longest palindromic subsequence).** `r = len(s) - L` where `L` is the
  length of the longest palindromic subsequence of `s`. -/
  theorem spec_S5 (s : Slice U8)
      (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 500)
      (hlower : ∀ (i : Nat), (hi : i < s.val.length) → isLowerAscii (s.val[i])) :
      ∀ r, Aegis.MinInsertions.min_insertions s = ok r →
        ∃ L : Nat,
          isPalindromicSubseqSize s.val L ∧
            (∀ m, isPalindromicSubseqSize s.val m → m ≤ L) ∧
              r.val = (s.val.length : Int) - (L : Int) := by
    sorry

  /-- **S8 (invariance under reversal).** Reversing the input leaves the answer unchanged. -/
  theorem spec_S8 (s t : Slice U8)
      (hs_lower : 1 ≤ s.val.length) (hs_upper : s.val.length ≤ 500)
      (ht_lower : 1 ≤ t.val.length) (ht_upper : t.val.length ≤ 500)
      (hlen : t.val.length = s.val.length)
      (hlower_s : ∀ (i : Nat), (hi : i < s.val.length) → isLowerAscii (s.val[i]))
      (hlower_t : ∀ (i : Nat), (hi : i < t.val.length) → isLowerAscii (t.val[i]))
      (hrev : ∀ (i : Nat), (hi : i < s.val.length) →
        t.val[i] = s.val[s.val.length - 1 - i]) :
      ∀ r q, Aegis.MinInsertions.min_insertions s = ok r →
        Aegis.MinInsertions.min_insertions t = ok q → r = q := by
    sorry

  /-- **S10 (relational, trimming equal ends).** If the first and last bytes of `s` agree, then
  the answer for `s` equals the answer for the inner slice `u` of length `len(s) - 2` with
  `u[i] = s[i+1]`. -/
  theorem spec_S10 (s u : Slice U8)
      (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 500)
      (hlower : ∀ (i : Nat), (hi : i < s.val.length) → isLowerAscii (s.val[i]))
      (hlen3 : 3 ≤ s.val.length)
      (hends : s.val[0] = s.val[s.val.length - 1])
      (hu_len : u.val.length = s.val.length - 2)
      (hu_val : ∀ (i : Nat), (hi : i < u.val.length) → u.val[i] = s.val[i + 1]) :
      ∀ r q, Aegis.MinInsertions.min_insertions s = ok r →
        Aegis.MinInsertions.min_insertions u = ok q → r = q := by
    sorry

  /-- **S11 (relational, unequal ends).** If the first and last bytes of `s` differ, then
  `r = 1 + min (answer for s[1..]) (answer for s[..len(s)-1])`, where `a` is the slice of length
  `len(s) - 1` with `a[i] = s[i+1]` and `b` is the slice of length `len(s) - 1` with
  `b[i] = s[i]`. -/
  theorem spec_S11 (s a b : Slice U8)
      (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 500)
      (hlower : ∀ (i : Nat), (hi : i < s.val.length) → isLowerAscii (s.val[i]))
      (hlen2 : 2 ≤ s.val.length)
      (hne : s.val[0] ≠ s.val[s.val.length - 1])
      (ha_len : a.val.length = s.val.length - 1)
      (ha_val : ∀ (i : Nat), (hi : i < a.val.length) → a.val[i] = s.val[i + 1])
      (hb_len : b.val.length = s.val.length - 1)
      (hb_val : ∀ (i : Nat), (hi : i < b.val.length) → b.val[i] = s.val[i]) :
      ∀ r ra rb, Aegis.MinInsertions.min_insertions s = ok r →
        Aegis.MinInsertions.min_insertions a = ok ra →
          Aegis.MinInsertions.min_insertions b = ok rb → r.val = 1 + min ra.val rb.val := by
    sorry

  /-- Placeholder so the template has a declared theorem; the draft adds the specifications. -/
  theorem draft_placeholder : True := by
    sorry

  /-! ### Sanity checks for the helper notions (not part of the specification) -/

  example : isPalindrome [97#u8, 98#u8, 97#u8] := by
    intro j hj
    simp only [List.length_cons, List.length_nil] at hj
    match j with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | n + 3 => omega

  example : ¬ isPalindrome [97#u8, 98#u8] := by
    intro h
    have h0 := h 0 (by simp)
    simp at h0

  /-! ### Program-level proof machinery for `min_insertions` -/

  /-- The `Int` value of the entry `b` of one DP row. -/
  def entRow (r : alloc.vec.Vec Std.I64) (b : Nat) : Int :=
    ((r.val[b]?).map (fun x => x.val)).getD 0

  /-- The `Int` value of the DP-table entry `(a,b)`. -/
  def ent (dp : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (a b : Nat) : Int :=
    ((dp.val[a]?).map (fun r => entRow r b)).getD 0

  /-- The DP table has `n` rows, each of length `n`. -/
  def dimsOK (dp : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (n : Nat) : Prop :=
    dp.val.length = n ∧ ∀ row ∈ dp.val, row.val.length = n

  /-- Expected value of the entry `(a,b)` inside the inner loop of `min_insertions`:
  entries of length `< len` are already computed, and among those of length exactly `len`
  the ones starting before `start`. -/
  def cell (l : List U8) (n len start : Nat) (a b : Nat) : Int :=
    if a ≤ b ∧ b < n ∧ (b - a + 1 < len ∨ (b - a + 1 = len ∧ a < start)) then
      (dpv l a b : Int)
    else 0

  /-- Expected table contents after the inner loop with parameter `len`. -/
  def cellAfter (l : List U8) (n len : Nat) (a b : Nat) : Int :=
    if a ≤ b ∧ b < n ∧ b - a + 1 ≤ len then (dpv l a b : Int) else 0

  /-- Invariant of the inner loop of `min_insertions`. -/
  def InvIn (l : List U8) (n len start : Nat)
      (dp : alloc.vec.Vec (alloc.vec.Vec Std.I64)) : Prop :=
    dimsOK dp n ∧ ∀ a b, ent dp a b = cell l n len start a b

  /-- Invariant of the outer loop of `min_insertions`. -/
  def InvOut (l : List U8) (n len : Nat)
      (dp : alloc.vec.Vec (alloc.vec.Vec Std.I64)) : Prop :=
    dimsOK dp n ∧ ∀ a b, ent dp a b = cell l n len 0 a b

  /-- Postcondition of the inner loop. -/
  def InvLen (l : List U8) (n len : Nat)
      (dp : alloc.vec.Vec (alloc.vec.Vec Std.I64)) : Prop :=
    dimsOK dp n ∧ ∀ a b, ent dp a b = cellAfter l n len a b

  /-- Postcondition of the outer loop. -/
  def InvDone (l : List U8) (n : Nat)
      (dp : alloc.vec.Vec (alloc.vec.Vec Std.I64)) : Prop :=
    dimsOK dp n ∧ ∀ a b, a ≤ b → b < n → ent dp a b = (dpv l a b : Int)

  theorem entRow_eq (r : alloc.vec.Vec Std.I64) (b : Nat) (v : I64)
      (h : r.val[b]? = some v) : entRow r b = v.val := by
    simp [entRow, h]

  theorem ent_eq (dp : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (a b : Nat)
      (r : alloc.vec.Vec Std.I64) (h : dp.val[a]? = some r) : ent dp a b = entRow r b := by
    simp [ent, h]

  theorem dimsOK_length {dp : alloc.vec.Vec (alloc.vec.Vec Std.I64)} {n : Nat}
      (h : dimsOK dp n) : dp.val.length = n := h.1

  theorem dimsOK_row_length {dp : alloc.vec.Vec (alloc.vec.Vec Std.I64)} {n : Nat}
      (h : dimsOK dp n) (i : Nat) (hi : i < dp.val.length) : (dp.val[i]).val.length = n :=
    h.2 _ (List.getElem_mem hi)

  theorem getElem?_set_of_lt {α : Type} (l : List α) (i : Nat) (a : α) (j : Nat)
      (hi : i < l.length) : (l.set i a)[j]? = if j = i then some a else l[j]? := by
    rw [List.getElem?_set]
    by_cases h : j = i
    · subst h; simp [hi]
    · rw [if_neg (fun hh => h hh.symm)]
      simp [h]

  theorem dimsOK_set {dp : alloc.vec.Vec (alloc.vec.Vec Std.I64)} {n : Nat}
      (h : dimsOK dp n) (i : Usize) (r : alloc.vec.Vec Std.I64) (hr : r.val.length = n) :
      dimsOK (dp.set i r) n := by
    obtain ⟨h1, h2⟩ := h
    refine ⟨by simp [alloc.vec.Vec.set_val_eq, h1], ?_⟩
    intro row hrow
    have hmem : row ∈ dp.val.set i.val r := by simpa [alloc.vec.Vec.set_val_eq] using hrow
    rcases List.mem_or_eq_of_mem_set hmem with hmem | rfl
    · exact h2 _ hmem
    · exact hr

  theorem entRow_set (r : alloc.vec.Vec Std.I64) (j : Usize) (v : I64) (b : Nat)
      (hj : j.val < r.val.length) :
      entRow (r.set j v) b = if b = j.val then v.val else entRow r b := by
    simp only [entRow, alloc.vec.Vec.set_val_eq, getElem?_set_of_lt _ _ _ _ hj]
    by_cases hb : b = j.val <;> simp [hb]

  theorem ent_set_entry (dp : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (row : alloc.vec.Vec Std.I64) (i j : Usize) (v : I64) (a b : Nat)
      (hi : dp.val[i.val]? = some row) (hj : j.val < row.val.length) :
      ent (dp.set i (row.set j v)) a b
        = if a = i.val ∧ b = j.val then v.val else ent dp a b := by
    have hlt : i.val < dp.val.length := by
      by_contra hc
      rw [List.getElem?_eq_none (by omega)] at hi
      exact absurd hi.symm (by simp)
    have hset : (dp.set i (row.set j v)).val = dp.val.set i.val (row.set j v) :=
      alloc.vec.Vec.set_val_eq ..
    unfold ent
    rw [hset]
    rw [getElem?_set_of_lt _ _ _ _ hlt]
    by_cases ha : a = i.val
    · subst ha
      rw [if_pos rfl, hi]
      simp only [Option.map_some]
      rw [entRow_set row j v b hj]
      by_cases hb : b = j.val <;> simp [hb]
    · rw [if_neg (fun hh => ha hh), if_neg (fun hh => ha hh.1)]

  /-- `bind` distributes over `if`. -/
  theorem bind_ite_b {α β : Type} (c : Prop) [Decidable c] (a b : Result α)
      (k : α → Result β) :
      Std.bind (if c then a else b) k =
        (if c then Std.bind a k else Std.bind b k) := by
    by_cases h : c <;> simp [h]

  /-- `Prod.casesOn` on a variable pair. -/
  theorem prod_cases_eq {α β γ : Type} (x : α × β) (f : α → β → γ) :
      Prod.casesOn x f = f x.1 x.2 := by
    obtain ⟨a, b⟩ := x
    rfl

  /-- Repeatedly apply `step`, splitting `if`s and `match`es (also under `bind`s). -/
  macro "step_auto" : tactic =>
    `(tactic| (repeat' (first
        | step
        | (spec_split as h)
        | (rw [bind_ite_b])
        | (simp only [prod_cases_eq]))))

  /-! #### Basic properties of `dpv` -/

  theorem dpv_invalid {l : List U8} {lo hi : Nat} (h : ¬(lo ≤ hi ∧ hi < l.length)) :
      dpv l lo hi = 0 := by
    rw [dpv]
    simp [h]

  theorem dpv_self (l : List U8) (a : Nat) : dpv l a a = 0 := by
    rw [dpv]
    by_cases h : a ≤ a ∧ a < l.length <;> simp [h]

  theorem dpv_end_eq {l : List U8} {lo hi : Nat} (h1 : lo < hi) (h2 : hi < l.length)
      (h3 : l[lo]? = l[hi]?) : dpv l lo hi = dpv l (lo + 1) (hi - 1) := by
    have h : lo ≤ hi ∧ hi < l.length := ⟨by omega, h2⟩
    rw [dpv, dif_pos h]
    rw [if_neg (by omega), if_pos h3]

  theorem dpv_end_ne {l : List U8} {lo hi : Nat} (h1 : lo < hi) (h2 : hi < l.length)
      (h3 : ¬ (l[lo]? = l[hi]?)) :
      dpv l lo hi = 1 + min (dpv l (lo + 1) hi) (dpv l lo (hi - 1)) := by
    have h : lo ≤ hi ∧ hi < l.length := ⟨by omega, h2⟩
    rw [dpv, dif_pos h]
    rw [if_neg (by omega), if_neg h3]

  theorem dpv_le {l : List U8} {lo hi : Nat} (h1 : lo ≤ hi) (h2 : hi < l.length) :
      dpv l lo hi ≤ hi - lo + 1 := by
    suffices key : ∀ d lo hi, hi - lo = d → lo ≤ hi → hi < l.length →
        dpv l lo hi ≤ hi - lo + 1 from key _ lo hi rfl h1 h2
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro lo hi hd h1 h2
      subst hd
      rw [dpv, dif_pos (show lo ≤ hi ∧ hi < l.length from ⟨h1, h2⟩)]
      by_cases heq : lo = hi
      · simp [heq]
      · rw [if_neg heq]
        by_cases hc : l[lo]? = l[hi]?
        · rw [if_pos hc]
          by_cases hlt : lo + 1 ≤ hi - 1
          · have h5 : hi - 1 < l.length := by omega
            have h6 : hi - 1 - (lo + 1) < hi - lo := by omega
            have := ih (hi - 1 - (lo + 1)) h6 (lo + 1) (hi - 1) rfl hlt h5
            omega
          · have hz : dpv l (lo + 1) (hi - 1) = 0 :=
              dpv_invalid (by omega)
            omega
        · rw [if_neg hc]
          have hA := ih (hi - (lo + 1)) (by omega) (lo + 1) hi rfl (by omega) h2
          have hB := ih (hi - 1 - lo) (by omega) lo (hi - 1) rfl (by omega) (by omega)
          omega

  /-! #### Basic properties of `cell` / `cellAfter` -/

  theorem cell_true {l : List U8} {n len start a b : Nat}
      (h : a ≤ b ∧ b < n ∧ (b - a + 1 < len ∨ (b - a + 1 = len ∧ a < start))) :
      cell l n len start a b = (dpv l a b : Int) := by
    unfold cell
    rw [if_pos h]

  theorem cell_false {l : List U8} {n len start a b : Nat}
      (h : ¬ (a ≤ b ∧ b < n ∧ (b - a + 1 < len ∨ (b - a + 1 = len ∧ a < start)))) :
      cell l n len start a b = 0 := by
    unfold cell
    rw [if_neg h]

  theorem cellAfter_true {l : List U8} {n len a b : Nat}
      (h : a ≤ b ∧ b < n ∧ b - a + 1 ≤ len) :
      cellAfter l n len a b = (dpv l a b : Int) := by
    unfold cellAfter
    rw [if_pos h]

  theorem cellAfter_false {l : List U8} {n len a b : Nat}
      (h : ¬ (a ≤ b ∧ b < n ∧ b - a + 1 ≤ len)) : cellAfter l n len a b = 0 := by
    unfold cellAfter
    rw [if_neg h]

  /-- The table is initially (before any inner loop) filled with `0`. -/
  theorem cell_two (l : List U8) (n a b : Nat) : cell l n 2 0 a b = 0 := by
    unfold cell
    by_cases h : a ≤ b ∧ b < n ∧ (b - a + 1 < 2 ∨ (b - a + 1 = 2 ∧ a < 0))
    · rw [if_pos h]
      obtain ⟨h1, -, h3 | ⟨h3, h4⟩⟩ := h
      · have hba : b = a := by omega
        subst hba
        simp [dpv_self]
      · omega
    · rw [if_neg h]

  /-- After the inner loop with parameter `len`, the outer invariant with `len+1` holds. -/
  theorem cell_succ (l : List U8) (n len a b : Nat) :
      cell l n (len + 1) 0 a b = cellAfter l n len a b := by
    unfold cell cellAfter
    by_cases h : a ≤ b ∧ b < n ∧ b - a + 1 ≤ len
    · rw [if_pos h]
      rw [if_pos (show a ≤ b ∧ b < n ∧
          (b - a + 1 < len + 1 ∨ (b - a + 1 = len + 1 ∧ a < 0)) from
        ⟨h.1, h.2.1, Or.inl (by omega)⟩)]
    · rw [if_neg h, if_neg]
      intro hh
      rcases hh with ⟨h1, h2, h3 | ⟨h3, h4⟩⟩
      · exact h ⟨h1, h2, by omega⟩
      · omega

  /-- Advancing `start` by one changes `cell` only at the cell that is being written. -/
  theorem cell_start_succ {l : List U8} {n len start a b : Nat}
      (h : a ≠ start ∨ b - a + 1 ≠ len) :
      cell l n len start a b = cell l n len (start + 1) a b := by
    unfold cell
    have hiff :
        (a ≤ b ∧ b < n ∧ (b - a + 1 < len ∨ (b - a + 1 = len ∧ a < start)))
          ↔ (a ≤ b ∧ b < n ∧ (b - a + 1 < len ∨ (b - a + 1 = len ∧ a < start + 1))) := by
      by_cases hl : b - a + 1 = len
      · have ha : a ≠ start := by
          rcases h with h | h
          · exact h
          · exact absurd hl h
        constructor <;> rintro ⟨h1, h2, h3 | ⟨h3, h4⟩⟩
        · exact absurd h3 (by omega)
        · exact ⟨h1, h2, Or.inr ⟨h3, by omega⟩⟩
        · exact absurd h3 (by omega)
        · exact ⟨h1, h2, Or.inr ⟨h3, by omega⟩⟩
      · constructor <;> rintro ⟨h1, h2, h3 | ⟨h3, h4⟩⟩
        · exact ⟨h1, h2, Or.inl h3⟩
        · exact absurd h3 hl
        · exact ⟨h1, h2, Or.inl h3⟩
        · exact absurd h3 hl
    by_cases hc : a ≤ b ∧ b < n ∧ (b - a + 1 < len ∨ (b - a + 1 = len ∧ a < start))
    · rw [if_pos hc, if_pos (hiff.mp hc)]
    · rw [if_neg hc, if_neg (fun hh => hc (hiff.mpr hh))]

  /-- `dpv` of a two-element interval with equal ends vanishes. -/
  theorem dpv_pair {l : List U8} {a : Nat} (h : a + 1 < l.length) (he : l[a]? = l[a + 1]?) :
      dpv l a (a + 1) = 0 := by
    have h1 : a < a + 1 := by omega
    have h2 : dpv l a (a + 1) = dpv l (a + 1) (a + 1 - 1) := dpv_end_eq h1 h he
    have h3 : dpv l (a + 1) (a + 1 - 1) = 0 := dpv_invalid (by omega)
    omega

  /-- The value `cell` assigns to the cell written by the inner loop. -/
  theorem cell_ends {l : List U8} {n len start : Nat} (hlen : 1 ≤ len) (h : start + len ≤ n) :
      cell l n len (start + 1) start (start + len - 1) = (dpv l start (start + len - 1) : Int) := by
    apply cell_true
    exact ⟨by omega, by omega, Or.inr ⟨by omega, by omega⟩⟩

  /-- A cell of length `< len` already holds its `dpv` value. -/
  theorem cell_of_lt {l : List U8} {n len start a b : Nat} (h1 : a ≤ b) (h2 : b < n)
      (h3 : b - a + 1 < len) : cell l n len start a b = (dpv l a b : Int) :=
    cell_true ⟨h1, h2, Or.inl h3⟩

  /-- The `ent` of the table is the value stored in the underlying list. -/
  theorem ent_getElem (dp : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (a b : Nat)
      (ha : a < dp.val.length) (hb : b < (dp.val[a]'ha).val.length) :
      ent dp a b = ((dp.val[a]'ha).val[b]'hb).val := by
    rw [ent_eq dp a b (dp.val[a]'ha) (List.getElem?_eq_getElem ha)]
    simp [entRow, List.getElem?_eq_getElem hb]

  /-- Outside the written cell, advancing `start` does not change `cell`. -/
  theorem cell_start_succ_of_ne {l : List U8} {n len start a b e : Nat}
      (he : e = start + len - 1) (h : ¬ (a = start ∧ b = e)) :
      cell l n len start a b = cell l n len (start + 1) a b := by
    rcases Nat.lt_or_ge b a with hlt | hge
    · have h1 : ¬ (a ≤ b ∧ b < n ∧
          (b - a + 1 < len ∨ (b - a + 1 = len ∧ a < start))) := by
        rintro ⟨h1, -⟩
        omega
      have h2 : ¬ (a ≤ b ∧ b < n ∧
          (b - a + 1 < len ∨ (b - a + 1 = len ∧ a < start + 1))) := by
        rintro ⟨h1, -⟩
        omega
      rw [cell_false h1, cell_false h2]
    · refine cell_start_succ ?_
      by_cases ha : a = start
      · refine Or.inr ?_
        intro hb
        exact h ⟨ha, by omega⟩
      · exact Or.inl ha

  /-- Once `start + len` exceeds `n` no cell of length `len` is left to write, so the `cell`
  invariant has become the `cellAfter` one. -/
  theorem cell_eq_cellAfter {l : List U8} {n len start : Nat} (h : n < start + len) (a b : Nat) :
      cell l n len start a b = cellAfter l n len a b := by
    unfold cell cellAfter
    by_cases hc : a ≤ b ∧ b < n ∧ (b - a + 1 < len ∨ (b - a + 1 = len ∧ a < start))
    · have hc2 : a ≤ b ∧ b < n ∧ b - a + 1 ≤ len := by
        obtain ⟨h1, h2, h3 | ⟨h3, -⟩⟩ := hc
        · exact ⟨h1, h2, by omega⟩
        · exact ⟨h1, h2, by omega⟩
      rw [if_pos hc, if_pos hc2]
    · have hc2 : ¬ (a ≤ b ∧ b < n ∧ b - a + 1 ≤ len) := by
        rintro ⟨h1, h2, h3⟩
        exact hc ⟨h1, h2, by
          rcases lt_or_eq_of_le h3 with h' | h'
          · exact Or.inl h'
          · exact Or.inr ⟨h', by omega⟩⟩
      rw [if_neg hc, if_neg hc2]

  /-- Writing the value of the interval `[start, start+len-1]` into its own cell preserves the
  inner loop invariant, after `start` has been advanced by one. -/
  theorem InvIn_set {l : List U8} {n len start : Nat} {dp : alloc.vec.Vec (alloc.vec.Vec Std.I64)}
      {row : alloc.vec.Vec Std.I64} (i j : Usize) (val : I64)
      (hinv : InvIn l n len start dp)
      (hi : dp.val[i.val]? = some row)
      (hilen : i.val = start) (hjlen : j.val < row.val.length)
      (hjstart : j.val = start + len - 1) (hlen : 1 ≤ len) (hbound : start + len ≤ n)
      (hrowlen : row.val.length = n)
      (hval : val.val = (dpv l start (start + len - 1) : Int)) :
      InvIn l n len (start + 1) (dp.set i (row.set j val)) := by
    obtain ⟨hdims, hent⟩ := hinv
    have hrl : (row.set j val).val.length = n := by
      rw [alloc.vec.Vec.set_val_eq, List.length_set]
      exact hrowlen
    refine ⟨dimsOK_set hdims i (row.set j val) hrl, ?_⟩
    intro a b
    rw [ent_set_entry dp row i j val a b hi hjlen]
    by_cases hab : a = i.val ∧ b = j.val
    · rw [if_pos hab, hval]
      obtain ⟨h1, h2⟩ := hab
      rw [h1, h2, hilen, hjstart]
      exact (cell_ends hlen hbound).symm
    · rw [if_neg hab, hent a b]
      refine cell_start_succ_of_ne (e := start + len - 1) rfl ?_
      rintro ⟨h1, h2⟩
      exact hab ⟨by omega, by omega⟩

  /-! #### Specifications of the loops of `min_insertions` -/

  /-! ##### Auxiliary lemmas for the initialisation loop -/

  /-- Appending one element to a row: the entry function only changes at the new index. -/
  theorem entRow_append_one {r r' : alloc.vec.Vec Std.I64} {v : I64}
      (h : r'.val = r.val ++ [v]) (b : Nat) :
      entRow r' b = if b = r.val.length then v.val else entRow r b := by
    unfold entRow
    rw [h, List.getElem?_append]
    by_cases hb : b < r.val.length
    · rw [if_pos hb, if_neg (by omega)]
    · rw [if_neg hb]
      by_cases hbe : b = r.val.length
      · rw [if_pos hbe]
        have h0 : b - r.val.length = 0 := by omega
        rw [h0]
        rfl
      · rw [if_neg hbe]
        have h1 : ([v] : List I64)[b - r.val.length]? = none :=
          List.getElem?_eq_none (by simp; omega)
        have h2 : r.val[b]? = none := List.getElem?_eq_none (by omega)
        rw [h1, h2]

  /-- Appending one row to the table: the entry function only changes at the new index. -/
  theorem ent_append_one {dp dp' : alloc.vec.Vec (alloc.vec.Vec Std.I64)}
      {row : alloc.vec.Vec Std.I64} (h : dp'.val = dp.val ++ [row]) (a b : Nat) :
      ent dp' a b = if a = dp.val.length then entRow row b else ent dp a b := by
    unfold ent
    rw [h, List.getElem?_append]
    by_cases ha : a < dp.val.length
    · rw [if_pos ha, if_neg (by omega)]
    · rw [if_neg ha]
      by_cases hae : a = dp.val.length
      · rw [if_pos hae]
        have h0 : a - dp.val.length = 0 := by omega
        rw [h0]
        rfl
      · rw [if_neg hae]
        have h1 : ([row] : List (alloc.vec.Vec Std.I64))[a - dp.val.length]? = none :=
          List.getElem?_eq_none (by simp; omega)
        have h2 : dp.val[a]? = none := List.getElem?_eq_none (by omega)
        rw [h1, h2]

  /-- Membership in `l ++ [x]`. -/
  theorem mem_append_singleton {α : Type} {l : List α} {x y : α} (h : y ∈ l ++ [x]) :
      y ∈ l ∨ y = x := by
    rw [List.mem_append] at h
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (by simpa using h)

  /-- The inner initialisation loop fills a row with zeroes. -/
  theorem loop0_row_spec (n : Usize) (hn5 : n.val ≤ 500) (row : alloc.vec.Vec Std.I64)
      (j : Usize) (hlen : row.val.length = j.val) (hle : j.val ≤ n.val)
      (hzero : ∀ b, entRow row b = 0) :
      Aegis.MinInsertions.min_insertions_loop0_loop0 n row j
        ⦃ row' => row'.val.length = n.val ∧ ∀ b, entRow row' b = 0 ⦄ := by
    unfold Aegis.MinInsertions.min_insertions_loop0_loop0
    apply loop.spec_decr_nat
      (measure := fun p : alloc.vec.Vec Std.I64 × Usize => n.val - p.2.val)
      (inv := fun p : alloc.vec.Vec Std.I64 × Usize =>
        p.1.val.length = p.2.val ∧ p.2.val ≤ n.val ∧ ∀ b, entRow p.1 b = 0)
      (post := fun row' => row'.val.length = n.val ∧ ∀ b, entRow row' b = 0)
    · intro p hp
      obtain ⟨row', j'⟩ := p
      obtain ⟨hlen', hle', hzero'⟩ := hp
      dsimp only at *
      unfold Aegis.MinInsertions.min_insertions_loop0_loop0.body
      spec_split as hlt
      · have hltn : j'.val < n.val := by simpa using hlt
        have hmax : row'.val.length < Usize.max := by
          rw [hlen']
          have := hn5
          scalar_tac
        step
        step
        refine ⟨?_, ?_, ?_, ?_⟩
        · simp [row1_post, hlen', j1_post]
        · omega
        · intro b
          rw [entRow_append_one row1_post]
          by_cases hb : b = row'.val.length
          · rw [if_pos hb]; simp
          · rw [if_neg hb]; exact hzero' b
        · omega
      · have hge : n.val ≤ j'.val := by simpa using hlt
        simp only [WP.spec_ok]
        exact ⟨by omega, hzero'⟩
    · exact ⟨hlen, hle, hzero⟩

  /-- The initialisation loop fills the table with zeroes. -/
  theorem loop0_spec (n : Usize) (hn5 : n.val ≤ 500) :
      Aegis.MinInsertions.min_insertions_loop0 n (alloc.vec.Vec.new (alloc.vec.Vec Std.I64)) 0#usize
        ⦃ dp => dimsOK dp n.val ∧ ∀ a b, ent dp a b = 0 ⦄ := by
    unfold Aegis.MinInsertions.min_insertions_loop0
    apply loop.spec_decr_nat
      (measure := fun p : alloc.vec.Vec (alloc.vec.Vec Std.I64) × Usize => n.val - p.2.val)
      (inv := fun p : alloc.vec.Vec (alloc.vec.Vec Std.I64) × Usize =>
        p.1.val.length = p.2.val ∧ p.2.val ≤ n.val ∧
          ∀ r ∈ p.1.val, r.val.length = n.val ∧ ∀ b, entRow r b = 0)
      (post := fun dp => dimsOK dp n.val ∧ ∀ a b, ent dp a b = 0)
    · intro p hp
      obtain ⟨dp, i⟩ := p
      obtain ⟨hdlen, hdle, hdrows⟩ := hp
      dsimp only at *
      unfold Aegis.MinInsertions.min_insertions_loop0.body
      spec_split as hlt
      · have hltn : i.val < n.val := by simpa using hlt
        have hmax : dp.val.length < Usize.max := by rw [hdlen]; scalar_tac
        step with (loop0_row_spec n hn5 (alloc.vec.Vec.new Std.I64) 0#usize rfl (by simp)
          (by intro b; simp [entRow]))
        step
        step
        refine ⟨?_, ?_, ?_, ?_⟩
        · simp [dp1_post, hdlen, i1_post]
        · simp [i1_post]
          omega
        · intro r hr
          rw [dp1_post] at hr
          rcases mem_append_singleton hr with hr | rfl
          · exact hdrows r hr
          · exact ⟨row_post, row_post1⟩
        · simp [i1_post]
          omega
      · have hge : n.val ≤ i.val := by simpa using hlt
        simp only [WP.spec_ok]
        refine ⟨⟨by omega, ?_⟩, ?_⟩
        · intro row hrow
          exact (hdrows row hrow).1
        · intro a b
          by_cases ha : a < dp.val.length
          · rw [ent_eq dp a b (dp.val[a]) (List.getElem?_eq_getElem ha)]
            exact (hdrows (dp.val[a]) (List.getElem_mem ha)).2 b
          · unfold ent
            rw [List.getElem?_eq_none (by omega)]
            rfl
    · refine ⟨rfl, by simp, ?_⟩
      intro r hr
      simp at hr

  /-- Body of the inner loop of `min_insertions`. -/
  theorem loop_inner_body_spec (s : Slice U8) (l : List U8) (hs : s.val = l)
      (n : Usize) (hn : n.val = l.length) (hn5 : n.val ≤ 500)
      (len : Usize) (hlen : 2 ≤ len.val) (hlenb : len.val ≤ n.val + 1)
      (dp : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (start : Usize)
      (hstart : start.val ≤ n.val)
      (hinv : InvIn l n.val len.val start.val dp) :
      Aegis.MinInsertions.min_insertions_loop1_loop0.body s n len dp start
        ⦃ r => match r with
          | .done dp' => InvLen l n.val len.val dp'
          | .cont p => InvIn l n.val len.val p.2.val p.1 ∧ p.2.val = start.val + 1 ∧
              p.2.val ≤ n.val ⦄ := by
    unfold Aegis.MinInsertions.min_insertions_loop1_loop0.body
    step
    spec_split as hbr
    · step
      step
      step
      rw [bind_ite_b]
      spec_split as hends
      · obtain ⟨hdims, hent⟩ := hinv
        have hile : start.val + len.val ≤ n.val := by
          have h := hbr
          simp at h
          omega
        have hstartn : start.val < n.val := by omega
        have hdplen : dp.val.length = n.val := hdims.1
        have hsl : s.val.length = n.val := by rw [hs]; exact hn.symm
        have hendn : end.val < n.val := by
          have h1 : end.val = i.val - 1 := end_post
          omega
        rw [bind_ite_b]
        spec_split as hlen2
        · step* by omega
          have hlen_x : x.1.val.length = n.val := by
            rw [x_post]
            exact hdims.2 _ (List.getElem_mem (show start.val < dp.val.length from by omega))
          obtain ⟨v, back⟩ := x
          have hv : v.val.length = n.val := by simpa using hlen_x
          have hback : back = dp.set start := by simpa using x_post1
          have hxv : v = (dp.val)[start.val] := by simpa using x_post
          step* by omega
          obtain ⟨old, back1⟩ := x
          have hb1 : back1 = v.set «end» := by simpa using x_post1
          rw [hback, hb1]
          step* by omega
          refine ⟨?_, start1_post, by omega⟩
          rw [start1_post]
          have h2v : (2#usize : Usize).val = 2 := by simp
          have hlenv : len.val = 2 := by rw [hlen2]; exact h2v
          have hi : dp.val[start.val]? = some v := by
            rw [hxv]
            exact List.getElem?_eq_getElem (by omega)
          have hee : «end».val = start.val + 1 := by omega
          have hstartl : start.val + 1 < l.length := by omega
          have hi1 : l[start.val]? = some i1 := by
            rw [← hs, i1_post]
            exact List.getElem?_eq_getElem (by omega)
          have hi2 : l[«end».val]? = some i2 := by
            rw [← hs, i2_post]
            exact List.getElem?_eq_getElem (by omega)
          have hll : l[start.val]? = l[start.val + 1]? := by
            rw [hi1, ← hee, hi2, hends]
          have hdpv : dpv l start.val (start.val + 1) = 0 := dpv_pair hstartl hll
          have hent2 : ∀ (a b : ℕ), ent dp a b = cell l (↑n) (↑2#usize) (↑start) a b := by
            intro a b
            rw [← hlen2]
            exact hent a b
          have hjlen : «end».val < v.val.length := by omega
          have hjst : «end».val = start.val + (2#usize).val - 1 := by omega
          have hl1 : 1 ≤ (2#usize).val := by omega
          have hbnd : start.val + (2#usize).val ≤ n.val := by omega
          refine InvIn_set (i := start) (j := «end») (row := v) (val := 0#i64)
            (len := (2#usize).val) ⟨hdims, hent2⟩ hi rfl hjlen hjst hl1 hbnd hv ?_
          show (0#i64).val = (dpv l start.val (start.val + (2#usize).val - 1) : Int)
          rw [h2v, show start.val + 2 - 1 = start.val + 1 from by omega, hdpv]
          norm_num
        · step as ⟨i3, hi3⟩
          step as ⟨v, hv⟩
          have hvlen : v.val.length = n.val := by
            rw [hv]
            exact hdims.2 _ (List.getElem_mem (by omega))
          step as ⟨i4, hi4⟩
          step as ⟨i5, hi5⟩
          · step
            obtain ⟨r1, back⟩ := x
            have hr1 : r1 = (↑dp)[↑start] := by simpa using x_post
            have hback : back = dp.set start := by simpa using x_post1
            have hr1len : r1.val.length = n.val := by
              rw [hr1]
              exact hdims.2 _ (List.getElem_mem (by omega))
            step as ⟨p, hp, hp1⟩
            obtain ⟨o1, o2⟩ := p
            have ho2 : o2 = r1.set «end» := by simpa using hp1
            rw [hback, ho2]
            step as ⟨start1, hstart1⟩
            refine ⟨?_, hstart1, by omega⟩
            rw [hstart1]
            have hend : «end».val = start.val + len.val - 1 := by
              have h1 : «end».val = i.val - 1 := end_post
              omega
            have hlen2v : len.val ≠ 2 := by
              intro h
              apply hlen2
              apply UScalar.eq_of_val_eq
              rw [h]
              simp
            have hlen3 : 3 ≤ len.val := by omega
            have hi1' : l[start.val]? = some i1 := by
              rw [← hs, i1_post]
              exact List.getElem?_eq_getElem (by omega)
            have hi2' : l[«end».val]? = some i2 := by
              rw [← hs, i2_post]
              exact List.getElem?_eq_getElem (by omega)
            have hll : l[start.val]? = l[«end».val]? := by
              rw [hi1', hi2', hends]
            have hdpveq : dpv l start.val («end».val) = dpv l (start.val + 1) («end».val - 1) :=
              dpv_end_eq (by omega) (by omega) hll
            have hvvlen : (dp.val[i3.val]).val.length = n.val :=
              hdims.2 _ (List.getElem_mem (by omega))
            have hval5 : i5.val = (dpv l start.val (start.val + len.val - 1) : Int) := by
              have hA : i5.val = ent dp i3.val i4.val := by
                rw [hi5]
                simp only [hv]
                exact (ent_getElem dp i3.val i4.val (by omega) (by omega)).symm
              have hB : ent dp i3.val i4.val = (dpv l i3.val i4.val : Int) := by
                rw [hent]
                apply cell_of_lt
                · omega
                · omega
                · omega
              have hC : dpv l i3.val i4.val = dpv l (start.val + 1) («end».val - 1) := by
                rw [hi3, hi4]
              have hD : dpv l start.val («end».val) = dpv l start.val (start.val + len.val - 1) := by
                rw [hend]
              calc i5.val = ent dp i3.val i4.val := hA
                _ = (dpv l i3.val i4.val : Int) := hB
                _ = (dpv l (start.val + 1) («end».val - 1) : Int) := by rw [hC]
                _ = (dpv l start.val («end».val) : Int) := by rw [hdpveq]
                _ = (dpv l start.val (start.val + len.val - 1) : Int) := by rw [hD]
            have hi : dp.val[start.val]? = some r1 := by
              rw [hr1]
              exact List.getElem?_eq_getElem (by omega)
            have hjlen : «end».val < r1.val.length := by omega
            refine InvIn_set (i := start) (j := «end») (row := r1) (val := i5)
              ⟨hdims, hent⟩ hi rfl hjlen hend (by omega) (by omega) hr1len hval5
      · obtain ⟨hdims, hent⟩ := hinv
        have hile : start.val + len.val ≤ n.val := by
          have h := hbr
          simp at h
          omega
        have hstartn : start.val < n.val := by omega
        have hdplen : dp.val.length = n.val := hdims.1
        have hsl : s.val.length = n.val := by rw [hs]; exact hn.symm
        have hend : «end».val = start.val + len.val - 1 := by
          have h1 : «end».val = i.val - 1 := end_post
          omega
        have hendn : «end».val < n.val := by omega
        have hi1' : l[start.val]? = some i1 := by
          rw [← hs, i1_post]
          exact List.getElem?_eq_getElem (by omega)
        have hi2' : l[«end».val]? = some i2 := by
          rw [← hs, i2_post]
          exact List.getElem?_eq_getElem (by omega)
        have hne : ¬ (l[start.val]? = l[«end».val]?) := by
          rw [hi1', hi2']
          intro h
          exact hends (by simpa using h)
        have hdpvne : dpv l start.val «end».val
            = 1 + min (dpv l (start.val + 1) «end».val) (dpv l start.val («end».val - 1)) :=
          dpv_end_ne (by omega) (by omega) hne
        step as ⟨i3, hi3⟩
        step as ⟨v, hv⟩
        have hvlen : (dp.val[i3.val]).val.length = n.val :=
          hdims.2 _ (List.getElem_mem (by omega))
        step as ⟨left, hleft⟩
        step as ⟨w1, hw1⟩
        have hw1len : (dp.val[start.val]).val.length = n.val :=
          hdims.2 _ (List.getElem_mem (by omega))
        step as ⟨i4, hi4⟩
        step as ⟨right, hright⟩
        have hleftv : left.val = (dpv l (start.val + 1) «end».val : Int) := by
          have h1 : left.val = ent dp i3.val «end».val := by
            rw [hleft]
            simp only [hv]
            exact (ent_getElem dp i3.val «end».val (by omega) (by omega)).symm
          have h2 : ent dp i3.val «end».val = (dpv l i3.val «end».val : Int) := by
            rw [hent]
            apply cell_of_lt
            · omega
            · omega
            · omega
          calc left.val = ent dp i3.val «end».val := h1
            _ = (dpv l i3.val «end».val : Int) := h2
            _ = (dpv l (start.val + 1) «end».val : Int) := by rw [hi3]
        have hrightv : right.val = (dpv l start.val («end».val - 1) : Int) := by
          have h1 : right.val = ent dp start.val i4.val := by
            rw [hright]
            simp only [hw1]
            exact (ent_getElem dp start.val i4.val (by omega) (by omega)).symm
          have h2 : ent dp start.val i4.val = (dpv l start.val i4.val : Int) := by
            rw [hent]
            apply cell_of_lt
            · omega
            · omega
            · omega
          calc right.val = ent dp start.val i4.val := h1
            _ = (dpv l start.val i4.val : Int) := h2
            _ = (dpv l start.val («end».val - 1) : Int) := by rw [hi4]
        rw [bind_ite_b]
        spec_split as hlt
        · have hlti : (dpv l (start.val + 1) «end».val : Int)
              < (dpv l start.val («end».val - 1) : Int) := by
            have h := (IScalar.lt_equiv left right).1 hlt
            rw [hleftv] at h
            rw [hrightv] at h
            exact h
          have hmin : min (dpv l (start.val + 1) «end».val) (dpv l start.val («end».val - 1))
              = dpv l (start.val + 1) «end».val := by
            apply min_eq_left
            omega
          step as ⟨i5, hi5⟩
          step as ⟨q, hq, hq1⟩
          obtain ⟨r2, back2⟩ := q
          have hr2 : r2 = (↑dp)[↑start] := by simpa using hq
          have hback2 : back2 = dp.set start := by simpa using hq1
          have hr2len : r2.val.length = n.val := by
            rw [hr2]
            exact hdims.2 _ (List.getElem_mem (by omega))
          step as ⟨p, hp, hp1⟩
          obtain ⟨o1, o2⟩ := p
          have ho2 : o2 = r2.set «end» := by simpa using hp1
          rw [hback2, ho2]
          step as ⟨start1, hstart1⟩
          refine ⟨?_, hstart1, by omega⟩
          rw [hstart1]
          have hval5 : i5.val = (dpv l start.val (start.val + len.val - 1) : Int) := by
            calc i5.val = left.val + 1 := hi5
              _ = (dpv l (start.val + 1) «end».val : Int) + 1 := by rw [hleftv]
              _ = ((1 + min (dpv l (start.val + 1) «end».val)
                    (dpv l start.val («end».val - 1)) : Nat) : Int) := by
                    rw [hmin]; push_cast; ring
              _ = (dpv l start.val «end».val : Int) := by rw [← hdpvne]
              _ = (dpv l start.val (start.val + len.val - 1) : Int) := by rw [hend]
          have hi : dp.val[start.val]? = some r2 := by
            rw [hr2]
            exact List.getElem?_eq_getElem (by omega)
          have hjlen : «end».val < r2.val.length := by omega
          exact InvIn_set (i := start) (j := «end») (row := r2) (val := i5)
            ⟨hdims, hent⟩ hi rfl hjlen hend (by omega) (by omega) hr2len hval5
        · have hlt' : ¬ ((left.val : Int) < (right.val : Int)) := by
            intro h
            exact hlt ((IScalar.lt_equiv left right).2 h)
          have hlei : (dpv l start.val («end».val - 1) : Int)
              ≤ (dpv l (start.val + 1) «end».val : Int) := by
            rw [← hrightv, ← hleftv]
            omega
          have hmin : min (dpv l (start.val + 1) «end».val) (dpv l start.val («end».val - 1))
              = dpv l start.val («end».val - 1) := by
            apply min_eq_right
            omega
          step as ⟨i5, hi5⟩
          · rw [hrightv]
            have h := dpv_le (l := l) (lo := start.val) (hi := «end».val - 1) (by omega) (by omega)
            have h2 : (dpv l start.val («end».val - 1) : Int) ≤ 500 := by omega
            scalar_tac
          · step as ⟨q, hq, hq1⟩
            obtain ⟨r2, back2⟩ := q
            have hr2 : r2 = (↑dp)[↑start] := by simpa using hq
            have hback2 : back2 = dp.set start := by simpa using hq1
            have hr2len : r2.val.length = n.val := by
              rw [hr2]
              exact hdims.2 _ (List.getElem_mem (by omega))
            step as ⟨p, hp, hp1⟩
            obtain ⟨o1, o2⟩ := p
            have ho2 : o2 = r2.set «end» := by simpa using hp1
            rw [hback2, ho2]
            step as ⟨start1, hstart1⟩
            refine ⟨?_, hstart1, by omega⟩
            rw [hstart1]
            have hval5 : i5.val = (dpv l start.val (start.val + len.val - 1) : Int) := by
              calc i5.val = right.val + 1 := hi5
                _ = (dpv l start.val («end».val - 1) : Int) + 1 := by rw [hrightv]
                _ = ((1 + min (dpv l (start.val + 1) «end».val)
                      (dpv l start.val («end».val - 1)) : Nat) : Int) := by
                      rw [hmin]; push_cast; ring
                _ = (dpv l start.val «end».val : Int) := by rw [← hdpvne]
                _ = (dpv l start.val (start.val + len.val - 1) : Int) := by rw [hend]
            have hi : dp.val[start.val]? = some r2 := by
              rw [hr2]
              exact List.getElem?_eq_getElem (by omega)
            have hjlen : «end».val < r2.val.length := by omega
            exact InvIn_set (i := start) (j := «end») (row := r2) (val := i5)
              ⟨hdims, hent⟩ hi rfl hjlen hend (by omega) (by omega) hr2len hval5
    · simp only [WP.spec_ok]
      obtain ⟨hdims, hent⟩ := hinv
      refine ⟨hdims, fun a b => ?_⟩
      rw [hent a b]
      apply cell_eq_cellAfter
      have h := hbr
      simp at h
      omega

  /-- The inner loop of `min_insertions` fills all cells of length `≤ len`. -/
  theorem loop_inner_spec (s : Slice U8) (l : List U8) (hs : s.val = l)
      (n : Usize) (hn : n.val = l.length) (hn5 : n.val ≤ 500)
      (len : Usize) (hlen : 2 ≤ len.val) (hlenb : len.val ≤ n.val + 1)
      (dp : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (start : Usize)
      (hstart : start.val ≤ n.val)
      (hinv : InvIn l n.val len.val start.val dp) :
      Aegis.MinInsertions.min_insertions_loop1_loop0 s n dp len start
        ⦃ dp' => InvLen l n.val len.val dp' ⦄ := by
    unfold Aegis.MinInsertions.min_insertions_loop1_loop0
    apply loop.spec_decr_nat
      (measure := fun p : alloc.vec.Vec (alloc.vec.Vec Std.I64) × Usize => Usize.size - p.2.val)
      (inv := fun p => InvIn l n.val len.val p.2.val p.1 ∧ p.2.val ≤ n.val)
      (post := fun dp' => InvLen l n.val len.val dp')
    · intro p hp
      obtain ⟨dp', start'⟩ := p
      obtain ⟨hinv', hle'⟩ := hp
      dsimp only at *
      refine WP.spec_mono
        (loop_inner_body_spec s l hs n hn hn5 len hlen hlenb dp' start' hle' hinv') ?_
      rintro (⟨dp2, s2⟩ | dp2) hr
      · dsimp only at hr ⊢
        obtain ⟨hr1, hr2, hr3⟩ := hr
        exact ⟨⟨hr1, hr3⟩, by scalar_tac⟩
      · dsimp only at hr ⊢
        exact hr
    · exact ⟨hinv, hstart⟩

  /-- Body of the outer loop of `min_insertions`. -/
  theorem loop_outer_body_spec (s : Slice U8) (l : List U8) (hs : s.val = l)
      (n : Usize) (hn : n.val = l.length) (hn5 : n.val ≤ 500)
      (len : Usize) (hlen : 2 ≤ len.val)
      (dp : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (hinv : InvOut l n.val len.val dp) :
      Aegis.MinInsertions.min_insertions_loop1.body s n dp len
        ⦃ r => match r with
          | .done dp' => InvDone l n.val dp'
          | .cont p => InvOut l n.val p.2.val p.1 ∧ p.2.val = len.val + 1 ∧
              p.2.val ≤ n.val + 1 ⦄ := by
    unfold Aegis.MinInsertions.min_insertions_loop1.body
    spec_split as hbr
    · have hinv' : InvIn l n.val len.val (0#usize).val dp := hinv
      step with loop_inner_spec
      step
      obtain ⟨hdims, hent⟩ := dp1_post
      have hle : len.val ≤ n.val := by simpa using hbr
      refine ⟨⟨hdims, fun a b => ?_⟩, len1_post, by omega⟩
      rw [len1_post, cell_succ, hent a b]
    · have hgt : n.val < len.val := by
        simp at hbr
        omega
      simp only [WP.spec_ok]
      obtain ⟨hdims, hent⟩ := hinv
      refine ⟨hdims, fun a b h1 h2 => ?_⟩
      rw [hent a b]
      rw [cell_true]
      exact ⟨h1, h2, Or.inl (by omega)⟩

  /-- The outer loop of `min_insertions` fills the whole table. -/
  theorem loop_outer_spec (s : Slice U8) (l : List U8) (hs : s.val = l)
      (n : Usize) (hn : n.val = l.length) (hn5 : n.val ≤ 500)
      (dp : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (len : Usize)
      (hlen : 2 ≤ len.val) (hlen2 : len.val ≤ n.val + 1) (hinv : InvOut l n.val len.val dp) :
      Aegis.MinInsertions.min_insertions_loop1 s n dp len
        ⦃ dp' => InvDone l n.val dp' ⦄ := by
    unfold Aegis.MinInsertions.min_insertions_loop1
    apply loop.spec_decr_nat
      (measure := fun p : alloc.vec.Vec (alloc.vec.Vec Std.I64) × Usize => n.val + 1 - p.2.val)
      (inv := fun p => InvOut l n.val p.2.val p.1 ∧ 2 ≤ p.2.val ∧ p.2.val ≤ n.val + 1)
      (post := fun dp' => InvDone l n.val dp')
    · intro p hp
      obtain ⟨dp', start'⟩ := p
      obtain ⟨hinv', hge, hle⟩ := hp
      dsimp only at *
      refine WP.spec_mono (loop_outer_body_spec s l hs n hn hn5 start' hge dp' hinv') ?_
      rintro (⟨dp2, s2⟩ | dp2) hr
      · dsimp only at hr ⊢
        obtain ⟨hr1, hr2, hr3⟩ := hr
        have hr2' : s2.val = start'.val + 1 := hr2
        have hr3' : s2.val ≤ n.val + 1 := hr3
        refine ⟨⟨hr1, by omega, hr3'⟩, ?_⟩
        exact Nat.sub_lt_sub_left (k := start'.val) (m := n.val + 1) (n := s2.val)
          (by omega) (by omega)
      · dsimp only at hr ⊢
        exact hr
    · exact ⟨hinv, hlen, hlen2⟩

  /-- The value returned by `min_insertions` is the DP value of the whole interval. -/
  theorem min_insertions_dpv (s : Slice U8) (r : I64)
      (hn5 : s.val.length ≤ 500)
      (h : Aegis.MinInsertions.min_insertions s = ok r) :
      r.val = (s.val.length : Int) - (lpsOf s.val 0 (s.val.length - 1) : Int) := by
    have hmain : Aegis.MinInsertions.min_insertions s ⦃ r' =>
        r'.val = (s.val.length : Int) - (lpsOf s.val 0 (s.val.length - 1) : Int) ⦄ := by
      unfold Aegis.MinInsertions.min_insertions
      dsimp only
      spec_split as hn1
      · rw [WP.spec_ok]
        have hL : s.val.length ≤ 1 := by
          simpa [Slice.len_val, Slice.length] using hn1
        have hlps : lpsOf s.val 0 (s.val.length - 1) = s.val.length := by
          rcases Nat.eq_zero_or_pos s.val.length with h0 | h1
          · have hsub : s.val.length - 1 = 0 := by omega
            rw [hsub, lpsOf, dif_neg (by omega)]
            omega
          · have h1' : s.val.length = 1 := by omega
            have hsub : s.val.length - 1 = 0 := by omega
            rw [hsub, lpsOf, dif_pos (by omega : 0 ≤ 0 ∧ 0 < s.val.length), if_pos rfl]
            omega
        rw [hlps]
        simp
      · -- main case: `2 ≤ n`
        have hn2 : 2 ≤ s.val.length := by
          have h := hn1
          simp at h
          omega
        have hlen : 2 ≤ (2#usize : Usize).val := by simp
        step with loop0_spec as ⟨dp, hpost0, hpost1⟩
        have hinv : InvOut s.val (Slice.len s).val 2 dp :=
          ⟨hpost0, fun a b => by rw [hpost1 a b, cell_two]⟩
        have hlen2 : (2#usize : Usize).val ≤ (Slice.len s).val + 1 := by
          exact le_trans hn2 (Nat.le_succ _)
        step with (loop_outer_spec s s.val rfl (Slice.len s) (Slice.len_val s) hn5 dp
          (2#usize) hlen hlen2 hinv) as ⟨dp1, hpost⟩
        obtain ⟨hdims, hent⟩ := hpost
        step
        step
        -- final: `r.val = dpv l 0 (n-1) = n - lps`
        have h0 : 0 < dp1.val.length := by
          rw [hdims.1]; omega
        have hrowlen : (dp1.val[0]).val.length = s.val.length := by
          have h := dimsOK_row_length hdims 0 h0
          simpa [Slice.len_val, Slice.length] using h
        have hidx : i.val = s.val.length - 1 := by
          have h := i_post
          simp only [Slice.len_val, Slice.length] at h
          omega
        have hv : v.val = (dp1.val[0]).val := by rw [v_post]
        have hi : i.val < v.val.length := by
          rw [hv, hrowlen]; omega
        have hkey : (dpv s.val 0 (s.val.length - 1) : Int)
            = (s.val.length : Int) - (lpsOf s.val 0 (s.val.length - 1) : Int) := by
          have h := dpv_add_lpsOf (l := s.val) (lo := 0) (hi := s.val.length - 1)
            (by omega) (by omega)
          have h' : dpv s.val 0 (s.val.length - 1)
              + lpsOf s.val 0 (s.val.length - 1) = s.val.length := by omega
          omega
        have hsome : dp1.val[0]? = some (dp1.val[0]) := List.getElem?_eq_getElem h0
        have hentry : (Option.map (fun y => y.val) ((dp1.val[0]).val[s.val.length - 1]?)).getD 0
            = ent dp1 0 (s.val.length - 1) := by
          rw [ent_eq dp1 0 (s.val.length - 1) (dp1.val[0]) hsome]
          unfold entRow
          rfl
        refine WP.spec_mono (alloc.vec.Vec.index_usize_spec v i hi) ?_
        intro x hx
        have hx2 : x.val = (Option.map (fun y => y.val) (v.val[i.val]?)).getD 0 := by
          rw [hx, List.getElem?_eq_getElem hi]
          rfl
        rw [hx2, hv, hidx, hentry, hent 0 (s.val.length - 1) (by omega) (by omega)]
        exact hkey
    rw [h] at hmain
    simpa [Std.WP.spec_ok] using hmain

  /-! ### Specification S12 -/

  /-- **S12 (relational, longest common subsequence with the reversal).**
  `r = len(s) - C` where `C` is the largest `m` for which there are increasing index sequences
  `i_0 < … < i_(m-1)` and `j_0 < … < j_(m-1)` with `s[i_a] = s[len(s)-1-j_a]`. -/
  theorem spec_9 (s : Slice U8)
      (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 500)
      (hlower : ∀ (i : Nat), (hi : i < s.val.length) → isLowerAscii (s.val[i])) :
      ∀ r, Aegis.MinInsertions.min_insertions s = ok r →
        ∃ C : Nat,
          isCommonSubseqSize s.val C ∧
            (∀ m, isCommonSubseqSize s.val m → m ≤ C) ∧
              r.val = (s.val.length : Int) - (C : Int) := by
    intro r hr
    refine ⟨lpsOf s.val 0 (s.val.length - 1), ?_, ?_, ?_⟩
    · rw [isCommonSubseqSize_iff_IsCSS]
      exact IsCSS.of_isPalinIn (l := s.val) (m := lpsOf s.val 0 (s.val.length - 1))
        hlen_lower (IsPalinIn.lpsOf (lo := 0) (hi := s.val.length - 1) (by omega) (by omega))
    · intro m hm
      rw [isCommonSubseqSize_iff_IsCSS] at hm
      obtain ⟨M, hmM, hM⟩ := IsFamily.to_isPalinIn (IsFamily.of_IsCSS hm)
      exact le_trans hmM (IsPalinIn.le_lpsOf hM (by omega))
    · exact min_insertions_dpv s r hlen_upper hr

  end AegisSpec.MinInsertions

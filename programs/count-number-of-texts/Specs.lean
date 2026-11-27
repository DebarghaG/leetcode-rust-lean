import Aegis.CountTexts.Code.Funs

/-!
# Specifications of `Aegis.CountTexts.count_texts`

LeetCode problem `count-number-of-texts`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result Aegis.CountTexts

namespace AegisSpec.CountTexts

def M : ℤ := 1000000007

def threePressDigits : Finset ℕ := {50, 51, 52, 53, 54, 56}

def fourPressDigits : Finset ℕ := {55, 57}

def maxPresses (d : U8) : ℕ := if d.val ∈ fourPressDigits then 4 else 3

def countCompositions (k : ℕ) : ℕ → ℕ
  | 0 => 1
  | (n + 1) =>
    (Finset.range k).sum (fun i => if i ≤ n then countCompositions k (n - i) else 0)

def runs : List U8 → List (U8 × ℕ)
  | [] => []
  | b :: bs =>
    match runs bs with
    | [] => [(b, 1)]
    | (b', L) :: rest =>
      if b'.val = b.val then (b, L + 1) :: rest else (b, 1) :: (b', L) :: rest

def textsCount (keys : List U8) : ℕ :=
  ((runs keys).map (fun r => countCompositions (maxPresses r.1) r.2)).prod

/-- Let M = 1000000007. For a valid digit byte d, define k(d) = 4 if d is the ASCII code for '7' or '9', and k(d) = 3 otherwise. For an integer L >= 1 and such a d, let g_d(L) be the number of sequences (a_1, ..., a_t) of positive integers with a_1 + ... + a_t = L and each a_j <= k(d). Partition pressed_keys into its maximal nonempty contiguous runs of equal bytes; let their lengths be L_1, ..., L_m and their digit bytes be d_1, ..., d_m in left-to-right order. Whenever count_texts returns a result r, r = (product over j = 1..m of g_{d_j}(L_j)) mod M.
  Preconditions: len(pressed_keys) is between 1 and 100000 inclusive, and for every i with 0 <= i < len(pressed_keys), pressed_keys[i] is one of the ASCII bytes for digits '2' through '9' (byte values 50 through 57 inclusive). -/
theorem spec_1 (pressed_keys : Slice U8)
    (hlen_low : 1 ≤ pressed_keys.val.length)
    (hlen_high : pressed_keys.val.length ≤ 100000)
    (hvalid : ∀ i (hi : i < pressed_keys.val.length),
      50 ≤ (pressed_keys.val[i]).val ∧ (pressed_keys.val[i]).val ≤ 57) :
    ∀ r : I64, count_texts pressed_keys = ok r →
      r.val = ((textsCount pressed_keys.val : ℕ) : ℤ) % M := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (pressed_keys : Slice U8)
    (hlen_low : 1 ≤ pressed_keys.val.length)
    (hlen_high : pressed_keys.val.length ≤ 100000)
    (hvalid : ∀ i (hi : i < pressed_keys.val.length),
      50 ≤ (pressed_keys.val[i]).val ∧ (pressed_keys.val[i]).val ≤ 57), ∀ r : I64, count_texts pressed_keys = ok r →
      r.val = ((textsCount pressed_keys.val : ℕ) : ℤ) % M) := by
  sorry

/-- For every input satisfying the preconditions, count_texts returns a result r; it does not fail, panic, or overflow.
  Preconditions: len(pressed_keys) is between 1 and 100000 inclusive, and for every i with 0 <= i < len(pressed_keys), pressed_keys[i] is one of the ASCII bytes for digits '2' through '9' (byte values 50 through 57 inclusive). -/
theorem spec_2 (pressed_keys : Slice U8)
    (hlen_low : 1 ≤ pressed_keys.val.length)
    (hlen_high : pressed_keys.val.length ≤ 100000)
    (hvalid : ∀ i (hi : i < pressed_keys.val.length),
      50 ≤ (pressed_keys.val[i]).val ∧ (pressed_keys.val[i]).val ≤ 57) :
    ∃ r : I64, count_texts pressed_keys = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (pressed_keys : Slice U8)
    (hlen_low : 1 ≤ pressed_keys.val.length)
    (hlen_high : pressed_keys.val.length ≤ 100000)
    (hvalid : ∀ i (hi : i < pressed_keys.val.length),
      50 ≤ (pressed_keys.val[i]).val ∧ (pressed_keys.val[i]).val ≤ 57), ∃ r : I64, count_texts pressed_keys = ok r) := by
  sorry

/-- Let M = 1000000007. For every input satisfying the preconditions, whenever count_texts returns a result r, 0 <= r < M.
  Preconditions: len(pressed_keys) is between 1 and 100000 inclusive, and for every i with 0 <= i < len(pressed_keys), pressed_keys[i] is one of the ASCII bytes for digits '2' through '9' (byte values 50 through 57 inclusive). -/
theorem spec_3 (pressed_keys : Slice U8)
    (hlen_low : 1 ≤ pressed_keys.val.length)
    (hlen_high : pressed_keys.val.length ≤ 100000)
    (hvalid : ∀ i (hi : i < pressed_keys.val.length),
      50 ≤ (pressed_keys.val[i]).val ∧ (pressed_keys.val[i]).val ≤ 57) :
    ∀ r : I64, count_texts pressed_keys = ok r → 0 ≤ r.val ∧ r.val < M := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (pressed_keys : Slice U8)
    (hlen_low : 1 ≤ pressed_keys.val.length)
    (hlen_high : pressed_keys.val.length ≤ 100000)
    (hvalid : ∀ i (hi : i < pressed_keys.val.length),
      50 ≤ (pressed_keys.val[i]).val ∧ (pressed_keys.val[i]).val ≤ 57), ∀ r : I64, count_texts pressed_keys = ok r → 0 ≤ r.val ∧ r.val < M) := by
  sorry

/-- Let M = 1000000007. For every input satisfying the preconditions and every split position s with 1 <= s < len(pressed_keys) such that pressed_keys[s-1] != pressed_keys[s], if count_texts(pressed_keys[0..s]) returns r_left, count_texts(pressed_keys[s..len(pressed_keys)]) returns r_right, and count_texts(pressed_keys) returns r, then r = (r_left * r_right) mod M.
  Preconditions: len(pressed_keys) is between 1 and 100000 inclusive, and for every i with 0 <= i < len(pressed_keys), pressed_keys[i] is one of the ASCII bytes for digits '2' through '9' (byte values 50 through 57 inclusive). -/
theorem spec_4 (pressed_keys : Slice U8)
    (hlen_low : 1 ≤ pressed_keys.val.length)
    (hlen_high : pressed_keys.val.length ≤ 100000)
    (hvalid : ∀ i (hi : i < pressed_keys.val.length),
      50 ≤ (pressed_keys.val[i]).val ∧ (pressed_keys.val[i]).val ≤ 57) :
    ∀ (s : ℕ) (_hs_low : 1 ≤ s) (hs_high : s < pressed_keys.val.length)
      (_hcut : (pressed_keys.val.get ⟨s - 1, by omega⟩).val ≠
        (pressed_keys.val.get ⟨s, by omega⟩).val)
      (left right : Slice U8),
      left.val = pressed_keys.val.take s →
      right.val = pressed_keys.val.drop s →
      ∀ (r_left r_right r : I64),
        count_texts left = ok r_left →
        count_texts right = ok r_right →
        count_texts pressed_keys = ok r →
        r.val = (r_left.val * r_right.val) % M := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (pressed_keys : Slice U8)
    (hlen_low : 1 ≤ pressed_keys.val.length)
    (hlen_high : pressed_keys.val.length ≤ 100000)
    (hvalid : ∀ i (hi : i < pressed_keys.val.length),
      50 ≤ (pressed_keys.val[i]).val ∧ (pressed_keys.val[i]).val ≤ 57), ∀ (s : ℕ) (_hs_low : 1 ≤ s) (hs_high : s < pressed_keys.val.length)
      (_hcut : (pressed_keys.val.get ⟨s - 1, by omega⟩).val ≠
        (pressed_keys.val.get ⟨s, by omega⟩).val)
      (left right : Slice U8),
      left.val = pressed_keys.val.take s →
      right.val = pressed_keys.val.drop s →
      ∀ (r_left r_right r : I64),
        count_texts left = ok r_left →
        count_texts right = ok r_right →
        count_texts pressed_keys = ok r →
        r.val = (r_left.val * r_right.val) % M) := by
  sorry

/-- For every input satisfying the preconditions, let rev be the byte slice with len(rev) = len(pressed_keys) and rev[i] = pressed_keys[len(pressed_keys)-1-i] for every i with 0 <= i < len(pressed_keys). If count_texts(pressed_keys) returns r and count_texts(rev) returns r_rev, then r = r_rev.
  Preconditions: len(pressed_keys) is between 1 and 100000 inclusive, and for every i with 0 <= i < len(pressed_keys), pressed_keys[i] is one of the ASCII bytes for digits '2' through '9' (byte values 50 through 57 inclusive). -/
theorem spec_5 (pressed_keys rev : Slice U8)
    (hlen_low : 1 ≤ pressed_keys.val.length)
    (hlen_high : pressed_keys.val.length ≤ 100000)
    (hvalid : ∀ i (hi : i < pressed_keys.val.length),
      50 ≤ (pressed_keys.val[i]).val ∧ (pressed_keys.val[i]).val ≤ 57)
    (hrev : rev.val = pressed_keys.val.reverse) :
    ∀ (r r_rev : I64), count_texts pressed_keys = ok r → count_texts rev = ok r_rev →
      r.val = r_rev.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (pressed_keys rev : Slice U8)
    (hlen_low : 1 ≤ pressed_keys.val.length)
    (hlen_high : pressed_keys.val.length ≤ 100000)
    (hvalid : ∀ i (hi : i < pressed_keys.val.length),
      50 ≤ (pressed_keys.val[i]).val ∧ (pressed_keys.val[i]).val ≤ 57)
    (hrev : rev.val = pressed_keys.val.reverse), ∀ (r r_rev : I64), count_texts pressed_keys = ok r → count_texts rev = ok r_rev →
      r.val = r_rev.val) := by
  sorry

/-- Let phi be any map on the valid digit bytes such that phi maps the set of ASCII codes for {2,3,4,5,6,8} bijectively onto itself and maps the set of ASCII codes for {7,9} bijectively onto itself. For every input satisfying the preconditions, define pressed_keys' by pressed_keys'[i] = phi(pressed_keys[i]) for every i with 0 <= i < len(pressed_keys). If count_texts(pressed_keys) returns r and count_texts(pressed_keys') returns r', then r = r'.
  Preconditions: len(pressed_keys) is between 1 and 100000 inclusive, and for every i with 0 <= i < len(pressed_keys), pressed_keys[i] is one of the ASCII bytes for digits '2' through '9' (byte values 50 through 57 inclusive). -/
theorem spec_6 (pressed_keys pressed_keys' : Slice U8) (phi : U8 → U8)
    (hlen_low : 1 ≤ pressed_keys.val.length)
    (hlen_high : pressed_keys.val.length ≤ 100000)
    (hvalid : ∀ i (hi : i < pressed_keys.val.length),
      50 ≤ (pressed_keys.val[i]).val ∧ (pressed_keys.val[i]).val ≤ 57)
    (h_three_map : ∀ d : U8, d.val ∈ threePressDigits → (phi d).val ∈ threePressDigits)
    (h_three_surj : ∀ e : U8, e.val ∈ threePressDigits →
      ∃ d : U8, d.val ∈ threePressDigits ∧ phi d = e)
    (h_four_map : ∀ d : U8, d.val ∈ fourPressDigits → (phi d).val ∈ fourPressDigits)
    (h_four_surj : ∀ e : U8, e.val ∈ fourPressDigits →
      ∃ d : U8, d.val ∈ fourPressDigits ∧ phi d = e)
    (hmap : pressed_keys'.val = pressed_keys.val.map phi) :
    ∀ (r r' : I64), count_texts pressed_keys = ok r → count_texts pressed_keys' = ok r' →
      r.val = r'.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (pressed_keys pressed_keys' : Slice U8) (phi : U8 → U8)
    (hlen_low : 1 ≤ pressed_keys.val.length)
    (hlen_high : pressed_keys.val.length ≤ 100000)
    (hvalid : ∀ i (hi : i < pressed_keys.val.length),
      50 ≤ (pressed_keys.val[i]).val ∧ (pressed_keys.val[i]).val ≤ 57)
    (h_three_map : ∀ d : U8, d.val ∈ threePressDigits → (phi d).val ∈ threePressDigits)
    (h_three_surj : ∀ e : U8, e.val ∈ threePressDigits →
      ∃ d : U8, d.val ∈ threePressDigits ∧ phi d = e)
    (h_four_map : ∀ d : U8, d.val ∈ fourPressDigits → (phi d).val ∈ fourPressDigits)
    (h_four_surj : ∀ e : U8, e.val ∈ fourPressDigits →
      ∃ d : U8, d.val ∈ fourPressDigits ∧ phi d = e)
    (hmap : pressed_keys'.val = pressed_keys.val.map phi), ∀ (r r' : I64), count_texts pressed_keys = ok r → count_texts pressed_keys' = ok r' →
      r.val = r'.val) := by
  sorry

end AegisSpec.CountTexts

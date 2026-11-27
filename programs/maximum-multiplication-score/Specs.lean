import Aegis.MaxScore.Code.Funs

/-!
# Specifications of `Aegis.MaxScore.max_score`

LeetCode problem `maximum-multiplication-score`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxScore

open Aeneas.Std (Slice I64 IScalar)

def elem (s : Slice Std.I64) (i : Nat) : Int :=
  ((s.val[i]?).map IScalar.val).getD 0

def IsQuad (b : Slice Std.I64) (i0 i1 i2 i3 : Nat) : Prop :=
  i0 < i1 ∧ i1 < i2 ∧ i2 < i3 ∧ i3 < b.val.length

def score (a b : Slice Std.I64) (i0 i1 i2 i3 : Nat) : Int :=
  elem a 0 * elem b i0 + elem a 1 * elem b i1 + elem a 2 * elem b i2 +
    elem a 3 * elem b i3

def quadSum (b : Slice Std.I64) (i0 i1 i2 i3 : Nat) : Int :=
  elem b i0 + elem b i1 + elem b i2 + elem b i3

def IsMaxQuadSum (b : Slice Std.I64) (m : Int) : Prop :=
  (∃ i0 i1 i2 i3, IsQuad b i0 i1 i2 i3 ∧ quadSum b i0 i1 i2 i3 = m) ∧
    ∀ i0 i1 i2 i3, IsQuad b i0 i1 i2 i3 → quadSum b i0 i1 i2 i3 ≤ m

def IsMinQuadSum (b : Slice Std.I64) (m : Int) : Prop :=
  (∃ i0 i1 i2 i3, IsQuad b i0 i1 i2 i3 ∧ quadSum b i0 i1 i2 i3 = m) ∧
    ∀ i0 i1 i2 i3, IsQuad b i0 i1 i2 i3 → m ≤ quadSum b i0 i1 i2 i3

/-- Whenever max_score(a,b) returns a result r, r is exactly the maximum score over all valid choices of four increasing indices in b: (1) for every quadruple of integers i0,i1,i2,i3 with 0 <= i0 < i1 < i2 < i3 < len(b), a[0]*b[i0] + a[1]*b[i1] + a[2]*b[i2] + a[3]*b[i3] <= r; and (2) there exist integers j0,j1,j2,j3 with 0 <= j0 < j1 < j2 < j3 < len(b) such that a[0]*b[j0] + a[1]*b[j1] + a[2]*b[j2] + a[3]*b[j3] = r.
  Preconditions: len(a) = 4; 4 <= len(b) <= 100000; for every i with 0 <= i < 4, -100000 <= a[i] <= 100000; for every j with 0 <= j < len(b), -100000 <= b[j] <= 100000. -/
theorem spec_1 (a b : Slice Std.I64) (r : Std.I64)
    (ha_len : a.val.length = 4)
    (hb_len : 4 ≤ b.val.length) (hb_len_ub : b.val.length ≤ 100000)
    (ha_bounds : ∀ i, i < 4 → -100000 ≤ elem a i ∧ elem a i ≤ 100000)
    (hb_bounds : ∀ j, j < b.val.length → -100000 ≤ elem b j ∧ elem b j ≤ 100000)
    (hr : Aegis.MaxScore.max_score a b = ok r) :
    (∀ i0 i1 i2 i3, IsQuad b i0 i1 i2 i3 →
        score a b i0 i1 i2 i3 ≤ r.val) ∧
      (∃ j0 j1 j2 j3, IsQuad b j0 j1 j2 j3 ∧
        score a b j0 j1 j2 j3 = r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (a b : Slice Std.I64) (r : Std.I64)
    (ha_len : a.val.length = 4)
    (hb_len : 4 ≤ b.val.length) (hb_len_ub : b.val.length ≤ 100000)
    (ha_bounds : ∀ i, i < 4 → -100000 ≤ elem a i ∧ elem a i ≤ 100000)
    (hb_bounds : ∀ j, j < b.val.length → -100000 ≤ elem b j ∧ elem b j ≤ 100000)
    (hr : Aegis.MaxScore.max_score a b = ok r), (∀ i0 i1 i2 i3, IsQuad b i0 i1 i2 i3 →
        score a b i0 i1 i2 i3 ≤ r.val) ∧
      (∃ j0 j1 j2 j3, IsQuad b j0 j1 j2 j3 ∧
        score a b j0 j1 j2 j3 = r.val)) := by
  sorry

/-- The call max_score(a,b) returns a result: there exists an i64 r such that max_score(a,b) returns r. It does not fail, panic, overflow, or access an out-of-bounds index.
  Preconditions: len(a) = 4; 4 <= len(b) <= 100000; for every i with 0 <= i < 4, -100000 <= a[i] <= 100000; for every j with 0 <= j < len(b), -100000 <= b[j] <= 100000. -/
theorem spec_2 (a b : Slice Std.I64)
    (ha_len : a.val.length = 4)
    (hb_len : 4 ≤ b.val.length) (hb_len_ub : b.val.length ≤ 100000)
    (ha_bounds : ∀ i, i < 4 → -100000 ≤ elem a i ∧ elem a i ≤ 100000)
    (hb_bounds : ∀ j, j < b.val.length → -100000 ≤ elem b j ∧ elem b j ≤ 100000) :
    ∃ r : Std.I64, Aegis.MaxScore.max_score a b = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (a b : Slice Std.I64)
    (ha_len : a.val.length = 4)
    (hb_len : 4 ≤ b.val.length) (hb_len_ub : b.val.length ≤ 100000)
    (ha_bounds : ∀ i, i < 4 → -100000 ≤ elem a i ∧ elem a i ≤ 100000)
    (hb_bounds : ∀ j, j < b.val.length → -100000 ≤ elem b j ∧ elem b j ≤ 100000), ∃ r : Std.I64, Aegis.MaxScore.max_score a b = ok r) := by
  sorry

/-- Whenever max_score(a,b) returns a result r, for every quadruple of integers i0,i1,i2,i3 with 0 <= i0 < i1 < i2 < i3 < len(b), we have a[0]*b[i0] + a[1]*b[i1] + a[2]*b[i2] + a[3]*b[i3] <= r.
  Preconditions: len(a) = 4; 4 <= len(b) <= 100000; for every i with 0 <= i < 4, -100000 <= a[i] <= 100000; for every j with 0 <= j < len(b), -100000 <= b[j] <= 100000. -/
theorem spec_3 (a b : Slice Std.I64) (r : Std.I64)
    (ha_len : a.val.length = 4)
    (hb_len : 4 ≤ b.val.length) (hb_len_ub : b.val.length ≤ 100000)
    (ha_bounds : ∀ i, i < 4 → -100000 ≤ elem a i ∧ elem a i ≤ 100000)
    (hb_bounds : ∀ j, j < b.val.length → -100000 ≤ elem b j ∧ elem b j ≤ 100000)
    (hr : Aegis.MaxScore.max_score a b = ok r) :
    ∀ i0 i1 i2 i3, IsQuad b i0 i1 i2 i3 → score a b i0 i1 i2 i3 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (a b : Slice Std.I64) (r : Std.I64)
    (ha_len : a.val.length = 4)
    (hb_len : 4 ≤ b.val.length) (hb_len_ub : b.val.length ≤ 100000)
    (ha_bounds : ∀ i, i < 4 → -100000 ≤ elem a i ∧ elem a i ≤ 100000)
    (hb_bounds : ∀ j, j < b.val.length → -100000 ≤ elem b j ∧ elem b j ≤ 100000)
    (hr : Aegis.MaxScore.max_score a b = ok r), ∀ i0 i1 i2 i3, IsQuad b i0 i1 i2 i3 → score a b i0 i1 i2 i3 ≤ r.val) := by
  sorry

/-- Whenever max_score(a,b) returns a result r, there exist integers j0,j1,j2,j3 with 0 <= j0 < j1 < j2 < j3 < len(b) such that a[0]*b[j0] + a[1]*b[j1] + a[2]*b[j2] + a[3]*b[j3] = r.
  Preconditions: len(a) = 4; 4 <= len(b) <= 100000; for every i with 0 <= i < 4, -100000 <= a[i] <= 100000; for every j with 0 <= j < len(b), -100000 <= b[j] <= 100000. -/
theorem spec_4 (a b : Slice Std.I64) (r : Std.I64)
    (ha_len : a.val.length = 4)
    (hb_len : 4 ≤ b.val.length) (hb_len_ub : b.val.length ≤ 100000)
    (ha_bounds : ∀ i, i < 4 → -100000 ≤ elem a i ∧ elem a i ≤ 100000)
    (hb_bounds : ∀ j, j < b.val.length → -100000 ≤ elem b j ∧ elem b j ≤ 100000)
    (hr : Aegis.MaxScore.max_score a b = ok r) :
    ∃ j0 j1 j2 j3, IsQuad b j0 j1 j2 j3 ∧ score a b j0 j1 j2 j3 = r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (a b : Slice Std.I64) (r : Std.I64)
    (ha_len : a.val.length = 4)
    (hb_len : 4 ≤ b.val.length) (hb_len_ub : b.val.length ≤ 100000)
    (ha_bounds : ∀ i, i < 4 → -100000 ≤ elem a i ∧ elem a i ≤ 100000)
    (hb_bounds : ∀ j, j < b.val.length → -100000 ≤ elem b j ∧ elem b j ≤ 100000)
    (hr : Aegis.MaxScore.max_score a b = ok r), ∃ j0 j1 j2 j3, IsQuad b j0 j1 j2 j3 ∧ score a b j0 j1 j2 j3 = r.val) := by
  sorry

/-- Whenever max_score(a,b) returns a result r, we have -40000000000 <= r <= 40000000000.
  Preconditions: len(a) = 4; 4 <= len(b) <= 100000; for every i with 0 <= i < 4, -100000 <= a[i] <= 100000; for every j with 0 <= j < len(b), -100000 <= b[j] <= 100000. -/
theorem spec_5 (a b : Slice Std.I64) (r : Std.I64)
    (ha_len : a.val.length = 4)
    (hb_len : 4 ≤ b.val.length) (hb_len_ub : b.val.length ≤ 100000)
    (ha_bounds : ∀ i, i < 4 → -100000 ≤ elem a i ∧ elem a i ≤ 100000)
    (hb_bounds : ∀ j, j < b.val.length → -100000 ≤ elem b j ∧ elem b j ≤ 100000)
    (hr : Aegis.MaxScore.max_score a b = ok r) :
    -40000000000 ≤ r.val ∧ r.val ≤ 40000000000 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (a b : Slice Std.I64) (r : Std.I64)
    (ha_len : a.val.length = 4)
    (hb_len : 4 ≤ b.val.length) (hb_len_ub : b.val.length ≤ 100000)
    (ha_bounds : ∀ i, i < 4 → -100000 ≤ elem a i ∧ elem a i ≤ 100000)
    (hb_bounds : ∀ j, j < b.val.length → -100000 ≤ elem b j ∧ elem b j ≤ 100000)
    (hr : Aegis.MaxScore.max_score a b = ok r), -40000000000 ≤ r.val ∧ r.val ≤ 40000000000) := by
  sorry

/-- Whenever max_score(a,b) returns a result r, r = a[0]*b[0] + a[1]*b[1] + a[2]*b[2] + a[3]*b[3].
  Preconditions: len(a) = 4; len(b) = 4; -100000 <= a[i] <= 100000 for i=0..3; -100000 <= b[j] <= 100000 for j=0..3. -/
theorem spec_6 (a b : Slice Std.I64) (r : Std.I64)
    (ha_len : a.val.length = 4)
    (hb_len : b.val.length = 4)
    (ha_bounds : ∀ i, i < 4 → -100000 ≤ elem a i ∧ elem a i ≤ 100000)
    (hb_bounds : ∀ j, j < 4 → -100000 ≤ elem b j ∧ elem b j ≤ 100000)
    (hr : Aegis.MaxScore.max_score a b = ok r) :
    r.val = elem a 0 * elem b 0 + elem a 1 * elem b 1 + elem a 2 * elem b 2 +
      elem a 3 * elem b 3 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (a b : Slice Std.I64) (r : Std.I64)
    (ha_len : a.val.length = 4)
    (hb_len : b.val.length = 4)
    (ha_bounds : ∀ i, i < 4 → -100000 ≤ elem a i ∧ elem a i ≤ 100000)
    (hb_bounds : ∀ j, j < 4 → -100000 ≤ elem b j ∧ elem b j ≤ 100000)
    (hr : Aegis.MaxScore.max_score a b = ok r), r.val = elem a 0 * elem b 0 + elem a 1 * elem b 1 + elem a 2 * elem b 2 +
      elem a 3 * elem b 3) := by
  sorry

/-- Whenever max_score(a,b) returns a result r, the following holds: if c > 0, then r = c * max { b[i0] + b[i1] + b[i2] + b[i3] | 0 <= i0 < i1 < i2 < i3 < len(b) }; if c < 0, then r = c * min { b[i0] + b[i1] + b[i2] + b[i3] | 0 <= i0 < i1 < i2 < i3 < len(b) }; if c = 0, then r = 0.
  Preconditions: len(a) = 4; 4 <= len(b) <= 100000; a[0] = a[1] = a[2] = a[3] = c for some integer c with -100000 <= c <= 100000; -100000 <= b[j] <= 100000 for every 0 <= j < len(b). -/
theorem spec_7 (a b : Slice Std.I64) (c : Int) (r : Std.I64)
    (ha_len : a.val.length = 4)
    (hb_len : 4 ≤ b.val.length) (hb_len_ub : b.val.length ≤ 100000)
    (hc_bounds : -100000 ≤ c ∧ c ≤ 100000)
    (ha_const : elem a 0 = c ∧ elem a 1 = c ∧ elem a 2 = c ∧ elem a 3 = c)
    (hb_bounds : ∀ j, j < b.val.length → -100000 ≤ elem b j ∧ elem b j ≤ 100000)
    (hr : Aegis.MaxScore.max_score a b = ok r) :
    (0 < c → ∀ m : Int, IsMaxQuadSum b m → r.val = c * m) ∧
      (c < 0 → ∀ m : Int, IsMinQuadSum b m → r.val = c * m) ∧
        (c = 0 → r.val = 0) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (a b : Slice Std.I64) (c : Int) (r : Std.I64)
    (ha_len : a.val.length = 4)
    (hb_len : 4 ≤ b.val.length) (hb_len_ub : b.val.length ≤ 100000)
    (hc_bounds : -100000 ≤ c ∧ c ≤ 100000)
    (ha_const : elem a 0 = c ∧ elem a 1 = c ∧ elem a 2 = c ∧ elem a 3 = c)
    (hb_bounds : ∀ j, j < b.val.length → -100000 ≤ elem b j ∧ elem b j ≤ 100000)
    (hr : Aegis.MaxScore.max_score a b = ok r), (0 < c → ∀ m : Int, IsMaxQuadSum b m → r.val = c * m) ∧
      (c < 0 → ∀ m : Int, IsMinQuadSum b m → r.val = c * m) ∧
        (c = 0 → r.val = 0)) := by
  sorry

/-- Whenever max_score(a,b) returns a result r, r = d * (a[0] + a[1] + a[2] + a[3]).
  Preconditions: len(a) = 4; 4 <= len(b) <= 100000; -100000 <= a[i] <= 100000 for i=0..3; b[j] = d for every 0 <= j < len(b), for some integer d with -100000 <= d <= 100000. -/
theorem spec_8 (a b : Slice Std.I64) (d : Int) (r : Std.I64)
    (ha_len : a.val.length = 4)
    (hb_len : 4 ≤ b.val.length) (hb_len_ub : b.val.length ≤ 100000)
    (hd_bounds : -100000 ≤ d ∧ d ≤ 100000)
    (hb_const : ∀ j, j < b.val.length → elem b j = d)
    (ha_bounds : ∀ i, i < 4 → -100000 ≤ elem a i ∧ elem a i ≤ 100000)
    (hr : Aegis.MaxScore.max_score a b = ok r) :
    r.val = d * (elem a 0 + elem a 1 + elem a 2 + elem a 3) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (a b : Slice Std.I64) (d : Int) (r : Std.I64)
    (ha_len : a.val.length = 4)
    (hb_len : 4 ≤ b.val.length) (hb_len_ub : b.val.length ≤ 100000)
    (hd_bounds : -100000 ≤ d ∧ d ≤ 100000)
    (hb_const : ∀ j, j < b.val.length → elem b j = d)
    (ha_bounds : ∀ i, i < 4 → -100000 ≤ elem a i ∧ elem a i ≤ 100000)
    (hr : Aegis.MaxScore.max_score a b = ok r), r.val = d * (elem a 0 + elem a 1 + elem a 2 + elem a 3)) := by
  sorry

/-- For every such b', if max_score(a,b) returns r and max_score(a,b') returns r', then r' >= r.
  Preconditions: len(a) = 4; for every slice b' considered, 4 <= len(b) <= len(b') <= 100000; -100000 <= a[i] <= 100000 for i=0..3; -100000 <= b[j] <= 100000 for every 0 <= j < len(b); -100000 <= b'[j] <= 100000 for every 0 <= j < len(b'); and b'[i] = b[i] for every 0 <= i < len(b). -/
theorem spec_9 (a b b' : Slice Std.I64) (r r' : Std.I64)
    (ha_len : a.val.length = 4)
    (hb_len : 4 ≤ b.val.length)
    (hbb'_len : b.val.length ≤ b'.val.length)
    (hb'_len : b'.val.length ≤ 100000)
    (ha_bounds : ∀ i, i < 4 → -100000 ≤ elem a i ∧ elem a i ≤ 100000)
    (hb_bounds : ∀ j, j < b.val.length → -100000 ≤ elem b j ∧ elem b j ≤ 100000)
    (hb'_bounds : ∀ j, j < b'.val.length → -100000 ≤ elem b' j ∧ elem b' j ≤ 100000)
    (hprefix : ∀ i, i < b.val.length → elem b' i = elem b i)
    (hr : Aegis.MaxScore.max_score a b = ok r)
    (hr' : Aegis.MaxScore.max_score a b' = ok r') :
    r.val ≤ r'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (a b b' : Slice Std.I64) (r r' : Std.I64)
    (ha_len : a.val.length = 4)
    (hb_len : 4 ≤ b.val.length)
    (hbb'_len : b.val.length ≤ b'.val.length)
    (hb'_len : b'.val.length ≤ 100000)
    (ha_bounds : ∀ i, i < 4 → -100000 ≤ elem a i ∧ elem a i ≤ 100000)
    (hb_bounds : ∀ j, j < b.val.length → -100000 ≤ elem b j ∧ elem b j ≤ 100000)
    (hb'_bounds : ∀ j, j < b'.val.length → -100000 ≤ elem b' j ∧ elem b' j ≤ 100000)
    (hprefix : ∀ i, i < b.val.length → elem b' i = elem b i)
    (hr : Aegis.MaxScore.max_score a b = ok r)
    (hr' : Aegis.MaxScore.max_score a b' = ok r'), r.val ≤ r'.val) := by
  sorry

/-- For such b and b', if max_score(a,b) returns r and max_score(a,b') returns r', then r' = r + c * (a[0] + a[1] + a[2] + a[3]).
  Preconditions: len(a) = 4; 4 <= len(b) = len(b') <= 100000; -100000 <= a[i] <= 100000 for i=0..3; -100000 <= b[j] <= 100000 and -100000 <= b'[j] <= 100000 for every 0 <= j < len(b); and there is an integer c such that b'[j] = b[j] + c for every 0 <= j < len(b). -/
theorem spec_10 (a b b' : Slice Std.I64) (c : Int) (r r' : Std.I64)
    (ha_len : a.val.length = 4)
    (hb_len : 4 ≤ b.val.length) (hb_len_ub : b.val.length ≤ 100000)
    (hbb'_len : b.val.length = b'.val.length)
    (ha_bounds : ∀ i, i < 4 → -100000 ≤ elem a i ∧ elem a i ≤ 100000)
    (hb_bounds : ∀ j, j < b.val.length → -100000 ≤ elem b j ∧ elem b j ≤ 100000)
    (hb'_bounds : ∀ j, j < b.val.length → -100000 ≤ elem b' j ∧ elem b' j ≤ 100000)
    (hshift : ∀ j, j < b.val.length → elem b' j = elem b j + c)
    (hr : Aegis.MaxScore.max_score a b = ok r)
    (hr' : Aegis.MaxScore.max_score a b' = ok r') :
    r'.val = r.val + c * (elem a 0 + elem a 1 + elem a 2 + elem a 3) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (a b b' : Slice Std.I64) (c : Int) (r r' : Std.I64)
    (ha_len : a.val.length = 4)
    (hb_len : 4 ≤ b.val.length) (hb_len_ub : b.val.length ≤ 100000)
    (hbb'_len : b.val.length = b'.val.length)
    (ha_bounds : ∀ i, i < 4 → -100000 ≤ elem a i ∧ elem a i ≤ 100000)
    (hb_bounds : ∀ j, j < b.val.length → -100000 ≤ elem b j ∧ elem b j ≤ 100000)
    (hb'_bounds : ∀ j, j < b.val.length → -100000 ≤ elem b' j ∧ elem b' j ≤ 100000)
    (hshift : ∀ j, j < b.val.length → elem b' j = elem b j + c)
    (hr : Aegis.MaxScore.max_score a b = ok r)
    (hr' : Aegis.MaxScore.max_score a b' = ok r'), r'.val = r.val + c * (elem a 0 + elem a 1 + elem a 2 + elem a 3)) := by
  sorry

/-- For such a', if max_score(a,b) returns r and max_score(a',b) returns r', then r' = c * r.
  Preconditions: len(a) = 4; 4 <= len(b) <= 100000; c > 0 is an integer; a' is a slice with len(a') = 4 and a'[i] = c * a[i] for i=0..3; -100000 <= a[i] <= 100000 and -100000 <= a'[i] <= 100000 for i=0..3; -100000 <= b[j] <= 100000 for every 0 <= j < len(b). -/
theorem spec_11 (a a' b : Slice Std.I64) (c : Int) (r r' : Std.I64)
    (ha_len : a.val.length = 4)
    (ha'_len : a'.val.length = 4)
    (hb_len : 4 ≤ b.val.length) (hb_len_ub : b.val.length ≤ 100000)
    (hc_pos : 0 < c)
    (hscale : ∀ i, i < 4 → elem a' i = c * elem a i)
    (ha_bounds : ∀ i, i < 4 → -100000 ≤ elem a i ∧ elem a i ≤ 100000)
    (ha'_bounds : ∀ i, i < 4 → -100000 ≤ elem a' i ∧ elem a' i ≤ 100000)
    (hb_bounds : ∀ j, j < b.val.length → -100000 ≤ elem b j ∧ elem b j ≤ 100000)
    (hr : Aegis.MaxScore.max_score a b = ok r)
    (hr' : Aegis.MaxScore.max_score a' b = ok r') :
    r'.val = c * r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (a a' b : Slice Std.I64) (c : Int) (r r' : Std.I64)
    (ha_len : a.val.length = 4)
    (ha'_len : a'.val.length = 4)
    (hb_len : 4 ≤ b.val.length) (hb_len_ub : b.val.length ≤ 100000)
    (hc_pos : 0 < c)
    (hscale : ∀ i, i < 4 → elem a' i = c * elem a i)
    (ha_bounds : ∀ i, i < 4 → -100000 ≤ elem a i ∧ elem a i ≤ 100000)
    (ha'_bounds : ∀ i, i < 4 → -100000 ≤ elem a' i ∧ elem a' i ≤ 100000)
    (hb_bounds : ∀ j, j < b.val.length → -100000 ≤ elem b j ∧ elem b j ≤ 100000)
    (hr : Aegis.MaxScore.max_score a b = ok r)
    (hr' : Aegis.MaxScore.max_score a' b = ok r'), r'.val = c * r.val) := by
  sorry

/-- For such b and b', if max_score(a,b) returns r and max_score(a,b') returns r', then r' >= r.
  Preconditions: len(a) = 4; 4 <= len(b) = len(b') <= 100000; a[i] >= 0 for i=0..3; -100000 <= a[i] <= 100000 for i=0..3; -100000 <= b[j] <= 100000 and -100000 <= b'[j] <= 100000 for every 0 <= j < len(b); and b'[j] >= b[j] for every 0 <= j < len(b). -/
theorem spec_12 (a b b' : Slice Std.I64) (r r' : Std.I64)
    (ha_len : a.val.length = 4)
    (hb_len : 4 ≤ b.val.length) (hb_len_ub : b.val.length ≤ 100000)
    (hbb'_len : b.val.length = b'.val.length)
    (ha_nonneg : ∀ i, i < 4 → 0 ≤ elem a i)
    (ha_bounds : ∀ i, i < 4 → -100000 ≤ elem a i ∧ elem a i ≤ 100000)
    (hb_bounds : ∀ j, j < b.val.length → -100000 ≤ elem b j ∧ elem b j ≤ 100000)
    (hb'_bounds : ∀ j, j < b.val.length → -100000 ≤ elem b' j ∧ elem b' j ≤ 100000)
    (hmono : ∀ j, j < b.val.length → elem b j ≤ elem b' j)
    (hr : Aegis.MaxScore.max_score a b = ok r)
    (hr' : Aegis.MaxScore.max_score a b' = ok r') :
    r.val ≤ r'.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (a b b' : Slice Std.I64) (r r' : Std.I64)
    (ha_len : a.val.length = 4)
    (hb_len : 4 ≤ b.val.length) (hb_len_ub : b.val.length ≤ 100000)
    (hbb'_len : b.val.length = b'.val.length)
    (ha_nonneg : ∀ i, i < 4 → 0 ≤ elem a i)
    (ha_bounds : ∀ i, i < 4 → -100000 ≤ elem a i ∧ elem a i ≤ 100000)
    (hb_bounds : ∀ j, j < b.val.length → -100000 ≤ elem b j ∧ elem b j ≤ 100000)
    (hb'_bounds : ∀ j, j < b.val.length → -100000 ≤ elem b' j ∧ elem b' j ≤ 100000)
    (hmono : ∀ j, j < b.val.length → elem b j ≤ elem b' j)
    (hr : Aegis.MaxScore.max_score a b = ok r)
    (hr' : Aegis.MaxScore.max_score a b' = ok r'), r.val ≤ r'.val) := by
  sorry

end AegisSpec.MaxScore

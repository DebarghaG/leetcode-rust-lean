import Aegis.PassThePillow.Code.Funs

/-!
# Specifications of `Aegis.PassThePillow.pass_the_pillow`

LeetCode problem `pass-the-pillow`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.PassThePillow

  def period (n : Int) : Int := 2 * (n - 1)

  /-- Let P = 2*(n-1). Whenever pass_the_pillow n time returns a result ans, let q be the unique integer such that 0 <= q < P and time = k*P + q for some nonnegative integer k. Then ans = 1+q if q <= n-1, and ans = 2*n - 1 - q if q > n-1. This is exactly the 1-based index of the person holding the pillow after time seconds in the bouncing pass sequence that starts at person 1.
    Preconditions: n and time are integers with 2 <= n <= 1000 and 1 <= time <= 1000. -/
  theorem spec_1 (n time ans : Std.I64)
      (hn : 2 ≤ n.val) (hn_ub : n.val ≤ 1000)
      (ht : 1 ≤ time.val) (ht_ub : time.val ≤ 1000)
      (hres : Aegis.PassThePillow.pass_the_pillow n time = ok ans) :
      ∃ k : Int, ∃ q : Int, 0 ≤ k ∧ 0 ≤ q ∧ q < period n.val ∧
        time.val = k * period n.val + q ∧
        ans.val = if q ≤ n.val - 1 then 1 + q else 2 * n.val - 1 - q := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n time ans : Std.I64)
        (hn : 2 ≤ n.val) (hn_ub : n.val ≤ 1000)
        (ht : 1 ≤ time.val) (ht_ub : time.val ≤ 1000)
        (hres : Aegis.PassThePillow.pass_the_pillow n time = ok ans), ∃ k : Int, ∃ q : Int, 0 ≤ k ∧ 0 ≤ q ∧ q < period n.val ∧
          time.val = k * period n.val + q ∧
          ans.val = if q ≤ n.val - 1 then 1 + q else 2 * n.val - 1 - q) := by
    sorry

  /-- For every n and time satisfying the preconditions, pass_the_pillow n time returns a result ans; it does not fail, overflow, panic, or access an out-of-bounds index.
    Preconditions: n and time are integers with 2 <= n <= 1000 and 1 <= time <= 1000. -/
  theorem spec_2 (n time : Std.I64)
      (hn : 2 ≤ n.val) (hn_ub : n.val ≤ 1000)
      (ht : 1 ≤ time.val) (ht_ub : time.val ≤ 1000) :
      ∃ ans : Std.I64, Aegis.PassThePillow.pass_the_pillow n time = ok ans := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n time : Std.I64)
        (hn : 2 ≤ n.val) (hn_ub : n.val ≤ 1000)
        (ht : 1 ≤ time.val) (ht_ub : time.val ≤ 1000), ∃ ans : Std.I64, Aegis.PassThePillow.pass_the_pillow n time = ok ans) := by
    sorry

  /-- Whenever pass_the_pillow n time returns a result ans, 1 <= ans <= n.
    Preconditions: n and time are integers with 2 <= n <= 1000 and 1 <= time <= 1000. -/
  theorem spec_3 (n time ans : Std.I64)
      (hn : 2 ≤ n.val) (hn_ub : n.val ≤ 1000)
      (ht : 1 ≤ time.val) (ht_ub : time.val ≤ 1000)
      (hres : Aegis.PassThePillow.pass_the_pillow n time = ok ans) :
      1 ≤ ans.val ∧ ans.val ≤ n.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n time ans : Std.I64)
        (hn : 2 ≤ n.val) (hn_ub : n.val ≤ 1000)
        (ht : 1 ≤ time.val) (ht_ub : time.val ≤ 1000)
        (hres : Aegis.PassThePillow.pass_the_pillow n time = ok ans), 1 ≤ ans.val ∧ ans.val ≤ n.val) := by
    sorry

  /-- Whenever pass_the_pillow n time returns a result ans, ans = time + 1.
    Preconditions: n and time are integers with 2 <= n <= 1000, 1 <= time <= 1000, and time <= n-1. -/
  theorem spec_4 (n time ans : Std.I64)
      (hn : 2 ≤ n.val) (hn_ub : n.val ≤ 1000)
      (ht : 1 ≤ time.val) (ht_ub : time.val ≤ 1000)
      (htn : time.val ≤ n.val - 1)
      (hres : Aegis.PassThePillow.pass_the_pillow n time = ok ans) :
      ans.val = time.val + 1 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n time ans : Std.I64)
        (hn : 2 ≤ n.val) (hn_ub : n.val ≤ 1000)
        (ht : 1 ≤ time.val) (ht_ub : time.val ≤ 1000)
        (htn : time.val ≤ n.val - 1)
        (hres : Aegis.PassThePillow.pass_the_pillow n time = ok ans), ans.val = time.val + 1) := by
    sorry

  /-- Whenever pass_the_pillow n time returns a result ans, ans = 2*n - 1 - time.
    Preconditions: n and time are integers with 2 <= n <= 1000, 1 <= time <= 1000, and n <= time <= 2*(n-1). -/
  theorem spec_5 (n time ans : Std.I64)
      (hn : 2 ≤ n.val) (hn_ub : n.val ≤ 1000)
      (ht : 1 ≤ time.val) (ht_ub : time.val ≤ 1000)
      (hnt : n.val ≤ time.val)
      (htn : time.val ≤ 2 * (n.val - 1))
      (hres : Aegis.PassThePillow.pass_the_pillow n time = ok ans) :
      ans.val = 2 * n.val - 1 - time.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n time ans : Std.I64)
        (hn : 2 ≤ n.val) (hn_ub : n.val ≤ 1000)
        (ht : 1 ≤ time.val) (ht_ub : time.val ≤ 1000)
        (hnt : n.val ≤ time.val)
        (htn : time.val ≤ 2 * (n.val - 1))
        (hres : Aegis.PassThePillow.pass_the_pillow n time = ok ans), ans.val = 2 * n.val - 1 - time.val) := by
    sorry

  /-- Whenever pass_the_pillow 2 time returns a result ans, ans = 1 if time is even, and ans = 2 if time is odd.
    Preconditions: n = 2 and 1 <= time <= 1000. -/
  theorem spec_6 (time ans : Std.I64)
      (ht : 1 ≤ time.val) (ht_ub : time.val ≤ 1000)
      (hres : Aegis.PassThePillow.pass_the_pillow 2#i64 time = ok ans) :
      ans.val = if time.val % 2 = 0 then 1 else 2 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (time ans : Std.I64)
        (ht : 1 ≤ time.val) (ht_ub : time.val ≤ 1000)
        (hres : Aegis.PassThePillow.pass_the_pillow 2#i64 time = ok ans), ans.val = if time.val % 2 = 0 then 1 else 2) := by
    sorry

  /-- If t1 ≡ t2 (mod 2*(n-1)), then whenever pass_the_pillow n t1 returns ans1 and pass_the_pillow n t2 returns ans2, we have ans1 = ans2.
    Preconditions: n is an integer with 2 <= n <= 1000, and t1, t2 are integers with 1 <= t1 <= 1000 and 1 <= t2 <= 1000. -/
  theorem spec_7 (n t1 t2 ans1 ans2 : Std.I64)
      (hn : 2 ≤ n.val) (hn_ub : n.val ≤ 1000)
      (ht1 : 1 ≤ t1.val) (ht1_ub : t1.val ≤ 1000)
      (ht2 : 1 ≤ t2.val) (ht2_ub : t2.val ≤ 1000)
      (hmod : t1.val ≡ t2.val [ZMOD period n.val])
      (h1 : Aegis.PassThePillow.pass_the_pillow n t1 = ok ans1)
      (h2 : Aegis.PassThePillow.pass_the_pillow n t2 = ok ans2) :
      ans1.val = ans2.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n t1 t2 ans1 ans2 : Std.I64)
        (hn : 2 ≤ n.val) (hn_ub : n.val ≤ 1000)
        (ht1 : 1 ≤ t1.val) (ht1_ub : t1.val ≤ 1000)
        (ht2 : 1 ≤ t2.val) (ht2_ub : t2.val ≤ 1000)
        (hmod : t1.val ≡ t2.val [ZMOD period n.val])
        (h1 : Aegis.PassThePillow.pass_the_pillow n t1 = ok ans1)
        (h2 : Aegis.PassThePillow.pass_the_pillow n t2 = ok ans2), ans1.val = ans2.val) := by
    sorry

  /-- If t1 + t2 ≡ 0 (mod 2*(n-1)), then whenever pass_the_pillow n t1 returns ans1 and pass_the_pillow n t2 returns ans2, we have ans1 = ans2.
    Preconditions: n is an integer with 2 <= n <= 1000, and t1, t2 are integers with 1 <= t1 <= 1000 and 1 <= t2 <= 1000. -/
  theorem spec_8 (n t1 t2 ans1 ans2 : Std.I64)
      (hn : 2 ≤ n.val) (hn_ub : n.val ≤ 1000)
      (ht1 : 1 ≤ t1.val) (ht1_ub : t1.val ≤ 1000)
      (ht2 : 1 ≤ t2.val) (ht2_ub : t2.val ≤ 1000)
      (hmod : t1.val + t2.val ≡ 0 [ZMOD period n.val])
      (h1 : Aegis.PassThePillow.pass_the_pillow n t1 = ok ans1)
      (h2 : Aegis.PassThePillow.pass_the_pillow n t2 = ok ans2) :
      ans1.val = ans2.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n t1 t2 ans1 ans2 : Std.I64)
        (hn : 2 ≤ n.val) (hn_ub : n.val ≤ 1000)
        (ht1 : 1 ≤ t1.val) (ht1_ub : t1.val ≤ 1000)
        (ht2 : 1 ≤ t2.val) (ht2_ub : t2.val ≤ 1000)
        (hmod : t1.val + t2.val ≡ 0 [ZMOD period n.val])
        (h1 : Aegis.PassThePillow.pass_the_pillow n t1 = ok ans1)
        (h2 : Aegis.PassThePillow.pass_the_pillow n t2 = ok ans2), ans1.val = ans2.val) := by
    sorry

  /-- Whenever pass_the_pillow n time returns a result ans, ans = n if and only if time ≡ n-1 (mod 2*(n-1)).
    Preconditions: n and time are integers with 2 <= n <= 1000 and 1 <= time <= 1000. -/
  theorem spec_9 (n time ans : Std.I64)
      (hn : 2 ≤ n.val) (hn_ub : n.val ≤ 1000)
      (ht : 1 ≤ time.val) (ht_ub : time.val ≤ 1000)
      (hres : Aegis.PassThePillow.pass_the_pillow n time = ok ans) :
      (ans.val = n.val) ↔ time.val ≡ n.val - 1 [ZMOD period n.val] := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n time ans : Std.I64)
        (hn : 2 ≤ n.val) (hn_ub : n.val ≤ 1000)
        (ht : 1 ≤ time.val) (ht_ub : time.val ≤ 1000)
        (hres : Aegis.PassThePillow.pass_the_pillow n time = ok ans), (ans.val = n.val) ↔ time.val ≡ n.val - 1 [ZMOD period n.val]) := by
    sorry

  /-- Whenever pass_the_pillow n time returns a result ans, ans = 1 if and only if time ≡ 0 (mod 2*(n-1)).
    Preconditions: n and time are integers with 2 <= n <= 1000 and 1 <= time <= 1000. -/
  theorem spec_10 (n time ans : Std.I64)
      (hn : 2 ≤ n.val) (hn_ub : n.val ≤ 1000)
      (ht : 1 ≤ time.val) (ht_ub : time.val ≤ 1000)
      (hres : Aegis.PassThePillow.pass_the_pillow n time = ok ans) :
      (ans.val = 1) ↔ time.val ≡ 0 [ZMOD period n.val] := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n time ans : Std.I64)
        (hn : 2 ≤ n.val) (hn_ub : n.val ≤ 1000)
        (ht : 1 ≤ time.val) (ht_ub : time.val ≤ 1000)
        (hres : Aegis.PassThePillow.pass_the_pillow n time = ok ans), (ans.val = 1) ↔ time.val ≡ 0 [ZMOD period n.val]) := by
    sorry

  /-- Let P = 2*(n-1). Whenever pass_the_pillow n time returns a result ans, ans = 2 if and only if time ≡ 1 (mod P) or time ≡ P-1 (mod P).
    Preconditions: n and time are integers with 2 <= n <= 1000 and 1 <= time <= 1000. -/
  theorem spec_11 (n time ans : Std.I64)
      (hn : 2 ≤ n.val) (hn_ub : n.val ≤ 1000)
      (ht : 1 ≤ time.val) (ht_ub : time.val ≤ 1000)
      (hres : Aegis.PassThePillow.pass_the_pillow n time = ok ans) :
      (ans.val = 2) ↔
        (time.val ≡ 1 [ZMOD period n.val] ∨
          time.val ≡ period n.val - 1 [ZMOD period n.val]) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n time ans : Std.I64)
        (hn : 2 ≤ n.val) (hn_ub : n.val ≤ 1000)
        (ht : 1 ≤ time.val) (ht_ub : time.val ≤ 1000)
        (hres : Aegis.PassThePillow.pass_the_pillow n time = ok ans), (ans.val = 2) ↔
          (time.val ≡ 1 [ZMOD period n.val] ∨
            time.val ≡ period n.val - 1 [ZMOD period n.val])) := by
    sorry

  end AegisSpec.PassThePillow

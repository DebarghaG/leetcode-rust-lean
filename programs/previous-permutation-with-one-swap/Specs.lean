import Aegis.PrevPermOpt1.Code.Funs

/-!
# Specifications of `Aegis.PrevPermOpt1.prev_perm_opt1`

LeetCode problem `previous-permutation-with-one-swap`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.PrevPermOpt1

  open Aegis.PrevPermOpt1

  def sliceVals (arr : Slice Std.I64) : List ℤ := arr.val.map (fun x => x.val)

  def vecVals (r : alloc.vec.Vec Std.I64) : List ℤ := r.val.map (fun x => x.val)

  @[simp]
  theorem sliceVals_length (arr : Slice Std.I64) :
      (sliceVals arr).length = arr.val.length := by
    simp [sliceVals]

  @[simp]
  theorem vecVals_length (r : alloc.vec.Vec Std.I64) :
      (vecVals r).length = r.val.length := by
    simp [vecVals]

  def elemAt (l : List ℤ) (i : ℕ) : ℤ := l.getD i 0

  def Nondecreasing (l : List ℤ) : Prop := l.Pairwise (· ≤ ·)

  def StrictlyDecreasing (l : List ℤ) : Prop := l.Pairwise (· > ·)

  def HasInversion (l : List ℤ) : Prop :=
    ∃ (i j : ℕ), i < j ∧ j < l.length ∧ elemAt l j < elemAt l i

  def IsSwap (a b : List ℤ) : Prop :=
    ∃ (p q : ℕ), p < q ∧ q < a.length ∧ b.length = a.length ∧
      elemAt b p = elemAt a q ∧ elemAt b q = elemAt a p ∧
      ∀ (k : ℕ), k < a.length → k ≠ p → k ≠ q → elemAt b k = elemAt a k

  def LexLt (s t : List ℤ) : Prop :=
    ∃ (k : ℕ), k < s.length ∧ k < t.length ∧
      (∀ (i : ℕ), i < k → elemAt s i = elemAt t i) ∧ elemAt s k < elemAt t k

  def LexLe (s t : List ℤ) : Prop := s = t ∨ LexLt s t

  def countOcc (l : List ℤ) (v : ℤ) : ℕ := l.countP (fun x => decide (x = v))

  /-- The function returns a result r such that len(r) = len(arr) and: (a) if there are indices 0 <= i < j < len(arr) with arr[i] > arr[j], then r is the lexicographically largest vector s with len(s)=len(arr) such that s is obtainable from arr by swapping two distinct positions and s <_lex arr; (b) if no such pair of indices exists (equivalently arr[0] <= arr[1] <= ... <= arr[len(arr)-1]), then r = arr. Here s <_lex arr means there is an index k with 0 <= k < len(arr) such that s[t]=arr[t] for every t with 0 <= t < k and s[k] < arr[k]. A vector s is obtainable from arr by swapping two distinct positions if there exist p and q with 0 <= p < q < len(arr) such that s[p]=arr[q], s[q]=arr[p], and s[t]=arr[t] for every t with 0 <= t < len(arr) and t not in {p,q}.
    Preconditions: 1 <= len(arr) <= 10000 and for every index i with 0 <= i < len(arr), 1 <= arr[i] <= 10000. -/
  theorem spec_1 (arr : Slice Std.I64)
      (hpos : 1 ≤ (sliceVals arr).length) (hlen : (sliceVals arr).length ≤ 10000)
      (hbounds : ∀ (i : ℕ), i < (sliceVals arr).length →
        1 ≤ elemAt (sliceVals arr) i ∧ elemAt (sliceVals arr) i ≤ 10000) :
      ∃ r, prev_perm_opt1 arr = ok r ∧ (vecVals r).length = (sliceVals arr).length ∧
        (HasInversion (sliceVals arr) →
          IsSwap (sliceVals arr) (vecVals r) ∧ LexLt (vecVals r) (sliceVals arr) ∧
            (∀ (s : List ℤ), s.length = (sliceVals arr).length → IsSwap (sliceVals arr) s →
              LexLt s (sliceVals arr) → LexLe s (vecVals r))) ∧
        (¬ HasInversion (sliceVals arr) → vecVals r = sliceVals arr) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hpos : 1 ≤ (sliceVals arr).length) (hlen : (sliceVals arr).length ≤ 10000)
        (hbounds : ∀ (i : ℕ), i < (sliceVals arr).length →
          1 ≤ elemAt (sliceVals arr) i ∧ elemAt (sliceVals arr) i ≤ 10000), ∃ r, prev_perm_opt1 arr = ok r ∧ (vecVals r).length = (sliceVals arr).length ∧
          (HasInversion (sliceVals arr) →
            IsSwap (sliceVals arr) (vecVals r) ∧ LexLt (vecVals r) (sliceVals arr) ∧
              (∀ (s : List ℤ), s.length = (sliceVals arr).length → IsSwap (sliceVals arr) s →
                LexLt s (sliceVals arr) → LexLe s (vecVals r))) ∧
          (¬ HasInversion (sliceVals arr) → vecVals r = sliceVals arr)) := by
    sorry

  /-- The function returns a result r for every input satisfying the preconditions; it does not fail, panic, or overflow.
    Preconditions: 1 <= len(arr) <= 10000 and for every index i with 0 <= i < len(arr), 1 <= arr[i] <= 10000. -/
  theorem spec_2 (arr : Slice Std.I64)
      (hpos : 1 ≤ (sliceVals arr).length) (hlen : (sliceVals arr).length ≤ 10000)
      (hbounds : ∀ (i : ℕ), i < (sliceVals arr).length →
        1 ≤ elemAt (sliceVals arr) i ∧ elemAt (sliceVals arr) i ≤ 10000) :
      ∃ r, prev_perm_opt1 arr = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hpos : 1 ≤ (sliceVals arr).length) (hlen : (sliceVals arr).length ≤ 10000)
        (hbounds : ∀ (i : ℕ), i < (sliceVals arr).length →
          1 ≤ elemAt (sliceVals arr) i ∧ elemAt (sliceVals arr) i ≤ 10000), ∃ r, prev_perm_opt1 arr = ok r) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = len(arr).
    Preconditions: 1 <= len(arr) <= 10000 and for every index i with 0 <= i < len(arr), 1 <= arr[i] <= 10000. -/
  theorem spec_3 (arr : Slice Std.I64)
      (hpos : 1 ≤ (sliceVals arr).length) (hlen : (sliceVals arr).length ≤ 10000)
      (hbounds : ∀ (i : ℕ), i < (sliceVals arr).length →
        1 ≤ elemAt (sliceVals arr) i ∧ elemAt (sliceVals arr) i ≤ 10000) :
      ∀ r, prev_perm_opt1 arr = ok r → (vecVals r).length = (sliceVals arr).length := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hpos : 1 ≤ (sliceVals arr).length) (hlen : (sliceVals arr).length ≤ 10000)
        (hbounds : ∀ (i : ℕ), i < (sliceVals arr).length →
          1 ≤ elemAt (sliceVals arr) i ∧ elemAt (sliceVals arr) i ≤ 10000), ∀ r, prev_perm_opt1 arr = ok r → (vecVals r).length = (sliceVals arr).length) := by
    sorry

  /-- Whenever the function returns a result r, r is a permutation of arr: for every integer value v, the number of indices i with 0 <= i < len(arr) and arr[i] = v equals the number of indices i with 0 <= i < len(r) and r[i] = v.
    Preconditions: 1 <= len(arr) <= 10000 and for every index i with 0 <= i < len(arr), 1 <= arr[i] <= 10000. -/
  theorem spec_4 (arr : Slice Std.I64)
      (hpos : 1 ≤ (sliceVals arr).length) (hlen : (sliceVals arr).length ≤ 10000)
      (hbounds : ∀ (i : ℕ), i < (sliceVals arr).length →
        1 ≤ elemAt (sliceVals arr) i ∧ elemAt (sliceVals arr) i ≤ 10000) :
      ∀ r, prev_perm_opt1 arr = ok r →
        ∀ v : ℤ, countOcc (vecVals r) v = countOcc (sliceVals arr) v := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hpos : 1 ≤ (sliceVals arr).length) (hlen : (sliceVals arr).length ≤ 10000)
        (hbounds : ∀ (i : ℕ), i < (sliceVals arr).length →
          1 ≤ elemAt (sliceVals arr) i ∧ elemAt (sliceVals arr) i ≤ 10000), ∀ r, prev_perm_opt1 arr = ok r →
          ∀ v : ℤ, countOcc (vecVals r) v = countOcc (sliceVals arr) v) := by
    sorry

  /-- Whenever the function returns a result r, for every index i with 0 <= i < len(r), we have 1 <= r[i] <= 10000.
    Preconditions: 1 <= len(arr) <= 10000 and for every index i with 0 <= i < len(arr), 1 <= arr[i] <= 10000. -/
  theorem spec_5 (arr : Slice Std.I64)
      (hpos : 1 ≤ (sliceVals arr).length) (hlen : (sliceVals arr).length ≤ 10000)
      (hbounds : ∀ (i : ℕ), i < (sliceVals arr).length →
        1 ≤ elemAt (sliceVals arr) i ∧ elemAt (sliceVals arr) i ≤ 10000) :
      ∀ r, prev_perm_opt1 arr = ok r →
        ∀ (i : ℕ), i < (vecVals r).length →
          1 ≤ elemAt (vecVals r) i ∧ elemAt (vecVals r) i ≤ 10000 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hpos : 1 ≤ (sliceVals arr).length) (hlen : (sliceVals arr).length ≤ 10000)
        (hbounds : ∀ (i : ℕ), i < (sliceVals arr).length →
          1 ≤ elemAt (sliceVals arr) i ∧ elemAt (sliceVals arr) i ≤ 10000), ∀ r, prev_perm_opt1 arr = ok r →
          ∀ (i : ℕ), i < (vecVals r).length →
            1 ≤ elemAt (vecVals r) i ∧ elemAt (vecVals r) i ≤ 10000) := by
    sorry

  /-- If arr is nondecreasing, meaning arr[0] <= arr[1] <= ... <= arr[len(arr)-1] (the condition is vacuous when len(arr)=1), then the function returns r with r = arr.
    Preconditions: 1 <= len(arr) <= 10000 and for every index i with 0 <= i < len(arr), 1 <= arr[i] <= 10000. -/
  theorem spec_6 (arr : Slice Std.I64)
      (hpos : 1 ≤ (sliceVals arr).length) (hlen : (sliceVals arr).length ≤ 10000)
      (hbounds : ∀ (i : ℕ), i < (sliceVals arr).length →
        1 ≤ elemAt (sliceVals arr) i ∧ elemAt (sliceVals arr) i ≤ 10000)
      (hnd : Nondecreasing (sliceVals arr)) :
      ∃ r, prev_perm_opt1 arr = ok r ∧ vecVals r = sliceVals arr := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hpos : 1 ≤ (sliceVals arr).length) (hlen : (sliceVals arr).length ≤ 10000)
        (hbounds : ∀ (i : ℕ), i < (sliceVals arr).length →
          1 ≤ elemAt (sliceVals arr) i ∧ elemAt (sliceVals arr) i ≤ 10000)
        (hnd : Nondecreasing (sliceVals arr)), ∃ r, prev_perm_opt1 arr = ok r ∧ vecVals r = sliceVals arr) := by
    sorry

  /-- If there exist indices 0 <= i < j < len(arr) with arr[i] > arr[j], then the function returns r with r <_lex arr, where r <_lex arr means there is an index k with 0 <= k < len(arr) such that r[t]=arr[t] for every t with 0 <= t < k and r[k] < arr[k].
    Preconditions: 1 <= len(arr) <= 10000 and for every index i with 0 <= i < len(arr), 1 <= arr[i] <= 10000. -/
  theorem spec_7 (arr : Slice Std.I64)
      (hpos : 1 ≤ (sliceVals arr).length) (hlen : (sliceVals arr).length ≤ 10000)
      (hbounds : ∀ (i : ℕ), i < (sliceVals arr).length →
        1 ≤ elemAt (sliceVals arr) i ∧ elemAt (sliceVals arr) i ≤ 10000)
      (hinv : HasInversion (sliceVals arr)) :
      ∃ r, prev_perm_opt1 arr = ok r ∧ LexLt (vecVals r) (sliceVals arr) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hpos : 1 ≤ (sliceVals arr).length) (hlen : (sliceVals arr).length ≤ 10000)
        (hbounds : ∀ (i : ℕ), i < (sliceVals arr).length →
          1 ≤ elemAt (sliceVals arr) i ∧ elemAt (sliceVals arr) i ≤ 10000)
        (hinv : HasInversion (sliceVals arr)), ∃ r, prev_perm_opt1 arr = ok r ∧ LexLt (vecVals r) (sliceVals arr)) := by
    sorry

  /-- If there exist indices 0 <= i < j < len(arr) with arr[i] > arr[j], let i0 be the largest index with 0 <= i0 < len(arr)-1 and arr[i0] > arr[i0+1]. Then the function returns r such that r[k] = arr[k] for every k with 0 <= k < i0, and r[i0] < arr[i0].
    Preconditions: 1 <= len(arr) <= 10000 and for every index i with 0 <= i < len(arr), 1 <= arr[i] <= 10000. -/
  theorem spec_8 (arr : Slice Std.I64)
      (hpos : 1 ≤ (sliceVals arr).length) (hlen : (sliceVals arr).length ≤ 10000)
      (hbounds : ∀ (i : ℕ), i < (sliceVals arr).length →
        1 ≤ elemAt (sliceVals arr) i ∧ elemAt (sliceVals arr) i ≤ 10000)
      (hinv : HasInversion (sliceVals arr))
      (i0 : ℕ) (hi0 : i0 + 1 < (sliceVals arr).length)
      (hpiv : elemAt (sliceVals arr) (i0 + 1) < elemAt (sliceVals arr) i0)
      (hmax : ∀ (k : ℕ), k + 1 < (sliceVals arr).length →
        elemAt (sliceVals arr) (k + 1) < elemAt (sliceVals arr) k → k ≤ i0) :
      ∃ r, prev_perm_opt1 arr = ok r ∧ (vecVals r).length = (sliceVals arr).length ∧
        (∀ (k : ℕ), k < i0 → elemAt (vecVals r) k = elemAt (sliceVals arr) k) ∧
        elemAt (vecVals r) i0 < elemAt (sliceVals arr) i0 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hpos : 1 ≤ (sliceVals arr).length) (hlen : (sliceVals arr).length ≤ 10000)
        (hbounds : ∀ (i : ℕ), i < (sliceVals arr).length →
          1 ≤ elemAt (sliceVals arr) i ∧ elemAt (sliceVals arr) i ≤ 10000)
        (hinv : HasInversion (sliceVals arr))
        (i0 : ℕ) (hi0 : i0 + 1 < (sliceVals arr).length)
        (hpiv : elemAt (sliceVals arr) (i0 + 1) < elemAt (sliceVals arr) i0)
        (hmax : ∀ (k : ℕ), k + 1 < (sliceVals arr).length →
          elemAt (sliceVals arr) (k + 1) < elemAt (sliceVals arr) k → k ≤ i0), ∃ r, prev_perm_opt1 arr = ok r ∧ (vecVals r).length = (sliceVals arr).length ∧
          (∀ (k : ℕ), k < i0 → elemAt (vecVals r) k = elemAt (sliceVals arr) k) ∧
          elemAt (vecVals r) i0 < elemAt (sliceVals arr) i0) := by
    sorry

  /-- If there exist indices 0 <= i < j < len(arr) with arr[i] > arr[j], let i0 be the largest index with 0 <= i0 < len(arr)-1 and arr[i0] > arr[i0+1], and let v be the largest value in the set { arr[j] | i0 < j < len(arr) and arr[j] < arr[i0] }. Then the function returns r with r[i0] = v. Equivalently, r[i0] < arr[i0], there exists j with i0 < j < len(arr) and arr[j] = r[i0], and for every j with i0 < j < len(arr) and arr[j] < arr[i0], we have arr[j] <= r[i0].
    Preconditions: 1 <= len(arr) <= 10000 and for every index i with 0 <= i < len(arr), 1 <= arr[i] <= 10000. -/
  theorem spec_9 (arr : Slice Std.I64)
      (hpos : 1 ≤ (sliceVals arr).length) (hlen : (sliceVals arr).length ≤ 10000)
      (hbounds : ∀ (i : ℕ), i < (sliceVals arr).length →
        1 ≤ elemAt (sliceVals arr) i ∧ elemAt (sliceVals arr) i ≤ 10000)
      (hinv : HasInversion (sliceVals arr))
      (i0 : ℕ) (hi0 : i0 + 1 < (sliceVals arr).length)
      (hpiv : elemAt (sliceVals arr) (i0 + 1) < elemAt (sliceVals arr) i0)
      (hmax : ∀ (k : ℕ), k + 1 < (sliceVals arr).length →
        elemAt (sliceVals arr) (k + 1) < elemAt (sliceVals arr) k → k ≤ i0) :
      ∃ r, prev_perm_opt1 arr = ok r ∧ (vecVals r).length = (sliceVals arr).length ∧
        elemAt (vecVals r) i0 < elemAt (sliceVals arr) i0 ∧
        (∃ j, i0 < j ∧ j < (sliceVals arr).length ∧
          elemAt (sliceVals arr) j = elemAt (vecVals r) i0) ∧
        (∀ (j : ℕ), i0 < j → j < (sliceVals arr).length →
          elemAt (sliceVals arr) j < elemAt (sliceVals arr) i0 →
          elemAt (sliceVals arr) j ≤ elemAt (vecVals r) i0) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hpos : 1 ≤ (sliceVals arr).length) (hlen : (sliceVals arr).length ≤ 10000)
        (hbounds : ∀ (i : ℕ), i < (sliceVals arr).length →
          1 ≤ elemAt (sliceVals arr) i ∧ elemAt (sliceVals arr) i ≤ 10000)
        (hinv : HasInversion (sliceVals arr))
        (i0 : ℕ) (hi0 : i0 + 1 < (sliceVals arr).length)
        (hpiv : elemAt (sliceVals arr) (i0 + 1) < elemAt (sliceVals arr) i0)
        (hmax : ∀ (k : ℕ), k + 1 < (sliceVals arr).length →
          elemAt (sliceVals arr) (k + 1) < elemAt (sliceVals arr) k → k ≤ i0), ∃ r, prev_perm_opt1 arr = ok r ∧ (vecVals r).length = (sliceVals arr).length ∧
          elemAt (vecVals r) i0 < elemAt (sliceVals arr) i0 ∧
          (∃ j, i0 < j ∧ j < (sliceVals arr).length ∧
            elemAt (sliceVals arr) j = elemAt (vecVals r) i0) ∧
          (∀ (j : ℕ), i0 < j → j < (sliceVals arr).length →
            elemAt (sliceVals arr) j < elemAt (sliceVals arr) i0 →
            elemAt (sliceVals arr) j ≤ elemAt (vecVals r) i0)) := by
    sorry

  /-- If there exist indices 0 <= i < j < len(arr) with arr[i] > arr[j], let i0 be the largest index with 0 <= i0 < len(arr)-1 and arr[i0] > arr[i0+1], let v be the largest value in { arr[j] | i0 < j < len(arr) and arr[j] < arr[i0] }, and let j0 be the smallest index with i0 < j0 < len(arr) and arr[j0] = v. Then the function returns r such that r[i0] = arr[j0], r[j0] = arr[i0], and r[k] = arr[k] for every k with 0 <= k < len(arr) and k not in {i0,j0}.
    Preconditions: 1 <= len(arr) <= 10000 and for every index i with 0 <= i < len(arr), 1 <= arr[i] <= 10000. -/
  theorem spec_10 (arr : Slice Std.I64)
      (hpos : 1 ≤ (sliceVals arr).length) (hlen : (sliceVals arr).length ≤ 10000)
      (hbounds : ∀ (i : ℕ), i < (sliceVals arr).length →
        1 ≤ elemAt (sliceVals arr) i ∧ elemAt (sliceVals arr) i ≤ 10000)
      (hinv : HasInversion (sliceVals arr))
      (i0 : ℕ) (hi0 : i0 + 1 < (sliceVals arr).length)
      (hpiv : elemAt (sliceVals arr) (i0 + 1) < elemAt (sliceVals arr) i0)
      (hmax : ∀ (k : ℕ), k + 1 < (sliceVals arr).length →
        elemAt (sliceVals arr) (k + 1) < elemAt (sliceVals arr) k → k ≤ i0)
      (v : ℤ) (j0 : ℕ)
      (hj0_lo : i0 < j0) (hj0_hi : j0 < (sliceVals arr).length)
      (hj0_v : elemAt (sliceVals arr) j0 = v)
      (hv_lt : v < elemAt (sliceVals arr) i0)
      (hv_max : ∀ (j : ℕ), i0 < j → j < (sliceVals arr).length →
        elemAt (sliceVals arr) j < elemAt (sliceVals arr) i0 → elemAt (sliceVals arr) j ≤ v)
      (hj0_min : ∀ (j : ℕ), i0 < j → j < j0 → elemAt (sliceVals arr) j ≠ v) :
      ∃ r, prev_perm_opt1 arr = ok r ∧ (vecVals r).length = (sliceVals arr).length ∧
        elemAt (vecVals r) i0 = elemAt (sliceVals arr) j0 ∧
        elemAt (vecVals r) j0 = elemAt (sliceVals arr) i0 ∧
        ∀ (k : ℕ), k < (sliceVals arr).length → k ≠ i0 → k ≠ j0 →
          elemAt (vecVals r) k = elemAt (sliceVals arr) k := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hpos : 1 ≤ (sliceVals arr).length) (hlen : (sliceVals arr).length ≤ 10000)
        (hbounds : ∀ (i : ℕ), i < (sliceVals arr).length →
          1 ≤ elemAt (sliceVals arr) i ∧ elemAt (sliceVals arr) i ≤ 10000)
        (hinv : HasInversion (sliceVals arr))
        (i0 : ℕ) (hi0 : i0 + 1 < (sliceVals arr).length)
        (hpiv : elemAt (sliceVals arr) (i0 + 1) < elemAt (sliceVals arr) i0)
        (hmax : ∀ (k : ℕ), k + 1 < (sliceVals arr).length →
          elemAt (sliceVals arr) (k + 1) < elemAt (sliceVals arr) k → k ≤ i0)
        (v : ℤ) (j0 : ℕ)
        (hj0_lo : i0 < j0) (hj0_hi : j0 < (sliceVals arr).length)
        (hj0_v : elemAt (sliceVals arr) j0 = v)
        (hv_lt : v < elemAt (sliceVals arr) i0)
        (hv_max : ∀ (j : ℕ), i0 < j → j < (sliceVals arr).length →
          elemAt (sliceVals arr) j < elemAt (sliceVals arr) i0 → elemAt (sliceVals arr) j ≤ v)
        (hj0_min : ∀ (j : ℕ), i0 < j → j < j0 → elemAt (sliceVals arr) j ≠ v), ∃ r, prev_perm_opt1 arr = ok r ∧ (vecVals r).length = (sliceVals arr).length ∧
          elemAt (vecVals r) i0 = elemAt (sliceVals arr) j0 ∧
          elemAt (vecVals r) j0 = elemAt (sliceVals arr) i0 ∧
          ∀ (k : ℕ), k < (sliceVals arr).length → k ≠ i0 → k ≠ j0 →
            elemAt (vecVals r) k = elemAt (sliceVals arr) k) := by
    sorry

  /-- Whenever the function returns a result r, for every vector s with len(s)=len(arr) for which there exist p and q with 0 <= p < q < len(arr) such that s[p]=arr[q], s[q]=arr[p], and s[t]=arr[t] for every t not in {p,q}, and for which s <_lex arr (i.e. there is k with 0 <= k < len(arr), s[t]=arr[t] for all t<k, and s[k]<arr[k]), we have s <=_lex r, where s <=_lex r means either s=r or there is k with 0 <= k < len(arr), s[t]=r[t] for all t<k, and s[k]<r[k].
    Preconditions: 1 <= len(arr) <= 10000 and for every index i with 0 <= i < len(arr), 1 <= arr[i] <= 10000. -/
  theorem spec_11 (arr : Slice Std.I64)
      (hpos : 1 ≤ (sliceVals arr).length) (hlen : (sliceVals arr).length ≤ 10000)
      (hbounds : ∀ (i : ℕ), i < (sliceVals arr).length →
        1 ≤ elemAt (sliceVals arr) i ∧ elemAt (sliceVals arr) i ≤ 10000) :
      ∀ r, prev_perm_opt1 arr = ok r →
        ∀ (s : List ℤ), s.length = (sliceVals arr).length → IsSwap (sliceVals arr) s →
          LexLt s (sliceVals arr) → LexLe s (vecVals r) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hpos : 1 ≤ (sliceVals arr).length) (hlen : (sliceVals arr).length ≤ 10000)
        (hbounds : ∀ (i : ℕ), i < (sliceVals arr).length →
          1 ≤ elemAt (sliceVals arr) i ∧ elemAt (sliceVals arr) i ≤ 10000), ∀ r, prev_perm_opt1 arr = ok r →
          ∀ (s : List ℤ), s.length = (sliceVals arr).length → IsSwap (sliceVals arr) s →
            LexLt s (sliceVals arr) → LexLe s (vecVals r)) := by
    sorry

  /-- Whenever the function returns a result r, r = arr if and only if arr is nondecreasing, meaning arr[0] <= arr[1] <= ... <= arr[len(arr)-1].
    Preconditions: 1 <= len(arr) <= 10000 and for every index i with 0 <= i < len(arr), 1 <= arr[i] <= 10000. -/
  theorem spec_12 (arr : Slice Std.I64)
      (hpos : 1 ≤ (sliceVals arr).length) (hlen : (sliceVals arr).length ≤ 10000)
      (hbounds : ∀ (i : ℕ), i < (sliceVals arr).length →
        1 ≤ elemAt (sliceVals arr) i ∧ elemAt (sliceVals arr) i ≤ 10000) :
      ∀ r, prev_perm_opt1 arr = ok r →
        (vecVals r = sliceVals arr ↔ Nondecreasing (sliceVals arr)) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hpos : 1 ≤ (sliceVals arr).length) (hlen : (sliceVals arr).length ≤ 10000)
        (hbounds : ∀ (i : ℕ), i < (sliceVals arr).length →
          1 ≤ elemAt (sliceVals arr) i ∧ elemAt (sliceVals arr) i ≤ 10000), ∀ r, prev_perm_opt1 arr = ok r →
          (vecVals r = sliceVals arr ↔ Nondecreasing (sliceVals arr))) := by
    sorry

  /-- If len(arr) = 1, then the function returns r with len(r)=1 and r[0] = arr[0].
    Preconditions: 1 <= len(arr) <= 10000 and for every index i with 0 <= i < len(arr), 1 <= arr[i] <= 10000. -/
  theorem spec_13 (arr : Slice Std.I64)
      (hpos : 1 ≤ (sliceVals arr).length) (hlen : (sliceVals arr).length ≤ 10000)
      (hbounds : ∀ (i : ℕ), i < (sliceVals arr).length →
        1 ≤ elemAt (sliceVals arr) i ∧ elemAt (sliceVals arr) i ≤ 10000)
      (h1 : (sliceVals arr).length = 1) :
      ∃ r, prev_perm_opt1 arr = ok r ∧ (vecVals r).length = 1 ∧
        elemAt (vecVals r) 0 = elemAt (sliceVals arr) 0 := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hpos : 1 ≤ (sliceVals arr).length) (hlen : (sliceVals arr).length ≤ 10000)
        (hbounds : ∀ (i : ℕ), i < (sliceVals arr).length →
          1 ≤ elemAt (sliceVals arr) i ∧ elemAt (sliceVals arr) i ≤ 10000)
        (h1 : (sliceVals arr).length = 1), ∃ r, prev_perm_opt1 arr = ok r ∧ (vecVals r).length = 1 ∧
          elemAt (vecVals r) 0 = elemAt (sliceVals arr) 0) := by
    sorry

  /-- If len(arr) >= 2 and arr[0] > arr[1] > ... > arr[len(arr)-1], then the function returns r such that r[k] = arr[k] for every k with 0 <= k < len(arr)-2, r[len(arr)-2] = arr[len(arr)-1], and r[len(arr)-1] = arr[len(arr)-2].
    Preconditions: 1 <= len(arr) <= 10000 and for every index i with 0 <= i < len(arr), 1 <= arr[i] <= 10000. -/
  theorem spec_14 (arr : Slice Std.I64)
      (hpos : 1 ≤ (sliceVals arr).length) (hlen : (sliceVals arr).length ≤ 10000)
      (hbounds : ∀ (i : ℕ), i < (sliceVals arr).length →
        1 ≤ elemAt (sliceVals arr) i ∧ elemAt (sliceVals arr) i ≤ 10000)
      (h2 : 2 ≤ (sliceVals arr).length)
      (hdec : StrictlyDecreasing (sliceVals arr)) :
      ∃ r, prev_perm_opt1 arr = ok r ∧ (vecVals r).length = (sliceVals arr).length ∧
        (∀ (k : ℕ), k < (sliceVals arr).length - 2 →
          elemAt (vecVals r) k = elemAt (sliceVals arr) k) ∧
        elemAt (vecVals r) ((sliceVals arr).length - 2) =
          elemAt (sliceVals arr) ((sliceVals arr).length - 1) ∧
        elemAt (vecVals r) ((sliceVals arr).length - 1) =
          elemAt (sliceVals arr) ((sliceVals arr).length - 2) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hpos : 1 ≤ (sliceVals arr).length) (hlen : (sliceVals arr).length ≤ 10000)
        (hbounds : ∀ (i : ℕ), i < (sliceVals arr).length →
          1 ≤ elemAt (sliceVals arr) i ∧ elemAt (sliceVals arr) i ≤ 10000)
        (h2 : 2 ≤ (sliceVals arr).length)
        (hdec : StrictlyDecreasing (sliceVals arr)), ∃ r, prev_perm_opt1 arr = ok r ∧ (vecVals r).length = (sliceVals arr).length ∧
          (∀ (k : ℕ), k < (sliceVals arr).length - 2 →
            elemAt (vecVals r) k = elemAt (sliceVals arr) k) ∧
          elemAt (vecVals r) ((sliceVals arr).length - 2) =
            elemAt (sliceVals arr) ((sliceVals arr).length - 1) ∧
          elemAt (vecVals r) ((sliceVals arr).length - 1) =
            elemAt (sliceVals arr) ((sliceVals arr).length - 2)) := by
    sorry

  /-- Whenever the function returns a result r, either r = arr or there exist indices p and q with 0 <= p < q < len(arr) such that r[p]=arr[q], r[q]=arr[p], and r[k]=arr[k] for every k with 0 <= k < len(arr) and k not in {p,q}.
    Preconditions: 1 <= len(arr) <= 10000 and for every index i with 0 <= i < len(arr), 1 <= arr[i] <= 10000. -/
  theorem spec_15 (arr : Slice Std.I64)
      (hpos : 1 ≤ (sliceVals arr).length) (hlen : (sliceVals arr).length ≤ 10000)
      (hbounds : ∀ (i : ℕ), i < (sliceVals arr).length →
        1 ≤ elemAt (sliceVals arr) i ∧ elemAt (sliceVals arr) i ≤ 10000) :
      ∀ r, prev_perm_opt1 arr = ok r →
        vecVals r = sliceVals arr ∨ IsSwap (sliceVals arr) (vecVals r) := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hpos : 1 ≤ (sliceVals arr).length) (hlen : (sliceVals arr).length ≤ 10000)
        (hbounds : ∀ (i : ℕ), i < (sliceVals arr).length →
          1 ≤ elemAt (sliceVals arr) i ∧ elemAt (sliceVals arr) i ≤ 10000), ∀ r, prev_perm_opt1 arr = ok r →
          vecVals r = sliceVals arr ∨ IsSwap (sliceVals arr) (vecVals r)) := by
    sorry

  /-- Whenever the function returns a result r, r <=_lex arr, where r <=_lex arr means either r = arr or there is an index k with 0 <= k < len(arr) such that r[t]=arr[t] for every t with 0 <= t < k and r[k] < arr[k].
    Preconditions: 1 <= len(arr) <= 10000 and for every index i with 0 <= i < len(arr), 1 <= arr[i] <= 10000. -/
  theorem spec_16 (arr : Slice Std.I64)
      (hpos : 1 ≤ (sliceVals arr).length) (hlen : (sliceVals arr).length ≤ 10000)
      (hbounds : ∀ (i : ℕ), i < (sliceVals arr).length →
        1 ≤ elemAt (sliceVals arr) i ∧ elemAt (sliceVals arr) i ≤ 10000) :
      ∀ r, prev_perm_opt1 arr = ok r → LexLe (vecVals r) (sliceVals arr) := by
    sorry

  theorem spec_16_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hpos : 1 ≤ (sliceVals arr).length) (hlen : (sliceVals arr).length ≤ 10000)
        (hbounds : ∀ (i : ℕ), i < (sliceVals arr).length →
          1 ≤ elemAt (sliceVals arr) i ∧ elemAt (sliceVals arr) i ≤ 10000), ∀ r, prev_perm_opt1 arr = ok r → LexLe (vecVals r) (sliceVals arr)) := by
    sorry

  /-- If there exist indices 0 <= i < j < len(arr) with arr[i] > arr[j], then the function returns r such that the set { k | 0 <= k < len(arr) and r[k] != arr[k] } has exactly two elements; writing them as p < q, we have r[p] = arr[q] < arr[p] and r[q] = arr[p] > arr[q].
    Preconditions: 1 <= len(arr) <= 10000 and for every index i with 0 <= i < len(arr), 1 <= arr[i] <= 10000. -/
  theorem spec_17 (arr : Slice Std.I64)
      (hpos : 1 ≤ (sliceVals arr).length) (hlen : (sliceVals arr).length ≤ 10000)
      (hbounds : ∀ (i : ℕ), i < (sliceVals arr).length →
        1 ≤ elemAt (sliceVals arr) i ∧ elemAt (sliceVals arr) i ≤ 10000)
      (hinv : HasInversion (sliceVals arr)) :
      ∀ r, prev_perm_opt1 arr = ok r →
        ∃ (p q : ℕ), p < q ∧ q < (sliceVals arr).length ∧
          elemAt (vecVals r) p = elemAt (sliceVals arr) q ∧
          elemAt (vecVals r) p < elemAt (sliceVals arr) p ∧
          elemAt (vecVals r) q = elemAt (sliceVals arr) p ∧
          elemAt (sliceVals arr) q < elemAt (vecVals r) q ∧
          (∀ (k : ℕ), k < (sliceVals arr).length → k ≠ p → k ≠ q →
            elemAt (vecVals r) k = elemAt (sliceVals arr) k) ∧
          (vecVals r).length = (sliceVals arr).length := by
    sorry

  theorem spec_17_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hpos : 1 ≤ (sliceVals arr).length) (hlen : (sliceVals arr).length ≤ 10000)
        (hbounds : ∀ (i : ℕ), i < (sliceVals arr).length →
          1 ≤ elemAt (sliceVals arr) i ∧ elemAt (sliceVals arr) i ≤ 10000)
        (hinv : HasInversion (sliceVals arr)), ∀ r, prev_perm_opt1 arr = ok r →
          ∃ (p q : ℕ), p < q ∧ q < (sliceVals arr).length ∧
            elemAt (vecVals r) p = elemAt (sliceVals arr) q ∧
            elemAt (vecVals r) p < elemAt (sliceVals arr) p ∧
            elemAt (vecVals r) q = elemAt (sliceVals arr) p ∧
            elemAt (sliceVals arr) q < elemAt (vecVals r) q ∧
            (∀ (k : ℕ), k < (sliceVals arr).length → k ≠ p → k ≠ q →
              elemAt (vecVals r) k = elemAt (sliceVals arr) k) ∧
            (vecVals r).length = (sliceVals arr).length) := by
    sorry

  end AegisSpec.PrevPermOpt1

import Aegis.ThreeSum.Code.Funs

/-!
# Specifications of `Aegis.ThreeSum.three_sum`

LeetCode problem `3sum`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.ThreeSum

  abbrev VecI64 : Type := Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64

  abbrev VecVecI64 : Type := Aeneas.Std.alloc.vec.Vec (Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64)

  abbrev SliceI64 : Type := Aeneas.Std.Slice Aeneas.Std.I64

  def vecVals (v : VecI64) : List Int := v.val.map fun x => x.val

  def vecIthVal (v : VecI64) (i : Nat) : Int := ((v.val[i]?).map fun x => x.val).getD 0

  def sliceVals (nums : SliceI64) : List Int := nums.val.map fun x => x.val

  def sliceIthVal (nums : SliceI64) (i : Nat) : Int := ((nums.val[i]?).map fun x => x.val).getD 0

  def ValidInput (nums : SliceI64) : Prop :=
    3 ≤ nums.val.length ∧ nums.val.length ≤ 3000 ∧
      ∀ i, i < nums.val.length →
        -100000 ≤ sliceIthVal nums i ∧ sliceIthVal nums i ≤ 100000

  def SameMultiset (l₁ l₂ : List Int) : Prop := l₁.Perm l₂

  def HasMultiset (t : List Int) (x y z : Int) : Prop := t.Perm [x, y, z]

  def Realized (nums : SliceI64) (x y z : Int) : Prop :=
    ∃ (i j k : Nat),
      i < nums.val.length ∧ j < nums.val.length ∧ k < nums.val.length ∧
        i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
          sliceIthVal nums i = x ∧ sliceIthVal nums j = y ∧ sliceIthVal nums k = z

  def distinctValues (nums : SliceI64) : Finset Int := (sliceVals nums).toFinset

  noncomputable def zeroSumMultisets (nums : SliceI64) : Finset (Int × Int × Int) :=
    by
    classical
    exact
      (((distinctValues nums).product ((distinctValues nums).product (distinctValues nums))).image
          (fun p : Int × Int × Int => (p.1, p.2.1, p.2.2))).filter
        (fun t : Int × Int × Int =>
          t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 ∧ t.1 + t.2.1 + t.2.2 = 0 ∧
            Realized nums t.1 t.2.1 t.2.2)

  noncomputable def zeroSumMultisetCount (nums : SliceI64) : Nat :=
    (zeroSumMultisets nums).card

  /-- The function returns a result r such that: (a) len(r[p]) = 3 for every p with 0 <= p < len(r); (b) for all p, q with 0 <= p < q < len(r), r[p] is not a permutation of r[q]; (c) for every multiset M of three integers, some element of r has M as its multiset of entries if and only if the three elements of M sum to 0 and there exist pairwise distinct indices i, j, k with 0 <= i, j, k < len(nums) and {nums[i], nums[j], nums[k]} = M.
    Preconditions: 3 <= len(nums) <= 3000, and for every i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000. -/
  theorem spec_1 (nums : SliceI64) (h : ValidInput nums) :
      ∃ r : VecVecI64,
        Aegis.ThreeSum.three_sum nums = ok r ∧
          (∀ (p : Nat) (hp : p < r.val.length), (r.val[p]).val.length = 3) ∧
          (∀ (p q : Nat) (hp : p < r.val.length) (hq : q < r.val.length), p < q →
            ¬ SameMultiset (vecVals r.val[p]) (vecVals r.val[q])) ∧
          (∀ x y z : Int,
            (∃ (p : Nat) (_hp : p < r.val.length), HasMultiset (vecVals r.val[p]) x y z) ↔
              (x + y + z = 0 ∧ Realized nums x y z)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : SliceI64) (h : ValidInput nums), ∃ r : VecVecI64,
          Aegis.ThreeSum.three_sum nums = ok r ∧
            (∀ (p : Nat) (hp : p < r.val.length), (r.val[p]).val.length = 3) ∧
            (∀ (p q : Nat) (hp : p < r.val.length) (hq : q < r.val.length), p < q →
              ¬ SameMultiset (vecVals r.val[p]) (vecVals r.val[q])) ∧
            (∀ x y z : Int,
              (∃ (p : Nat) (_hp : p < r.val.length), HasMultiset (vecVals r.val[p]) x y z) ↔
                (x + y + z = 0 ∧ Realized nums x y z))) := by
    sorry

  /-- Whenever the function returns a result r, every element of r has exactly three entries: for every p with 0 <= p < len(r), len(r[p]) = 3.
    Preconditions: 3 <= len(nums) <= 3000, and for every i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000. -/
  theorem spec_2 (nums : SliceI64) (h : ValidInput nums) (r : VecVecI64)
      (hr : Aegis.ThreeSum.three_sum nums = ok r) :
      ∀ (p : Nat) (hp : p < r.val.length), (r.val[p]).val.length = 3 := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : SliceI64) (h : ValidInput nums) (r : VecVecI64)
        (hr : Aegis.ThreeSum.three_sum nums = ok r), ∀ (p : Nat) (hp : p < r.val.length), (r.val[p]).val.length = 3) := by
    sorry

  /-- Whenever the function returns a result r, every triplet in r sums to zero: for every p with 0 <= p < len(r), r[p][0] + r[p][1] + r[p][2] = 0.
    Preconditions: 3 <= len(nums) <= 3000, and for every i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000. -/
  theorem spec_3 (nums : SliceI64) (h : ValidInput nums) (r : VecVecI64)
      (hr : Aegis.ThreeSum.three_sum nums = ok r) :
      ∀ (p : Nat) (hp : p < r.val.length),
        vecIthVal (r.val[p]) 0 + vecIthVal (r.val[p]) 1 + vecIthVal (r.val[p]) 2 = 0 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : SliceI64) (h : ValidInput nums) (r : VecVecI64)
        (hr : Aegis.ThreeSum.three_sum nums = ok r), ∀ (p : Nat) (hp : p < r.val.length),
          vecIthVal (r.val[p]) 0 + vecIthVal (r.val[p]) 1 + vecIthVal (r.val[p]) 2 = 0) := by
    sorry

  /-- Whenever the function returns a result r, every element of r is realized by three pairwise distinct positions of nums: for every p with 0 <= p < len(r) there exist indices i, j, k with 0 <= i, j, k < len(nums), i, j, k pairwise distinct, such that nums[i] = r[p][0], nums[j] = r[p][1] and nums[k] = r[p][2].
    Preconditions: 3 <= len(nums) <= 3000, and for every i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000. -/
  theorem spec_4 (nums : SliceI64) (h : ValidInput nums) (r : VecVecI64)
      (hr : Aegis.ThreeSum.three_sum nums = ok r) :
      ∀ (p : Nat) (hp : p < r.val.length),
        ∃ (i j k : Nat),
          i < nums.val.length ∧ j < nums.val.length ∧ k < nums.val.length ∧
            i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
              sliceIthVal nums i = vecIthVal (r.val[p]) 0 ∧
              sliceIthVal nums j = vecIthVal (r.val[p]) 1 ∧
              sliceIthVal nums k = vecIthVal (r.val[p]) 2 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : SliceI64) (h : ValidInput nums) (r : VecVecI64)
        (hr : Aegis.ThreeSum.three_sum nums = ok r), ∀ (p : Nat) (hp : p < r.val.length),
          ∃ (i j k : Nat),
            i < nums.val.length ∧ j < nums.val.length ∧ k < nums.val.length ∧
              i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
                sliceIthVal nums i = vecIthVal (r.val[p]) 0 ∧
                sliceIthVal nums j = vecIthVal (r.val[p]) 1 ∧
                sliceIthVal nums k = vecIthVal (r.val[p]) 2) := by
    sorry

  /-- Whenever the function returns a result r, no two returned triplets have the same multiset of values: for all p, q with 0 <= p < q < len(r), the multiset {r[p][0], r[p][1], r[p][2]} differs from the multiset {r[q][0], r[q][1], r[q][2]}; equivalently, r[p] is not a permutation of r[q].
    Preconditions: 3 <= len(nums) <= 3000, and for every i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000. -/
  theorem spec_5 (nums : SliceI64) (h : ValidInput nums) (r : VecVecI64)
      (hr : Aegis.ThreeSum.three_sum nums = ok r) :
      ∀ (p q : Nat) (hp : p < r.val.length) (hq : q < r.val.length), p < q →
        ¬ SameMultiset (vecVals r.val[p]) (vecVals r.val[q]) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : SliceI64) (h : ValidInput nums) (r : VecVecI64)
        (hr : Aegis.ThreeSum.three_sum nums = ok r), ∀ (p q : Nat) (hp : p < r.val.length) (hq : q < r.val.length), p < q →
          ¬ SameMultiset (vecVals r.val[p]) (vecVals r.val[q])) := by
    sorry

  /-- Whenever the function returns a result r, every zero-sum triple of values taken at pairwise distinct positions of nums occurs in r: for all pairwise distinct i, j, k with 0 <= i, j, k < len(nums) and nums[i] + nums[j] + nums[k] = 0, there exists p with 0 <= p < len(r) such that the multiset {r[p][0], r[p][1], r[p][2]} equals the multiset {nums[i], nums[j], nums[k]}.
    Preconditions: 3 <= len(nums) <= 3000, and for every i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000. -/
  theorem spec_6 (nums : SliceI64) (h : ValidInput nums) (r : VecVecI64)
      (hr : Aegis.ThreeSum.three_sum nums = ok r) :
      ∀ (i j k : Nat),
        i < nums.val.length → j < nums.val.length → k < nums.val.length →
          i ≠ j → i ≠ k → j ≠ k →
            sliceIthVal nums i + sliceIthVal nums j + sliceIthVal nums k = 0 →
              ∃ (p : Nat) (_hp : p < r.val.length),
                HasMultiset (vecVals r.val[p]) (sliceIthVal nums i) (sliceIthVal nums j)
                  (sliceIthVal nums k) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : SliceI64) (h : ValidInput nums) (r : VecVecI64)
        (hr : Aegis.ThreeSum.three_sum nums = ok r), ∀ (i j k : Nat),
          i < nums.val.length → j < nums.val.length → k < nums.val.length →
            i ≠ j → i ≠ k → j ≠ k →
              sliceIthVal nums i + sliceIthVal nums j + sliceIthVal nums k = 0 →
                ∃ (p : Nat) (_hp : p < r.val.length),
                  HasMultiset (vecVals r.val[p]) (sliceIthVal nums i) (sliceIthVal nums j)
                    (sliceIthVal nums k)) := by
    sorry

  /-- Whenever the function returns a result r, len(r) equals the number of distinct multisets M of three integers such that the three elements of M sum to 0 and there exist pairwise distinct indices i, j, k with 0 <= i, j, k < len(nums) and {nums[i], nums[j], nums[k]} = M.
    Preconditions: 3 <= len(nums) <= 3000, and for every i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000. -/
  theorem spec_7 (nums : SliceI64) (h : ValidInput nums) (r : VecVecI64)
      (hr : Aegis.ThreeSum.three_sum nums = ok r) :
      r.val.length = zeroSumMultisetCount nums := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : SliceI64) (h : ValidInput nums) (r : VecVecI64)
        (hr : Aegis.ThreeSum.three_sum nums = ok r), r.val.length = zeroSumMultisetCount nums) := by
    sorry

  /-- The function returns a result r on every input satisfying the preconditions; it never fails, i.e. it does not panic, does not perform an out-of-bounds access, and does not overflow 64-bit arithmetic.
    Preconditions: 3 <= len(nums) <= 3000, and for every i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000. -/
  theorem spec_8 (nums : SliceI64) (h : ValidInput nums) :
      ∃ r : VecVecI64, Aegis.ThreeSum.three_sum nums = ok r := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : SliceI64) (h : ValidInput nums), ∃ r : VecVecI64, Aegis.ThreeSum.three_sum nums = ok r) := by
    sorry

  end AegisSpec.ThreeSum

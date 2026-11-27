import Aegis.NumberOfArithmeticSlices.Code.Funs

/-!
# Specifications of `Aegis.NumberOfArithmeticSlices.number_of_arithmetic_slices`

LeetCode problem `arithmetic-slices`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.NumberOfArithmeticSlices

  def Values (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

  def ValidInput (nums : Slice Std.I64) : Prop :=
    1 ≤ nums.val.length ∧ nums.val.length ≤ 5000 ∧
      ∀ i (h : i < nums.val.length), -1000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000

  def diffsOf (a : List Int) : List Int := (a.zip a.tail).map (fun p => p.2 - p.1)

  def IsArithProg (l : List Int) : Prop := (diffsOf l).Pairwise (fun x y => x = y)

  def ArithWindow (a : List Int) (i j : Nat) : Prop :=
    i + 2 ≤ j ∧ j < a.length ∧ IsArithProg ((a.drop i).take (j + 1 - i))

  instance decidableIsArithProg (l : List Int) : Decidable (IsArithProg l) :=
    inferInstanceAs (Decidable ((diffsOf l).Pairwise (fun x y => x = y)))

  instance decidableArithWindow (a : List Int) (i j : Nat) : Decidable (ArithWindow a i j) :=
    inferInstanceAs
      (Decidable (i + 2 ≤ j ∧ j < a.length ∧ IsArithProg ((a.drop i).take (j + 1 - i))))

  def arithPairCount (a : List Int) : Nat :=
    (((Finset.range a.length).product (Finset.range a.length)).filter
      (fun p : Nat × Nat => ArithWindow a p.1 p.2)).card

  def tri (t : Nat) : Int := ((t : Int) * ((t : Int) - 1)) / 2

  def closeBlock (cur : List Int) (done : List (List Int)) : List (List Int) :=
    cur.reverse :: done

  def runsAux : List Int → List Int → List (List Int) → List (List Int)
    | [], cur, done => closeBlock cur done
    | d :: ds, [], done => runsAux ds [d] done
    | d :: ds, c :: cur, done =>
        if d = c then runsAux ds (d :: c :: cur) done
        else runsAux ds [d] (closeBlock (c :: cur) done)

  def runs (l : List Int) : List (List Int) :=
    match l with
    | [] => []
    | d :: ds => (runsAux ds [d] []).reverse

  def blockSum (a : List Int) : Int :=
    ((runs (diffsOf a)).map (fun b => tri b.length)).sum

  /-- Let n = len(nums). Let C be the number of ordered pairs (i,j) of integers such that 0 <= i, i+2 <= j < n, and for every k with i <= k < j-1, nums[k+1]-nums[k] = nums[k+2]-nums[k+1]. Whenever the function returns a result r, r = C.
    Preconditions: 1 <= len(nums) <= 5000, and for every i with 0 <= i < len(nums), -1000 <= nums[i] <= 1000. -/
  theorem spec_1 (nums : Slice Std.I64) (hpre : ValidInput nums) :
      ∀ r, Aegis.NumberOfArithmeticSlices.number_of_arithmetic_slices nums = ok r →
        r.val = (arithPairCount (Values nums) : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (hpre : ValidInput nums), ∀ r, Aegis.NumberOfArithmeticSlices.number_of_arithmetic_slices nums = ok r →
          r.val = (arithPairCount (Values nums) : Int)) := by
    sorry

  /-- For every input nums satisfying the preconditions, the function returns a result (it does not fail, panic, or overflow).
    Preconditions: 1 <= len(nums) <= 5000, and for every i with 0 <= i < len(nums), -1000 <= nums[i] <= 1000. -/
  theorem spec_2 (nums : Slice Std.I64) (hpre : ValidInput nums) :
      ∃ r, Aegis.NumberOfArithmeticSlices.number_of_arithmetic_slices nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (hpre : ValidInput nums), ∃ r, Aegis.NumberOfArithmeticSlices.number_of_arithmetic_slices nums = ok r) := by
    sorry

  /-- Let n = len(nums). Whenever the function returns a result r, 0 <= r <= (n-1)*(n-2)/2.
    Preconditions: 1 <= len(nums) <= 5000, and for every i with 0 <= i < len(nums), -1000 <= nums[i] <= 1000. -/
  theorem spec_3 (nums : Slice Std.I64) (hpre : ValidInput nums) :
      ∀ r, Aegis.NumberOfArithmeticSlices.number_of_arithmetic_slices nums = ok r →
        0 ≤ r.val ∧ r.val ≤ tri (nums.val.length - 1) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (hpre : ValidInput nums), ∀ r, Aegis.NumberOfArithmeticSlices.number_of_arithmetic_slices nums = ok r →
          0 ≤ r.val ∧ r.val ≤ tri (nums.val.length - 1)) := by
    sorry

  /-- Let n = len(nums). Whenever the function returns a result r, r > 0 if and only if there exists an integer i such that 0 <= i < n-2 and nums[i+1]-nums[i] = nums[i+2]-nums[i+1].
    Preconditions: 1 <= len(nums) <= 5000, and for every i with 0 <= i < len(nums), -1000 <= nums[i] <= 1000. -/
  theorem spec_4 (nums : Slice Std.I64) (hpre : ValidInput nums) :
      ∀ r, Aegis.NumberOfArithmeticSlices.number_of_arithmetic_slices nums = ok r →
        (0 < r.val ↔
          ∃ i, ∃ (hi : i < nums.val.length - 2),
            (nums.val[i+1]).val - (nums.val[i]).val
              = (nums.val[i+2]).val - (nums.val[i+1]).val) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (hpre : ValidInput nums), ∀ r, Aegis.NumberOfArithmeticSlices.number_of_arithmetic_slices nums = ok r →
          (0 < r.val ↔
            ∃ i, ∃ (hi : i < nums.val.length - 2),
              (nums.val[i+1]).val - (nums.val[i]).val
                = (nums.val[i+2]).val - (nums.val[i+1]).val)) := by
    sorry

  /-- Let n = len(nums), and for 0 <= k < n-1 let d[k] = nums[k+1]-nums[k]. Partition the index set {0,1,...,n-2} (empty when n=1) into its unique maximal contiguous blocks B such that all d[k] for k in B are equal and adjacent blocks have different d-values. For a block B let t = |B|. Whenever the function returns a result r, r = sum over all such blocks B of t*(t-1)/2.
    Preconditions: 1 <= len(nums) <= 5000, and for every i with 0 <= i < len(nums), -1000 <= nums[i] <= 1000. -/
  theorem spec_5 (nums : Slice Std.I64) (hpre : ValidInput nums) :
      ∀ r, Aegis.NumberOfArithmeticSlices.number_of_arithmetic_slices nums = ok r →
        r.val = blockSum (Values nums) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (hpre : ValidInput nums), ∀ r, Aegis.NumberOfArithmeticSlices.number_of_arithmetic_slices nums = ok r →
          r.val = blockSum (Values nums)) := by
    sorry

  /-- For every slice b satisfying 1 <= len(b) <= 5000 and -1000 <= b[i] <= 1000 for all i, if len(b)=len(nums) and b[i]=nums[len(nums)-1-i] for every i with 0 <= i < len(nums), then whenever the function returns q on nums and q_b on b, q = q_b.
    Preconditions: 1 <= len(nums) <= 5000, and for every i with 0 <= i < len(nums), -1000 <= nums[i] <= 1000. -/
  theorem spec_6 (nums : Slice Std.I64) (hpre : ValidInput nums)
      (b : Slice Std.I64) (hb : ValidInput b)
      (hlen : b.val.length = nums.val.length)
      (hrev : ∀ i (h : i < nums.val.length),
        (b.val[i]).val = (nums.val[nums.val.length - 1 - i]).val) :
      ∀ q qb, Aegis.NumberOfArithmeticSlices.number_of_arithmetic_slices nums = ok q →
        Aegis.NumberOfArithmeticSlices.number_of_arithmetic_slices b = ok qb →
          q.val = qb.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (hpre : ValidInput nums)
        (b : Slice Std.I64) (hb : ValidInput b)
        (hlen : b.val.length = nums.val.length)
        (hrev : ∀ i (h : i < nums.val.length),
          (b.val[i]).val = (nums.val[nums.val.length - 1 - i]).val), ∀ q qb, Aegis.NumberOfArithmeticSlices.number_of_arithmetic_slices nums = ok q →
          Aegis.NumberOfArithmeticSlices.number_of_arithmetic_slices b = ok qb →
            q.val = qb.val) := by
    sorry

  /-- For every integer c and every slice b satisfying 1 <= len(b) <= 5000 and -1000 <= b[i] <= 1000 for all i, if len(b)=len(nums) and b[i]=nums[i]+c for every i with 0 <= i < len(nums) (integer addition), then whenever the function returns q on nums and q_b on b, q = q_b.
    Preconditions: 1 <= len(nums) <= 5000, and for every i with 0 <= i < len(nums), -1000 <= nums[i] <= 1000. -/
  theorem spec_7 (nums : Slice Std.I64) (hpre : ValidInput nums) (c : Int)
      (b : Slice Std.I64) (hb : ValidInput b)
      (hlen : b.val.length = nums.val.length)
      (hadd : ∀ i (h : i < nums.val.length), (b.val[i]).val = (nums.val[i]).val + c) :
      ∀ q qb, Aegis.NumberOfArithmeticSlices.number_of_arithmetic_slices nums = ok q →
        Aegis.NumberOfArithmeticSlices.number_of_arithmetic_slices b = ok qb →
          q.val = qb.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (hpre : ValidInput nums) (c : Int)
        (b : Slice Std.I64) (hb : ValidInput b)
        (hlen : b.val.length = nums.val.length)
        (hadd : ∀ i (h : i < nums.val.length), (b.val[i]).val = (nums.val[i]).val + c), ∀ q qb, Aegis.NumberOfArithmeticSlices.number_of_arithmetic_slices nums = ok q →
          Aegis.NumberOfArithmeticSlices.number_of_arithmetic_slices b = ok qb →
            q.val = qb.val) := by
    sorry

  /-- For every integer c with c != 0 and every slice b satisfying 1 <= len(b) <= 5000 and -1000 <= b[i] <= 1000 for all i, if len(b)=len(nums) and b[i]=c*nums[i] for every i with 0 <= i < len(nums) (integer multiplication), then whenever the function returns q on nums and q_b on b, q = q_b.
    Preconditions: 1 <= len(nums) <= 5000, and for every i with 0 <= i < len(nums), -1000 <= nums[i] <= 1000. -/
  theorem spec_8 (nums : Slice Std.I64) (hpre : ValidInput nums) (c : Int) (hc : c ≠ 0)
      (b : Slice Std.I64) (hb : ValidInput b)
      (hlen : b.val.length = nums.val.length)
      (hmul : ∀ i (h : i < nums.val.length), (b.val[i]).val = c * (nums.val[i]).val) :
      ∀ q qb, Aegis.NumberOfArithmeticSlices.number_of_arithmetic_slices nums = ok q →
        Aegis.NumberOfArithmeticSlices.number_of_arithmetic_slices b = ok qb →
          q.val = qb.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (hpre : ValidInput nums) (c : Int) (hc : c ≠ 0)
        (b : Slice Std.I64) (hb : ValidInput b)
        (hlen : b.val.length = nums.val.length)
        (hmul : ∀ i (h : i < nums.val.length), (b.val[i]).val = c * (nums.val[i]).val), ∀ q qb, Aegis.NumberOfArithmeticSlices.number_of_arithmetic_slices nums = ok q →
          Aegis.NumberOfArithmeticSlices.number_of_arithmetic_slices b = ok qb →
            q.val = qb.val) := by
    sorry

  /-- For every slice b satisfying 1 <= len(b) <= 5000 and -1000 <= b[i] <= 1000 for all i, if len(b) <= len(nums) and b[i]=nums[i] for every i with 0 <= i < len(b), then whenever the function returns q on nums and q_b on b, q >= q_b.
    Preconditions: 1 <= len(nums) <= 5000, and for every i with 0 <= i < len(nums), -1000 <= nums[i] <= 1000. -/
  theorem spec_9 (nums : Slice Std.I64) (hpre : ValidInput nums)
      (b : Slice Std.I64) (hb : ValidInput b)
      (hlen : b.val.length ≤ nums.val.length)
      (hprefix : ∀ i (h : i < b.val.length), (b.val[i]).val = (nums.val[i]).val) :
      ∀ q qb, Aegis.NumberOfArithmeticSlices.number_of_arithmetic_slices nums = ok q →
        Aegis.NumberOfArithmeticSlices.number_of_arithmetic_slices b = ok qb →
          qb.val ≤ q.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (hpre : ValidInput nums)
        (b : Slice Std.I64) (hb : ValidInput b)
        (hlen : b.val.length ≤ nums.val.length)
        (hprefix : ∀ i (h : i < b.val.length), (b.val[i]).val = (nums.val[i]).val), ∀ q qb, Aegis.NumberOfArithmeticSlices.number_of_arithmetic_slices nums = ok q →
          Aegis.NumberOfArithmeticSlices.number_of_arithmetic_slices b = ok qb →
            qb.val ≤ q.val) := by
    sorry

  /-- For every such pair (i,j) with 0 <= i, i+2 <= j < len(nums) and all consecutive differences on nums[i..j] equal, whenever the function returns a result r, r >= (j-i)*(j-i-1)/2.
    Preconditions: 1 <= len(nums) <= 5000, for every i with 0 <= i < len(nums), -1000 <= nums[i] <= 1000, and there exist integers i,j with 0 <= i, i+2 <= j < len(nums) such that nums[i..j] is arithmetic. -/
  theorem spec_10 (nums : Slice Std.I64) (hpre : ValidInput nums)
      (i j : Nat) (hij : i + 2 ≤ j) (hj : j < nums.val.length)
      (harith : ∀ k (hk1 : i ≤ k) (hk2 : k < j - 1),
        (nums.val[k+1]).val - (nums.val[k]).val
          = (nums.val[k+2]).val - (nums.val[k+1]).val) :
      ∀ r, Aegis.NumberOfArithmeticSlices.number_of_arithmetic_slices nums = ok r →
        tri (j - i) ≤ r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (hpre : ValidInput nums)
        (i j : Nat) (hij : i + 2 ≤ j) (hj : j < nums.val.length)
        (harith : ∀ k (hk1 : i ≤ k) (hk2 : k < j - 1),
          (nums.val[k+1]).val - (nums.val[k]).val
            = (nums.val[k+2]).val - (nums.val[k+1]).val), ∀ r, Aegis.NumberOfArithmeticSlices.number_of_arithmetic_slices nums = ok r →
          tri (j - i) ≤ r.val) := by
    sorry

  end AegisSpec.NumberOfArithmeticSlices

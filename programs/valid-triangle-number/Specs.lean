import Aegis.TriangleNumber.Code.Funs

/-!
# Specifications of `Aegis.TriangleNumber.triangle_number`

LeetCode problem `valid-triangle-number`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.TriangleNumber

namespace AegisSpec.TriangleNumber

  def elems (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

  abbrev IsTriangle (a b c : ℤ) : Prop := a + b > c ∧ a + c > b ∧ b + c > a

  abbrev ITriple (n : ℕ) : Type := Fin n × Fin n × Fin n

  def ITriple.i {n : ℕ} (t : ITriple n) : Fin n := t.1

  def ITriple.j {n : ℕ} (t : ITriple n) : Fin n := t.2.1

  def ITriple.k {n : ℕ} (t : ITriple n) : Fin n := t.2.2

  def orderedTriples (l : List ℤ) : Finset (ITriple l.length) :=
    Finset.univ.filter (fun t => t.i < t.j ∧ t.j < t.k)

  def triangleTriples (l : List ℤ) : Finset (ITriple l.length) :=
    Finset.univ.filter
      (fun t => t.i < t.j ∧ t.j < t.k ∧ IsTriangle (l.get t.i) (l.get t.j) (l.get t.k))

  def triangleCount (l : List ℤ) : ℕ := (triangleTriples l).card

  def tailIneqTriples (l : List ℤ) : Finset (ITriple l.length) :=
    Finset.univ.filter (fun t => t.i < t.j ∧ t.j < t.k ∧ l.get t.i + l.get t.j > l.get t.k)

  def tailIneqCount (l : List ℤ) : ℕ := (tailIneqTriples l).card

  def countWhere (l : List ℤ) (p : ℤ → Prop) [DecidablePred p] : ℕ :=
    ((Finset.univ : Finset (Fin l.length)).filter (fun i => p (l.get i))).card

  def pairCount (l : List ℤ) (x : ℤ) : ℕ :=
    ((Finset.univ : Finset (Fin l.length × Fin l.length)).filter
      (fun p => p.1 < p.2 ∧ IsTriangle (l.get p.1) (l.get p.2) x)).card

  def Nondecreasing (l : List ℤ) : Prop := ∀ i j : Fin l.length, i ≤ j → l.get i ≤ l.get j

  def InBounds (l : List ℤ) : Prop := ∀ i : Fin l.length, 0 ≤ l.get i ∧ l.get i ≤ 1000

  def choose3 (p : ℕ) : ℕ := p * (p - 1) * (p - 2) / 6

  /-- Whenever the call triangle_number(nums) returns a result r, r is the number of triples (i,j,k) of indices such that 0 <= i < j < k < len(nums) and the three mathematical integers nums[i], nums[j], nums[k] satisfy all three strict triangle inequalities: nums[i] + nums[j] > nums[k], nums[i] + nums[k] > nums[j], and nums[j] + nums[k] > nums[i]. Equivalently, r = |{ (i,j,k) : 0 <= i < j < k < len(nums) and the three displayed inequalities hold }|.
    Preconditions: len(nums) >= 1, len(nums) <= 1000, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000. -/
  theorem spec_1 (nums : Slice Std.I64)
      (hlen_lo : 1 ≤ (elems nums).length) (hlen_hi : (elems nums).length ≤ 1000)
      (hbounds : InBounds (elems nums))
      (r : Std.I64) (hres : triangle_number nums = ok r) :
      r.val = (triangleCount (elems nums) : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lo : 1 ≤ (elems nums).length) (hlen_hi : (elems nums).length ≤ 1000)
        (hbounds : InBounds (elems nums))
        (r : Std.I64) (hres : triangle_number nums = ok r), r.val = (triangleCount (elems nums) : ℤ)) := by
    sorry

  /-- For every nums satisfying the preconditions, the call triangle_number(nums) returns a result; it does not fail, panic, or overflow.
    Preconditions: len(nums) >= 1, len(nums) <= 1000, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000. -/
  theorem spec_2 (nums : Slice Std.I64)
      (hlen_lo : 1 ≤ (elems nums).length) (hlen_hi : (elems nums).length ≤ 1000)
      (hbounds : InBounds (elems nums)) :
      ∃ r : Std.I64, triangle_number nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lo : 1 ≤ (elems nums).length) (hlen_hi : (elems nums).length ≤ 1000)
        (hbounds : InBounds (elems nums)), ∃ r : Std.I64, triangle_number nums = ok r) := by
    sorry

  /-- Let p be the number of indices i with 0 <= i < len(nums) and nums[i] > 0. Whenever triangle_number(nums) returns a result r, r <= p*(p-1)*(p-2)/6, which is C(p,3) with the convention that this value is 0 when p < 3.
    Preconditions: len(nums) >= 1, len(nums) <= 1000, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000. -/
  theorem spec_3 (nums : Slice Std.I64)
      (hlen_lo : 1 ≤ (elems nums).length) (hlen_hi : (elems nums).length ≤ 1000)
      (hbounds : InBounds (elems nums))
      (r : Std.I64) (hres : triangle_number nums = ok r) :
      r.val ≤ (choose3 (countWhere (elems nums) (fun x => 0 < x)) : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lo : 1 ≤ (elems nums).length) (hlen_hi : (elems nums).length ≤ 1000)
        (hbounds : InBounds (elems nums))
        (r : Std.I64) (hres : triangle_number nums = ok r), r.val ≤ (choose3 (countWhere (elems nums) (fun x => 0 < x)) : ℤ)) := by
    sorry

  /-- Whenever triangle_number(nums) returns a result r, r = 0.
    Preconditions: 1 <= len(nums) <= 2 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000. -/
  theorem spec_4 (nums : Slice Std.I64)
      (hlen_lo : 1 ≤ (elems nums).length) (hlen_hi : (elems nums).length ≤ 2)
      (hbounds : InBounds (elems nums))
      (r : Std.I64) (hres : triangle_number nums = ok r) :
      r.val = 0 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lo : 1 ≤ (elems nums).length) (hlen_hi : (elems nums).length ≤ 2)
        (hbounds : InBounds (elems nums))
        (r : Std.I64) (hres : triangle_number nums = ok r), r.val = 0) := by
    sorry

  /-- Whenever triangle_number(nums) returns a result r, r = 1 if nums[0] + nums[1] > nums[2] and nums[0] + nums[2] > nums[1] and nums[1] + nums[2] > nums[0], and r = 0 otherwise.
    Preconditions: len(nums) = 3 and for every i with 0 <= i < 3, 0 <= nums[i] <= 1000. -/
  theorem spec_5 (nums : Slice Std.I64)
      (hlen : (elems nums).length = 3)
      (hbounds : InBounds (elems nums))
      (r : Std.I64) (hres : triangle_number nums = ok r) :
      r.val =
        if IsTriangle ((elems nums).get ⟨0, by omega⟩) ((elems nums).get ⟨1, by omega⟩)
          ((elems nums).get ⟨2, by omega⟩) then 1 else 0 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : (elems nums).length = 3)
        (hbounds : InBounds (elems nums))
        (r : Std.I64) (hres : triangle_number nums = ok r), r.val =
          if IsTriangle ((elems nums).get ⟨0, by omega⟩) ((elems nums).get ⟨1, by omega⟩)
            ((elems nums).get ⟨2, by omega⟩) then 1 else 0) := by
    sorry

  /-- Whenever triangle_number(nums) returns a result r, r = len(nums)*(len(nums)-1)*(len(nums)-2)/6, which equals C(len(nums),3) and is 0 when len(nums) < 3.
    Preconditions: len(nums) >= 1, len(nums) <= 1000, and there exists an integer c with 1 <= c <= 1000 such that nums[i] = c for every i with 0 <= i < len(nums). -/
  theorem spec_6 (nums : Slice Std.I64)
      (hlen_lo : 1 ≤ (elems nums).length) (hlen_hi : (elems nums).length ≤ 1000)
      (hconst : ∃ c : ℤ, 1 ≤ c ∧ c ≤ 1000 ∧ ∀ i : Fin (elems nums).length, (elems nums).get i = c)
      (r : Std.I64) (hres : triangle_number nums = ok r) :
      r.val = (choose3 (elems nums).length : ℤ) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lo : 1 ≤ (elems nums).length) (hlen_hi : (elems nums).length ≤ 1000)
        (hconst : ∃ c : ℤ, 1 ≤ c ∧ c ≤ 1000 ∧ ∀ i : Fin (elems nums).length, (elems nums).get i = c)
        (r : Std.I64) (hres : triangle_number nums = ok r), r.val = (choose3 (elems nums).length : ℤ)) := by
    sorry

  /-- Let m be the number of indices i with 0 <= i < len(nums) and nums[i] = 1. Whenever triangle_number(nums) returns a result r, r = m*(m-1)*(m-2)/6, which equals C(m,3) and is 0 when m < 3.
    Preconditions: 1 <= len(nums) <= 1000 and for every i with 0 <= i < len(nums), nums[i] = 0 or nums[i] = 1. -/
  theorem spec_7 (nums : Slice Std.I64)
      (hlen_lo : 1 ≤ (elems nums).length) (hlen_hi : (elems nums).length ≤ 1000)
      (h01 : ∀ i : Fin (elems nums).length, (elems nums).get i = 0 ∨ (elems nums).get i = 1)
      (r : Std.I64) (hres : triangle_number nums = ok r) :
      r.val = (choose3 (countWhere (elems nums) (fun x => x = 1)) : ℤ) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lo : 1 ≤ (elems nums).length) (hlen_hi : (elems nums).length ≤ 1000)
        (h01 : ∀ i : Fin (elems nums).length, (elems nums).get i = 0 ∨ (elems nums).get i = 1)
        (r : Std.I64) (hres : triangle_number nums = ok r), r.val = (choose3 (countWhere (elems nums) (fun x => x = 1)) : ℤ)) := by
    sorry

  /-- Whenever triangle_number(nums) returns r and triangle_number(nums') returns r', we have r = r'.
    Preconditions: Both nums and nums' satisfy the problem constraints: 1 <= len(nums) = len(nums') <= 1000 and all entries are between 0 and 1000. There exists a bijection p from {0,...,len(nums)-1} to itself such that nums'[i] = nums[p(i)] for every i with 0 <= i < len(nums). -/
  theorem spec_8 (nums nums' : Slice Std.I64)
      (hlen : (elems nums).length = (elems nums').length)
      (hlen_lo : 1 ≤ (elems nums).length) (hlen_hi : (elems nums).length ≤ 1000)
      (hbounds : InBounds (elems nums)) (hbounds' : InBounds (elems nums'))
      (hperm : ∃ p : Equiv.Perm (Fin (elems nums).length),
        ∀ i : Fin (elems nums).length,
          (elems nums').get ⟨i.val, by have := i.isLt; omega⟩ = (elems nums).get (p i))
      (r r' : Std.I64) (hres : triangle_number nums = ok r)
      (hres' : triangle_number nums' = ok r') :
      r.val = r'.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums nums' : Slice Std.I64)
        (hlen : (elems nums).length = (elems nums').length)
        (hlen_lo : 1 ≤ (elems nums).length) (hlen_hi : (elems nums).length ≤ 1000)
        (hbounds : InBounds (elems nums)) (hbounds' : InBounds (elems nums'))
        (hperm : ∃ p : Equiv.Perm (Fin (elems nums).length),
          ∀ i : Fin (elems nums).length,
            (elems nums').get ⟨i.val, by have := i.isLt; omega⟩ = (elems nums).get (p i))
        (r r' : Std.I64) (hres : triangle_number nums = ok r)
        (hres' : triangle_number nums' = ok r'), r.val = r'.val) := by
    sorry

  /-- Whenever triangle_number(nums) returns r and triangle_number(nums') returns r', r' = r + q, where q is the number of pairs (i,j) with 0 <= i < j < n such that nums[i] + nums[j] > x, nums[i] + x > nums[j], and nums[j] + x > nums[i].
    Preconditions: Let n = len(nums). We have 1 <= n <= 999, len(nums') = n+1, nums'[i] = nums[i] for every 0 <= i < n, nums'[n] = x, and all entries of nums and nums' are between 0 and 1000. -/
  theorem spec_9 (nums nums' : Slice Std.I64) (x : ℤ)
      (hn_lo : 1 ≤ (elems nums).length) (hn_hi : (elems nums).length ≤ 999)
      (hlen' : (elems nums').length = (elems nums).length + 1)
      (hpre : ∀ i : Fin (elems nums).length,
        (elems nums').get ⟨i.val, by have := i.isLt; omega⟩ = (elems nums).get i)
      (hlast : (elems nums').get ⟨(elems nums).length, by omega⟩ = x)
      (hbounds : InBounds (elems nums)) (hbounds' : InBounds (elems nums'))
      (r r' : Std.I64) (hres : triangle_number nums = ok r)
      (hres' : triangle_number nums' = ok r') :
      r'.val = r.val + (pairCount (elems nums) x : ℤ) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (x : ℤ)
        (hn_lo : 1 ≤ (elems nums).length) (hn_hi : (elems nums).length ≤ 999)
        (hlen' : (elems nums').length = (elems nums).length + 1)
        (hpre : ∀ i : Fin (elems nums).length,
          (elems nums').get ⟨i.val, by have := i.isLt; omega⟩ = (elems nums).get i)
        (hlast : (elems nums').get ⟨(elems nums).length, by omega⟩ = x)
        (hbounds : InBounds (elems nums)) (hbounds' : InBounds (elems nums'))
        (r r' : Std.I64) (hres : triangle_number nums = ok r)
        (hres' : triangle_number nums' = ok r'), r'.val = r.val + (pairCount (elems nums) x : ℤ)) := by
    sorry

  /-- Whenever triangle_number(nums) returns a result r, r = |{ (i,j,k) : 0 <= i < j < k < len(b) and b[i] + b[j] > b[k] }|. For nondecreasing nonnegative b, a triple i<j<k satisfies all three strict triangle inequalities exactly when b[i] + b[j] > b[k].
    Preconditions: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000; b is a nondecreasing reordering of nums. -/
  theorem spec_10 (nums : Slice Std.I64) (b : List ℤ)
      (hlen_lo : 1 ≤ (elems nums).length) (hlen_hi : (elems nums).length ≤ 1000)
      (hbounds : InBounds (elems nums))
      (hperm : (elems nums).Perm b) (hsorted : Nondecreasing b)
      (r : Std.I64) (hres : triangle_number nums = ok r) :
      r.val = (tailIneqCount b : ℤ) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (b : List ℤ)
        (hlen_lo : 1 ≤ (elems nums).length) (hlen_hi : (elems nums).length ≤ 1000)
        (hbounds : InBounds (elems nums))
        (hperm : (elems nums).Perm b) (hsorted : Nondecreasing b)
        (r : Std.I64) (hres : triangle_number nums = ok r), r.val = (tailIneqCount b : ℤ)) := by
    sorry

  /-- Whenever triangle_number(nums) returns a result r, every counted index triple (i,j,k) has nums[i] > 0, nums[j] > 0, and nums[k] > 0. Consequently, if at most two entries of nums are positive, r = 0.
    Preconditions: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000. -/
  theorem spec_11 (nums : Slice Std.I64)
      (hlen_lo : 1 ≤ (elems nums).length) (hlen_hi : (elems nums).length ≤ 1000)
      (hbounds : InBounds (elems nums))
      (r : Std.I64) (hres : triangle_number nums = ok r) :
      (∀ t ∈ triangleTriples (elems nums),
          0 < (elems nums).get t.i ∧
            0 < (elems nums).get t.j ∧ 0 < (elems nums).get t.k) ∧
        (countWhere (elems nums) (fun x => 0 < x) ≤ 2 → r.val = 0) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lo : 1 ≤ (elems nums).length) (hlen_hi : (elems nums).length ≤ 1000)
        (hbounds : InBounds (elems nums))
        (r : Std.I64) (hres : triangle_number nums = ok r), (∀ t ∈ triangleTriples (elems nums),
            0 < (elems nums).get t.i ∧
              0 < (elems nums).get t.j ∧ 0 < (elems nums).get t.k) ∧
          (countWhere (elems nums) (fun x => 0 < x) ≤ 2 → r.val = 0)) := by
    sorry

end AegisSpec.TriangleNumber

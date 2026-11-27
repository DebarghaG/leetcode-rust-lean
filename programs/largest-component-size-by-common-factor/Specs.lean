import Aegis.LargestComponentSize.Code.Funs

/-!
# Specifications of `Aegis.LargestComponentSize.largest_component_size`

LeetCode problem `largest-component-size-by-common-factor`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.LargestComponentSize

  open Aegis.LargestComponentSize (largest_component_size)

  def elems (nums : Slice I64) : List ℤ := nums.val.map (fun x => x.val)

  def entry (vals : List ℤ) (i : ℕ) : ℤ := vals.getD i 0

  def size (nums : Slice I64) : ℕ := (elems nums).length

  def Constraints (nums : Slice I64) : Prop :=
    1 ≤ size nums ∧ size nums ≤ 20000 ∧
      (∀ i, i < size nums → 1 ≤ entry (elems nums) i ∧ entry (elems nums) i ≤ 100000) ∧
      (∀ i j, i < j → j < size nums → entry (elems nums) i ≠ entry (elems nums) j)

  def Edge (vals : List ℤ) (i j : ℕ) : Prop :=
    i < vals.length ∧ j < vals.length ∧ i ≠ j ∧ 1 < Int.gcd (entry vals i) (entry vals j)

  def Reachable (vals : List ℤ) (i j : ℕ) : Prop :=
    Relation.ReflTransGen (Edge vals) i j

  noncomputable def CompSize (vals : List ℤ) (i : ℕ) : ℕ := by
    classical
    exact ((Finset.range vals.length).filter (fun j => Reachable vals i j)).card

  noncomputable def MaxCompSize (vals : List ℤ) : ℕ :=
    (Finset.range vals.length).sup (CompSize vals)

  def GraphConnected (vals : List ℤ) : Prop :=
    ∀ i j, i < j → j < vals.length → Reachable vals i j

  noncomputable def DivCount (vals : List ℤ) (p : ℕ) : ℕ := by
    classical
    exact ((Finset.range vals.length).filter (fun i => (p : ℤ) ∣ entry vals i)).card

  /-- The function returns a result r, and r is the size of the largest connected component of the undirected graph G(nums) whose vertices are the indices 0,1,...,len(nums)-1, with an edge between distinct indices i and j iff gcd(nums[i], nums[j]) > 1. Equivalently, r = max over 0 <= i < len(nums) of |C(i)|, where C(i) is the set of indices connected to i by a path in G(nums) (including i itself).
    Preconditions: The slice nums satisfies the problem constraints: 1 <= len(nums) <= 20000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000; and for every i,j with 0 <= i < j < len(nums), nums[i] != nums[j]. -/
  theorem spec_1 (nums : Slice I64) (h : Constraints nums) :
      ∃ r : I64, largest_component_size nums = ok r ∧
        r.val = (MaxCompSize (elems nums) : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice I64) (h : Constraints nums), ∃ r : I64, largest_component_size nums = ok r ∧
          r.val = (MaxCompSize (elems nums) : ℤ)) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r and does not fail (no panic, out-of-bounds access, or arithmetic overflow).
    Preconditions: The slice nums satisfies the problem constraints: 1 <= len(nums) <= 20000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000; and for every i,j with 0 <= i < j < len(nums), nums[i] != nums[j]. -/
  theorem spec_2 (nums : Slice I64) (h : Constraints nums) :
      ∃ r : I64, largest_component_size nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice I64) (h : Constraints nums), ∃ r : I64, largest_component_size nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 1 <= r <= len(nums).
    Preconditions: The slice nums satisfies the problem constraints: 1 <= len(nums) <= 20000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000; and for every i,j with 0 <= i < j < len(nums), nums[i] != nums[j]. -/
  theorem spec_3 (nums : Slice I64) (h : Constraints nums) (r : I64)
      (hr : largest_component_size nums = ok r) :
      1 ≤ r.val ∧ r.val ≤ (size nums : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice I64) (h : Constraints nums) (r : I64)
        (hr : largest_component_size nums = ok r), 1 ≤ r.val ∧ r.val ≤ (size nums : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r = 1.
    Preconditions: The slice nums satisfies the problem constraints and len(nums) = 1. -/
  theorem spec_4 (nums : Slice I64) (h : Constraints nums) (hlen : size nums = 1)
      (r : I64) (hr : largest_component_size nums = ok r) :
      r.val = 1 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice I64) (h : Constraints nums) (hlen : size nums = 1)
        (r : I64) (hr : largest_component_size nums = ok r), r.val = 1) := by
    sorry

  /-- Whenever the function returns a result r, r = 1 if and only if for every pair of distinct indices i,j with 0 <= i < j < len(nums), gcd(nums[i], nums[j]) = 1 (equivalently, no two distinct values in nums share a common factor greater than 1).
    Preconditions: The slice nums satisfies the problem constraints: 1 <= len(nums) <= 20000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000; and for every i,j with 0 <= i < j < len(nums), nums[i] != nums[j]. -/
  theorem spec_5 (nums : Slice I64) (h : Constraints nums) (r : I64)
      (hr : largest_component_size nums = ok r) :
      (r.val = 1 ↔
        ∀ i j, i < j → j < size nums →
          Int.gcd (entry (elems nums) i) (entry (elems nums) j) = 1) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice I64) (h : Constraints nums) (r : I64)
        (hr : largest_component_size nums = ok r), (r.val = 1 ↔
          ∀ i j, i < j → j < size nums →
            Int.gcd (entry (elems nums) i) (entry (elems nums) j) = 1)) := by
    sorry

  /-- Whenever the function returns a result r, r = len(nums).
    Preconditions: The slice nums satisfies the problem constraints, and there exists an integer d > 1 such that d divides nums[i] for every i with 0 <= i < len(nums). -/
  theorem spec_6 (nums : Slice I64) (h : Constraints nums)
      (hd : ∃ d : ℤ, 1 < d ∧ ∀ i, i < size nums → d ∣ entry (elems nums) i)
      (r : I64) (hr : largest_component_size nums = ok r) :
      r.val = (size nums : ℤ) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice I64) (h : Constraints nums)
        (hd : ∃ d : ℤ, 1 < d ∧ ∀ i, i < size nums → d ∣ entry (elems nums) i)
        (r : I64) (hr : largest_component_size nums = ok r), r.val = (size nums : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, there exists an index i with 0 <= i < len(nums) such that the connected component C(i) in G(nums) has size exactly r.
    Preconditions: The slice nums satisfies the problem constraints: 1 <= len(nums) <= 20000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000; and for every i,j with 0 <= i < j < len(nums), nums[i] != nums[j]. -/
  theorem spec_7 (nums : Slice I64) (h : Constraints nums) (r : I64)
      (hr : largest_component_size nums = ok r) :
      ∃ i, i < size nums ∧ (CompSize (elems nums) i : ℤ) = r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice I64) (h : Constraints nums) (r : I64)
        (hr : largest_component_size nums = ok r), ∃ i, i < size nums ∧ (CompSize (elems nums) i : ℤ) = r.val) := by
    sorry

  /-- Whenever the function returns a result r, for every index i with 0 <= i < len(nums), the connected component C(i) in G(nums) has size at most r.
    Preconditions: The slice nums satisfies the problem constraints: 1 <= len(nums) <= 20000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000; and for every i,j with 0 <= i < j < len(nums), nums[i] != nums[j]. -/
  theorem spec_8 (nums : Slice I64) (h : Constraints nums) (r : I64)
      (hr : largest_component_size nums = ok r) :
      ∀ i, i < size nums → (CompSize (elems nums) i : ℤ) ≤ r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice I64) (h : Constraints nums) (r : I64)
        (hr : largest_component_size nums = ok r), ∀ i, i < size nums → (CompSize (elems nums) i : ℤ) ≤ r.val) := by
    sorry

  /-- If the function returns r on nums and r' on nums', then r = r'.
    Preconditions: Both nums and nums' satisfy the problem constraints, and nums' is a permutation of nums: len(nums') = len(nums) and there is a bijection pi on {0,...,len(nums)-1} such that nums'[k] = nums[pi(k)] for every k with 0 <= k < len(nums). -/
  theorem spec_9 (nums nums' : Slice I64) (h : Constraints nums)
      (h' : Constraints nums') (hperm : (elems nums').Perm (elems nums))
      (r r' : I64) (hr : largest_component_size nums = ok r)
      (hr' : largest_component_size nums' = ok r') :
      r = r' := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums nums' : Slice I64) (h : Constraints nums)
        (h' : Constraints nums') (hperm : (elems nums').Perm (elems nums))
        (r r' : I64) (hr : largest_component_size nums = ok r)
        (hr' : largest_component_size nums' = ok r'), r = r') := by
    sorry

  /-- Whenever the function returns a result r, for every prime p, if k_p is the number of indices i with 0 <= i < len(nums) such that p divides nums[i], then r >= k_p. Consequently, all indices whose values are divisible by the same prime p lie in one connected component of size at least k_p.
    Preconditions: The slice nums satisfies the problem constraints: 1 <= len(nums) <= 20000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000; and for every i,j with 0 <= i < j < len(nums), nums[i] != nums[j]. -/
  theorem spec_10 (nums : Slice I64) (h : Constraints nums) (r : I64)
      (hr : largest_component_size nums = ok r) :
      (∀ p : ℕ, Nat.Prime p → (DivCount (elems nums) p : ℤ) ≤ r.val) ∧
      (∀ p : ℕ, Nat.Prime p → ∀ i j, i < size nums → j < size nums →
        (p : ℤ) ∣ entry (elems nums) i → (p : ℤ) ∣ entry (elems nums) j →
        Reachable (elems nums) i j) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice I64) (h : Constraints nums) (r : I64)
        (hr : largest_component_size nums = ok r), (∀ p : ℕ, Nat.Prime p → (DivCount (elems nums) p : ℤ) ≤ r.val) ∧
        (∀ p : ℕ, Nat.Prime p → ∀ i j, i < size nums → j < size nums →
          (p : ℤ) ∣ entry (elems nums) i → (p : ℤ) ∣ entry (elems nums) j →
          Reachable (elems nums) i j)) := by
    sorry

  /-- Whenever the function returns a result r, r = len(nums) if and only if the graph G(nums) is connected, i.e. for every pair of indices i,j with 0 <= i < j < len(nums) there is a path between i and j in G(nums).
    Preconditions: The slice nums satisfies the problem constraints: 1 <= len(nums) <= 20000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000; and for every i,j with 0 <= i < j < len(nums), nums[i] != nums[j]. -/
  theorem spec_11 (nums : Slice I64) (h : Constraints nums) (r : I64)
      (hr : largest_component_size nums = ok r) :
      (r.val = (size nums : ℤ) ↔ GraphConnected (elems nums)) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice I64) (h : Constraints nums) (r : I64)
        (hr : largest_component_size nums = ok r), (r.val = (size nums : ℤ) ↔ GraphConnected (elems nums))) := by
    sorry

  end AegisSpec.LargestComponentSize

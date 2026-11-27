import Aegis.MinBuildTime.Code.Funs

/-!
# Specifications of `Aegis.MinBuildTime.min_build_time`

LeetCode problem `minimum-time-to-build-blocks`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MinBuildTime

  namespace AegisSpec.MinBuildTime

  def content (blocks : Slice Std.I64) : List Int := blocks.val.map (fun x => x.val)

  def listMax (l : List Int) : Int := l.foldr max (l.headD 0)

  def listMin (l : List Int) : Int := l.foldr min (l.headD 0)

  def occurrences (v : Int) (l : List Int) : Nat := (l.filter (fun x => decide (x = v))).length

  def ceilLog2 (n : Nat) : Nat := Nat.clog 2 n

  def selectIndices (bs : List Int) (S : Finset Nat) : List Int :=
    ((List.range bs.length).filter (fun i => decide (i ∈ S))).map (fun i => bs.getD i 0)

  def SliceOK (bs : List Int) : Prop :=
    1 ≤ bs.length ∧ bs.length ≤ 1000 ∧
      ∀ i, i < bs.length → 1 ≤ bs.getD i 0 ∧ bs.getD i 0 ≤ 100000

  def SplitOK (s : Int) : Prop := 1 ≤ s ∧ s ≤ 100

  theorem ceilLog2_spec (n : Nat) :
      n ≤ 2 ^ ceilLog2 n ∧ ∀ g : Nat, n ≤ 2 ^ g → ceilLog2 n ≤ g := by
    refine ⟨?_, ?_⟩
    · simpa [ceilLog2] using Nat.le_pow_clog (b := 2) (by norm_num) n
    · intro g hg
      simpa [ceilLog2] using
        (Nat.clog_le_iff_le_pow (b := 2) (by norm_num) (x := n) (y := g)).mpr hg

  inductive FBTree : Type where
    | leaf (label : Nat) : FBTree
    | node (l r : FBTree) : FBTree
  deriving Repr, DecidableEq

  namespace FBTree

  def leaves : FBTree → List Nat
    | leaf i => [i]
    | node l r => l.leaves ++ r.leaves

  def contains : FBTree → Nat → Bool
    | leaf j, i => i == j
    | node l r, i => l.contains i || r.contains i

  def depthOf : FBTree → Nat → Nat
    | leaf _, _ => 0
    | node l r, i =>
      if l.contains i then l.depthOf i + 1
      else if r.contains i then r.depthOf i + 1 else 0

  end FBTree

  def treeCost (t : FBTree) (bs : List Int) (split : Int) : Int :=
    listMax ((List.range bs.length).map fun i => (t.depthOf i : Int) * split + bs.getD i 0)

  def IsLabelledTree (t : FBTree) (bs : List Int) : Prop := t.leaves = List.range bs.length

  def IsOptimalTree (t : FBTree) (bs : List Int) (split : Int) : Prop :=
    IsLabelledTree t bs ∧
      ∀ t' : FBTree, IsLabelledTree t' bs → treeCost t bs split ≤ treeCost t' bs split

  def threeLeafValue (bs : List Int) (split : Int) : Int :=
    listMin ((List.range 3).map fun i =>
      max (split + bs.getD i 0)
        (2 * split +
          listMax (((List.range 3).filter fun j => decide (j ≠ i)).map fun j => bs.getD j 0)))

  /-- Whenever min_build_time(blocks, split) returns a result r, r is the minimum, over all full binary trees T with exactly len(blocks) leaves labelled bijectively by the indices 0,...,len(blocks)-1, of max_{0 <= i < len(blocks)} (d_T(i) * split + blocks[i]), where d_T(i) is the number of internal nodes on the path from the root of T to the leaf labelled i; for len(blocks)=1 the tree is a single leaf and d_T(0)=0.
    Preconditions: len(blocks) is between 1 and 1000 inclusive; for every i with 0 <= i < len(blocks), 1 <= blocks[i] <= 100000; 1 <= split <= 100. -/
  theorem spec_1 (blocks : Slice Std.I64) (split : Std.I64) (r : Std.I64)
      (hblocks : SliceOK (content blocks)) (hsplit : SplitOK split.val)
      (hres : min_build_time blocks split = ok r) :
      ∃ t : FBTree,
        IsOptimalTree t (content blocks) split.val ∧
          treeCost t (content blocks) split.val = r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (blocks : Slice Std.I64) (split : Std.I64) (r : Std.I64)
        (hblocks : SliceOK (content blocks)) (hsplit : SplitOK split.val)
        (hres : min_build_time blocks split = ok r), ∃ t : FBTree,
          IsOptimalTree t (content blocks) split.val ∧
            treeCost t (content blocks) split.val = r.val) := by
    sorry

  /-- For every blocks and split satisfying the preconditions, min_build_time(blocks, split) returns a result; it does not fail due to overflow, panic, out-of-bounds access, or nontermination.
    Preconditions: len(blocks) is between 1 and 1000 inclusive; for every i with 0 <= i < len(blocks), 1 <= blocks[i] <= 100000; 1 <= split <= 100. -/
  theorem spec_2 (blocks : Slice Std.I64) (split : Std.I64)
      (hblocks : SliceOK (content blocks)) (hsplit : SplitOK split.val) :
      ∃ r : Std.I64, min_build_time blocks split = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (blocks : Slice Std.I64) (split : Std.I64)
        (hblocks : SliceOK (content blocks)) (hsplit : SplitOK split.val), ∃ r : Std.I64, min_build_time blocks split = ok r) := by
    sorry

  /-- Whenever min_build_time(blocks, split) returns r, r >= max_{0 <= i < len(blocks)} blocks[i].
    Preconditions: len(blocks) is between 1 and 1000 inclusive; for every i with 0 <= i < len(blocks), 1 <= blocks[i] <= 100000; 1 <= split <= 100. -/
  theorem spec_3 (blocks : Slice Std.I64) (split : Std.I64) (r : Std.I64)
      (hblocks : SliceOK (content blocks)) (hsplit : SplitOK split.val)
      (hres : min_build_time blocks split = ok r) :
      listMax (content blocks) ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (blocks : Slice Std.I64) (split : Std.I64) (r : Std.I64)
        (hblocks : SliceOK (content blocks)) (hsplit : SplitOK split.val)
        (hres : min_build_time blocks split = ok r), listMax (content blocks) ≤ r.val) := by
    sorry

  /-- Whenever min_build_time(blocks, split) returns r, r <= h * split + max_{0 <= i < len(blocks)} blocks[i], where n = len(blocks) and h is the least nonnegative integer with n <= 2^h.
    Preconditions: len(blocks) is between 1 and 1000 inclusive; for every i with 0 <= i < len(blocks), 1 <= blocks[i] <= 100000; 1 <= split <= 100. -/
  theorem spec_4 (blocks : Slice Std.I64) (split : Std.I64) (r : Std.I64)
      (hblocks : SliceOK (content blocks)) (hsplit : SplitOK split.val)
      (hres : min_build_time blocks split = ok r) :
      r.val ≤
        (ceilLog2 (content blocks).length : Int) * split.val + listMax (content blocks) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (blocks : Slice Std.I64) (split : Std.I64) (r : Std.I64)
        (hblocks : SliceOK (content blocks)) (hsplit : SplitOK split.val)
        (hres : min_build_time blocks split = ok r), r.val ≤
          (ceilLog2 (content blocks).length : Int) * split.val + listMax (content blocks)) := by
    sorry

  /-- Whenever min_build_time(blocks, split) returns r, r = t + split * h, where n = len(blocks) and h is the least nonnegative integer with n <= 2^h.
    Preconditions: len(blocks) is between 1 and 1000 inclusive; for every i with 0 <= i < len(blocks), 1 <= blocks[i] <= 100000; 1 <= split <= 100; there exists an integer t such that blocks[i] = t for every i with 0 <= i < len(blocks). -/
  theorem spec_5 (blocks : Slice Std.I64) (split : Std.I64) (r : Std.I64) (t : Int)
      (hblocks : SliceOK (content blocks)) (hsplit : SplitOK split.val)
      (hconst : ∀ i, i < (content blocks).length → (content blocks).getD i 0 = t)
      (hres : min_build_time blocks split = ok r) :
      r.val = t + split.val * (ceilLog2 (content blocks).length : Int) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (blocks : Slice Std.I64) (split : Std.I64) (r : Std.I64) (t : Int)
        (hblocks : SliceOK (content blocks)) (hsplit : SplitOK split.val)
        (hconst : ∀ i, i < (content blocks).length → (content blocks).getD i 0 = t)
        (hres : min_build_time blocks split = ok r), r.val = t + split.val * (ceilLog2 (content blocks).length : Int)) := by
    sorry

  /-- If min_build_time(blocks, split) returns r and min_build_time(blocks', split) returns r', then r = r'.
    Preconditions: blocks and blocks' are lists with the same length and entries in [1,100000]; len(blocks) is between 1 and 1000 inclusive; len(blocks') = len(blocks); for every integer v, the number of indices i with blocks[i] = v equals the number of indices j with blocks'[j] = v; 1 <= split <= 100. -/
  theorem spec_6 (blocks blocks' : Slice Std.I64) (split : Std.I64)
      (r r' : Std.I64)
      (hblocks : SliceOK (content blocks))
      (hblocks' : ∀ i, i < (content blocks').length →
        1 ≤ (content blocks').getD i 0 ∧ (content blocks').getD i 0 ≤ 100000)
      (hlen : (content blocks').length = (content blocks).length)
      (hperm : ∀ v : Int, occurrences v (content blocks) = occurrences v (content blocks'))
      (hsplit : SplitOK split.val)
      (hres : min_build_time blocks split = ok r)
      (hres' : min_build_time blocks' split = ok r') :
      r = r' := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (blocks blocks' : Slice Std.I64) (split : Std.I64)
        (r r' : Std.I64)
        (hblocks : SliceOK (content blocks))
        (hblocks' : ∀ i, i < (content blocks').length →
          1 ≤ (content blocks').getD i 0 ∧ (content blocks').getD i 0 ≤ 100000)
        (hlen : (content blocks').length = (content blocks).length)
        (hperm : ∀ v : Int, occurrences v (content blocks) = occurrences v (content blocks'))
        (hsplit : SplitOK split.val)
        (hres : min_build_time blocks split = ok r)
        (hres' : min_build_time blocks' split = ok r'), r = r') := by
    sorry

  /-- If min_build_time(blocks, split1) returns r1 and min_build_time(blocks, split2) returns r2, then r1 <= r2.
    Preconditions: len(blocks) is between 1 and 1000 inclusive; for every i with 0 <= i < len(blocks), 1 <= blocks[i] <= 100000; split1 and split2 are integers with 1 <= split1 <= split2 <= 100. -/
  theorem spec_7 (blocks : Slice Std.I64) (split1 split2 : Std.I64)
      (r1 r2 : Std.I64)
      (hblocks : SliceOK (content blocks))
      (hsplit : 1 ≤ split1.val ∧ split1.val ≤ split2.val ∧ split2.val ≤ 100)
      (hres1 : min_build_time blocks split1 = ok r1)
      (hres2 : min_build_time blocks split2 = ok r2) :
      r1.val ≤ r2.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (blocks : Slice Std.I64) (split1 split2 : Std.I64)
        (r1 r2 : Std.I64)
        (hblocks : SliceOK (content blocks))
        (hsplit : 1 ≤ split1.val ∧ split1.val ≤ split2.val ∧ split2.val ≤ 100)
        (hres1 : min_build_time blocks split1 = ok r1)
        (hres2 : min_build_time blocks split2 = ok r2), r1.val ≤ r2.val) := by
    sorry

  /-- If min_build_time(blocks1, split) returns r1 and min_build_time(blocks2, split) returns r2, then r1 <= r2.
    Preconditions: blocks1 and blocks2 are lists with the same length n, where 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= blocks1[i] <= blocks2[i] <= 100000; 1 <= split <= 100. -/
  theorem spec_8 (blocks1 blocks2 : Slice Std.I64) (split : Std.I64)
      (r1 r2 : Std.I64)
      (hblocks1 : SliceOK (content blocks1))
      (hblocks2 : ∀ i, i < (content blocks2).length →
        1 ≤ (content blocks2).getD i 0 ∧ (content blocks2).getD i 0 ≤ 100000)
      (hlen : (content blocks2).length = (content blocks1).length)
      (hle : ∀ i, i < (content blocks1).length →
        (content blocks1).getD i 0 ≤ (content blocks2).getD i 0)
      (hsplit : SplitOK split.val)
      (hres1 : min_build_time blocks1 split = ok r1)
      (hres2 : min_build_time blocks2 split = ok r2) :
      r1.val ≤ r2.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (blocks1 blocks2 : Slice Std.I64) (split : Std.I64)
        (r1 r2 : Std.I64)
        (hblocks1 : SliceOK (content blocks1))
        (hblocks2 : ∀ i, i < (content blocks2).length →
          1 ≤ (content blocks2).getD i 0 ∧ (content blocks2).getD i 0 ≤ 100000)
        (hlen : (content blocks2).length = (content blocks1).length)
        (hle : ∀ i, i < (content blocks1).length →
          (content blocks1).getD i 0 ≤ (content blocks2).getD i 0)
        (hsplit : SplitOK split.val)
        (hres1 : min_build_time blocks1 split = ok r1)
        (hres2 : min_build_time blocks2 split = ok r2), r1.val ≤ r2.val) := by
    sorry

  /-- If min_build_time(sub, split) returns rS and min_build_time(blocks, split) returns r, then rS <= r.
    Preconditions: len(blocks) is between 1 and 1000 inclusive; for every i with 0 <= i < len(blocks), 1 <= blocks[i] <= 100000; 1 <= split <= 100; S is a nonempty subset of {0,...,len(blocks)-1}; sub is the list of values blocks[i] for i in S in increasing order of i. -/
  theorem spec_9 (blocks sub : Slice Std.I64) (split : Std.I64)
      (rS r : Std.I64) (S : Finset Nat)
      (hblocks : SliceOK (content blocks)) (hsplit : SplitOK split.val)
      (hSne : S.Nonempty)
      (hSsub : ∀ i, i ∈ S → i < (content blocks).length)
      (hsub : content sub = selectIndices (content blocks) S)
      (hresS : min_build_time sub split = ok rS)
      (hres : min_build_time blocks split = ok r) :
      rS.val ≤ r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (blocks sub : Slice Std.I64) (split : Std.I64)
        (rS r : Std.I64) (S : Finset Nat)
        (hblocks : SliceOK (content blocks)) (hsplit : SplitOK split.val)
        (hSne : S.Nonempty)
        (hSsub : ∀ i, i ∈ S → i < (content blocks).length)
        (hsub : content sub = selectIndices (content blocks) S)
        (hresS : min_build_time sub split = ok rS)
        (hres : min_build_time blocks split = ok r), rS.val ≤ r.val) := by
    sorry

  /-- Whenever min_build_time(blocks, split) returns r, r >= h * split + min_{0 <= i < len(blocks)} blocks[i], where n = len(blocks) and h is the least nonnegative integer with n <= 2^h.
    Preconditions: len(blocks) is between 1 and 1000 inclusive; for every i with 0 <= i < len(blocks), 1 <= blocks[i] <= 100000; 1 <= split <= 100. -/
  theorem spec_10 (blocks : Slice Std.I64) (split : Std.I64) (r : Std.I64)
      (hblocks : SliceOK (content blocks)) (hsplit : SplitOK split.val)
      (hres : min_build_time blocks split = ok r) :
      (ceilLog2 (content blocks).length : Int) * split.val + listMin (content blocks) ≤
        r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (blocks : Slice Std.I64) (split : Std.I64) (r : Std.I64)
        (hblocks : SliceOK (content blocks)) (hsplit : SplitOK split.val)
        (hres : min_build_time blocks split = ok r), (ceilLog2 (content blocks).length : Int) * split.val + listMin (content blocks) ≤
          r.val) := by
    sorry

  /-- Whenever min_build_time(blocks, split) returns r, r >= split + max_{0 <= i < len(blocks)} blocks[i].
    Preconditions: len(blocks) is between 1 and 1000 inclusive; for every i with 0 <= i < len(blocks), 1 <= blocks[i] <= 100000; 1 <= split <= 100; len(blocks) >= 2. -/
  theorem spec_11 (blocks : Slice Std.I64) (split : Std.I64) (r : Std.I64)
      (hblocks : SliceOK (content blocks)) (hsplit : SplitOK split.val)
      (hlen : 2 ≤ (content blocks).length)
      (hres : min_build_time blocks split = ok r) :
      split.val + listMax (content blocks) ≤ r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (blocks : Slice Std.I64) (split : Std.I64) (r : Std.I64)
        (hblocks : SliceOK (content blocks)) (hsplit : SplitOK split.val)
        (hlen : 2 ≤ (content blocks).length)
        (hres : min_build_time blocks split = ok r), split.val + listMax (content blocks) ≤ r.val) := by
    sorry

  /-- Whenever min_build_time(blocks, split) returns r, r = min_{i in {0,1,2}} max( split + blocks[i], 2*split + max_{j in {0,1,2}, j != i} blocks[j] ).
    Preconditions: len(blocks) is between 1 and 1000 inclusive; for every i with 0 <= i < len(blocks), 1 <= blocks[i] <= 100000; 1 <= split <= 100; len(blocks) = 3. -/
  theorem spec_12 (blocks : Slice Std.I64) (split : Std.I64) (r : Std.I64)
      (hblocks : SliceOK (content blocks)) (hsplit : SplitOK split.val)
      (hlen : (content blocks).length = 3)
      (hres : min_build_time blocks split = ok r) :
      r.val = threeLeafValue (content blocks) split.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (blocks : Slice Std.I64) (split : Std.I64) (r : Std.I64)
        (hblocks : SliceOK (content blocks)) (hsplit : SplitOK split.val)
        (hlen : (content blocks).length = 3)
        (hres : min_build_time blocks split = ok r), r.val = threeLeafValue (content blocks) split.val) := by
    sorry

  /-- If min_build_time(blocks, split) returns r and min_build_time(blocks_plus_c, split) returns r', then r' = r + c.
    Preconditions: len(blocks) is between 1 and 1000 inclusive; for every i with 0 <= i < len(blocks), 1 <= blocks[i] <= 100000; 1 <= split <= 100; c is an integer with 0 <= c and, for every i, 1 <= blocks[i] + c <= 100000; blocks_plus_c is the list with (blocks_plus_c)[i] = blocks[i] + c. -/
  theorem spec_13 (blocks blocks_plus_c : Slice Std.I64) (split : Std.I64)
      (r r' : Std.I64) (c : Int)
      (hblocks : SliceOK (content blocks)) (hsplit : SplitOK split.val)
      (hc : 0 ≤ c)
      (hcblocks : ∀ i, i < (content blocks).length →
        1 ≤ (content blocks).getD i 0 + c ∧ (content blocks).getD i 0 + c ≤ 100000)
      (hlen : (content blocks_plus_c).length = (content blocks).length)
      (hplus : content blocks_plus_c = (content blocks).map (fun x => x + c))
      (hres : min_build_time blocks split = ok r)
      (hres' : min_build_time blocks_plus_c split = ok r') :
      r'.val = r.val + c := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (blocks blocks_plus_c : Slice Std.I64) (split : Std.I64)
        (r r' : Std.I64) (c : Int)
        (hblocks : SliceOK (content blocks)) (hsplit : SplitOK split.val)
        (hc : 0 ≤ c)
        (hcblocks : ∀ i, i < (content blocks).length →
          1 ≤ (content blocks).getD i 0 + c ∧ (content blocks).getD i 0 + c ≤ 100000)
        (hlen : (content blocks_plus_c).length = (content blocks).length)
        (hplus : content blocks_plus_c = (content blocks).map (fun x => x + c))
        (hres : min_build_time blocks split = ok r)
        (hres' : min_build_time blocks_plus_c split = ok r'), r'.val = r.val + c) := by
    sorry

  /-- If min_build_time(blocks, split) returns r and min_build_time(c_blocks, c * split) returns r', then r' = c * r.
    Preconditions: len(blocks) is between 1 and 1000 inclusive; for every i with 0 <= i < len(blocks), 1 <= blocks[i] <= 100000; 1 <= split <= 100; c is an integer with c >= 1, 1 <= c * split <= 100, and for every i, 1 <= c * blocks[i] <= 100000; c_blocks is the list with (c_blocks)[i] = c * blocks[i]. -/
  theorem spec_14 (blocks c_blocks : Slice Std.I64) (split splitc : Std.I64)
      (r r' : Std.I64) (c : Int)
      (hblocks : SliceOK (content blocks)) (hsplit : SplitOK split.val)
      (hc : 1 ≤ c)
      (hcsplit : 1 ≤ c * split.val ∧ c * split.val ≤ 100)
      (hcentries : ∀ i, i < (content blocks).length →
        1 ≤ c * (content blocks).getD i 0 ∧ c * (content blocks).getD i 0 ≤ 100000)
      (hlen : (content c_blocks).length = (content blocks).length)
      (hcblocks : content c_blocks = (content blocks).map (fun x => c * x))
      (hsplitc : splitc.val = c * split.val)
      (hres : min_build_time blocks split = ok r)
      (hres' : min_build_time c_blocks splitc = ok r') :
      r'.val = c * r.val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (blocks c_blocks : Slice Std.I64) (split splitc : Std.I64)
        (r r' : Std.I64) (c : Int)
        (hblocks : SliceOK (content blocks)) (hsplit : SplitOK split.val)
        (hc : 1 ≤ c)
        (hcsplit : 1 ≤ c * split.val ∧ c * split.val ≤ 100)
        (hcentries : ∀ i, i < (content blocks).length →
          1 ≤ c * (content blocks).getD i 0 ∧ c * (content blocks).getD i 0 ≤ 100000)
        (hlen : (content c_blocks).length = (content blocks).length)
        (hcblocks : content c_blocks = (content blocks).map (fun x => c * x))
        (hsplitc : splitc.val = c * split.val)
        (hres : min_build_time blocks split = ok r)
        (hres' : min_build_time c_blocks splitc = ok r'), r'.val = c * r.val) := by
    sorry

  /-- Whenever min_build_time(blocks, split) returns r, there exists a full binary tree T with exactly len(blocks) leaves labelled bijectively by the indices 0,...,len(blocks)-1 and attaining r such that for all i,j, if blocks[i] > blocks[j] then d_T(i) <= d_T(j), where d_T(i) is the number of internal nodes on the root-to-leaf path to the leaf labelled i. Equivalently, there is an optimal schedule in which larger blocks are never assigned to deeper leaves than smaller blocks.
    Preconditions: len(blocks) is between 1 and 1000 inclusive; for every i with 0 <= i < len(blocks), 1 <= blocks[i] <= 100000; 1 <= split <= 100. -/
  theorem spec_15 (blocks : Slice Std.I64) (split : Std.I64) (r : Std.I64)
      (hblocks : SliceOK (content blocks)) (hsplit : SplitOK split.val)
      (hres : min_build_time blocks split = ok r) :
      ∃ t : FBTree,
        IsOptimalTree t (content blocks) split.val ∧
          treeCost t (content blocks) split.val = r.val ∧
            ∀ i j : Fin (content blocks).length,
              (content blocks).get j < (content blocks).get i →
                t.depthOf i.val ≤ t.depthOf j.val := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (blocks : Slice Std.I64) (split : Std.I64) (r : Std.I64)
        (hblocks : SliceOK (content blocks)) (hsplit : SplitOK split.val)
        (hres : min_build_time blocks split = ok r), ∃ t : FBTree,
          IsOptimalTree t (content blocks) split.val ∧
            treeCost t (content blocks) split.val = r.val ∧
              ∀ i j : Fin (content blocks).length,
                (content blocks).get j < (content blocks).get i →
                  t.depthOf i.val ≤ t.depthOf j.val) := by
    sorry

  end AegisSpec.MinBuildTime

import Aegis.SplitPainting.Code.Funs

/-!
# Specifications of `Aegis.SplitPainting.split_painting`

LeetCode problem `describe-the-painting`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.SplitPainting

  structure Seg where
    s : ℤ
    e : ℤ
    c : ℤ
  deriving Repr, DecidableEq

  structure Row where
    l : ℤ
    r : ℤ
    m : ℤ
  deriving Repr, DecidableEq

  def rowOf (v : alloc.vec.Vec I64) : List ℤ := v.val.map IScalar.val

  def inRows (segments : Slice (alloc.vec.Vec I64)) : List (List ℤ) :=
    segments.val.map rowOf

  def outRows (painting : alloc.vec.Vec (alloc.vec.Vec I64)) : List (List ℤ) :=
    painting.val.map rowOf

  def segOfRow (r : List ℤ) : Seg := ⟨r.getD 0 0, r.getD 1 0, r.getD 2 0⟩

  def rowOfList (r : List ℤ) : Row := ⟨r.getD 0 0, r.getD 1 0, r.getD 2 0⟩

  def segsOf (segments : Slice (alloc.vec.Vec I64)) : List Seg :=
    (inRows segments).map segOfRow

  def rowsOf (painting : alloc.vec.Vec (alloc.vec.Vec I64)) : List Row :=
    (outRows painting).map rowOfList

  def Row.toSeg (t : Row) : Seg := ⟨t.l, t.r, t.m⟩

  def ValidSeg (t : Seg) : Prop :=
    0 ≤ t.s ∧ t.s < t.e ∧ t.e ≤ 100000 ∧ 1 ≤ t.c ∧ t.c ≤ 1000000000

  @[reducible] def Covers (t : Seg) (x : ℤ) : Prop := t.s ≤ x ∧ x < t.e

  def activeSegs (S : List Seg) (x : ℤ) : Finset Seg :=
    S.toFinset.filter (fun t => Covers t x)

  def activeColors (S : List Seg) (x : ℤ) : Finset ℤ :=
    (activeSegs S x).image (fun t => t.c)

  def mix (S : List Seg) (x : ℤ) : ℤ :=
    ∑ t ∈ activeSegs S x, t.c

  def painted (S : List Seg) (x : ℤ) : Prop := ∃ t ∈ S, Covers t x

  def InIv (l r x : ℤ) : Prop := l ≤ x ∧ x < r

  def IvDisjoint (l₁ r₁ l₂ r₂ : ℤ) : Prop := r₁ ≤ l₂ ∨ r₂ ≤ l₁

  def MaximalLeft (S : List Seg) (l r : ℤ) : Prop :=
    ¬ ∃ a : ℤ, a < l ∧ (∀ x : ℤ, a ≤ x → x < r → painted S x) ∧
        (∀ x y : ℤ, a ≤ x → x < r → a ≤ y → y < r → activeColors S x = activeColors S y)

  def MaximalRight (S : List Seg) (l r : ℤ) : Prop :=
    ¬ ∃ b : ℤ, r < b ∧ (∀ x : ℤ, l ≤ x → x < b → painted S x) ∧
        (∀ x y : ℤ, l ≤ x → x < b → l ≤ y → y < b → activeColors S x = activeColors S y)

  def Maximal (S : List Seg) (l r : ℤ) : Prop := MaximalLeft S l r ∧ MaximalRight S l r

  def SortedByStart (rows : List Row) : Prop := rows.Pairwise (fun a b => a.l ≤ b.l)

  def adjacentPairs : List Row → List (Row × Row)
    | [] => []
    | [_] => []
    | a :: b :: rest => (a, b) :: adjacentPairs (b :: rest)

  def sAt (S : List Seg) (i : ℕ) : ℤ := (S.getD i ⟨0, 0, 0⟩).s

  def eAt (S : List Seg) (i : ℕ) : ℤ := (S.getD i ⟨0, 0, 0⟩).e

  def cAt (S : List Seg) (i : ℕ) : ℤ := (S.getD i ⟨0, 0, 0⟩).c

  def startSet (S : List Seg) : Finset ℤ := (S.map (fun t => t.s)).toFinset

  def endSet (S : List Seg) : Finset ℤ := (S.map (fun t => t.e)).toFinset

  def Lmin (S : List Seg) : ℤ := ((S.map (fun t => t.s)).min?).getD 0

  def Rmax (S : List Seg) : ℤ := ((S.map (fun t => t.e)).max?).getD 0

  def cmin (S : List Seg) : ℤ := ((S.map (fun t => t.c)).min?).getD 0

  def csum (S : List Seg) : ℤ := (S.map (fun t => t.c)).sum

  /-- Let painting be the returned list. For every point x define A(x) = { c_i : 0 <= i < n and s_i <= x < e_i } and mix(x) = sum_{c in A(x)} c. A point x is painted iff A(x) is nonempty, equivalently mix(x) > 0. Sort the rows of painting by increasing first coordinate; write them as (l_j, r_j, m_j) for 0 <= j < k, where k = len(painting). Then: (1) k >= 1; every original row has length 3, and for every j, l_j < r_j and m_j > 0. (2) For every point x, x lies in the union of the intervals [l_j, r_j) if and only if x is painted. (3) For every j, A(x) is constant over l_j <= x < r_j; write this set as A_j, and m_j = sum_{c in A_j} c. (4) The intervals [l_j, r_j) are pairwise disjoint; since they are sorted, r_j <= l_{j+1} for every 0 <= j < k-1. (5) k is the minimum possible number of half-open segments with integer endpoints that cover exactly the painted set and on each of which A(x) is constant; equivalently, each [l_j, r_j) is a maximal nonempty interval on which A(x) is constant inside the painted set, and for every j with r_j = l_{j+1}, A_j != A_{j+1}. Adjacent rows may have m_j = m_{j+1} when their active color sets differ.
    Preconditions: Let n = len(segments). Assume 1 <= n <= 20000. For every i with 0 <= i < n, len(segments[i]) = 3. Write s_i = segments[i][0], e_i = segments[i][1], c_i = segments[i][2]. Assume 0 <= s_i < e_i <= 100000, 1 <= c_i <= 1000000000, and the c_i are pairwise distinct. -/
  theorem spec_1
      (segments : Slice (alloc.vec.Vec I64))
      (painting : alloc.vec.Vec (alloc.vec.Vec I64))
      (n : ℕ) (hn : n = (inRows segments).length)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 20000)
      (hlen : ∀ v ∈ inRows segments, v.length = 3)
      (hvalid : ∀ t ∈ segsOf segments, ValidSeg t)
      (hne : ((segsOf segments).map (fun t => t.c)).Nodup)
      (hret : Aegis.SplitPainting.split_painting segments = ok painting)
      (sorted : List Row) (hperm : List.Perm sorted (rowsOf painting))
      (hsorted : SortedByStart sorted) :
      (1 ≤ (rowsOf painting).length ∧
        (∀ v ∈ outRows painting, v.length = 3) ∧
        (∀ t ∈ rowsOf painting, t.l < t.r ∧ 0 < t.m)) ∧
      (∀ x : ℤ, (∃ t ∈ rowsOf painting, InIv t.l t.r x) ↔ painted (segsOf segments) x) ∧
      (∀ t ∈ rowsOf painting,
        (∀ x y : ℤ, t.l ≤ x → x < t.r → t.l ≤ y → y < t.r →
          activeColors (segsOf segments) x = activeColors (segsOf segments) y) ∧
        (∑ c ∈ activeColors (segsOf segments) t.l, c = t.m)) ∧
      (∀ a ∈ rowsOf painting, ∀ b ∈ rowsOf painting, a ≠ b →
        IvDisjoint a.l a.r b.l b.r) ∧
      (∀ p ∈ adjacentPairs sorted, p.1.r ≤ p.2.l) ∧
      (∀ t ∈ rowsOf painting, Maximal (segsOf segments) t.l t.r) ∧
      (∀ p ∈ adjacentPairs sorted, p.1.r = p.2.l →
        activeColors (segsOf segments) p.1.l ≠ activeColors (segsOf segments) p.2.l) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (segments : Slice (alloc.vec.Vec I64))
        (painting : alloc.vec.Vec (alloc.vec.Vec I64))
        (n : ℕ) (hn : n = (inRows segments).length)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 20000)
        (hlen : ∀ v ∈ inRows segments, v.length = 3)
        (hvalid : ∀ t ∈ segsOf segments, ValidSeg t)
        (hne : ((segsOf segments).map (fun t => t.c)).Nodup)
        (hret : Aegis.SplitPainting.split_painting segments = ok painting)
        (sorted : List Row) (hperm : List.Perm sorted (rowsOf painting))
        (hsorted : SortedByStart sorted), (1 ≤ (rowsOf painting).length ∧
          (∀ v ∈ outRows painting, v.length = 3) ∧
          (∀ t ∈ rowsOf painting, t.l < t.r ∧ 0 < t.m)) ∧
        (∀ x : ℤ, (∃ t ∈ rowsOf painting, InIv t.l t.r x) ↔ painted (segsOf segments) x) ∧
        (∀ t ∈ rowsOf painting,
          (∀ x y : ℤ, t.l ≤ x → x < t.r → t.l ≤ y → y < t.r →
            activeColors (segsOf segments) x = activeColors (segsOf segments) y) ∧
          (∑ c ∈ activeColors (segsOf segments) t.l, c = t.m)) ∧
        (∀ a ∈ rowsOf painting, ∀ b ∈ rowsOf painting, a ≠ b →
          IvDisjoint a.l a.r b.l b.r) ∧
        (∀ p ∈ adjacentPairs sorted, p.1.r ≤ p.2.l) ∧
        (∀ t ∈ rowsOf painting, Maximal (segsOf segments) t.l t.r) ∧
        (∀ p ∈ adjacentPairs sorted, p.1.r = p.2.l →
          activeColors (segsOf segments) p.1.l ≠ activeColors (segsOf segments) p.2.l)) := by
    sorry

  /-- Let painting be the returned list. Then painting is nonempty, every row of painting has length 3, and for every row (l, r, m) in painting, l < r and m > 0.
    Preconditions: Let n = len(segments). Assume 1 <= n <= 20000. For every i with 0 <= i < n, len(segments[i]) = 3. Write s_i = segments[i][0], e_i = segments[i][1], c_i = segments[i][2]. Assume 0 <= s_i < e_i <= 100000, 1 <= c_i <= 1000000000, and the c_i are pairwise distinct. -/
  theorem spec_2
      (segments : Slice (alloc.vec.Vec I64))
      (painting : alloc.vec.Vec (alloc.vec.Vec I64))
      (n : ℕ) (hn : n = (inRows segments).length)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 20000)
      (hlen : ∀ v ∈ inRows segments, v.length = 3)
      (hvalid : ∀ t ∈ segsOf segments, ValidSeg t)
      (hne : ((segsOf segments).map (fun t => t.c)).Nodup)
      (hret : Aegis.SplitPainting.split_painting segments = ok painting) :
      0 < (rowsOf painting).length ∧
      (∀ v ∈ outRows painting, v.length = 3) ∧
      (∀ t ∈ rowsOf painting, t.l < t.r ∧ 0 < t.m) := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (segments : Slice (alloc.vec.Vec I64))
        (painting : alloc.vec.Vec (alloc.vec.Vec I64))
        (n : ℕ) (hn : n = (inRows segments).length)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 20000)
        (hlen : ∀ v ∈ inRows segments, v.length = 3)
        (hvalid : ∀ t ∈ segsOf segments, ValidSeg t)
        (hne : ((segsOf segments).map (fun t => t.c)).Nodup)
        (hret : Aegis.SplitPainting.split_painting segments = ok painting), 0 < (rowsOf painting).length ∧
        (∀ v ∈ outRows painting, v.length = 3) ∧
        (∀ t ∈ rowsOf painting, t.l < t.r ∧ 0 < t.m)) := by
    sorry

  /-- Let painting be the returned list. Let S = {s_i : 0 <= i < n} union {e_i : 0 <= i < n}. Let Lmin = min_{0 <= i < n} s_i and Rmax = max_{0 <= i < n} e_i. For every row (l, r, m) in painting, l is in S, r is in S, and Lmin <= l < r <= Rmax.
    Preconditions: Let n = len(segments). Assume 1 <= n <= 20000. For every i with 0 <= i < n, len(segments[i]) = 3. Write s_i = segments[i][0], e_i = segments[i][1], c_i = segments[i][2]. Assume 0 <= s_i < e_i <= 100000, 1 <= c_i <= 1000000000, and the c_i are pairwise distinct. -/
  theorem spec_3
      (segments : Slice (alloc.vec.Vec I64))
      (painting : alloc.vec.Vec (alloc.vec.Vec I64))
      (n : ℕ) (hn : n = (inRows segments).length)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 20000)
      (hlen : ∀ v ∈ inRows segments, v.length = 3)
      (hvalid : ∀ t ∈ segsOf segments, ValidSeg t)
      (hne : ((segsOf segments).map (fun t => t.c)).Nodup)
      (hret : Aegis.SplitPainting.split_painting segments = ok painting) :
      ∀ t ∈ rowsOf painting,
        t.l ∈ startSet (segsOf segments) ∪ endSet (segsOf segments) ∧
        t.r ∈ startSet (segsOf segments) ∪ endSet (segsOf segments) ∧
        Lmin (segsOf segments) ≤ t.l ∧ t.l < t.r ∧ t.r ≤ Rmax (segsOf segments) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (segments : Slice (alloc.vec.Vec I64))
        (painting : alloc.vec.Vec (alloc.vec.Vec I64))
        (n : ℕ) (hn : n = (inRows segments).length)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 20000)
        (hlen : ∀ v ∈ inRows segments, v.length = 3)
        (hvalid : ∀ t ∈ segsOf segments, ValidSeg t)
        (hne : ((segsOf segments).map (fun t => t.c)).Nodup)
        (hret : Aegis.SplitPainting.split_painting segments = ok painting), ∀ t ∈ rowsOf painting,
          t.l ∈ startSet (segsOf segments) ∪ endSet (segsOf segments) ∧
          t.r ∈ startSet (segsOf segments) ∪ endSet (segsOf segments) ∧
          Lmin (segsOf segments) ≤ t.l ∧ t.l < t.r ∧ t.r ≤ Rmax (segsOf segments)) := by
    sorry

  /-- Let painting be the returned list. For every point x, x lies in at least one returned half-open interval [l, r) from painting if and only if there exists i with 0 <= i < n and s_i <= x < e_i.
    Preconditions: Let n = len(segments). Assume 1 <= n <= 20000. For every i with 0 <= i < n, len(segments[i]) = 3. Write s_i = segments[i][0], e_i = segments[i][1], c_i = segments[i][2]. Assume 0 <= s_i < e_i <= 100000, 1 <= c_i <= 1000000000, and the c_i are pairwise distinct. -/
  theorem spec_4
      (segments : Slice (alloc.vec.Vec I64))
      (painting : alloc.vec.Vec (alloc.vec.Vec I64))
      (n : ℕ) (hn : n = (inRows segments).length)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 20000)
      (hlen : ∀ v ∈ inRows segments, v.length = 3)
      (hvalid : ∀ t ∈ segsOf segments, ValidSeg t)
      (hne : ((segsOf segments).map (fun t => t.c)).Nodup)
      (hret : Aegis.SplitPainting.split_painting segments = ok painting) :
      ∀ x : ℤ, (∃ t ∈ rowsOf painting, InIv t.l t.r x) ↔ painted (segsOf segments) x := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (segments : Slice (alloc.vec.Vec I64))
        (painting : alloc.vec.Vec (alloc.vec.Vec I64))
        (n : ℕ) (hn : n = (inRows segments).length)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 20000)
        (hlen : ∀ v ∈ inRows segments, v.length = 3)
        (hvalid : ∀ t ∈ segsOf segments, ValidSeg t)
        (hne : ((segsOf segments).map (fun t => t.c)).Nodup)
        (hret : Aegis.SplitPainting.split_painting segments = ok painting), ∀ x : ℤ, (∃ t ∈ rowsOf painting, InIv t.l t.r x) ↔ painted (segsOf segments) x) := by
    sorry

  /-- Let painting be the returned list. For every row (l, r, m) in painting and every point x with l <= x < r, m = sum_{i: 0 <= i < n and s_i <= x < e_i} c_i.
    Preconditions: Let n = len(segments). Assume 1 <= n <= 20000. For every i with 0 <= i < n, len(segments[i]) = 3. Write s_i = segments[i][0], e_i = segments[i][1], c_i = segments[i][2]. Assume 0 <= s_i < e_i <= 100000, 1 <= c_i <= 1000000000, and the c_i are pairwise distinct. -/
  theorem spec_5
      (segments : Slice (alloc.vec.Vec I64))
      (painting : alloc.vec.Vec (alloc.vec.Vec I64))
      (n : ℕ) (hn : n = (inRows segments).length)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 20000)
      (hlen : ∀ v ∈ inRows segments, v.length = 3)
      (hvalid : ∀ t ∈ segsOf segments, ValidSeg t)
      (hne : ((segsOf segments).map (fun t => t.c)).Nodup)
      (hret : Aegis.SplitPainting.split_painting segments = ok painting) :
      ∀ t ∈ rowsOf painting, ∀ x : ℤ, InIv t.l t.r x → t.m = mix (segsOf segments) x := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (segments : Slice (alloc.vec.Vec I64))
        (painting : alloc.vec.Vec (alloc.vec.Vec I64))
        (n : ℕ) (hn : n = (inRows segments).length)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 20000)
        (hlen : ∀ v ∈ inRows segments, v.length = 3)
        (hvalid : ∀ t ∈ segsOf segments, ValidSeg t)
        (hne : ((segsOf segments).map (fun t => t.c)).Nodup)
        (hret : Aegis.SplitPainting.split_painting segments = ok painting), ∀ t ∈ rowsOf painting, ∀ x : ℤ, InIv t.l t.r x → t.m = mix (segsOf segments) x) := by
    sorry

  /-- Let painting be the returned list. For any two distinct rows (l, r, m) and (l', r', m') of painting, the half-open intervals [l, r) and [l', r') are disjoint. Equivalently, after sorting the rows by increasing l as (l_j, r_j, m_j) for 0 <= j < k, r_j <= l_{j+1} for every 0 <= j < k-1.
    Preconditions: Let n = len(segments). Assume 1 <= n <= 20000. For every i with 0 <= i < n, len(segments[i]) = 3. Write s_i = segments[i][0], e_i = segments[i][1], c_i = segments[i][2]. Assume 0 <= s_i < e_i <= 100000, 1 <= c_i <= 1000000000, and the c_i are pairwise distinct. -/
  theorem spec_6
      (segments : Slice (alloc.vec.Vec I64))
      (painting : alloc.vec.Vec (alloc.vec.Vec I64))
      (n : ℕ) (hn : n = (inRows segments).length)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 20000)
      (hlen : ∀ v ∈ inRows segments, v.length = 3)
      (hvalid : ∀ t ∈ segsOf segments, ValidSeg t)
      (hne : ((segsOf segments).map (fun t => t.c)).Nodup)
      (hret : Aegis.SplitPainting.split_painting segments = ok painting)
      (sorted : List Row) (hperm : List.Perm sorted (rowsOf painting))
      (hsorted : SortedByStart sorted) :
      (∀ a ∈ rowsOf painting, ∀ b ∈ rowsOf painting, a ≠ b →
        IvDisjoint a.l a.r b.l b.r) ∧
      (∀ p ∈ adjacentPairs sorted, p.1.r ≤ p.2.l) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (segments : Slice (alloc.vec.Vec I64))
        (painting : alloc.vec.Vec (alloc.vec.Vec I64))
        (n : ℕ) (hn : n = (inRows segments).length)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 20000)
        (hlen : ∀ v ∈ inRows segments, v.length = 3)
        (hvalid : ∀ t ∈ segsOf segments, ValidSeg t)
        (hne : ((segsOf segments).map (fun t => t.c)).Nodup)
        (hret : Aegis.SplitPainting.split_painting segments = ok painting)
        (sorted : List Row) (hperm : List.Perm sorted (rowsOf painting))
        (hsorted : SortedByStart sorted), (∀ a ∈ rowsOf painting, ∀ b ∈ rowsOf painting, a ≠ b →
          IvDisjoint a.l a.r b.l b.r) ∧
        (∀ p ∈ adjacentPairs sorted, p.1.r ≤ p.2.l)) := by
    sorry

  /-- Let painting be the returned list. Sort its rows by increasing first coordinate as (l_j, r_j, m_j) for 0 <= j < k, and define A(x) = { c_i : 0 <= i < n and s_i <= x < e_i }. For every j with 0 <= j < k-1 and r_j = l_{j+1}, we have A(l_j) != A(l_{j+1}); equivalently, the set of active colors changes at their common endpoint. Thus no two adjacent output segments with the same active color set can be merged. Two adjacent segments may nevertheless have m_j = m_{j+1}, and they must still be kept separate when their active color sets differ.
    Preconditions: Let n = len(segments). Assume 1 <= n <= 20000. For every i with 0 <= i < n, len(segments[i]) = 3. Write s_i = segments[i][0], e_i = segments[i][1], c_i = segments[i][2]. Assume 0 <= s_i < e_i <= 100000, 1 <= c_i <= 1000000000, and the c_i are pairwise distinct. -/
  theorem spec_7
      (segments : Slice (alloc.vec.Vec I64))
      (painting : alloc.vec.Vec (alloc.vec.Vec I64))
      (n : ℕ) (hn : n = (inRows segments).length)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 20000)
      (hlen : ∀ v ∈ inRows segments, v.length = 3)
      (hvalid : ∀ t ∈ segsOf segments, ValidSeg t)
      (hne : ((segsOf segments).map (fun t => t.c)).Nodup)
      (hret : Aegis.SplitPainting.split_painting segments = ok painting)
      (sorted : List Row) (hperm : List.Perm sorted (rowsOf painting))
      (hsorted : SortedByStart sorted) :
      ∀ p ∈ adjacentPairs sorted, p.1.r = p.2.l →
        activeColors (segsOf segments) p.1.l ≠ activeColors (segsOf segments) p.2.l := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (segments : Slice (alloc.vec.Vec I64))
        (painting : alloc.vec.Vec (alloc.vec.Vec I64))
        (n : ℕ) (hn : n = (inRows segments).length)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 20000)
        (hlen : ∀ v ∈ inRows segments, v.length = 3)
        (hvalid : ∀ t ∈ segsOf segments, ValidSeg t)
        (hne : ((segsOf segments).map (fun t => t.c)).Nodup)
        (hret : Aegis.SplitPainting.split_painting segments = ok painting)
        (sorted : List Row) (hperm : List.Perm sorted (rowsOf painting))
        (hsorted : SortedByStart sorted), ∀ p ∈ adjacentPairs sorted, p.1.r = p.2.l →
          activeColors (segsOf segments) p.1.l ≠ activeColors (segsOf segments) p.2.l) := by
    sorry

  /-- Whenever the preconditions hold, the function returns a result; it does not fail by arithmetic overflow, out-of-bounds access, or panic.
    Preconditions: Let n = len(segments). Assume 1 <= n <= 20000. For every i with 0 <= i < n, len(segments[i]) = 3. Write s_i = segments[i][0], e_i = segments[i][1], c_i = segments[i][2]. Assume 0 <= s_i < e_i <= 100000, 1 <= c_i <= 1000000000, and the c_i are pairwise distinct. -/
  theorem spec_8
      (segments : Slice (alloc.vec.Vec I64))
      (n : ℕ) (hn : n = (inRows segments).length)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 20000)
      (hlen : ∀ v ∈ inRows segments, v.length = 3)
      (hvalid : ∀ t ∈ segsOf segments, ValidSeg t)
      (hne : ((segsOf segments).map (fun t => t.c)).Nodup) :
      ∃ painting : alloc.vec.Vec (alloc.vec.Vec I64),
        Aegis.SplitPainting.split_painting segments = ok painting := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (segments : Slice (alloc.vec.Vec I64))
        (n : ℕ) (hn : n = (inRows segments).length)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 20000)
        (hlen : ∀ v ∈ inRows segments, v.length = 3)
        (hvalid : ∀ t ∈ segsOf segments, ValidSeg t)
        (hne : ((segsOf segments).map (fun t => t.c)).Nodup), ∃ painting : alloc.vec.Vec (alloc.vec.Vec I64),
          Aegis.SplitPainting.split_painting segments = ok painting) := by
    sorry

  /-- Let painting be the returned list. Considered as a set of rows ignoring order, painting is exactly { (s_0, e_0, c_0) }. Equivalently, after sorting, k = 1, l_0 = s_0, r_0 = e_0, and m_0 = c_0.
    Preconditions: Let n = len(segments). Assume 1 <= n <= 20000. For every i with 0 <= i < n, len(segments[i]) = 3. Write s_i = segments[i][0], e_i = segments[i][1], c_i = segments[i][2]. Assume 0 <= s_i < e_i <= 100000, 1 <= c_i <= 1000000000, and the c_i are pairwise distinct. Also assume n = 1. -/
  theorem spec_9
      (segments : Slice (alloc.vec.Vec I64))
      (painting : alloc.vec.Vec (alloc.vec.Vec I64))
      (n : ℕ) (hn : n = (inRows segments).length)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 20000) (hn_one : n = 1)
      (hlen : ∀ v ∈ inRows segments, v.length = 3)
      (hvalid : ∀ t ∈ segsOf segments, ValidSeg t)
      (hne : ((segsOf segments).map (fun t => t.c)).Nodup)
      (hret : Aegis.SplitPainting.split_painting segments = ok painting) :
      List.Perm ((rowsOf painting).map Row.toSeg)
        [⟨sAt (segsOf segments) 0, eAt (segsOf segments) 0, cAt (segsOf segments) 0⟩] := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (segments : Slice (alloc.vec.Vec I64))
        (painting : alloc.vec.Vec (alloc.vec.Vec I64))
        (n : ℕ) (hn : n = (inRows segments).length)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 20000) (hn_one : n = 1)
        (hlen : ∀ v ∈ inRows segments, v.length = 3)
        (hvalid : ∀ t ∈ segsOf segments, ValidSeg t)
        (hne : ((segsOf segments).map (fun t => t.c)).Nodup)
        (hret : Aegis.SplitPainting.split_painting segments = ok painting), List.Perm ((rowsOf painting).map Row.toSeg)
          [⟨sAt (segsOf segments) 0, eAt (segsOf segments) 0, cAt (segsOf segments) 0⟩]) := by
    sorry

  /-- Let painting be the returned list. Considered as a set of rows ignoring order, painting is exactly { (s_i, e_i, c_i) : 0 <= i < n }.
    Preconditions: Let n = len(segments). Assume 1 <= n <= 20000. For every i with 0 <= i < n, len(segments[i]) = 3. Write s_i = segments[i][0], e_i = segments[i][1], c_i = segments[i][2]. Assume 0 <= s_i < e_i <= 100000, 1 <= c_i <= 1000000000, and the c_i are pairwise distinct. Also assume that for all i, j with 0 <= i < j < n, the intervals [s_i, e_i) and [s_j, e_j) do not overlap, i.e., e_i <= s_j or e_j <= s_i. -/
  theorem spec_10
      (segments : Slice (alloc.vec.Vec I64))
      (painting : alloc.vec.Vec (alloc.vec.Vec I64))
      (n : ℕ) (hn : n = (inRows segments).length)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 20000)
      (hlen : ∀ v ∈ inRows segments, v.length = 3)
      (hvalid : ∀ t ∈ segsOf segments, ValidSeg t)
      (hne : ((segsOf segments).map (fun t => t.c)).Nodup)
      (hsep : ∀ a ∈ segsOf segments, ∀ b ∈ segsOf segments, a ≠ b →
        a.e ≤ b.s ∨ b.e ≤ a.s)
      (hret : Aegis.SplitPainting.split_painting segments = ok painting) :
      List.Perm ((rowsOf painting).map Row.toSeg) (segsOf segments) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (segments : Slice (alloc.vec.Vec I64))
        (painting : alloc.vec.Vec (alloc.vec.Vec I64))
        (n : ℕ) (hn : n = (inRows segments).length)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 20000)
        (hlen : ∀ v ∈ inRows segments, v.length = 3)
        (hvalid : ∀ t ∈ segsOf segments, ValidSeg t)
        (hne : ((segsOf segments).map (fun t => t.c)).Nodup)
        (hsep : ∀ a ∈ segsOf segments, ∀ b ∈ segsOf segments, a ≠ b →
          a.e ≤ b.s ∨ b.e ≤ a.s)
        (hret : Aegis.SplitPainting.split_painting segments = ok painting), List.Perm ((rowsOf painting).map Row.toSeg) (segsOf segments)) := by
    sorry

  /-- Let painting be the returned list. Considered as a set of rows ignoring order, painting is exactly { (s, e, sum_{i=0}^{n-1} c_i) }. In particular, it has exactly one row.
    Preconditions: Let n = len(segments). Assume 1 <= n <= 20000. For every i with 0 <= i < n, len(segments[i]) = 3. Write s_i = segments[i][0], e_i = segments[i][1], c_i = segments[i][2]. Assume 0 <= s_i < e_i <= 100000, 1 <= c_i <= 1000000000, and the c_i are pairwise distinct. Also assume there exist integers s and e such that for every i, s_i = s and e_i = e. -/
  theorem spec_11
      (segments : Slice (alloc.vec.Vec I64))
      (painting : alloc.vec.Vec (alloc.vec.Vec I64))
      (n : ℕ) (hn : n = (inRows segments).length)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 20000)
      (hlen : ∀ v ∈ inRows segments, v.length = 3)
      (hvalid : ∀ t ∈ segsOf segments, ValidSeg t)
      (hne : ((segsOf segments).map (fun t => t.c)).Nodup)
      (s e : ℤ) (hunif : ∀ t ∈ segsOf segments, t.s = s ∧ t.e = e)
      (hret : Aegis.SplitPainting.split_painting segments = ok painting) :
      List.Perm ((rowsOf painting).map Row.toSeg) [⟨s, e, csum (segsOf segments)⟩] := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (segments : Slice (alloc.vec.Vec I64))
        (painting : alloc.vec.Vec (alloc.vec.Vec I64))
        (n : ℕ) (hn : n = (inRows segments).length)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 20000)
        (hlen : ∀ v ∈ inRows segments, v.length = 3)
        (hvalid : ∀ t ∈ segsOf segments, ValidSeg t)
        (hne : ((segsOf segments).map (fun t => t.c)).Nodup)
        (s e : ℤ) (hunif : ∀ t ∈ segsOf segments, t.s = s ∧ t.e = e)
        (hret : Aegis.SplitPainting.split_painting segments = ok painting), List.Perm ((rowsOf painting).map Row.toSeg) [⟨s, e, csum (segsOf segments)⟩]) := by
    sorry

  /-- Let painting be the returned list. For every row (l, r, m) in painting, min_{0 <= i < n} c_i <= m <= sum_{i=0}^{n-1} c_i.
    Preconditions: Let n = len(segments). Assume 1 <= n <= 20000. For every i with 0 <= i < n, len(segments[i]) = 3. Write s_i = segments[i][0], e_i = segments[i][1], c_i = segments[i][2]. Assume 0 <= s_i < e_i <= 100000, 1 <= c_i <= 1000000000, and the c_i are pairwise distinct. -/
  theorem spec_12
      (segments : Slice (alloc.vec.Vec I64))
      (painting : alloc.vec.Vec (alloc.vec.Vec I64))
      (n : ℕ) (hn : n = (inRows segments).length)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 20000)
      (hlen : ∀ v ∈ inRows segments, v.length = 3)
      (hvalid : ∀ t ∈ segsOf segments, ValidSeg t)
      (hne : ((segsOf segments).map (fun t => t.c)).Nodup)
      (hret : Aegis.SplitPainting.split_painting segments = ok painting) :
      ∀ t ∈ rowsOf painting,
        cmin (segsOf segments) ≤ t.m ∧ t.m ≤ csum (segsOf segments) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (segments : Slice (alloc.vec.Vec I64))
        (painting : alloc.vec.Vec (alloc.vec.Vec I64))
        (n : ℕ) (hn : n = (inRows segments).length)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 20000)
        (hlen : ∀ v ∈ inRows segments, v.length = 3)
        (hvalid : ∀ t ∈ segsOf segments, ValidSeg t)
        (hne : ((segsOf segments).map (fun t => t.c)).Nodup)
        (hret : Aegis.SplitPainting.split_painting segments = ok painting), ∀ t ∈ rowsOf painting,
          cmin (segsOf segments) ≤ t.m ∧ t.m ≤ csum (segsOf segments)) := by
    sorry

  /-- Let painting be the list returned for segments and painting' the list returned for segments'. Sort both lists by increasing first coordinate. Then the sorted lists are equal row by row.
    Preconditions: Let n = len(segments). Assume 1 <= n <= 20000. For every i with 0 <= i < n, len(segments[i]) = 3. Write s_i = segments[i][0], e_i = segments[i][1], c_i = segments[i][2]. Assume 0 <= s_i < e_i <= 100000, 1 <= c_i <= 1000000000, and the c_i are pairwise distinct. Let segments' be another input with n' = len(segments'). Assume n' = n, len(segments'[i]) = 3 for every i, and writing s'_i, e'_i, c'_i for its entries, assume 0 <= s'_i < e'_i <= 100000, 1 <= c'_i <= 1000000000, and the c'_i are pairwise distinct. Also assume segments' is a permutation of the rows of segments. -/
  theorem spec_13
      (segments segments' : Slice (alloc.vec.Vec I64))
      (painting painting' : alloc.vec.Vec (alloc.vec.Vec I64))
      (n n' : ℕ)
      (hn : n = (inRows segments).length)
      (hn' : n' = (inRows segments').length)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 20000) (hn_eq : n' = n)
      (hlen : ∀ v ∈ inRows segments, v.length = 3)
      (hlen' : ∀ v ∈ inRows segments', v.length = 3)
      (hvalid : ∀ t ∈ segsOf segments, ValidSeg t)
      (hvalid' : ∀ t ∈ segsOf segments', ValidSeg t)
      (hne : ((segsOf segments).map (fun t => t.c)).Nodup)
      (hne' : ((segsOf segments').map (fun t => t.c)).Nodup)
      (hperm_in : List.Perm (inRows segments') (inRows segments))
      (hret : Aegis.SplitPainting.split_painting segments = ok painting)
      (hret' : Aegis.SplitPainting.split_painting segments' = ok painting')
      (sorted sorted' : List Row)
      (hperm : List.Perm sorted (rowsOf painting)) (hsorted : SortedByStart sorted)
      (hperm' : List.Perm sorted' (rowsOf painting')) (hsorted' : SortedByStart sorted') :
      sorted = sorted' := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (segments segments' : Slice (alloc.vec.Vec I64))
        (painting painting' : alloc.vec.Vec (alloc.vec.Vec I64))
        (n n' : ℕ)
        (hn : n = (inRows segments).length)
        (hn' : n' = (inRows segments').length)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 20000) (hn_eq : n' = n)
        (hlen : ∀ v ∈ inRows segments, v.length = 3)
        (hlen' : ∀ v ∈ inRows segments', v.length = 3)
        (hvalid : ∀ t ∈ segsOf segments, ValidSeg t)
        (hvalid' : ∀ t ∈ segsOf segments', ValidSeg t)
        (hne : ((segsOf segments).map (fun t => t.c)).Nodup)
        (hne' : ((segsOf segments').map (fun t => t.c)).Nodup)
        (hperm_in : List.Perm (inRows segments') (inRows segments))
        (hret : Aegis.SplitPainting.split_painting segments = ok painting)
        (hret' : Aegis.SplitPainting.split_painting segments' = ok painting')
        (sorted sorted' : List Row)
        (hperm : List.Perm sorted (rowsOf painting)) (hsorted : SortedByStart sorted)
        (hperm' : List.Perm sorted' (rowsOf painting')) (hsorted' : SortedByStart sorted'), sorted = sorted') := by
    sorry

  /-- Let painting be the returned list, sorted by increasing first coordinate as (l_j, r_j, m_j) for 0 <= j < k, and define A(x) = { c_i : 0 <= i < n and s_i <= x < e_i }. For every j, A(x) is constant on [l_j, r_j), and [l_j, r_j) is exactly a maximal nonempty interval contained in the painted set on which A(x) is constant: there is no point a < l_j such that [a, r_j) is contained in the painted set and A(x) is constant for all x with a <= x < r_j, and there is no point b > r_j such that [l_j, b) is contained in the painted set and A(x) is constant for all x with l_j <= x < b.
    Preconditions: Let n = len(segments). Assume 1 <= n <= 20000. For every i with 0 <= i < n, len(segments[i]) = 3. Write s_i = segments[i][0], e_i = segments[i][1], c_i = segments[i][2]. Assume 0 <= s_i < e_i <= 100000, 1 <= c_i <= 1000000000, and the c_i are pairwise distinct. -/
  theorem spec_14
      (segments : Slice (alloc.vec.Vec I64))
      (painting : alloc.vec.Vec (alloc.vec.Vec I64))
      (n : ℕ) (hn : n = (inRows segments).length)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 20000)
      (hlen : ∀ v ∈ inRows segments, v.length = 3)
      (hvalid : ∀ t ∈ segsOf segments, ValidSeg t)
      (hne : ((segsOf segments).map (fun t => t.c)).Nodup)
      (hret : Aegis.SplitPainting.split_painting segments = ok painting) :
      ∀ t ∈ rowsOf painting,
        (∀ x : ℤ, InIv t.l t.r x → activeColors (segsOf segments) x =
          activeColors (segsOf segments) t.l) ∧
        (∀ x : ℤ, InIv t.l t.r x → painted (segsOf segments) x) ∧
        Maximal (segsOf segments) t.l t.r := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (segments : Slice (alloc.vec.Vec I64))
        (painting : alloc.vec.Vec (alloc.vec.Vec I64))
        (n : ℕ) (hn : n = (inRows segments).length)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 20000)
        (hlen : ∀ v ∈ inRows segments, v.length = 3)
        (hvalid : ∀ t ∈ segsOf segments, ValidSeg t)
        (hne : ((segsOf segments).map (fun t => t.c)).Nodup)
        (hret : Aegis.SplitPainting.split_painting segments = ok painting), ∀ t ∈ rowsOf painting,
          (∀ x : ℤ, InIv t.l t.r x → activeColors (segsOf segments) x =
            activeColors (segsOf segments) t.l) ∧
          (∀ x : ℤ, InIv t.l t.r x → painted (segsOf segments) x) ∧
          Maximal (segsOf segments) t.l t.r) := by
    sorry

  /-- Let painting be the returned list and define mix(x) = sum_{i: 0 <= i < n and s_i <= x < e_i} c_i. For every point x in the painted set (that is, mix(x) > 0), there is exactly one row (l, r, m) of painting such that l <= x < r, and for this row m = mix(x).
    Preconditions: Let n = len(segments). Assume 1 <= n <= 20000. For every i with 0 <= i < n, len(segments[i]) = 3. Write s_i = segments[i][0], e_i = segments[i][1], c_i = segments[i][2]. Assume 0 <= s_i < e_i <= 100000, 1 <= c_i <= 1000000000, and the c_i are pairwise distinct. -/
  theorem spec_15
      (segments : Slice (alloc.vec.Vec I64))
      (painting : alloc.vec.Vec (alloc.vec.Vec I64))
      (n : ℕ) (hn : n = (inRows segments).length)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 20000)
      (hlen : ∀ v ∈ inRows segments, v.length = 3)
      (hvalid : ∀ t ∈ segsOf segments, ValidSeg t)
      (hne : ((segsOf segments).map (fun t => t.c)).Nodup)
      (hret : Aegis.SplitPainting.split_painting segments = ok painting) :
      ∀ x : ℤ, painted (segsOf segments) x →
        ∃ t ∈ rowsOf painting,
          InIv t.l t.r x ∧ t.m = mix (segsOf segments) x ∧
          (∀ t' ∈ rowsOf painting, InIv t'.l t'.r x → t' = t) := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (segments : Slice (alloc.vec.Vec I64))
        (painting : alloc.vec.Vec (alloc.vec.Vec I64))
        (n : ℕ) (hn : n = (inRows segments).length)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 20000)
        (hlen : ∀ v ∈ inRows segments, v.length = 3)
        (hvalid : ∀ t ∈ segsOf segments, ValidSeg t)
        (hne : ((segsOf segments).map (fun t => t.c)).Nodup)
        (hret : Aegis.SplitPainting.split_painting segments = ok painting), ∀ x : ℤ, painted (segsOf segments) x →
          ∃ t ∈ rowsOf painting,
            InIv t.l t.r x ∧ t.m = mix (segsOf segments) x ∧
            (∀ t' ∈ rowsOf painting, InIv t'.l t'.r x → t' = t)) := by
    sorry

  end AegisSpec.SplitPainting

import Aegis.LeastInterval.Code.Funs

/-!
# Specifications of `Aegis.LeastInterval.least_interval`

LeetCode problem `task-scheduler`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.LeastInterval

  namespace AegisSpec.LeastInterval

  def SizePre (tasks : Slice (alloc.vec.Vec Std.U8)) : Prop :=
    1 ≤ tasks.val.length ∧ tasks.val.length ≤ 10000

  def BytesPre (tasks : Slice (alloc.vec.Vec Std.U8)) : Prop :=
    ∀ v ∈ tasks.val, v.val.length = 1 ∧ ∀ b ∈ v.val, 65 ≤ b.val ∧ b.val ≤ 90

  def NPre (n : Std.I64) : Prop :=
    0 ≤ n.val ∧ n.val ≤ 100

  def occ (tasks : Slice (alloc.vec.Vec Std.U8)) (v : alloc.vec.Vec Std.U8) : ℕ :=
    (tasks.val.filter (fun t => decide (t = v))).length

  def maxfreq (tasks : Slice (alloc.vec.Vec Std.U8)) : ℕ :=
    (tasks.val.map (occ tasks)).foldr max 0

  def cntMax (tasks : Slice (alloc.vec.Vec Std.U8)) : ℕ :=
    ((tasks.val.toFinset).filter (fun v => occ tasks v = maxfreq tasks)).card

  def ValidSchedule (tasks : Slice (alloc.vec.Vec Std.U8)) (n : Std.I64) (L : ℕ)
      (s : Fin L → Option (alloc.vec.Vec Std.U8)) : Prop :=
    (∀ v, ((Finset.univ : Finset (Fin L)).filter (fun p => s p = some v)).card
        = occ tasks v) ∧
      (∀ p q : Fin L, p < q → ∀ v, s p = some v → s q = some v →
        (q.val : ℤ) - (p.val : ℤ) ≥ n.val + 1)

  /-- Let m = len(tasks). For each label v, let freq(v) be the number of indices i with 0 <= i < m and tasks[i] = v. Let maxfreq = max{ freq(tasks[i]) | 0 <= i < m }. Let cnt_max = |{ v | freq(v) = maxfreq }|. The function returns a result r and r = max(m, (maxfreq - 1) * (n + 1) + cnt_max).
    Preconditions: 1 <= len(tasks) <= 10000; for every i with 0 <= i < len(tasks), len(tasks[i]) = 1 and 65 <= tasks[i][0] <= 90; and 0 <= n <= 100. -/
  theorem spec_1 (tasks : Slice (alloc.vec.Vec Std.U8)) (n : Std.I64)
      (hsize : SizePre tasks) (hbytes : BytesPre tasks) (hn : NPre n) :
      ∃ r : Std.I64, least_interval tasks n = ok r ∧
        r.val = max (tasks.val.length : ℤ)
          (((maxfreq tasks : ℤ) - 1) * (n.val + 1) + (cntMax tasks : ℤ)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (tasks : Slice (alloc.vec.Vec Std.U8)) (n : Std.I64)
        (hsize : SizePre tasks) (hbytes : BytesPre tasks) (hn : NPre n), ∃ r : Std.I64, least_interval tasks n = ok r ∧
          r.val = max (tasks.val.length : ℤ)
            (((maxfreq tasks : ℤ) - 1) * (n.val + 1) + (cntMax tasks : ℤ))) := by
    sorry

  /-- The function returns a result r (it does not fail).
    Preconditions: 1 <= len(tasks) <= 10000; for every i with 0 <= i < len(tasks), len(tasks[i]) = 1 and 65 <= tasks[i][0] <= 90; and 0 <= n <= 100. -/
  theorem spec_2 (tasks : Slice (alloc.vec.Vec Std.U8)) (n : Std.I64)
      (hsize : SizePre tasks) (hbytes : BytesPre tasks) (hn : NPre n) :
      ∃ r : Std.I64, least_interval tasks n = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (tasks : Slice (alloc.vec.Vec Std.U8)) (n : Std.I64)
        (hsize : SizePre tasks) (hbytes : BytesPre tasks) (hn : NPre n), ∃ r : Std.I64, least_interval tasks n = ok r) := by
    sorry

  /-- Let m = len(tasks). The function returns a result r and r >= m.
    Preconditions: 1 <= len(tasks) <= 10000; for every i with 0 <= i < len(tasks), len(tasks[i]) = 1 and 65 <= tasks[i][0] <= 90; and 0 <= n <= 100. -/
  theorem spec_3 (tasks : Slice (alloc.vec.Vec Std.U8)) (n : Std.I64)
      (hsize : SizePre tasks) (hbytes : BytesPre tasks) (hn : NPre n) :
      ∃ r : Std.I64, least_interval tasks n = ok r ∧ (tasks.val.length : ℤ) ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (tasks : Slice (alloc.vec.Vec Std.U8)) (n : Std.I64)
        (hsize : SizePre tasks) (hbytes : BytesPre tasks) (hn : NPre n), ∃ r : Std.I64, least_interval tasks n = ok r ∧ (tasks.val.length : ℤ) ≤ r.val) := by
    sorry

  /-- Let maxfreq be the maximum frequency of any label in tasks, and let cnt_max be the number of distinct labels achieving that maximum frequency. The function returns a result r and r >= (maxfreq - 1) * (n + 1) + cnt_max.
    Preconditions: 1 <= len(tasks) <= 10000; for every i with 0 <= i < len(tasks), len(tasks[i]) = 1 and 65 <= tasks[i][0] <= 90; and 0 <= n <= 100. -/
  theorem spec_4 (tasks : Slice (alloc.vec.Vec Std.U8)) (n : Std.I64)
      (hsize : SizePre tasks) (hbytes : BytesPre tasks) (hn : NPre n) :
      ∃ r : Std.I64, least_interval tasks n = ok r ∧
        ((maxfreq tasks : ℤ) - 1) * (n.val + 1) + (cntMax tasks : ℤ) ≤ r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (tasks : Slice (alloc.vec.Vec Std.U8)) (n : Std.I64)
        (hsize : SizePre tasks) (hbytes : BytesPre tasks) (hn : NPre n), ∃ r : Std.I64, least_interval tasks n = ok r ∧
          ((maxfreq tasks : ℤ) - 1) * (n.val + 1) + (cntMax tasks : ℤ) ≤ r.val) := by
    sorry

  /-- Let m = len(tasks). For a label v, let freq(v) be the number of indices i with 0 <= i < m and tasks[i] = v. A schedule of length L is a function s : {0,1,...,L-1} -> Option (Vec U8) such that: (a) for every label v, the number of indices p with s[p] = Some v equals freq(v); (b) for any p < q with s[p] = s[q] = Some v, we have q - p >= n + 1. The function returns a result r and there exists a valid schedule of length r.
    Preconditions: 1 <= len(tasks) <= 10000; for every i with 0 <= i < len(tasks), len(tasks[i]) = 1 and 65 <= tasks[i][0] <= 90; and 0 <= n <= 100. -/
  theorem spec_5 (tasks : Slice (alloc.vec.Vec Std.U8)) (n : Std.I64)
      (hsize : SizePre tasks) (hbytes : BytesPre tasks) (hn : NPre n) :
      ∃ r : Std.I64, least_interval tasks n = ok r ∧
        ∃ s : Fin r.val.toNat → Option (alloc.vec.Vec Std.U8),
          ValidSchedule tasks n r.val.toNat s := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (tasks : Slice (alloc.vec.Vec Std.U8)) (n : Std.I64)
        (hsize : SizePre tasks) (hbytes : BytesPre tasks) (hn : NPre n), ∃ r : Std.I64, least_interval tasks n = ok r ∧
          ∃ s : Fin r.val.toNat → Option (alloc.vec.Vec Std.U8),
            ValidSchedule tasks n r.val.toNat s) := by
    sorry

  /-- Let m = len(tasks). Define a valid schedule of length L as in spec_5. The function returns a result r and for every integer L with 0 <= L < r, there does not exist a valid schedule of length L.
    Preconditions: 1 <= len(tasks) <= 10000; for every i with 0 <= i < len(tasks), len(tasks[i]) = 1 and 65 <= tasks[i][0] <= 90; and 0 <= n <= 100. -/
  theorem spec_6 (tasks : Slice (alloc.vec.Vec Std.U8)) (n : Std.I64)
      (hsize : SizePre tasks) (hbytes : BytesPre tasks) (hn : NPre n) :
      ∃ r : Std.I64, least_interval tasks n = ok r ∧
        ∀ L : ℕ, L < r.val.toNat →
          ¬ ∃ s : Fin L → Option (alloc.vec.Vec Std.U8), ValidSchedule tasks n L s := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (tasks : Slice (alloc.vec.Vec Std.U8)) (n : Std.I64)
        (hsize : SizePre tasks) (hbytes : BytesPre tasks) (hn : NPre n), ∃ r : Std.I64, least_interval tasks n = ok r ∧
          ∀ L : ℕ, L < r.val.toNat →
            ¬ ∃ s : Fin L → Option (alloc.vec.Vec Std.U8), ValidSchedule tasks n L s) := by
    sorry

  /-- Let r1 and r2 be the results returned by the function for tasks1 and tasks2 respectively, with the same n. Then r1 = r2.
    Preconditions: tasks1 and tasks2 are slices of Vec U8 such that 1 <= len(tasks1) = len(tasks2) <= 10000; for every i with 0 <= i < len(tasks1), len(tasks1[i]) = 1 and 65 <= tasks1[i][0] <= 90; similarly for tasks2; 0 <= n <= 100; and tasks2 is a permutation of tasks1 (i.e., for every label v, the number of occurrences of v in tasks1 equals the number of occurrences of v in tasks2). -/
  theorem spec_7 (tasks1 tasks2 : Slice (alloc.vec.Vec Std.U8)) (n : Std.I64)
      (hsize : 1 ≤ tasks1.val.length ∧ tasks1.val.length ≤ 10000)
      (hlen : tasks1.val.length = tasks2.val.length)
      (hbytes1 : BytesPre tasks1) (hbytes2 : BytesPre tasks2) (hn : NPre n)
      (hperm : ∀ v, occ tasks1 v = occ tasks2 v) :
      ∃ r1 r2 : Std.I64, least_interval tasks1 n = ok r1 ∧
        least_interval tasks2 n = ok r2 ∧ r1 = r2 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (tasks1 tasks2 : Slice (alloc.vec.Vec Std.U8)) (n : Std.I64)
        (hsize : 1 ≤ tasks1.val.length ∧ tasks1.val.length ≤ 10000)
        (hlen : tasks1.val.length = tasks2.val.length)
        (hbytes1 : BytesPre tasks1) (hbytes2 : BytesPre tasks2) (hn : NPre n)
        (hperm : ∀ v, occ tasks1 v = occ tasks2 v), ∃ r1 r2 : Std.I64, least_interval tasks1 n = ok r1 ∧
          least_interval tasks2 n = ok r2 ∧ r1 = r2) := by
    sorry

  /-- Let m = len(tasks). Let maxfreq be the maximum frequency of any label in tasks, and let cnt_max be the number of distinct labels achieving that maximum frequency. The function returns a result r and r <= m + (maxfreq - 1) * n * cnt_max.
    Preconditions: 1 <= len(tasks) <= 10000; for every i with 0 <= i < len(tasks), len(tasks[i]) = 1 and 65 <= tasks[i][0] <= 90; and 0 <= n <= 100. -/
  theorem spec_8 (tasks : Slice (alloc.vec.Vec Std.U8)) (n : Std.I64)
      (hsize : SizePre tasks) (hbytes : BytesPre tasks) (hn : NPre n) :
      ∃ r : Std.I64, least_interval tasks n = ok r ∧
        r.val ≤ (tasks.val.length : ℤ) + ((maxfreq tasks : ℤ) - 1) * n.val *
          (cntMax tasks : ℤ) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (tasks : Slice (alloc.vec.Vec Std.U8)) (n : Std.I64)
        (hsize : SizePre tasks) (hbytes : BytesPre tasks) (hn : NPre n), ∃ r : Std.I64, least_interval tasks n = ok r ∧
          r.val ≤ (tasks.val.length : ℤ) + ((maxfreq tasks : ℤ) - 1) * n.val *
            (cntMax tasks : ℤ)) := by
    sorry

  /-- Let r1 and r2 be the results returned by the function for tasks with cooling parameter n1 and n2 respectively. Then r1 <= r2.
    Preconditions: tasks is a slice of Vec U8 with 1 <= len(tasks) <= 10000; for every i with 0 <= i < len(tasks), len(tasks[i]) = 1 and 65 <= tasks[i][0] <= 90; and n1, n2 are integers with 0 <= n1 <= n2 <= 100. -/
  theorem spec_9 (tasks : Slice (alloc.vec.Vec Std.U8)) (n1 n2 : Std.I64)
      (hsize : SizePre tasks) (hbytes : BytesPre tasks)
      (hn : 0 ≤ n1.val ∧ n1.val ≤ n2.val ∧ n2.val ≤ 100) :
      ∃ r1 r2 : Std.I64, least_interval tasks n1 = ok r1 ∧
        least_interval tasks n2 = ok r2 ∧ r1.val ≤ r2.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (tasks : Slice (alloc.vec.Vec Std.U8)) (n1 n2 : Std.I64)
        (hsize : SizePre tasks) (hbytes : BytesPre tasks)
        (hn : 0 ≤ n1.val ∧ n1.val ≤ n2.val ∧ n2.val ≤ 100), ∃ r1 r2 : Std.I64, least_interval tasks n1 = ok r1 ∧
          least_interval tasks n2 = ok r2 ∧ r1.val ≤ r2.val) := by
    sorry

  end AegisSpec.LeastInterval

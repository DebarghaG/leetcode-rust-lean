import Aegis.ConstructDistancedSequence.Code.Funs

/-!
# Specifications of `Aegis.ConstructDistancedSequence.construct_distanced_sequence`

LeetCode problem `construct-the-lexicographically-largest-valid-sequence`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.ConstructDistancedSequence

  abbrev RVec : Type := Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64

  def Occurs (l : List Aeneas.Std.I64) (v : Int) (j : Nat) : Prop :=
    (l.map (fun x => x.val))[j]? = some v

  def OccursOnce (l : List Aeneas.Std.I64) (v : Int) : Prop :=
    ∃ j, Occurs l v j ∧ ∀ j', Occurs l v j' → j' = j

  def OccursTwiceAt (l : List Aeneas.Std.I64) (v : Int) (j1 j2 : Nat) : Prop :=
    j1 < j2 ∧ Occurs l v j1 ∧ Occurs l v j2 ∧ ∀ j, Occurs l v j → j = j1 ∨ j = j2

  def OccursTwice (l : List Aeneas.Std.I64) (v : Int) : Prop :=
    ∃ j1 j2, OccursTwiceAt l v j1 j2

  def IsValid (n : Int) (l : List Aeneas.Std.I64) : Prop :=
    (l.length : Int) = 2 * n - 1 ∧
    (∀ (j : Nat) (hj : j < l.length), 1 ≤ (l[j]'hj).val ∧ (l[j]'hj).val ≤ n) ∧
    OccursOnce l 1 ∧
    (∀ i : Int, 2 ≤ i → i ≤ n →
      ∃ j1 j2, OccursTwiceAt l i j1 j2 ∧ (j2 : Int) - (j1 : Int) = i)

  def LexGe : List Aeneas.Std.I64 → List Aeneas.Std.I64 → Prop
    | [], [] => True
    | [], _ :: _ => False
    | _ :: _, [] => True
    | a :: l₁, b :: l₂ => a.val > b.val ∨ (a.val = b.val ∧ LexGe l₁ l₂)

  /-- The function returns a result r such that r is the lexicographically largest valid sequence for n. A sequence r is valid for n if: (a) len(r) = 2n - 1; (b) for every index j with 0 <= j < len(r), 1 <= r[j] <= n; (c) the value 1 occurs exactly once in r; (d) for every i with 2 <= i <= n, the value i occurs exactly twice in r; (e) for every i with 2 <= i <= n, if j1 < j2 are the two indices with r[j1] = r[j2] = i, then j2 - j1 = i. Lexicographically largest means that for every valid sequence s for n, r is lexicographically greater than or equal to s.
    Preconditions: 1 <= n <= 20 -/
  theorem spec_1 (n : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn20 : n.val ≤ 20) :
      ∃ r : RVec,
        Aegis.ConstructDistancedSequence.construct_distanced_sequence n =
            Aeneas.Std.Result.ok r ∧
          IsValid n.val r.val ∧
            ∀ s : List Aeneas.Std.I64, IsValid n.val s → LexGe r.val s := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn20 : n.val ≤ 20), ∃ r : RVec,
          Aegis.ConstructDistancedSequence.construct_distanced_sequence n =
              Aeneas.Std.Result.ok r ∧
            IsValid n.val r.val ∧
              ∀ s : List Aeneas.Std.I64, IsValid n.val s → LexGe r.val s) := by
    sorry

  /-- The length of r is 2n - 1.
    Preconditions: 1 <= n <= 20 -/
  theorem spec_2 (n : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn20 : n.val ≤ 20) :
      ∀ r : RVec,
        Aegis.ConstructDistancedSequence.construct_distanced_sequence n =
            Aeneas.Std.Result.ok r →
          (r.val.length : Int) = 2 * n.val - 1 := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn20 : n.val ≤ 20), ∀ r : RVec,
          Aegis.ConstructDistancedSequence.construct_distanced_sequence n =
              Aeneas.Std.Result.ok r →
            (r.val.length : Int) = 2 * n.val - 1) := by
    sorry

  /-- For every index j with 0 <= j < len(r), 1 <= r[j] <= n.
    Preconditions: 1 <= n <= 20 -/
  theorem spec_3 (n : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn20 : n.val ≤ 20) :
      ∀ r : RVec,
        Aegis.ConstructDistancedSequence.construct_distanced_sequence n =
            Aeneas.Std.Result.ok r →
          ∀ (j : Nat) (hj : j < r.val.length),
            1 ≤ (r.val[j]'hj).val ∧ (r.val[j]'hj).val ≤ n.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn20 : n.val ≤ 20), ∀ r : RVec,
          Aegis.ConstructDistancedSequence.construct_distanced_sequence n =
              Aeneas.Std.Result.ok r →
            ∀ (j : Nat) (hj : j < r.val.length),
              1 ≤ (r.val[j]'hj).val ∧ (r.val[j]'hj).val ≤ n.val) := by
    sorry

  /-- The value 1 occurs exactly once in r, i.e., there is exactly one index j with r[j] = 1.
    Preconditions: 1 <= n <= 20 -/
  theorem spec_4 (n : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn20 : n.val ≤ 20) :
      ∀ r : RVec,
        Aegis.ConstructDistancedSequence.construct_distanced_sequence n =
            Aeneas.Std.Result.ok r →
          OccursOnce r.val 1 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn20 : n.val ≤ 20), ∀ r : RVec,
          Aegis.ConstructDistancedSequence.construct_distanced_sequence n =
              Aeneas.Std.Result.ok r →
            OccursOnce r.val 1) := by
    sorry

  /-- For every i with 2 <= i <= n, the value i occurs exactly twice in r, i.e., there are exactly two indices j with r[j] = i.
    Preconditions: 1 <= n <= 20 -/
  theorem spec_5 (n : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn20 : n.val ≤ 20) :
      ∀ r : RVec,
        Aegis.ConstructDistancedSequence.construct_distanced_sequence n =
            Aeneas.Std.Result.ok r →
          ∀ i : Int, 2 ≤ i → i ≤ n.val → OccursTwice r.val i := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn20 : n.val ≤ 20), ∀ r : RVec,
          Aegis.ConstructDistancedSequence.construct_distanced_sequence n =
              Aeneas.Std.Result.ok r →
            ∀ i : Int, 2 ≤ i → i ≤ n.val → OccursTwice r.val i) := by
    sorry

  /-- For every i with 2 <= i <= n, if j1 < j2 are the two indices with r[j1] = r[j2] = i, then j2 - j1 = i.
    Preconditions: 1 <= n <= 20 -/
  theorem spec_6 (n : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn20 : n.val ≤ 20) :
      ∀ r : RVec,
        Aegis.ConstructDistancedSequence.construct_distanced_sequence n =
            Aeneas.Std.Result.ok r →
          ∀ i : Int, 2 ≤ i → i ≤ n.val →
            ∃ j1 j2, OccursTwiceAt r.val i j1 j2 ∧ (j2 : Int) - (j1 : Int) = i := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn20 : n.val ≤ 20), ∀ r : RVec,
          Aegis.ConstructDistancedSequence.construct_distanced_sequence n =
              Aeneas.Std.Result.ok r →
            ∀ i : Int, 2 ≤ i → i ≤ n.val →
              ∃ j1 j2, OccursTwiceAt r.val i j1 j2 ∧ (j2 : Int) - (j1 : Int) = i) := by
    sorry

  /-- For every sequence s (of length 2n - 1) that is a valid sequence for n (i.e., satisfies the structural conditions: elements in [1, n], 1 occurs once, each i in [2, n] occurs twice with distance i apart), r is lexicographically greater than or equal to s.
    Preconditions: 1 <= n <= 20 -/
  theorem spec_7 (n : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn20 : n.val ≤ 20) :
      ∀ r : RVec,
        Aegis.ConstructDistancedSequence.construct_distanced_sequence n =
            Aeneas.Std.Result.ok r →
          ∀ s : List Aeneas.Std.I64, (s.length : Int) = 2 * n.val - 1 → IsValid n.val s →
            LexGe r.val s := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn20 : n.val ≤ 20), ∀ r : RVec,
          Aegis.ConstructDistancedSequence.construct_distanced_sequence n =
              Aeneas.Std.Result.ok r →
            ∀ s : List Aeneas.Std.I64, (s.length : Int) = 2 * n.val - 1 → IsValid n.val s →
              LexGe r.val s) := by
    sorry

  /-- The function does not fail; it returns a result r for every n with 1 <= n <= 20.
    Preconditions: 1 <= n <= 20 -/
  theorem spec_8 (n : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn20 : n.val ≤ 20) :
      ∃ r : RVec,
        Aegis.ConstructDistancedSequence.construct_distanced_sequence n =
          Aeneas.Std.Result.ok r := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn20 : n.val ≤ 20), ∃ r : RVec,
          Aegis.ConstructDistancedSequence.construct_distanced_sequence n =
            Aeneas.Std.Result.ok r) := by
    sorry

  /-- The sum of all elements of r equals n^2 + n - 1.
    Preconditions: 1 <= n <= 20 -/
  theorem spec_9 (n : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn20 : n.val ≤ 20) :
      ∀ r : RVec,
        Aegis.ConstructDistancedSequence.construct_distanced_sequence n =
            Aeneas.Std.Result.ok r →
          (r.val.map (fun x => x.val)).sum = n.val * n.val + n.val - 1 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn20 : n.val ≤ 20), ∀ r : RVec,
          Aegis.ConstructDistancedSequence.construct_distanced_sequence n =
              Aeneas.Std.Result.ok r →
            (r.val.map (fun x => x.val)).sum = n.val * n.val + n.val - 1) := by
    sorry

  /-- The set of values appearing in r is exactly {1, 2, ..., n}, i.e., for every integer v, v appears in r if and only if 1 <= v <= n.
    Preconditions: 1 <= n <= 20 -/
  theorem spec_10 (n : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn20 : n.val ≤ 20) :
      ∀ r : RVec,
        Aegis.ConstructDistancedSequence.construct_distanced_sequence n =
            Aeneas.Std.Result.ok r →
          ∀ v : Int, (∃ j, Occurs r.val v j) ↔ 1 ≤ v ∧ v ≤ n.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn20 : n.val ≤ 20), ∀ r : RVec,
          Aegis.ConstructDistancedSequence.construct_distanced_sequence n =
              Aeneas.Std.Result.ok r →
            ∀ v : Int, (∃ j, Occurs r.val v j) ↔ 1 ≤ v ∧ v ≤ n.val) := by
    sorry

  /-- r is a valid sequence for n: len(r) = 2n - 1; for every j with 0 <= j < len(r), 1 <= r[j] <= n; 1 occurs exactly once; for every i with 2 <= i <= n, i occurs exactly twice and the two occurrences are distance i apart.
    Preconditions: 1 <= n <= 20 -/
  theorem spec_11 (n : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn20 : n.val ≤ 20) :
      ∀ r : RVec,
        Aegis.ConstructDistancedSequence.construct_distanced_sequence n =
            Aeneas.Std.Result.ok r →
          IsValid n.val r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn20 : n.val ≤ 20), ∀ r : RVec,
          Aegis.ConstructDistancedSequence.construct_distanced_sequence n =
              Aeneas.Std.Result.ok r →
            IsValid n.val r.val) := by
    sorry

  /-- The maximum value among the elements of r is n.
    Preconditions: 1 <= n <= 20 -/
  theorem spec_12 (n : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn20 : n.val ≤ 20) :
      ∀ r : RVec,
        Aegis.ConstructDistancedSequence.construct_distanced_sequence n =
            Aeneas.Std.Result.ok r →
          (r.val.map (fun x => x.val)).max? = some n.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (n : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn20 : n.val ≤ 20), ∀ r : RVec,
          Aegis.ConstructDistancedSequence.construct_distanced_sequence n =
              Aeneas.Std.Result.ok r →
            (r.val.map (fun x => x.val)).max? = some n.val) := by
    sorry

  end AegisSpec.ConstructDistancedSequence

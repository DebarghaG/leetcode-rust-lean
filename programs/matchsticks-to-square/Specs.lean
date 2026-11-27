import Aegis.Makesquare.Code.Funs

/-!
# Specifications of `Aegis.Makesquare.makesquare`

LeetCode problem `matchsticks-to-square`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.Makesquare

def sliceLen (matchsticks : Slice I64) : ℕ := matchsticks.val.length

def entry (matchsticks : Slice I64) (i : ℕ) : ℤ :=
  match matchsticks.val[i]? with
  | some x => x.val
  | none => 0

def total (matchsticks : Slice I64) : ℤ := (matchsticks.val.map (fun x => x.val)).sum

def groupSum (matchsticks : Slice I64) (f : ℕ → ℕ) (k : ℕ) : ℤ :=
  ((List.range (sliceLen matchsticks)).map
    (fun i => if f i = k then entry matchsticks i else 0)).sum

def countEq (matchsticks : Slice I64) (v : ℤ) : ℕ :=
  ((List.range (sliceLen matchsticks)).filter
    (fun i => decide (entry matchsticks i = v))).length

def EntriesInRange (matchsticks : Slice I64) : Prop :=
  ∀ i, i < sliceLen matchsticks → 1 ≤ entry matchsticks i ∧ entry matchsticks i ≤ 100000000

def ValidInput (matchsticks : Slice I64) : Prop :=
  1 ≤ sliceLen matchsticks ∧ sliceLen matchsticks ≤ 15 ∧ EntriesInRange matchsticks

def IsFourPartition (matchsticks : Slice I64) (S : ℤ) : Prop :=
  ∃ f : ℕ → ℕ,
    (∀ i, i < sliceLen matchsticks → f i < 4) ∧
      ∀ k, k < 4 → groupSum matchsticks f k = S

/-- Let total = sum_{i=0}^{len(matchsticks)-1} matchsticks[i]. The function returns a Boolean result r (it does not fail) and r = true if and only if total is divisible by 4 and there exists a function f from the index set {0,...,len(matchsticks)-1} to {0,1,2,3} such that, for every k in {0,1,2,3}, sum_{0 <= i < len(matchsticks), f(i)=k} matchsticks[i] = total / 4. Equivalently, all sticks can be partitioned into four pairwise disjoint groups, using every stick exactly once, each group summing to total/4.
  Preconditions: 1 <= len(matchsticks) <= 15 and for every i with 0 <= i < len(matchsticks), 1 <= matchsticks[i] <= 100000000. -/
theorem spec_1 (matchsticks : Slice I64) (h : ValidInput matchsticks) :
    ∃ r : Bool,
      Aegis.Makesquare.makesquare matchsticks = ok r ∧
        (r = true ↔
          total matchsticks % 4 = 0 ∧ IsFourPartition matchsticks (total matchsticks / 4)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (matchsticks : Slice I64) (h : ValidInput matchsticks), ∃ r : Bool,
      Aegis.Makesquare.makesquare matchsticks = ok r ∧
        (r = true ↔
          total matchsticks % 4 = 0 ∧ IsFourPartition matchsticks (total matchsticks / 4))) := by
  sorry

/-- The call makesquare(matchsticks) returns Result.ok r for some Boolean r; it never fails, panics, overflows, or accesses an index out of bounds.
  Preconditions: 1 <= len(matchsticks) <= 15 and for every i with 0 <= i < len(matchsticks), 1 <= matchsticks[i] <= 100000000. -/
theorem spec_2 (matchsticks : Slice I64) (h : ValidInput matchsticks) :
    ∃ r : Bool, Aegis.Makesquare.makesquare matchsticks = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (matchsticks : Slice I64) (h : ValidInput matchsticks), ∃ r : Bool, Aegis.Makesquare.makesquare matchsticks = ok r) := by
  sorry

/-- Whenever makesquare(matchsticks) returns a result r, r = false.
  Preconditions: 1 <= len(matchsticks) <= 3 and for every i with 0 <= i < len(matchsticks), 1 <= matchsticks[i] <= 100000000. -/
theorem spec_3 (matchsticks : Slice I64) (h : ValidInput matchsticks)
    (hlen : sliceLen matchsticks ≤ 3) :
    ∀ r : Bool, Aegis.Makesquare.makesquare matchsticks = ok r → r = false := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (matchsticks : Slice I64) (h : ValidInput matchsticks)
    (hlen : sliceLen matchsticks ≤ 3), ∀ r : Bool, Aegis.Makesquare.makesquare matchsticks = ok r → r = false) := by
  sorry

/-- Whenever makesquare(matchsticks) returns a result r, r = true if and only if matchsticks[0] = matchsticks[1] = matchsticks[2] = matchsticks[3].
  Preconditions: len(matchsticks) = 4 and for every i with 0 <= i < len(matchsticks), 1 <= matchsticks[i] <= 100000000. -/
theorem spec_4 (matchsticks : Slice I64) (hlen : sliceLen matchsticks = 4)
    (h : EntriesInRange matchsticks) :
    ∀ r : Bool,
      Aegis.Makesquare.makesquare matchsticks = ok r →
        (r = true ↔
          entry matchsticks 0 = entry matchsticks 1 ∧
            entry matchsticks 1 = entry matchsticks 2 ∧
              entry matchsticks 2 = entry matchsticks 3) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (matchsticks : Slice I64) (hlen : sliceLen matchsticks = 4)
    (h : EntriesInRange matchsticks), ∀ r : Bool,
      Aegis.Makesquare.makesquare matchsticks = ok r →
        (r = true ↔
          entry matchsticks 0 = entry matchsticks 1 ∧
            entry matchsticks 1 = entry matchsticks 2 ∧
              entry matchsticks 2 = entry matchsticks 3)) := by
  sorry

/-- Whenever makesquare(matchsticks) returns a result r, r = true if and only if len(matchsticks) mod 4 = 0.
  Preconditions: 1 <= len(matchsticks) <= 15, for every i with 0 <= i < len(matchsticks), 1 <= matchsticks[i] <= 100000000, and there exists an integer L such that matchsticks[i] = L for every i with 0 <= i < len(matchsticks). -/
theorem spec_5 (matchsticks : Slice I64) (h : ValidInput matchsticks) (L : ℤ)
    (hL : ∀ i, i < sliceLen matchsticks → entry matchsticks i = L) :
    ∀ r : Bool,
      Aegis.Makesquare.makesquare matchsticks = ok r →
        (r = true ↔ sliceLen matchsticks % 4 = 0) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (matchsticks : Slice I64) (h : ValidInput matchsticks) (L : ℤ)
    (hL : ∀ i, i < sliceLen matchsticks → entry matchsticks i = L), ∀ r : Bool,
      Aegis.Makesquare.makesquare matchsticks = ok r →
        (r = true ↔ sliceLen matchsticks % 4 = 0)) := by
  sorry

/-- Whenever makesquare(matchsticks) returns a result r, if r = true then total = sum_{i=0}^{len(matchsticks)-1} matchsticks[i] satisfies total mod 4 = 0.
  Preconditions: 1 <= len(matchsticks) <= 15 and for every i with 0 <= i < len(matchsticks), 1 <= matchsticks[i] <= 100000000. -/
theorem spec_6 (matchsticks : Slice I64) (h : ValidInput matchsticks) :
    ∀ r : Bool,
      Aegis.Makesquare.makesquare matchsticks = ok r → r = true → total matchsticks % 4 = 0 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (matchsticks : Slice I64) (h : ValidInput matchsticks), ∀ r : Bool,
      Aegis.Makesquare.makesquare matchsticks = ok r → r = true → total matchsticks % 4 = 0) := by
  sorry

/-- Whenever makesquare(matchsticks) returns a result r, if r = true then for every i with 0 <= i < len(matchsticks), matchsticks[i] <= S.
  Preconditions: 1 <= len(matchsticks) <= 15, for every i with 0 <= i < len(matchsticks), 1 <= matchsticks[i] <= 100000000, and total = sum_{i=0}^{len(matchsticks)-1} matchsticks[i] is divisible by 4; let S = total / 4. -/
theorem spec_7 (matchsticks : Slice I64) (h : ValidInput matchsticks)
    (h4 : total matchsticks % 4 = 0) :
    ∀ r : Bool,
      Aegis.Makesquare.makesquare matchsticks = ok r →
        r = true → ∀ i, i < sliceLen matchsticks → entry matchsticks i ≤ total matchsticks / 4 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (matchsticks : Slice I64) (h : ValidInput matchsticks)
    (h4 : total matchsticks % 4 = 0), ∀ r : Bool,
      Aegis.Makesquare.makesquare matchsticks = ok r →
        r = true → ∀ i, i < sliceLen matchsticks → entry matchsticks i ≤ total matchsticks / 4) := by
  sorry

/-- Whenever makesquare(a) returns ra and makesquare(b) returns rb, ra = rb.
  Preconditions: Slices a and b each satisfy 1 <= len <= 15 and all entries in [1,100000000], and there is a bijection p from {0,...,len(a)-1} to {0,...,len(b)-1} such that b[p(i)] = a[i] for every i with 0 <= i < len(a). -/
theorem spec_8 (a b : Slice I64) (ha : ValidInput a) (hb : ValidInput b) (p : ℕ → ℕ)
    (hp : ∀ i, i < sliceLen a → p i < sliceLen b)
    (hinj : ∀ i₁, i₁ < sliceLen a → ∀ i₂, i₂ < sliceLen a → p i₁ = p i₂ → i₁ = i₂)
    (hsurj : ∀ j, j < sliceLen b → ∃ i, i < sliceLen a ∧ p i = j)
    (hval : ∀ i, i < sliceLen a → entry b (p i) = entry a i) :
    ∀ ra rb : Bool,
      Aegis.Makesquare.makesquare a = ok ra →
        Aegis.Makesquare.makesquare b = ok rb → ra = rb := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (a b : Slice I64) (ha : ValidInput a) (hb : ValidInput b) (p : ℕ → ℕ)
    (hp : ∀ i, i < sliceLen a → p i < sliceLen b)
    (hinj : ∀ i₁, i₁ < sliceLen a → ∀ i₂, i₂ < sliceLen a → p i₁ = p i₂ → i₁ = i₂)
    (hsurj : ∀ j, j < sliceLen b → ∃ i, i < sliceLen a ∧ p i = j)
    (hval : ∀ i, i < sliceLen a → entry b (p i) = entry a i), ∀ ra rb : Bool,
      Aegis.Makesquare.makesquare a = ok ra →
        Aegis.Makesquare.makesquare b = ok rb → ra = rb) := by
  sorry

/-- If there exists a function f from {0,...,len(matchsticks)-1} to {0,1,2,3} such that for every k in {0,1,2,3}, sum_{0 <= i < len(matchsticks), f(i)=k} matchsticks[i] = S, then whenever makesquare(matchsticks) returns a result r, r = true.
  Preconditions: 1 <= len(matchsticks) <= 15, for every i with 0 <= i < len(matchsticks), 1 <= matchsticks[i] <= 100000000, and total = sum_{i=0}^{len(matchsticks)-1} matchsticks[i] is divisible by 4; let S = total / 4. -/
theorem spec_9 (matchsticks : Slice I64) (h : ValidInput matchsticks)
    (h4 : total matchsticks % 4 = 0)
    (hw : IsFourPartition matchsticks (total matchsticks / 4)) :
    ∀ r : Bool, Aegis.Makesquare.makesquare matchsticks = ok r → r = true := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (matchsticks : Slice I64) (h : ValidInput matchsticks)
    (h4 : total matchsticks % 4 = 0)
    (hw : IsFourPartition matchsticks (total matchsticks / 4)), ∀ r : Bool, Aegis.Makesquare.makesquare matchsticks = ok r → r = true) := by
  sorry

/-- Let total = sum_{i=0}^{4} matchsticks[i] and S = total / 4 using integer division. Whenever makesquare(matchsticks) returns a result r, r = true if and only if total mod 4 = 0 and the number of indices i with 0 <= i < 5 and matchsticks[i] = S is exactly 3.
  Preconditions: len(matchsticks) = 5 and for every i with 0 <= i < len(matchsticks), 1 <= matchsticks[i] <= 100000000. -/
theorem spec_10 (matchsticks : Slice I64) (hlen : sliceLen matchsticks = 5)
    (h : EntriesInRange matchsticks) :
    ∀ r : Bool,
      Aegis.Makesquare.makesquare matchsticks = ok r →
        (r = true ↔ total matchsticks % 4 = 0 ∧ countEq matchsticks (total matchsticks / 4) = 3) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (matchsticks : Slice I64) (hlen : sliceLen matchsticks = 5)
    (h : EntriesInRange matchsticks), ∀ r : Bool,
      Aegis.Makesquare.makesquare matchsticks = ok r →
        (r = true ↔ total matchsticks % 4 = 0 ∧ countEq matchsticks (total matchsticks / 4) = 3)) := by
  sorry

/-- If makesquare(a) returns true, then whenever makesquare(b) returns rb, rb = true.
  Preconditions: Slice a satisfies 1 <= len(a) <= 15 and all entries in [1,100000000], len(a) + 4 <= 15, L is an integer with 1 <= L <= 100000000, and slice b satisfies len(b) = len(a) + 4, b[i] = a[i] for 0 <= i < len(a), and b[len(a)+j] = L for j = 0,1,2,3. -/
theorem spec_11 (a b : Slice I64) (L : ℤ) (ha : ValidInput a)
    (hle : sliceLen a + 4 ≤ 15) (hL : 1 ≤ L ∧ L ≤ 100000000)
    (hlen : sliceLen b = sliceLen a + 4)
    (hpre : ∀ i, i < sliceLen a → entry b i = entry a i)
    (hsuf : ∀ j, j < 4 → entry b (sliceLen a + j) = L) :
    Aegis.Makesquare.makesquare a = ok true →
      ∀ rb : Bool, Aegis.Makesquare.makesquare b = ok rb → rb = true := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (a b : Slice I64) (L : ℤ) (ha : ValidInput a)
    (hle : sliceLen a + 4 ≤ 15) (hL : 1 ≤ L ∧ L ≤ 100000000)
    (hlen : sliceLen b = sliceLen a + 4)
    (hpre : ∀ i, i < sliceLen a → entry b i = entry a i)
    (hsuf : ∀ j, j < 4 → entry b (sliceLen a + j) = L), Aegis.Makesquare.makesquare a = ok true →
      ∀ rb : Bool, Aegis.Makesquare.makesquare b = ok rb → rb = true) := by
  sorry

/-- Whenever makesquare(matchsticks) returns a result r, if r = true then total = sum_{i=0}^{len(matchsticks)-1} matchsticks[i] is divisible by 4 and S = total / 4 satisfies S <= 300000000.
  Preconditions: 1 <= len(matchsticks) <= 15 and for every i with 0 <= i < len(matchsticks), 1 <= matchsticks[i] <= 100000000. -/
theorem spec_12 (matchsticks : Slice I64) (h : ValidInput matchsticks) :
    ∀ r : Bool,
      Aegis.Makesquare.makesquare matchsticks = ok r →
        r = true → total matchsticks % 4 = 0 ∧ total matchsticks / 4 ≤ 300000000 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (matchsticks : Slice I64) (h : ValidInput matchsticks), ∀ r : Bool,
      Aegis.Makesquare.makesquare matchsticks = ok r →
        r = true → total matchsticks % 4 = 0 ∧ total matchsticks / 4 ≤ 300000000) := by
  sorry

end AegisSpec.Makesquare

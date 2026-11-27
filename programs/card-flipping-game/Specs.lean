import Aegis.Flipgame.Code.Funs

/-!
# Specifications of `Aegis.Flipgame.flipgame`

LeetCode problem `card-flipping-game`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.Flipgame

  def vals (s : Slice Std.I64) : List Int := s.val.map fun v => v.val

  def Appears (fronts backs : Slice Std.I64) (x : Int) : Prop :=
    ∃ i : Nat, (vals fronts)[i]? = some x ∨ (vals backs)[i]? = some x

  def Locked (fronts backs : Slice Std.I64) (x : Int) : Prop :=
    ∃ i : Nat, (vals fronts)[i]? = some x ∧ (vals backs)[i]? = some x

  def candidates (fronts backs : Slice Std.I64) : Set Int :=
    {x | Appears fronts backs x ∧ ¬ Locked fronts backs x}

  def IsIndexSet (n : Nat) (S : Finset Nat) : Prop := S ⊆ Finset.range n

  def upVal (fronts backs : Slice Std.I64) (S : Finset Nat) (i : Nat) : Option Int :=
    match (vals fronts)[i]?, (vals backs)[i]? with
    | some f, some b => some (if i ∈ S then b else f)
    | _, _ => none

  def downVal (fronts backs : Slice Std.I64) (S : Finset Nat) (i : Nat) : Option Int :=
    match (vals fronts)[i]?, (vals backs)[i]? with
    | some f, some b => some (if i ∈ S then f else b)
    | _, _ => none

  def Good (fronts backs : Slice Std.I64) (S : Finset Nat) (x : Int) : Prop :=
    (∃ i : Nat, downVal fronts backs S i = some x) ∧
      ∀ i : Nat, upVal fronts backs S i ≠ some x

  def swapCard (fronts backs : List Std.I64) (i : Nat) : List Std.I64 × List Std.I64 :=
    match fronts[i]?, backs[i]? with
    | some f, some b => (fronts.set i b, backs.set i f)
    | _, _ => (fronts, backs)

  def reindex (l : List Std.I64) (p : Nat → Nat) : List Std.I64 :=
    (List.range l.length).filterMap fun i => l[p i]?

  /-- For every input satisfying the preconditions, whenever flipgame(fronts, backs) returns a result r, the following holds. Define a value x to appear if there is some i with 0 <= i < n and (fronts[i] = x or backs[i] = x), and define x to be locked if there is some i with 0 <= i < n and fronts[i] = x and backs[i] = x. Let A be the set of all integers x that appear and are not locked. If A is nonempty, then r is the least integer in A: r is in A and r <= x for every x in A. If A is empty, then r = 0.
    Preconditions: Let n = len(fronts). The inputs satisfy len(fronts) = len(backs), 1 <= n <= 1000, and for every i with 0 <= i < n, 1 <= fronts[i] <= 2000 and 1 <= backs[i] <= 2000. -/
  theorem spec_1 (fronts backs : Slice Std.I64)
      (hl : fronts.val.length = backs.val.length)
      (hn1 : 1 ≤ fronts.val.length) (hn2 : fronts.val.length ≤ 1000)
      (hf : ∀ i (hi : i < fronts.val.length),
        1 ≤ (fronts.val[i]'hi).val ∧ (fronts.val[i]'hi).val ≤ 2000)
      (hb : ∀ i (hi : i < backs.val.length),
        1 ≤ (backs.val[i]'hi).val ∧ (backs.val[i]'hi).val ≤ 2000) :
      ∀ r : Std.I64, Aegis.Flipgame.flipgame fronts backs = ok r →
        (((candidates fronts backs).Nonempty →
            r.val ∈ candidates fronts backs ∧
              ∀ x ∈ candidates fronts backs, r.val ≤ x) ∧
          (candidates fronts backs = ∅ → r.val = 0)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (fronts backs : Slice Std.I64)
        (hl : fronts.val.length = backs.val.length)
        (hn1 : 1 ≤ fronts.val.length) (hn2 : fronts.val.length ≤ 1000)
        (hf : ∀ i (hi : i < fronts.val.length),
          1 ≤ (fronts.val[i]'hi).val ∧ (fronts.val[i]'hi).val ≤ 2000)
        (hb : ∀ i (hi : i < backs.val.length),
          1 ≤ (backs.val[i]'hi).val ∧ (backs.val[i]'hi).val ≤ 2000), ∀ r : Std.I64, Aegis.Flipgame.flipgame fronts backs = ok r →
          (((candidates fronts backs).Nonempty →
              r.val ∈ candidates fronts backs ∧
                ∀ x ∈ candidates fronts backs, r.val ≤ x) ∧
            (candidates fronts backs = ∅ → r.val = 0))) := by
    sorry

  /-- For every input satisfying the preconditions, flipgame(fronts, backs) returns a result r (it does not fail).
    Preconditions: Let n = len(fronts). The inputs satisfy len(fronts) = len(backs), 1 <= n <= 1000, and for every i with 0 <= i < n, 1 <= fronts[i] <= 2000 and 1 <= backs[i] <= 2000. -/
  theorem spec_2 (fronts backs : Slice Std.I64)
      (hl : fronts.val.length = backs.val.length)
      (hn1 : 1 ≤ fronts.val.length) (hn2 : fronts.val.length ≤ 1000)
      (hf : ∀ i (hi : i < fronts.val.length),
        1 ≤ (fronts.val[i]'hi).val ∧ (fronts.val[i]'hi).val ≤ 2000)
      (hb : ∀ i (hi : i < backs.val.length),
        1 ≤ (backs.val[i]'hi).val ∧ (backs.val[i]'hi).val ≤ 2000) :
      ∃ r : Std.I64, Aegis.Flipgame.flipgame fronts backs = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (fronts backs : Slice Std.I64)
        (hl : fronts.val.length = backs.val.length)
        (hn1 : 1 ≤ fronts.val.length) (hn2 : fronts.val.length ≤ 1000)
        (hf : ∀ i (hi : i < fronts.val.length),
          1 ≤ (fronts.val[i]'hi).val ∧ (fronts.val[i]'hi).val ≤ 2000)
        (hb : ∀ i (hi : i < backs.val.length),
          1 ≤ (backs.val[i]'hi).val ∧ (backs.val[i]'hi).val ≤ 2000), ∃ r : Std.I64, Aegis.Flipgame.flipgame fronts backs = ok r) := by
    sorry

  /-- For every input satisfying the preconditions, whenever flipgame(fronts, backs) returns a result r, we have 0 <= r <= 2000.
    Preconditions: Let n = len(fronts). The inputs satisfy len(fronts) = len(backs), 1 <= n <= 1000, and for every i with 0 <= i < n, 1 <= fronts[i] <= 2000 and 1 <= backs[i] <= 2000. -/
  theorem spec_3 (fronts backs : Slice Std.I64)
      (hl : fronts.val.length = backs.val.length)
      (hn1 : 1 ≤ fronts.val.length) (hn2 : fronts.val.length ≤ 1000)
      (hf : ∀ i (hi : i < fronts.val.length),
        1 ≤ (fronts.val[i]'hi).val ∧ (fronts.val[i]'hi).val ≤ 2000)
      (hb : ∀ i (hi : i < backs.val.length),
        1 ≤ (backs.val[i]'hi).val ∧ (backs.val[i]'hi).val ≤ 2000) :
      ∀ r : Std.I64, Aegis.Flipgame.flipgame fronts backs = ok r →
        0 ≤ r.val ∧ r.val ≤ 2000 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (fronts backs : Slice Std.I64)
        (hl : fronts.val.length = backs.val.length)
        (hn1 : 1 ≤ fronts.val.length) (hn2 : fronts.val.length ≤ 1000)
        (hf : ∀ i (hi : i < fronts.val.length),
          1 ≤ (fronts.val[i]'hi).val ∧ (fronts.val[i]'hi).val ≤ 2000)
        (hb : ∀ i (hi : i < backs.val.length),
          1 ≤ (backs.val[i]'hi).val ∧ (backs.val[i]'hi).val ≤ 2000), ∀ r : Std.I64, Aegis.Flipgame.flipgame fronts backs = ok r →
          0 ≤ r.val ∧ r.val ≤ 2000) := by
    sorry

  /-- For every input satisfying the preconditions, whenever flipgame(fronts, backs) returns a result r with r != 0, there exists an index i with 0 <= i < n such that fronts[i] = r or backs[i] = r.
    Preconditions: Let n = len(fronts). The inputs satisfy len(fronts) = len(backs), 1 <= n <= 1000, and for every i with 0 <= i < n, 1 <= fronts[i] <= 2000 and 1 <= backs[i] <= 2000. -/
  theorem spec_4 (fronts backs : Slice Std.I64)
      (hl : fronts.val.length = backs.val.length)
      (hn1 : 1 ≤ fronts.val.length) (hn2 : fronts.val.length ≤ 1000)
      (hf : ∀ i (hi : i < fronts.val.length),
        1 ≤ (fronts.val[i]'hi).val ∧ (fronts.val[i]'hi).val ≤ 2000)
      (hb : ∀ i (hi : i < backs.val.length),
        1 ≤ (backs.val[i]'hi).val ∧ (backs.val[i]'hi).val ≤ 2000) :
      ∀ r : Std.I64, Aegis.Flipgame.flipgame fronts backs = ok r → r.val ≠ 0 →
        Appears fronts backs r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (fronts backs : Slice Std.I64)
        (hl : fronts.val.length = backs.val.length)
        (hn1 : 1 ≤ fronts.val.length) (hn2 : fronts.val.length ≤ 1000)
        (hf : ∀ i (hi : i < fronts.val.length),
          1 ≤ (fronts.val[i]'hi).val ∧ (fronts.val[i]'hi).val ≤ 2000)
        (hb : ∀ i (hi : i < backs.val.length),
          1 ≤ (backs.val[i]'hi).val ∧ (backs.val[i]'hi).val ≤ 2000), ∀ r : Std.I64, Aegis.Flipgame.flipgame fronts backs = ok r → r.val ≠ 0 →
          Appears fronts backs r.val) := by
    sorry

  /-- For every input satisfying the preconditions, whenever flipgame(fronts, backs) returns a result r with r != 0, for every i with 0 <= i < n, it is not the case that both fronts[i] = r and backs[i] = r.
    Preconditions: Let n = len(fronts). The inputs satisfy len(fronts) = len(backs), 1 <= n <= 1000, and for every i with 0 <= i < n, 1 <= fronts[i] <= 2000 and 1 <= backs[i] <= 2000. -/
  theorem spec_5 (fronts backs : Slice Std.I64)
      (hl : fronts.val.length = backs.val.length)
      (hn1 : 1 ≤ fronts.val.length) (hn2 : fronts.val.length ≤ 1000)
      (hf : ∀ i (hi : i < fronts.val.length),
        1 ≤ (fronts.val[i]'hi).val ∧ (fronts.val[i]'hi).val ≤ 2000)
      (hb : ∀ i (hi : i < backs.val.length),
        1 ≤ (backs.val[i]'hi).val ∧ (backs.val[i]'hi).val ≤ 2000) :
      ∀ r : Std.I64, Aegis.Flipgame.flipgame fronts backs = ok r → r.val ≠ 0 →
        ∀ (i : Nat) (hi : i < fronts.val.length) (hi' : i < backs.val.length),
          ¬ ((fronts.val[i]'hi).val = r.val ∧ (backs.val[i]'hi').val = r.val) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (fronts backs : Slice Std.I64)
        (hl : fronts.val.length = backs.val.length)
        (hn1 : 1 ≤ fronts.val.length) (hn2 : fronts.val.length ≤ 1000)
        (hf : ∀ i (hi : i < fronts.val.length),
          1 ≤ (fronts.val[i]'hi).val ∧ (fronts.val[i]'hi).val ≤ 2000)
        (hb : ∀ i (hi : i < backs.val.length),
          1 ≤ (backs.val[i]'hi).val ∧ (backs.val[i]'hi).val ≤ 2000), ∀ r : Std.I64, Aegis.Flipgame.flipgame fronts backs = ok r → r.val ≠ 0 →
          ∀ (i : Nat) (hi : i < fronts.val.length) (hi' : i < backs.val.length),
            ¬ ((fronts.val[i]'hi).val = r.val ∧ (backs.val[i]'hi').val = r.val)) := by
    sorry

  /-- For every input satisfying the preconditions, whenever flipgame(fronts, backs) returns a result r with r != 0, there exists a set S of indices with S subset of {0,...,n-1} such that: (i) for some i in {0,...,n-1}, the down-facing value of card i under S is r, meaning fronts[i] = r if i is in S and backs[i] = r if i is not in S; and (ii) for every j in {0,...,n-1}, the up-facing value of card j under S is not r, meaning backs[j] != r if j is in S and fronts[j] != r if j is not in S.
    Preconditions: Let n = len(fronts). The inputs satisfy len(fronts) = len(backs), 1 <= n <= 1000, and for every i with 0 <= i < n, 1 <= fronts[i] <= 2000 and 1 <= backs[i] <= 2000. -/
  theorem spec_6 (fronts backs : Slice Std.I64)
      (hl : fronts.val.length = backs.val.length)
      (hn1 : 1 ≤ fronts.val.length) (hn2 : fronts.val.length ≤ 1000)
      (hf : ∀ i (hi : i < fronts.val.length),
        1 ≤ (fronts.val[i]'hi).val ∧ (fronts.val[i]'hi).val ≤ 2000)
      (hb : ∀ i (hi : i < backs.val.length),
        1 ≤ (backs.val[i]'hi).val ∧ (backs.val[i]'hi).val ≤ 2000) :
      ∀ r : Std.I64, Aegis.Flipgame.flipgame fronts backs = ok r → r.val ≠ 0 →
        ∃ S : Finset Nat, IsIndexSet fronts.val.length S ∧ Good fronts backs S r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (fronts backs : Slice Std.I64)
        (hl : fronts.val.length = backs.val.length)
        (hn1 : 1 ≤ fronts.val.length) (hn2 : fronts.val.length ≤ 1000)
        (hf : ∀ i (hi : i < fronts.val.length),
          1 ≤ (fronts.val[i]'hi).val ∧ (fronts.val[i]'hi).val ≤ 2000)
        (hb : ∀ i (hi : i < backs.val.length),
          1 ≤ (backs.val[i]'hi).val ∧ (backs.val[i]'hi).val ≤ 2000), ∀ r : Std.I64, Aegis.Flipgame.flipgame fronts backs = ok r → r.val ≠ 0 →
          ∃ S : Finset Nat, IsIndexSet fronts.val.length S ∧ Good fronts backs S r.val) := by
    sorry

  /-- For every input satisfying the preconditions, whenever flipgame(fronts, backs) returns a result r with r != 0, for every integer x with 1 <= x < r and every set S of indices with S subset of {0,...,n-1}, x is not good under S. That is, it is not the case that both (a) some card has x facing down under S and (b) no card has x facing up under S, where under S the up value of card i is backs[i] if i is in S and fronts[i] otherwise, and the down value is the other side.
    Preconditions: Let n = len(fronts). The inputs satisfy len(fronts) = len(backs), 1 <= n <= 1000, and for every i with 0 <= i < n, 1 <= fronts[i] <= 2000 and 1 <= backs[i] <= 2000. -/
  theorem spec_7 (fronts backs : Slice Std.I64)
      (hl : fronts.val.length = backs.val.length)
      (hn1 : 1 ≤ fronts.val.length) (hn2 : fronts.val.length ≤ 1000)
      (hf : ∀ i (hi : i < fronts.val.length),
        1 ≤ (fronts.val[i]'hi).val ∧ (fronts.val[i]'hi).val ≤ 2000)
      (hb : ∀ i (hi : i < backs.val.length),
        1 ≤ (backs.val[i]'hi).val ∧ (backs.val[i]'hi).val ≤ 2000) :
      ∀ r : Std.I64, Aegis.Flipgame.flipgame fronts backs = ok r → r.val ≠ 0 →
        ∀ x : Int, 1 ≤ x → x < r.val → ∀ S : Finset Nat, IsIndexSet fronts.val.length S →
          ¬ Good fronts backs S x := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (fronts backs : Slice Std.I64)
        (hl : fronts.val.length = backs.val.length)
        (hn1 : 1 ≤ fronts.val.length) (hn2 : fronts.val.length ≤ 1000)
        (hf : ∀ i (hi : i < fronts.val.length),
          1 ≤ (fronts.val[i]'hi).val ∧ (fronts.val[i]'hi).val ≤ 2000)
        (hb : ∀ i (hi : i < backs.val.length),
          1 ≤ (backs.val[i]'hi).val ∧ (backs.val[i]'hi).val ≤ 2000), ∀ r : Std.I64, Aegis.Flipgame.flipgame fronts backs = ok r → r.val ≠ 0 →
          ∀ x : Int, 1 ≤ x → x < r.val → ∀ S : Finset Nat, IsIndexSet fronts.val.length S →
            ¬ Good fronts backs S x) := by
    sorry

  /-- For every input satisfying the preconditions, whenever flipgame(fronts, backs) returns a result r, r = 0 if and only if there is no integer x and no set S of indices with S subset of {0,...,n-1} such that x is good under S, where under S the up value of card i is backs[i] if i is in S and fronts[i] otherwise, and x is good under S if x is the down value of some card and is not the up value of any card.
    Preconditions: Let n = len(fronts). The inputs satisfy len(fronts) = len(backs), 1 <= n <= 1000, and for every i with 0 <= i < n, 1 <= fronts[i] <= 2000 and 1 <= backs[i] <= 2000. -/
  theorem spec_8 (fronts backs : Slice Std.I64)
      (hl : fronts.val.length = backs.val.length)
      (hn1 : 1 ≤ fronts.val.length) (hn2 : fronts.val.length ≤ 1000)
      (hf : ∀ i (hi : i < fronts.val.length),
        1 ≤ (fronts.val[i]'hi).val ∧ (fronts.val[i]'hi).val ≤ 2000)
      (hb : ∀ i (hi : i < backs.val.length),
        1 ≤ (backs.val[i]'hi).val ∧ (backs.val[i]'hi).val ≤ 2000) :
      ∀ r : Std.I64, Aegis.Flipgame.flipgame fronts backs = ok r →
        (r.val = 0 ↔ ¬ ∃ x : Int, ∃ S : Finset Nat,
          IsIndexSet fronts.val.length S ∧ Good fronts backs S x) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (fronts backs : Slice Std.I64)
        (hl : fronts.val.length = backs.val.length)
        (hn1 : 1 ≤ fronts.val.length) (hn2 : fronts.val.length ≤ 1000)
        (hf : ∀ i (hi : i < fronts.val.length),
          1 ≤ (fronts.val[i]'hi).val ∧ (fronts.val[i]'hi).val ≤ 2000)
        (hb : ∀ i (hi : i < backs.val.length),
          1 ≤ (backs.val[i]'hi).val ∧ (backs.val[i]'hi).val ≤ 2000), ∀ r : Std.I64, Aegis.Flipgame.flipgame fronts backs = ok r →
          (r.val = 0 ↔ ¬ ∃ x : Int, ∃ S : Finset Nat,
            IsIndexSet fronts.val.length S ∧ Good fronts backs S x)) := by
    sorry

  /-- For every input satisfying the preconditions and every index i with 0 <= i < n, let fronts' and backs' be the arrays obtained from fronts and backs by swapping the two entries of card i: fronts'[i] = backs[i], backs'[i] = fronts[i], and for every j with 0 <= j < n and j != i, fronts'[j] = fronts[j] and backs'[j] = backs[j]. Whenever flipgame(fronts, backs) returns a result r and flipgame(fronts', backs') returns a result r', we have r = r'.
    Preconditions: Let n = len(fronts). The inputs satisfy len(fronts) = len(backs), 1 <= n <= 1000, and for every i with 0 <= i < n, 1 <= fronts[i] <= 2000 and 1 <= backs[i] <= 2000. -/
  theorem spec_9 (fronts backs : Slice Std.I64)
      (hl : fronts.val.length = backs.val.length)
      (hn1 : 1 ≤ fronts.val.length) (hn2 : fronts.val.length ≤ 1000)
      (hf : ∀ i (hi : i < fronts.val.length),
        1 ≤ (fronts.val[i]'hi).val ∧ (fronts.val[i]'hi).val ≤ 2000)
      (hb : ∀ i (hi : i < backs.val.length),
        1 ≤ (backs.val[i]'hi).val ∧ (backs.val[i]'hi).val ≤ 2000) :
      ∀ (i : Nat) (_hi : i < fronts.val.length) (fronts' backs' : Slice Std.I64),
        fronts'.val = (swapCard fronts.val backs.val i).1 →
        backs'.val = (swapCard fronts.val backs.val i).2 →
        ∀ r r' : Std.I64, Aegis.Flipgame.flipgame fronts backs = ok r →
          Aegis.Flipgame.flipgame fronts' backs' = ok r' → r.val = r'.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (fronts backs : Slice Std.I64)
        (hl : fronts.val.length = backs.val.length)
        (hn1 : 1 ≤ fronts.val.length) (hn2 : fronts.val.length ≤ 1000)
        (hf : ∀ i (hi : i < fronts.val.length),
          1 ≤ (fronts.val[i]'hi).val ∧ (fronts.val[i]'hi).val ≤ 2000)
        (hb : ∀ i (hi : i < backs.val.length),
          1 ≤ (backs.val[i]'hi).val ∧ (backs.val[i]'hi).val ≤ 2000), ∀ (i : Nat) (_hi : i < fronts.val.length) (fronts' backs' : Slice Std.I64),
          fronts'.val = (swapCard fronts.val backs.val i).1 →
          backs'.val = (swapCard fronts.val backs.val i).2 →
          ∀ r r' : Std.I64, Aegis.Flipgame.flipgame fronts backs = ok r →
            Aegis.Flipgame.flipgame fronts' backs' = ok r' → r.val = r'.val) := by
    sorry

  /-- For every input satisfying the preconditions and every permutation p of the index set {0,...,n-1}, define fronts' and backs' by fronts'[i] = fronts[p(i)] and backs'[i] = backs[p(i)] for every i with 0 <= i < n. Whenever flipgame(fronts, backs) returns a result r and flipgame(fronts', backs') returns a result r', we have r = r'.
    Preconditions: Let n = len(fronts). The inputs satisfy len(fronts) = len(backs), 1 <= n <= 1000, and for every i with 0 <= i < n, 1 <= fronts[i] <= 2000 and 1 <= backs[i] <= 2000. -/
  theorem spec_10 (fronts backs : Slice Std.I64)
      (hl : fronts.val.length = backs.val.length)
      (hn1 : 1 ≤ fronts.val.length) (hn2 : fronts.val.length ≤ 1000)
      (hf : ∀ i (hi : i < fronts.val.length),
        1 ≤ (fronts.val[i]'hi).val ∧ (fronts.val[i]'hi).val ≤ 2000)
      (hb : ∀ i (hi : i < backs.val.length),
        1 ≤ (backs.val[i]'hi).val ∧ (backs.val[i]'hi).val ≤ 2000) :
      ∀ (p : Nat → Nat),
        (∀ i, i < fronts.val.length → p i < fronts.val.length) →
        (∀ j, j < fronts.val.length → ∃ i, i < fronts.val.length ∧ p i = j) →
        ∀ (fronts' backs' : Slice Std.I64),
          fronts'.val = reindex fronts.val p →
          backs'.val = reindex backs.val p →
          ∀ r r' : Std.I64, Aegis.Flipgame.flipgame fronts backs = ok r →
            Aegis.Flipgame.flipgame fronts' backs' = ok r' → r.val = r'.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (fronts backs : Slice Std.I64)
        (hl : fronts.val.length = backs.val.length)
        (hn1 : 1 ≤ fronts.val.length) (hn2 : fronts.val.length ≤ 1000)
        (hf : ∀ i (hi : i < fronts.val.length),
          1 ≤ (fronts.val[i]'hi).val ∧ (fronts.val[i]'hi).val ≤ 2000)
        (hb : ∀ i (hi : i < backs.val.length),
          1 ≤ (backs.val[i]'hi).val ∧ (backs.val[i]'hi).val ≤ 2000), ∀ (p : Nat → Nat),
          (∀ i, i < fronts.val.length → p i < fronts.val.length) →
          (∀ j, j < fronts.val.length → ∃ i, i < fronts.val.length ∧ p i = j) →
          ∀ (fronts' backs' : Slice Std.I64),
            fronts'.val = reindex fronts.val p →
            backs'.val = reindex backs.val p →
            ∀ r r' : Std.I64, Aegis.Flipgame.flipgame fronts backs = ok r →
              Aegis.Flipgame.flipgame fronts' backs' = ok r' → r.val = r'.val) := by
    sorry

  /-- For every input satisfying the preconditions, whenever flipgame(fronts, backs) returns a result r, for every integer x with 1 <= x <= 2000, if x appears in fronts or backs and is not locked, then r != 0 and r <= x. Here x appears if there is i with 0 <= i < n and (fronts[i] = x or backs[i] = x), and x is locked if there is i with 0 <= i < n and fronts[i] = x and backs[i] = x.
    Preconditions: Let n = len(fronts). The inputs satisfy len(fronts) = len(backs), 1 <= n <= 1000, and for every i with 0 <= i < n, 1 <= fronts[i] <= 2000 and 1 <= backs[i] <= 2000. -/
  theorem spec_11 (fronts backs : Slice Std.I64)
      (hl : fronts.val.length = backs.val.length)
      (hn1 : 1 ≤ fronts.val.length) (hn2 : fronts.val.length ≤ 1000)
      (hf : ∀ i (hi : i < fronts.val.length),
        1 ≤ (fronts.val[i]'hi).val ∧ (fronts.val[i]'hi).val ≤ 2000)
      (hb : ∀ i (hi : i < backs.val.length),
        1 ≤ (backs.val[i]'hi).val ∧ (backs.val[i]'hi).val ≤ 2000) :
      ∀ r : Std.I64, Aegis.Flipgame.flipgame fronts backs = ok r →
        ∀ x : Int, 1 ≤ x → x ≤ 2000 → Appears fronts backs x →
          ¬ Locked fronts backs x → r.val ≠ 0 ∧ r.val ≤ x := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (fronts backs : Slice Std.I64)
        (hl : fronts.val.length = backs.val.length)
        (hn1 : 1 ≤ fronts.val.length) (hn2 : fronts.val.length ≤ 1000)
        (hf : ∀ i (hi : i < fronts.val.length),
          1 ≤ (fronts.val[i]'hi).val ∧ (fronts.val[i]'hi).val ≤ 2000)
        (hb : ∀ i (hi : i < backs.val.length),
          1 ≤ (backs.val[i]'hi).val ∧ (backs.val[i]'hi).val ≤ 2000), ∀ r : Std.I64, Aegis.Flipgame.flipgame fronts backs = ok r →
          ∀ x : Int, 1 ≤ x → x ≤ 2000 → Appears fronts backs x →
            ¬ Locked fronts backs x → r.val ≠ 0 ∧ r.val ≤ x) := by
    sorry

  end AegisSpec.Flipgame

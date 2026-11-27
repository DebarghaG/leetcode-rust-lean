import Aegis.MostSimilar.Code.Funs

/-!
# Specifications of `Aegis.MostSimilar.most_similar`

LeetCode problem `the-most-similar-path-in-a-graph`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MostSimilar

  abbrev ByteSeq := List Nat

  abbrev CityPath := List Int

  def vecBytes (v : alloc.vec.Vec Std.U8) : ByteSeq := v.val.map fun b => b.val

  def nameBytes (names : Slice (alloc.vec.Vec Std.U8)) (i : Nat) : Option ByteSeq :=
    (names.val[i]?).map vecBytes

  def targetName (targetPath : Slice (alloc.vec.Vec Std.U8)) (k : Nat) : Option ByteSeq :=
    (targetPath.val[k]?).map vecBytes

  def cityName (names : Slice (alloc.vec.Vec Std.U8)) (i : Int) : Option ByteSeq :=
    if 0 ≤ i then nameBytes names i.toNat else none

  def roadEndpoints (roads : Slice (alloc.vec.Vec Std.I64)) : List (List Int) :=
    roads.val.map fun r => r.val.map fun x => x.val

  def roadAt (roads : Slice (alloc.vec.Vec Std.I64)) (e : Nat) : Option (List Int) :=
    (roadEndpoints roads)[e]?

  def roadEntry (roads : Slice (alloc.vec.Vec Std.I64)) (e : Nat) (j : Nat) : Option Int :=
    (roadAt roads e).bind fun u => u[j]?

  def IsRoad (roads : Slice (alloc.vec.Vec Std.I64)) (a b : Int) : Prop :=
    ∃ u ∈ roadEndpoints roads, u = [a, b] ∨ u = [b, a]

  def resultPath (v : alloc.vec.Vec Std.I64) : CityPath := v.val.map fun x => x.val

  def CitiesInRange (n : Int) (p : CityPath) : Prop :=
    ∀ k, k < p.length → ∃ a, p[k]? = some a ∧ 0 ≤ a ∧ a < n

  def Joined (roads : Slice (alloc.vec.Vec Std.I64)) (p : CityPath) : Prop :=
    ∀ k a b, p[k]? = some a → p[k + 1]? = some b → IsRoad roads a b

  def ValidPath (n : Int) (roads : Slice (alloc.vec.Vec Std.I64))
      (targetPath : Slice (alloc.vec.Vec Std.U8)) (p : CityPath) : Prop :=
    p.length = targetPath.val.length ∧ CitiesInRange n p ∧ Joined roads p

  def Connected (n : Int) (roads : Slice (alloc.vec.Vec Std.I64)) : Prop :=
    ∀ a b : Int, 0 ≤ a → a < n → 0 ≤ b → b < n →
      ∃ p : CityPath, p.head? = some a ∧ p.getLast? = some b ∧ CitiesInRange n p ∧
        Joined roads p

  def mismatchAt (names : Slice (alloc.vec.Vec Std.U8))
      (targetPath : Slice (alloc.vec.Vec Std.U8)) (p : CityPath) (k : Nat) : Bool :=
    match p[k]? with
    | none => true
    | some a => decide (cityName names a ≠ targetName targetPath k)

  def ed (names : Slice (alloc.vec.Vec Std.U8)) (targetPath : Slice (alloc.vec.Vec Std.U8))
      (p : CityPath) : Nat :=
    ((List.range targetPath.val.length).filter (mismatchAt names targetPath p)).length

  def MatchesNames (names : Slice (alloc.vec.Vec Std.U8))
      (targetPath : Slice (alloc.vec.Vec Std.U8)) (p : CityPath) : Prop :=
    ∀ k a, k < targetPath.val.length → p[k]? = some a →
      cityName names a = targetName targetPath k

  def UpperName (s : ByteSeq) : Prop := s.length = 3 ∧ ∀ j ∈ s, 65 ≤ j ∧ j ≤ 90

  def HasCityWithName (n : Int) (names : Slice (alloc.vec.Vec Std.U8))
      (targetPath : Slice (alloc.vec.Vec Std.U8)) (k : Nat) : Prop :=
    ∃ i : Int, 0 ≤ i ∧ i < n ∧ cityName names i = targetName targetPath k

  def hasCityWithNameB (n : Int) (names : Slice (alloc.vec.Vec Std.U8))
      (targetPath : Slice (alloc.vec.Vec Std.U8)) (k : Nat) : Bool :=
    (List.range n.toNat).any fun j => decide (cityName names (j : Int) = targetName targetPath k)

  def MissingNameCount (n : Int) (names : Slice (alloc.vec.Vec Std.U8))
      (targetPath : Slice (alloc.vec.Vec Std.U8)) : Nat :=
    ((List.range targetPath.val.length).filter fun k =>
      hasCityWithNameB n names targetPath k == false).length

  def RoadsWF (n : Int) (roads : Slice (alloc.vec.Vec Std.I64)) : Prop :=
    (∀ e, e < roads.val.length →
      ∃ a b, roadAt roads e = some [a, b] ∧ 0 ≤ a ∧ a < n ∧ 0 ≤ b ∧ b < n ∧ a ≠ b) ∧
    (∀ e₁ e₂ a b, e₁ < roads.val.length → e₂ < roads.val.length →
      roadAt roads e₁ = some [a, b] →
      (roadAt roads e₂ = some [a, b] ∨ roadAt roads e₂ = some [b, a]) → e₁ = e₂)

  def SameUndirectedGraph (roads roads' : Slice (alloc.vec.Vec Std.I64)) : Prop :=
    ∃ f : List Int → List Int,
      (∀ u, f u = u ∨ f u = u.reverse) ∧
        (roadEndpoints roads').Perm ((roadEndpoints roads).map f)

  def Pre (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
      (names targetPath : Slice (alloc.vec.Vec Std.U8)) : Prop :=
    2 ≤ n.val ∧
    n.val ≤ 100 ∧
    RoadsWF n.val roads ∧
    n.val - 1 ≤ (roads.val.length : Int) ∧
    (roads.val.length : Int) ≤ n.val * (n.val - 1) / 2 ∧
    Connected n.val roads ∧
    names.val.length = n.val.toNat ∧
    (∀ i, i < names.val.length → ∃ s, names.val[i]? = some s ∧ UpperName (vecBytes s)) ∧
    1 ≤ targetPath.val.length ∧
    targetPath.val.length ≤ 100 ∧
    (∀ k, k < targetPath.val.length → ∃ s, targetPath.val[k]? = some s ∧ UpperName (vecBytes s))

  /-- Let a sequence p of city indices be a valid path if len(p) = len(targetPath), every entry p[k] satisfies 0 <= p[k] < n, and for every k with 0 <= k < len(p)-1 there is a road e with {p[k], p[k+1]} = {roads[e][0], roads[e][1]} (order of the two endpoints and order of roads ignored). For a valid path p, let ed(p) be the number of indices k with 0 <= k < len(targetPath) such that names[p[k]] is not byte-equal to targetPath[k] (same length and same bytes in the same order). The function returns a result r and does not fail. The returned r is a valid path and ed(r) is minimal among all valid paths: for every valid path q, ed(r) <= ed(q).
    Preconditions: n is an integer with 2 <= n <= 100. roads is a list of roads; each road e with 0 <= e < len(roads) has length 2, with entries a=roads[e][0] and b=roads[e][1] satisfying 0 <= a,b < n and a != b, and no unordered pair {a,b} occurs in more than one road. Also n - 1 <= len(roads) <= n*(n-1)/2, and the undirected graph on {0,...,n-1} with these roads is connected. names has length n; for every i with 0 <= i < n, names[i] has length 3 and all its bytes are upper-case ASCII letters. targetPath has length at least 1 and at most 100; for every k with 0 <= k < len(targetPath), targetPath[k] has length 3 and all its bytes are upper-case ASCII letters. -/
  theorem spec_1 (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
      (names targetPath : Slice (alloc.vec.Vec Std.U8)) (hpre : Pre n roads names targetPath) :
      ∃ r : alloc.vec.Vec Std.I64,
        Aegis.MostSimilar.most_similar n roads names targetPath = ok r ∧
          ValidPath n.val roads targetPath (resultPath r) ∧
          ∀ q : CityPath, ValidPath n.val roads targetPath q →
            ed names targetPath (resultPath r) ≤ ed names targetPath q := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
        (names targetPath : Slice (alloc.vec.Vec Std.U8)) (hpre : Pre n roads names targetPath), ∃ r : alloc.vec.Vec Std.I64,
          Aegis.MostSimilar.most_similar n roads names targetPath = ok r ∧
            ValidPath n.val roads targetPath (resultPath r) ∧
            ∀ q : CityPath, ValidPath n.val roads targetPath q →
              ed names targetPath (resultPath r) ≤ ed names targetPath q) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = len(targetPath).
    Preconditions: n is an integer with 2 <= n <= 100. roads is a list of roads; each road e with 0 <= e < len(roads) has length 2, with entries a=roads[e][0] and b=roads[e][1] satisfying 0 <= a,b < n and a != b, and no unordered pair {a,b} occurs in more than one road. Also n - 1 <= len(roads) <= n*(n-1)/2, and the undirected graph on {0,...,n-1} with these roads is connected. names has length n; for every i with 0 <= i < n, names[i] has length 3 and all its bytes are upper-case ASCII letters. targetPath has length at least 1 and at most 100; for every k with 0 <= k < len(targetPath), targetPath[k] has length 3 and all its bytes are upper-case ASCII letters. -/
  theorem spec_2 (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
      (names targetPath : Slice (alloc.vec.Vec Std.U8)) (hpre : Pre n roads names targetPath)
      (r : alloc.vec.Vec Std.I64)
      (h : Aegis.MostSimilar.most_similar n roads names targetPath = ok r) :
      r.val.length = targetPath.val.length := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
        (names targetPath : Slice (alloc.vec.Vec Std.U8)) (hpre : Pre n roads names targetPath)
        (r : alloc.vec.Vec Std.I64)
        (h : Aegis.MostSimilar.most_similar n roads names targetPath = ok r), r.val.length = targetPath.val.length) := by
    sorry

  /-- Whenever the function returns a result r, for every k with 0 <= k < len(r), the index r[k] is a city index: 0 <= r[k] < n.
    Preconditions: n is an integer with 2 <= n <= 100. roads is a list of roads; each road e with 0 <= e < len(roads) has length 2, with entries a=roads[e][0] and b=roads[e][1] satisfying 0 <= a,b < n and a != b, and no unordered pair {a,b} occurs in more than one road. Also n - 1 <= len(roads) <= n*(n-1)/2, and the undirected graph on {0,...,n-1} with these roads is connected. names has length n; for every i with 0 <= i < n, names[i] has length 3 and all its bytes are upper-case ASCII letters. targetPath has length at least 1 and at most 100; for every k with 0 <= k < len(targetPath), targetPath[k] has length 3 and all its bytes are upper-case ASCII letters. -/
  theorem spec_3 (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
      (names targetPath : Slice (alloc.vec.Vec Std.U8)) (hpre : Pre n roads names targetPath)
      (r : alloc.vec.Vec Std.I64)
      (h : Aegis.MostSimilar.most_similar n roads names targetPath = ok r) :
      CitiesInRange n.val (resultPath r) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
        (names targetPath : Slice (alloc.vec.Vec Std.U8)) (hpre : Pre n roads names targetPath)
        (r : alloc.vec.Vec Std.I64)
        (h : Aegis.MostSimilar.most_similar n roads names targetPath = ok r), CitiesInRange n.val (resultPath r)) := by
    sorry

  /-- Whenever the function returns a result r, for every k with 0 <= k < len(r)-1, there exists a road index e with 0 <= e < len(roads) such that either (roads[e][0] = r[k] and roads[e][1] = r[k+1]) or (roads[e][0] = r[k+1] and roads[e][1] = r[k]).
    Preconditions: n is an integer with 2 <= n <= 100. roads is a list of roads; each road e with 0 <= e < len(roads) has length 2, with entries a=roads[e][0] and b=roads[e][1] satisfying 0 <= a,b < n and a != b, and no unordered pair {a,b} occurs in more than one road. Also n - 1 <= len(roads) <= n*(n-1)/2, and the undirected graph on {0,...,n-1} with these roads is connected. names has length n; for every i with 0 <= i < n, names[i] has length 3 and all its bytes are upper-case ASCII letters. targetPath has length at least 1 and at most 100; for every k with 0 <= k < len(targetPath), targetPath[k] has length 3 and all its bytes are upper-case ASCII letters. -/
  theorem spec_4 (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
      (names targetPath : Slice (alloc.vec.Vec Std.U8)) (hpre : Pre n roads names targetPath)
      (r : alloc.vec.Vec Std.I64)
      (h : Aegis.MostSimilar.most_similar n roads names targetPath = ok r) :
      ∀ k a b, (resultPath r)[k]? = some a → (resultPath r)[k + 1]? = some b →
        ∃ e, e < roads.val.length ∧
          ((roadEntry roads e 0 = some a ∧ roadEntry roads e 1 = some b) ∨
            (roadEntry roads e 0 = some b ∧ roadEntry roads e 1 = some a)) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
        (names targetPath : Slice (alloc.vec.Vec Std.U8)) (hpre : Pre n roads names targetPath)
        (r : alloc.vec.Vec Std.I64)
        (h : Aegis.MostSimilar.most_similar n roads names targetPath = ok r), ∀ k a b, (resultPath r)[k]? = some a → (resultPath r)[k + 1]? = some b →
          ∃ e, e < roads.val.length ∧
            ((roadEntry roads e 0 = some a ∧ roadEntry roads e 1 = some b) ∨
              (roadEntry roads e 0 = some b ∧ roadEntry roads e 1 = some a))) := by
    sorry

  /-- Whenever the function returns a result r, if r is a valid path (len(r) = len(targetPath), all entries in [0,n), and consecutive entries are joined by a road), then for every valid path q in the same graph, ed(r) <= ed(q), where ed(p) counts the positions k with 0 <= k < len(targetPath) for which names[p[k]] is not byte-equal to targetPath[k].
    Preconditions: n is an integer with 2 <= n <= 100. roads is a list of roads; each road e with 0 <= e < len(roads) has length 2, with entries a=roads[e][0] and b=roads[e][1] satisfying 0 <= a,b < n and a != b, and no unordered pair {a,b} occurs in more than one road. Also n - 1 <= len(roads) <= n*(n-1)/2, and the undirected graph on {0,...,n-1} with these roads is connected. names has length n; for every i with 0 <= i < n, names[i] has length 3 and all its bytes are upper-case ASCII letters. targetPath has length at least 1 and at most 100; for every k with 0 <= k < len(targetPath), targetPath[k] has length 3 and all its bytes are upper-case ASCII letters. -/
  theorem spec_5 (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
      (names targetPath : Slice (alloc.vec.Vec Std.U8)) (hpre : Pre n roads names targetPath)
      (r : alloc.vec.Vec Std.I64)
      (h : Aegis.MostSimilar.most_similar n roads names targetPath = ok r)
      (hvalid : ValidPath n.val roads targetPath (resultPath r)) :
      ∀ q : CityPath, ValidPath n.val roads targetPath q →
        ed names targetPath (resultPath r) ≤ ed names targetPath q := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
        (names targetPath : Slice (alloc.vec.Vec Std.U8)) (hpre : Pre n roads names targetPath)
        (r : alloc.vec.Vec Std.I64)
        (h : Aegis.MostSimilar.most_similar n roads names targetPath = ok r)
        (hvalid : ValidPath n.val roads targetPath (resultPath r)), ∀ q : CityPath, ValidPath n.val roads targetPath q →
          ed names targetPath (resultPath r) ≤ ed names targetPath q) := by
    sorry

  /-- Whenever the function returns a result r, if there exists a valid path p such that for every k with 0 <= k < len(targetPath), names[p[k]] is byte-equal to targetPath[k], then r is a valid path and for every k with 0 <= k < len(targetPath), names[r[k]] is byte-equal to targetPath[k].
    Preconditions: n is an integer with 2 <= n <= 100. roads is a list of roads; each road e with 0 <= e < len(roads) has length 2, with entries a=roads[e][0] and b=roads[e][1] satisfying 0 <= a,b < n and a != b, and no unordered pair {a,b} occurs in more than one road. Also n - 1 <= len(roads) <= n*(n-1)/2, and the undirected graph on {0,...,n-1} with these roads is connected. names has length n; for every i with 0 <= i < n, names[i] has length 3 and all its bytes are upper-case ASCII letters. targetPath has length at least 1 and at most 100; for every k with 0 <= k < len(targetPath), targetPath[k] has length 3 and all its bytes are upper-case ASCII letters. -/
  theorem spec_6 (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
      (names targetPath : Slice (alloc.vec.Vec Std.U8)) (hpre : Pre n roads names targetPath)
      (r : alloc.vec.Vec Std.I64)
      (h : Aegis.MostSimilar.most_similar n roads names targetPath = ok r)
      (hwitness : ∃ p : CityPath, ValidPath n.val roads targetPath p ∧
        MatchesNames names targetPath p) :
      ValidPath n.val roads targetPath (resultPath r) ∧
        MatchesNames names targetPath (resultPath r) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
        (names targetPath : Slice (alloc.vec.Vec Std.U8)) (hpre : Pre n roads names targetPath)
        (r : alloc.vec.Vec Std.I64)
        (h : Aegis.MostSimilar.most_similar n roads names targetPath = ok r)
        (hwitness : ∃ p : CityPath, ValidPath n.val roads targetPath p ∧
          MatchesNames names targetPath p), ValidPath n.val roads targetPath (resultPath r) ∧
          MatchesNames names targetPath (resultPath r)) := by
    sorry

  /-- Whenever the function returns a result r, if no valid path p has names[p[k]] byte-equal to targetPath[k] for all k with 0 <= k < len(targetPath), then r is a valid path and ed(r) >= 1.
    Preconditions: n is an integer with 2 <= n <= 100. roads is a list of roads; each road e with 0 <= e < len(roads) has length 2, with entries a=roads[e][0] and b=roads[e][1] satisfying 0 <= a,b < n and a != b, and no unordered pair {a,b} occurs in more than one road. Also n - 1 <= len(roads) <= n*(n-1)/2, and the undirected graph on {0,...,n-1} with these roads is connected. names has length n; for every i with 0 <= i < n, names[i] has length 3 and all its bytes are upper-case ASCII letters. targetPath has length at least 1 and at most 100; for every k with 0 <= k < len(targetPath), targetPath[k] has length 3 and all its bytes are upper-case ASCII letters. -/
  theorem spec_7 (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
      (names targetPath : Slice (alloc.vec.Vec Std.U8)) (hpre : Pre n roads names targetPath)
      (r : alloc.vec.Vec Std.I64)
      (h : Aegis.MostSimilar.most_similar n roads names targetPath = ok r)
      (hnone : ¬ ∃ p : CityPath, ValidPath n.val roads targetPath p ∧
        MatchesNames names targetPath p) :
      ValidPath n.val roads targetPath (resultPath r) ∧
        1 ≤ ed names targetPath (resultPath r) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
        (names targetPath : Slice (alloc.vec.Vec Std.U8)) (hpre : Pre n roads names targetPath)
        (r : alloc.vec.Vec Std.I64)
        (h : Aegis.MostSimilar.most_similar n roads names targetPath = ok r)
        (hnone : ¬ ∃ p : CityPath, ValidPath n.val roads targetPath p ∧
          MatchesNames names targetPath p), ValidPath n.val roads targetPath (resultPath r) ∧
          1 ≤ ed names targetPath (resultPath r)) := by
    sorry

  /-- Whenever the function returns a result r and len(targetPath) = 1, then len(r) = 1 and 0 <= r[0] < n, and names[r[0]] is byte-equal to targetPath[0] if and only if there exists a city i with 0 <= i < n such that names[i] is byte-equal to targetPath[0]. Equivalently, ed(r) = 0 when such a city exists, and ed(r) = 1 otherwise.
    Preconditions: n is an integer with 2 <= n <= 100. roads is a list of roads; each road e with 0 <= e < len(roads) has length 2, with entries a=roads[e][0] and b=roads[e][1] satisfying 0 <= a,b < n and a != b, and no unordered pair {a,b} occurs in more than one road. Also n - 1 <= len(roads) <= n*(n-1)/2, and the undirected graph on {0,...,n-1} with these roads is connected. names has length n; for every i with 0 <= i < n, names[i] has length 3 and all its bytes are upper-case ASCII letters. targetPath has length at least 1 and at most 100; for every k with 0 <= k < len(targetPath), targetPath[k] has length 3 and all its bytes are upper-case ASCII letters. -/
  theorem spec_8 (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
      (names targetPath : Slice (alloc.vec.Vec Std.U8)) (hpre : Pre n roads names targetPath)
      (r : alloc.vec.Vec Std.I64)
      (h : Aegis.MostSimilar.most_similar n roads names targetPath = ok r)
      (hlen : targetPath.val.length = 1) :
      (resultPath r).length = 1 ∧
        CitiesInRange n.val (resultPath r) ∧
        (∀ a, (resultPath r)[0]? = some a →
          (cityName names a = targetName targetPath 0 ↔
            HasCityWithName n.val names targetPath 0)) ∧
        (HasCityWithName n.val names targetPath 0 → ed names targetPath (resultPath r) = 0) ∧
        (¬ HasCityWithName n.val names targetPath 0 → ed names targetPath (resultPath r) = 1) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
        (names targetPath : Slice (alloc.vec.Vec Std.U8)) (hpre : Pre n roads names targetPath)
        (r : alloc.vec.Vec Std.I64)
        (h : Aegis.MostSimilar.most_similar n roads names targetPath = ok r)
        (hlen : targetPath.val.length = 1), (resultPath r).length = 1 ∧
          CitiesInRange n.val (resultPath r) ∧
          (∀ a, (resultPath r)[0]? = some a →
            (cityName names a = targetName targetPath 0 ↔
              HasCityWithName n.val names targetPath 0)) ∧
          (HasCityWithName n.val names targetPath 0 → ed names targetPath (resultPath r) = 0) ∧
          (¬ HasCityWithName n.val names targetPath 0 → ed names targetPath (resultPath r) = 1)) := by
    sorry

  /-- Whenever the function returns a result r and r is a valid path, ed(r) is at least the number of indices k with 0 <= k < len(targetPath) for which there is no city i with 0 <= i < n and names[i] byte-equal to targetPath[k].
    Preconditions: n is an integer with 2 <= n <= 100. roads is a list of roads; each road e with 0 <= e < len(roads) has length 2, with entries a=roads[e][0] and b=roads[e][1] satisfying 0 <= a,b < n and a != b, and no unordered pair {a,b} occurs in more than one road. Also n - 1 <= len(roads) <= n*(n-1)/2, and the undirected graph on {0,...,n-1} with these roads is connected. names has length n; for every i with 0 <= i < n, names[i] has length 3 and all its bytes are upper-case ASCII letters. targetPath has length at least 1 and at most 100; for every k with 0 <= k < len(targetPath), targetPath[k] has length 3 and all its bytes are upper-case ASCII letters. -/
  theorem spec_9 (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
      (names targetPath : Slice (alloc.vec.Vec Std.U8)) (hpre : Pre n roads names targetPath)
      (r : alloc.vec.Vec Std.I64)
      (h : Aegis.MostSimilar.most_similar n roads names targetPath = ok r)
      (hvalid : ValidPath n.val roads targetPath (resultPath r)) :
      MissingNameCount n.val names targetPath ≤ ed names targetPath (resultPath r) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
        (names targetPath : Slice (alloc.vec.Vec Std.U8)) (hpre : Pre n roads names targetPath)
        (r : alloc.vec.Vec Std.I64)
        (h : Aegis.MostSimilar.most_similar n roads names targetPath = ok r)
        (hvalid : ValidPath n.val roads targetPath (resultPath r)), MissingNameCount n.val names targetPath ≤ ed names targetPath (resultPath r)) := by
    sorry

  /-- Whenever the function returns a result r and r is a valid path, 0 <= ed(r) <= len(targetPath).
    Preconditions: n is an integer with 2 <= n <= 100. roads is a list of roads; each road e with 0 <= e < len(roads) has length 2, with entries a=roads[e][0] and b=roads[e][1] satisfying 0 <= a,b < n and a != b, and no unordered pair {a,b} occurs in more than one road. Also n - 1 <= len(roads) <= n*(n-1)/2, and the undirected graph on {0,...,n-1} with these roads is connected. names has length n; for every i with 0 <= i < n, names[i] has length 3 and all its bytes are upper-case ASCII letters. targetPath has length at least 1 and at most 100; for every k with 0 <= k < len(targetPath), targetPath[k] has length 3 and all its bytes are upper-case ASCII letters. -/
  theorem spec_10 (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
      (names targetPath : Slice (alloc.vec.Vec Std.U8)) (hpre : Pre n roads names targetPath)
      (r : alloc.vec.Vec Std.I64)
      (h : Aegis.MostSimilar.most_similar n roads names targetPath = ok r)
      (hvalid : ValidPath n.val roads targetPath (resultPath r)) :
      0 ≤ ed names targetPath (resultPath r) ∧
        ed names targetPath (resultPath r) ≤ targetPath.val.length := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
        (names targetPath : Slice (alloc.vec.Vec Std.U8)) (hpre : Pre n roads names targetPath)
        (r : alloc.vec.Vec Std.I64)
        (h : Aegis.MostSimilar.most_similar n roads names targetPath = ok r)
        (hvalid : ValidPath n.val roads targetPath (resultPath r)), 0 ≤ ed names targetPath (resultPath r) ∧
          ed names targetPath (resultPath r) ≤ targetPath.val.length) := by
    sorry

  /-- Whenever the function returns a result r and r is a valid path, ed(r) = 0 if and only if for every k with 0 <= k < len(targetPath), names[r[k]] is byte-equal to targetPath[k].
    Preconditions: n is an integer with 2 <= n <= 100. roads is a list of roads; each road e with 0 <= e < len(roads) has length 2, with entries a=roads[e][0] and b=roads[e][1] satisfying 0 <= a,b < n and a != b, and no unordered pair {a,b} occurs in more than one road. Also n - 1 <= len(roads) <= n*(n-1)/2, and the undirected graph on {0,...,n-1} with these roads is connected. names has length n; for every i with 0 <= i < n, names[i] has length 3 and all its bytes are upper-case ASCII letters. targetPath has length at least 1 and at most 100; for every k with 0 <= k < len(targetPath), targetPath[k] has length 3 and all its bytes are upper-case ASCII letters. -/
  theorem spec_11 (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
      (names targetPath : Slice (alloc.vec.Vec Std.U8)) (hpre : Pre n roads names targetPath)
      (r : alloc.vec.Vec Std.I64)
      (h : Aegis.MostSimilar.most_similar n roads names targetPath = ok r)
      (hvalid : ValidPath n.val roads targetPath (resultPath r)) :
      ed names targetPath (resultPath r) = 0 ↔
        MatchesNames names targetPath (resultPath r) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
        (names targetPath : Slice (alloc.vec.Vec Std.U8)) (hpre : Pre n roads names targetPath)
        (r : alloc.vec.Vec Std.I64)
        (h : Aegis.MostSimilar.most_similar n roads names targetPath = ok r)
        (hvalid : ValidPath n.val roads targetPath (resultPath r)), ed names targetPath (resultPath r) = 0 ↔
          MatchesNames names targetPath (resultPath r)) := by
    sorry

  /-- Whenever the function returns a result r and r is a valid path, if there exists a city i with 0 <= i < n such that names[i] is byte-equal to targetPath[0], then ed(r) <= len(targetPath) - 1.
    Preconditions: n is an integer with 2 <= n <= 100. roads is a list of roads; each road e with 0 <= e < len(roads) has length 2, with entries a=roads[e][0] and b=roads[e][1] satisfying 0 <= a,b < n and a != b, and no unordered pair {a,b} occurs in more than one road. Also n - 1 <= len(roads) <= n*(n-1)/2, and the undirected graph on {0,...,n-1} with these roads is connected. names has length n; for every i with 0 <= i < n, names[i] has length 3 and all its bytes are upper-case ASCII letters. targetPath has length at least 1 and at most 100; for every k with 0 <= k < len(targetPath), targetPath[k] has length 3 and all its bytes are upper-case ASCII letters. -/
  theorem spec_12 (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
      (names targetPath : Slice (alloc.vec.Vec Std.U8)) (hpre : Pre n roads names targetPath)
      (r : alloc.vec.Vec Std.I64)
      (h : Aegis.MostSimilar.most_similar n roads names targetPath = ok r)
      (hvalid : ValidPath n.val roads targetPath (resultPath r))
      (hcity : HasCityWithName n.val names targetPath 0) :
      ed names targetPath (resultPath r) ≤ targetPath.val.length - 1 := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
        (names targetPath : Slice (alloc.vec.Vec Std.U8)) (hpre : Pre n roads names targetPath)
        (r : alloc.vec.Vec Std.I64)
        (h : Aegis.MostSimilar.most_similar n roads names targetPath = ok r)
        (hvalid : ValidPath n.val roads targetPath (resultPath r))
        (hcity : HasCityWithName n.val names targetPath 0), ed names targetPath (resultPath r) ≤ targetPath.val.length - 1) := by
    sorry

  /-- Under the preconditions, the function returns a result r (it does not fail due to overflow, out-of-bounds access, or panic).
    Preconditions: n is an integer with 2 <= n <= 100. roads is a list of roads; each road e with 0 <= e < len(roads) has length 2, with entries a=roads[e][0] and b=roads[e][1] satisfying 0 <= a,b < n and a != b, and no unordered pair {a,b} occurs in more than one road. Also n - 1 <= len(roads) <= n*(n-1)/2, and the undirected graph on {0,...,n-1} with these roads is connected. names has length n; for every i with 0 <= i < n, names[i] has length 3 and all its bytes are upper-case ASCII letters. targetPath has length at least 1 and at most 100; for every k with 0 <= k < len(targetPath), targetPath[k] has length 3 and all its bytes are upper-case ASCII letters. -/
  theorem spec_13 (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
      (names targetPath : Slice (alloc.vec.Vec Std.U8)) (hpre : Pre n roads names targetPath) :
      ∃ r : alloc.vec.Vec Std.I64,
        Aegis.MostSimilar.most_similar n roads names targetPath = ok r := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (n : Std.I64) (roads : Slice (alloc.vec.Vec Std.I64))
        (names targetPath : Slice (alloc.vec.Vec Std.U8)) (hpre : Pre n roads names targetPath), ∃ r : alloc.vec.Vec Std.I64,
          Aegis.MostSimilar.most_similar n roads names targetPath = ok r) := by
    sorry

  /-- Whenever the function returns r on input (n, roads, names, targetPath) and returns r' on input (n, roads', names, targetPath), both r and r' are valid paths of length len(targetPath), and ed(r) = ed(r'), where ed is computed using the common names and targetPath.
    Preconditions: n is an integer with 2 <= n <= 100. roads is a list of roads; each road e with 0 <= e < len(roads) has length 2, with entries a=roads[e][0] and b=roads[e][1] satisfying 0 <= a,b < n and a != b, and no unordered pair {a,b} occurs in more than one road. Also n - 1 <= len(roads) <= n*(n-1)/2, and the undirected graph on {0,...,n-1} with these roads is connected. names has length n; for every i with 0 <= i < n, names[i] has length 3 and all its bytes are upper-case ASCII letters. targetPath has length at least 1 and at most 100; for every k with 0 <= k < len(targetPath), targetPath[k] has length 3 and all its bytes are upper-case ASCII letters. In addition, roads' is any list obtained from roads by permuting its entries and/or replacing any road [a,b] by [b,a]; thus roads' satisfies the same constraints and describes the same undirected graph as roads. -/
  theorem spec_14 (n : Std.I64) (roads roads' : Slice (alloc.vec.Vec Std.I64))
      (names targetPath : Slice (alloc.vec.Vec Std.U8)) (hpre : Pre n roads names targetPath)
      (hsame : SameUndirectedGraph roads roads')
      (r r' : alloc.vec.Vec Std.I64)
      (h : Aegis.MostSimilar.most_similar n roads names targetPath = ok r)
      (h' : Aegis.MostSimilar.most_similar n roads' names targetPath = ok r') :
      ValidPath n.val roads targetPath (resultPath r) ∧
        ValidPath n.val roads' targetPath (resultPath r') ∧
        ed names targetPath (resultPath r) = ed names targetPath (resultPath r') := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (n : Std.I64) (roads roads' : Slice (alloc.vec.Vec Std.I64))
        (names targetPath : Slice (alloc.vec.Vec Std.U8)) (hpre : Pre n roads names targetPath)
        (hsame : SameUndirectedGraph roads roads')
        (r r' : alloc.vec.Vec Std.I64)
        (h : Aegis.MostSimilar.most_similar n roads names targetPath = ok r)
        (h' : Aegis.MostSimilar.most_similar n roads' names targetPath = ok r'), ValidPath n.val roads targetPath (resultPath r) ∧
          ValidPath n.val roads' targetPath (resultPath r') ∧
          ed names targetPath (resultPath r) = ed names targetPath (resultPath r')) := by
    sorry

  end AegisSpec.MostSimilar

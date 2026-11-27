import Aegis.MinimumTeachings.Code.Funs

/-!
# Specifications of `Aegis.MinimumTeachings.minimum_teachings`

LeetCode problem `minimum-number-of-people-to-teach`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MinimumTeachings

namespace AegisSpec.MinimumTeachings

def UserLangs (v : alloc.vec.Vec Std.I64) : Finset ℤ := (v.val.map fun x => x.val).toFinset

def Lang (languages : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : Finset ℤ :=
  match languages.val[i - 1]? with
  | some v => UserLangs v
  | none => ∅

def numUsers (languages : Slice (alloc.vec.Vec Std.I64)) : ℕ := languages.val.length

def numFriendships (friendships : Slice (alloc.vec.Vec Std.I64)) : ℕ :=
  friendships.val.length

def friendshipAt (friendships : Slice (alloc.vec.Vec Std.I64)) (k : ℕ) : Option (ℕ × ℕ) :=
  match friendships.val[k - 1]? with
  | some e =>
    match e.val.map (fun x => x.val) with
    | [a, b] => some (a.toNat, b.toNat)
    | _ => none
  | none => none

def Shares (languages : Slice (alloc.vec.Vec Std.I64)) (u v : ℕ) : Prop :=
  (Lang languages u ∩ Lang languages v).Nonempty

instance decidableShares (languages : Slice (alloc.vec.Vec Std.I64)) (u v : ℕ) :
    Decidable (Shares languages u v) :=
  inferInstanceAs (Decidable (Lang languages u ∩ Lang languages v).Nonempty)

def Bad (languages : Slice (alloc.vec.Vec Std.I64)) (u v : ℕ) : Prop :=
  Lang languages u ∩ Lang languages v = ∅

instance decidableBad (languages : Slice (alloc.vec.Vec Std.I64)) (u v : ℕ) :
    Decidable (Bad languages u v) :=
  inferInstanceAs (Decidable (Lang languages u ∩ Lang languages v = ∅))

def BadUsers (languages friendships : Slice (alloc.vec.Vec Std.I64)) : Finset ℕ :=
  (Finset.range (numFriendships friendships)).biUnion fun k =>
    match friendshipAt friendships (k + 1) with
    | some (u, v) => if Bad languages u v then {u, v} else ∅
    | none => ∅

def needOf (languages : Slice (alloc.vec.Vec Std.I64)) (S : Finset ℕ) (L : ℤ) : ℕ :=
  (S.filter fun i => L ∉ Lang languages i).card

def taughtSet (languages : Slice (alloc.vec.Vec Std.I64)) (S : Finset ℕ) (L : ℤ) : Finset ℕ :=
  S.filter fun i => L ∉ Lang languages i

def KnowsAfter (languages : Slice (alloc.vec.Vec Std.I64)) (T : Finset ℕ) (L : ℤ)
    (i : ℕ) : Prop :=
  L ∈ Lang languages i ∨ i ∈ T

noncomputable def minNeed (n : Std.I64) (languages : Slice (alloc.vec.Vec Std.I64))
    (S : Finset ℕ) : ℕ :=
  sInf {k : ℕ | ∃ L : ℤ, 1 ≤ L ∧ L ≤ n.val ∧ needOf languages S L = k}

def Constraints (n : Std.I64) (languages friendships : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  2 ≤ n.val ∧ n.val ≤ 500 ∧
  1 ≤ numUsers languages ∧ numUsers languages ≤ 500 ∧
  (∀ i, 1 ≤ i → i ≤ numUsers languages →
    ∃ v, languages.val[i - 1]? = some v ∧
      1 ≤ v.val.length ∧ v.val.length ≤ n.val.toNat ∧
      (v.val.map fun x => x.val).Nodup ∧
      (∀ x ∈ v.val, 1 ≤ x.val ∧ x.val ≤ n.val)) ∧
  1 ≤ numFriendships friendships ∧ numFriendships friendships ≤ 500 ∧
  (∀ k, 1 ≤ k → k ≤ numFriendships friendships →
    ∃ u v, friendshipAt friendships k = some (u, v) ∧ 1 ≤ u ∧ u < v ∧ v ≤ numUsers languages) ∧
  (∀ k k', 1 ≤ k → k ≤ numFriendships friendships → 1 ≤ k' → k' ≤ numFriendships friendships →
    k ≠ k' → friendshipAt friendships k ≠ friendshipAt friendships k')

/-- The function returns a result r, and r = min_{1 ≤ L ≤ n} need(L). Equivalently, r is the least number of users that must be taught one single language L so that after teaching, for every friendship entry (u,v), either u and v originally share a language or both u and v know L.
  Preconditions: n, languages, friendships satisfy the problem constraints: 2 ≤ n ≤ 500; m = len(languages) with 1 ≤ m ≤ 500; for every i with 1 ≤ i ≤ m, languages[i-1] is a nonempty list of distinct values in [1,n] with length at most n; 1 ≤ len(friendships) ≤ 500; every friendships[k] has length 2 and satisfies 1 ≤ friendships[k][0] < friendships[k][1] ≤ m; all friendship pairs are distinct. Define Lang(i) = { languages[i-1][j] | 0 ≤ j < len(languages[i-1]) }. Call a friendship entry (u,v) bad if Lang(u) ∩ Lang(v) = ∅. Define B = { i | 1 ≤ i ≤ m and i is an endpoint of at least one bad friendship entry }. For L ∈ [1,n], define need(L) = |{ i ∈ B | L ∉ Lang(i) }|. -/
theorem spec_1 (n : Std.I64) (languages friendships : Slice (alloc.vec.Vec Std.I64))
    (h : Constraints n languages friendships) :
    ∃ r : Std.I64, minimum_teachings n languages friendships = ok r ∧
      r.val = (minNeed n languages (BadUsers languages friendships) : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (languages friendships : Slice (alloc.vec.Vec Std.I64))
    (h : Constraints n languages friendships), ∃ r : Std.I64, minimum_teachings n languages friendships = ok r ∧
      r.val = (minNeed n languages (BadUsers languages friendships) : ℤ)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r; it does not fail by overflow, out-of-bounds access, or panic.
  Preconditions: n, languages, friendships satisfy the problem constraints stated in spec_1. Define m, Lang(i), bad friendship, B, and need(L) as in spec_1. -/
theorem spec_2 (n : Std.I64) (languages friendships : Slice (alloc.vec.Vec Std.I64))
    (h : Constraints n languages friendships) :
    ∃ r : Std.I64, minimum_teachings n languages friendships = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (languages friendships : Slice (alloc.vec.Vec Std.I64))
    (h : Constraints n languages friendships), ∃ r : Std.I64, minimum_teachings n languages friendships = ok r) := by
  sorry

/-- The function returns a result r and r ≥ 0.
  Preconditions: n, languages, friendships satisfy the problem constraints stated in spec_1. Define m, Lang(i), bad friendship, B, and need(L) as in spec_1. -/
theorem spec_3 (n : Std.I64) (languages friendships : Slice (alloc.vec.Vec Std.I64))
    (h : Constraints n languages friendships) :
    ∃ r : Std.I64, minimum_teachings n languages friendships = ok r ∧ 0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (languages friendships : Slice (alloc.vec.Vec Std.I64))
    (h : Constraints n languages friendships), ∃ r : Std.I64, minimum_teachings n languages friendships = ok r ∧ 0 ≤ r.val) := by
  sorry

/-- The function returns a result r and, if B is nonempty, then r ≤ |B| - 1.
  Preconditions: n, languages, friendships satisfy the problem constraints stated in spec_1. Define m, Lang(i), bad friendship, B, and need(L) as in spec_1. -/
theorem spec_4 (n : Std.I64) (languages friendships : Slice (alloc.vec.Vec Std.I64))
    (h : Constraints n languages friendships) :
    ∃ r : Std.I64, minimum_teachings n languages friendships = ok r ∧
      ((BadUsers languages friendships).Nonempty →
        r.val ≤ ((BadUsers languages friendships).card : ℤ) - 1) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (languages friendships : Slice (alloc.vec.Vec Std.I64))
    (h : Constraints n languages friendships), ∃ r : Std.I64, minimum_teachings n languages friendships = ok r ∧
      ((BadUsers languages friendships).Nonempty →
        r.val ≤ ((BadUsers languages friendships).card : ℤ) - 1)) := by
  sorry

/-- If every friendship entry (u,v) satisfies Lang(u) ∩ Lang(v) ≠ ∅ (equivalently B = ∅), then the function returns r = 0.
  Preconditions: n, languages, friendships satisfy the problem constraints stated in spec_1. Define m, Lang(i), bad friendship, B, and need(L) as in spec_1. -/
theorem spec_5 (n : Std.I64) (languages friendships : Slice (alloc.vec.Vec Std.I64))
    (h : Constraints n languages friendships)
    (hgood : ∀ k, 1 ≤ k → k ≤ numFriendships friendships → ∀ u v : ℕ,
      friendshipAt friendships k = some (u, v) → Shares languages u v) :
    ∃ r : Std.I64, minimum_teachings n languages friendships = ok r ∧ r.val = 0 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Std.I64) (languages friendships : Slice (alloc.vec.Vec Std.I64))
    (h : Constraints n languages friendships)
    (hgood : ∀ k, 1 ≤ k → k ≤ numFriendships friendships → ∀ u v : ℕ,
      friendshipAt friendships k = some (u, v) → Shares languages u v), ∃ r : Std.I64, minimum_teachings n languages friendships = ok r ∧ r.val = 0) := by
  sorry

/-- If B is nonempty, then the function returns a result r and r ≥ 1.
  Preconditions: n, languages, friendships satisfy the problem constraints stated in spec_1. Define m, Lang(i), bad friendship, B, and need(L) as in spec_1. -/
theorem spec_6 (n : Std.I64) (languages friendships : Slice (alloc.vec.Vec Std.I64))
    (h : Constraints n languages friendships)
    (hnonempty : (BadUsers languages friendships).Nonempty) :
    ∃ r : Std.I64, minimum_teachings n languages friendships = ok r ∧ 1 ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Std.I64) (languages friendships : Slice (alloc.vec.Vec Std.I64))
    (h : Constraints n languages friendships)
    (hnonempty : (BadUsers languages friendships).Nonempty), ∃ r : Std.I64, minimum_teachings n languages friendships = ok r ∧ 1 ≤ r.val) := by
  sorry

/-- If |B| = 2, then the function returns r = 1.
  Preconditions: n, languages, friendships satisfy the problem constraints stated in spec_1. Define m, Lang(i), bad friendship, B, and need(L) as in spec_1. -/
theorem spec_7 (n : Std.I64) (languages friendships : Slice (alloc.vec.Vec Std.I64))
    (h : Constraints n languages friendships)
    (hcard : (BadUsers languages friendships).card = 2) :
    ∃ r : Std.I64, minimum_teachings n languages friendships = ok r ∧ r.val = 1 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Std.I64) (languages friendships : Slice (alloc.vec.Vec Std.I64))
    (h : Constraints n languages friendships)
    (hcard : (BadUsers languages friendships).card = 2), ∃ r : Std.I64, minimum_teachings n languages friendships = ok r ∧ r.val = 1) := by
  sorry

/-- The function returns a result r and there exists a language L* ∈ [1,n] such that |{ i ∈ B | L* ∉ Lang(i) }| = r, and teaching L* to exactly the users in that set makes every friendship pair able to communicate: for every friendship entry (u,v), either Lang(u) ∩ Lang(v) ≠ ∅, or both u and v know L* after this teaching.
  Preconditions: n, languages, friendships satisfy the problem constraints stated in spec_1. Define m, Lang(i), bad friendship, B, and need(L) as in spec_1. -/
theorem spec_8 (n : Std.I64) (languages friendships : Slice (alloc.vec.Vec Std.I64))
    (h : Constraints n languages friendships) :
    ∃ r : Std.I64, minimum_teachings n languages friendships = ok r ∧
      ∃ L : ℤ, 1 ≤ L ∧ L ≤ n.val ∧
        (needOf languages (BadUsers languages friendships) L : ℤ) = r.val ∧
        (∀ k, 1 ≤ k → k ≤ numFriendships friendships → ∀ u v : ℕ,
          friendshipAt friendships k = some (u, v) →
            Shares languages u v ∨
              (KnowsAfter languages
                  (taughtSet languages (BadUsers languages friendships) L) L u ∧
                KnowsAfter languages
                  (taughtSet languages (BadUsers languages friendships) L) L v)) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Std.I64) (languages friendships : Slice (alloc.vec.Vec Std.I64))
    (h : Constraints n languages friendships), ∃ r : Std.I64, minimum_teachings n languages friendships = ok r ∧
      ∃ L : ℤ, 1 ≤ L ∧ L ≤ n.val ∧
        (needOf languages (BadUsers languages friendships) L : ℤ) = r.val ∧
        (∀ k, 1 ≤ k → k ≤ numFriendships friendships → ∀ u v : ℕ,
          friendshipAt friendships k = some (u, v) →
            Shares languages u v ∨
              (KnowsAfter languages
                  (taughtSet languages (BadUsers languages friendships) L) L u ∧
                KnowsAfter languages
                  (taughtSet languages (BadUsers languages friendships) L) L v))) := by
  sorry

/-- The function returns a result r, and for every L ∈ [1,n] and every set T ⊆ {1,...,m}, if teaching L to the users in T makes every friendship pair able to communicate (that is, for every friendship entry (u,v), either Lang(u) ∩ Lang(v) ≠ ∅, or both (L ∈ Lang(u) or u ∈ T) and (L ∈ Lang(v) or v ∈ T) hold), then |T| ≥ r.
  Preconditions: n, languages, friendships satisfy the problem constraints stated in spec_1. Define m, Lang(i), bad friendship, B, and need(L) as in spec_1. -/
theorem spec_9 (n : Std.I64) (languages friendships : Slice (alloc.vec.Vec Std.I64))
    (h : Constraints n languages friendships) :
    ∃ r : Std.I64, minimum_teachings n languages friendships = ok r ∧
      ∀ (L : ℤ) (T : Finset ℕ), 1 ≤ L → L ≤ n.val →
        T ⊆ Finset.Icc 1 (numUsers languages) →
        (∀ k, 1 ≤ k → k ≤ numFriendships friendships → ∀ u v : ℕ,
          friendshipAt friendships k = some (u, v) →
            Shares languages u v ∨
              ((L ∈ Lang languages u ∨ u ∈ T) ∧ (L ∈ Lang languages v ∨ v ∈ T))) →
        r.val ≤ (T.card : ℤ) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : Std.I64) (languages friendships : Slice (alloc.vec.Vec Std.I64))
    (h : Constraints n languages friendships), ∃ r : Std.I64, minimum_teachings n languages friendships = ok r ∧
      ∀ (L : ℤ) (T : Finset ℕ), 1 ≤ L → L ≤ n.val →
        T ⊆ Finset.Icc 1 (numUsers languages) →
        (∀ k, 1 ≤ k → k ≤ numFriendships friendships → ∀ u v : ℕ,
          friendshipAt friendships k = some (u, v) →
            Shares languages u v ∨
              ((L ∈ Lang languages u ∨ u ∈ T) ∧ (L ∈ Lang languages v ∨ v ∈ T))) →
        r.val ≤ (T.card : ℤ)) := by
  sorry

/-- The function returns results r and r' on the two inputs respectively, and r = r'.
  Preconditions: Two inputs (n, languages, friendships) and (n, languages', friendships) both satisfy the problem constraints stated in spec_1. Define Lang(i) from languages and Lang'(i) from languages'. Assume for every i with 1 ≤ i ≤ m, Lang'(i) = Lang(i) as sets, so only the order of languages inside each user's list may differ. -/
theorem spec_10 (n : Std.I64) (languages languages' friendships : Slice (alloc.vec.Vec Std.I64))
    (h : Constraints n languages friendships) (h' : Constraints n languages' friendships)
    (hm : numUsers languages' = numUsers languages)
    (hLang : ∀ i, 1 ≤ i → i ≤ numUsers languages → Lang languages' i = Lang languages i) :
    ∃ r r' : Std.I64, minimum_teachings n languages friendships = ok r ∧
      minimum_teachings n languages' friendships = ok r' ∧ r.val = r'.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : Std.I64) (languages languages' friendships : Slice (alloc.vec.Vec Std.I64))
    (h : Constraints n languages friendships) (h' : Constraints n languages' friendships)
    (hm : numUsers languages' = numUsers languages)
    (hLang : ∀ i, 1 ≤ i → i ≤ numUsers languages → Lang languages' i = Lang languages i), ∃ r r' : Std.I64, minimum_teachings n languages friendships = ok r ∧
      minimum_teachings n languages' friendships = ok r' ∧ r.val = r'.val) := by
  sorry

/-- The function returns a result r, and r = 1 if and only if there exists L ∈ [1,n] such that exactly one user in B does not already know L, that is, |{ i ∈ B | L ∉ Lang(i) }| = 1.
  Preconditions: n, languages, friendships satisfy the problem constraints stated in spec_1. Define m, Lang(i), bad friendship, B, and need(L) as in spec_1, and assume B is nonempty. -/
theorem spec_11 (n : Std.I64) (languages friendships : Slice (alloc.vec.Vec Std.I64))
    (h : Constraints n languages friendships)
    (hnonempty : (BadUsers languages friendships).Nonempty) :
    ∃ r : Std.I64, minimum_teachings n languages friendships = ok r ∧
      (r.val = 1 ↔ ∃ L : ℤ, 1 ≤ L ∧ L ≤ n.val ∧
        needOf languages (BadUsers languages friendships) L = 1) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n : Std.I64) (languages friendships : Slice (alloc.vec.Vec Std.I64))
    (h : Constraints n languages friendships)
    (hnonempty : (BadUsers languages friendships).Nonempty), ∃ r : Std.I64, minimum_teachings n languages friendships = ok r ∧
      (r.val = 1 ↔ ∃ L : ℤ, 1 ≤ L ∧ L ≤ n.val ∧
        needOf languages (BadUsers languages friendships) L = 1)) := by
  sorry

/-- The function returns results r and r' on the two inputs respectively, and r' ≤ r.
  Preconditions: Let (n, languages, friendships) and (n, languages', friendships) both satisfy the problem constraints stated in spec_1 with the same n, m, and friendships. Define Lang(i) and Lang'(i) as in spec_1. Assume Lang(i) ⊆ Lang'(i) for every i with 1 ≤ i ≤ m; the second input may only add languages to users. -/
theorem spec_12 (n : Std.I64) (languages languages' friendships : Slice (alloc.vec.Vec Std.I64))
    (h : Constraints n languages friendships) (h' : Constraints n languages' friendships)
    (hm : numUsers languages' = numUsers languages)
    (hsub : ∀ i, 1 ≤ i → i ≤ numUsers languages → Lang languages i ⊆ Lang languages' i) :
    ∃ r r' : Std.I64, minimum_teachings n languages friendships = ok r ∧
      minimum_teachings n languages' friendships = ok r' ∧ r'.val ≤ r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n : Std.I64) (languages languages' friendships : Slice (alloc.vec.Vec Std.I64))
    (h : Constraints n languages friendships) (h' : Constraints n languages' friendships)
    (hm : numUsers languages' = numUsers languages)
    (hsub : ∀ i, 1 ≤ i → i ≤ numUsers languages → Lang languages i ⊆ Lang languages' i), ∃ r r' : Std.I64, minimum_teachings n languages friendships = ok r ∧
      minimum_teachings n languages' friendships = ok r' ∧ r'.val ≤ r.val) := by
  sorry

/-- The function returns a result r and there exists L* ∈ [1,n] such that r = |{ i ∈ B | L* ∉ Lang(i) }| and L* ∈ ⋃_{i ∈ B} Lang(i); in particular, an optimal language can be chosen among the languages already known by at least one user in B.
  Preconditions: n, languages, friendships satisfy the problem constraints stated in spec_1. Define m, Lang(i), bad friendship, B, and need(L) as in spec_1, and assume B is nonempty. -/
theorem spec_13 (n : Std.I64) (languages friendships : Slice (alloc.vec.Vec Std.I64))
    (h : Constraints n languages friendships)
    (hnonempty : (BadUsers languages friendships).Nonempty) :
    ∃ r : Std.I64, minimum_teachings n languages friendships = ok r ∧
      ∃ L : ℤ, 1 ≤ L ∧ L ≤ n.val ∧
        r.val = (needOf languages (BadUsers languages friendships) L : ℤ) ∧
        ∃ i ∈ BadUsers languages friendships, L ∈ Lang languages i := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (n : Std.I64) (languages friendships : Slice (alloc.vec.Vec Std.I64))
    (h : Constraints n languages friendships)
    (hnonempty : (BadUsers languages friendships).Nonempty), ∃ r : Std.I64, minimum_teachings n languages friendships = ok r ∧
      ∃ L : ℤ, 1 ≤ L ∧ L ≤ n.val ∧
        r.val = (needOf languages (BadUsers languages friendships) L : ℤ) ∧
        ∃ i ∈ BadUsers languages friendships, L ∈ Lang languages i) := by
  sorry

end AegisSpec.MinimumTeachings

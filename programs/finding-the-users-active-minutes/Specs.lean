import Aegis.FindingUsersActiveMinutes.Code.Funs

/-!
# Specifications of `Aegis.FindingUsersActiveMinutes.finding_users_active_minutes`

LeetCode problem `finding-the-users-active-minutes`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.FindingUsersActiveMinutes

def RVal (r : alloc.vec.Vec Std.I64) : List Int := r.val.map (fun x => x.val)

def entries (logs : Slice (alloc.vec.Vec Std.I64)) : List (Int × Int) :=
  logs.val.filterMap (fun e =>
    match e.val with
    | [u, t] => some (u.val, t.val)
    | _ => none)

def users (logs : Slice (alloc.vec.Vec Std.I64)) : List Int :=
  ((entries logs).map (fun p => p.1)).dedup

def times (logs : Slice (alloc.vec.Vec Std.I64)) (u : Int) : List Int :=
  (((entries logs).filter (fun p => decide (p.1 = u))).map (fun p => p.2)).dedup

def uam (logs : Slice (alloc.vec.Vec Std.I64)) (u : Int) : Nat :=
  (times logs u).length

def distinctUsers (logs : Slice (alloc.vec.Vec Std.I64)) : Nat :=
  (users logs).length

def maxUam (logs : Slice (alloc.vec.Vec Std.I64)) : Nat :=
  ((users logs).map (fun u => uam logs u)).foldr max 0

def countUam (logs : Slice (alloc.vec.Vec Std.I64)) (j : Nat) : Nat :=
  ((users logs).filter (fun u => decide (uam logs u = j))).length

def IsUser (logs : Slice (alloc.vec.Vec Std.I64)) (u : Int) : Prop :=
  ∃ t : Int, (u, t) ∈ entries logs

def posAt (r : alloc.vec.Vec Std.I64) (i : Nat) : Prop :=
  ∃ x : Int, (RVal r)[i]? = some x ∧ 0 < x

def greatestPosIndex (r : alloc.vec.Vec Std.I64) : Option Nat :=
  ((List.range (RVal r).length).filter (fun (i : Nat) =>
      match (RVal r)[i]? with
      | some x => decide (0 < x)
      | none => false)).reverse.head?

def LogsShape (logs : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  (∀ e ∈ logs.val, ∃ u t : Std.I64, e.val = [u, t] ∧
    0 ≤ u.val ∧ u.val ≤ 10 ^ 9 ∧ 1 ≤ t.val ∧ t.val ≤ 10 ^ 5) ∧
  logs.val.length ≤ 10 ^ 4

def LogsValid (logs : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  logs.val ≠ [] ∧ LogsShape logs

/-- The function returns a result r such that len(r) = k and, for every j with 1 <= j <= k, r[j-1] = |{ u in U | UAM(u) = j }|. Equivalently, r is the 0-indexed vector of length k whose entry at index j-1 is the number of users whose number of distinct action minutes is exactly j.
  Preconditions: logs is a nonempty slice of vectors; for every i with 0 <= i < len(logs), logs[i] has length 2, 0 <= logs[i][0] <= 10^9, and 1 <= logs[i][1] <= 10^5; len(logs) <= 10^4; U is the set of all IDs u such that [u,t] occurs as a log entry for some t; for u in U, T(u) is the set of all times t such that [u,t] occurs as a log entry, and UAM(u) = |T(u)|; D = |U|; M = max_{u in U} UAM(u); and k is an integer with M <= k <= 10^5. -/
theorem spec_1 (logs : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hlogs : LogsValid logs) (hkM : (maxUam logs : Int) ≤ k.val) (hk : k.val ≤ 10 ^ 5) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.FindingUsersActiveMinutes.finding_users_active_minutes logs k = ok r ∧
      (RVal r).length = k.val.toNat ∧
      (∀ j : Nat, 1 ≤ j → j ≤ k.val.toNat →
        (RVal r)[j - 1]? = some ((countUam logs j : Nat) : Int)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (logs : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hlogs : LogsValid logs) (hkM : (maxUam logs : Int) ≤ k.val) (hk : k.val ≤ 10 ^ 5), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.FindingUsersActiveMinutes.finding_users_active_minutes logs k = ok r ∧
      (RVal r).length = k.val.toNat ∧
      (∀ j : Nat, 1 ≤ j → j ≤ k.val.toNat →
        (RVal r)[j - 1]? = some ((countUam logs j : Nat) : Int))) := by
  sorry

/-- Under these preconditions, the function returns a result r; in particular it does not fail, panic, or overflow.
  Preconditions: logs is a nonempty slice of vectors; for every i with 0 <= i < len(logs), logs[i] has length 2, 0 <= logs[i][0] <= 10^9, and 1 <= logs[i][1] <= 10^5; len(logs) <= 10^4; U is the set of all IDs u such that [u,t] occurs as a log entry for some t; for u in U, T(u) is the set of all times t such that [u,t] occurs as a log entry, and UAM(u) = |T(u)|; D = |U|; M = max_{u in U} UAM(u); and k is an integer with M <= k <= 10^5. -/
theorem spec_2 (logs : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hlogs : LogsValid logs) (hkM : (maxUam logs : Int) ≤ k.val) (hk : k.val ≤ 10 ^ 5) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.FindingUsersActiveMinutes.finding_users_active_minutes logs k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (logs : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hlogs : LogsValid logs) (hkM : (maxUam logs : Int) ≤ k.val) (hk : k.val ≤ 10 ^ 5), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.FindingUsersActiveMinutes.finding_users_active_minutes logs k = ok r) := by
  sorry

/-- Under these preconditions, whenever the function returns a result r, len(r) = k.
  Preconditions: logs is a nonempty slice of vectors; for every i with 0 <= i < len(logs), logs[i] has length 2, 0 <= logs[i][0] <= 10^9, and 1 <= logs[i][1] <= 10^5; len(logs) <= 10^4; U is the set of all IDs u such that [u,t] occurs as a log entry for some t; for u in U, T(u) is the set of all times t such that [u,t] occurs as a log entry, and UAM(u) = |T(u)|; D = |U|; M = max_{u in U} UAM(u); and k is an integer with M <= k <= 10^5. -/
theorem spec_3 (logs : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hlogs : LogsValid logs) (hkM : (maxUam logs : Int) ≤ k.val) (hk : k.val ≤ 10 ^ 5) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.FindingUsersActiveMinutes.finding_users_active_minutes logs k = ok r →
      (RVal r).length = k.val.toNat := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (logs : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hlogs : LogsValid logs) (hkM : (maxUam logs : Int) ≤ k.val) (hk : k.val ≤ 10 ^ 5), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.FindingUsersActiveMinutes.finding_users_active_minutes logs k = ok r →
      (RVal r).length = k.val.toNat) := by
  sorry

/-- Under these preconditions, whenever the function returns a result r, for every i with 0 <= i < len(r), 0 <= r[i].
  Preconditions: logs is a nonempty slice of vectors; for every i with 0 <= i < len(logs), logs[i] has length 2, 0 <= logs[i][0] <= 10^9, and 1 <= logs[i][1] <= 10^5; len(logs) <= 10^4; U is the set of all IDs u such that [u,t] occurs as a log entry for some t; for u in U, T(u) is the set of all times t such that [u,t] occurs as a log entry, and UAM(u) = |T(u)|; D = |U|; M = max_{u in U} UAM(u); and k is an integer with M <= k <= 10^5. -/
theorem spec_4 (logs : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hlogs : LogsValid logs) (hkM : (maxUam logs : Int) ≤ k.val) (hk : k.val ≤ 10 ^ 5) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.FindingUsersActiveMinutes.finding_users_active_minutes logs k = ok r →
      ∀ (i : Nat) (hi : i < (RVal r).length), 0 ≤ (RVal r)[i] := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (logs : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hlogs : LogsValid logs) (hkM : (maxUam logs : Int) ≤ k.val) (hk : k.val ≤ 10 ^ 5), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.FindingUsersActiveMinutes.finding_users_active_minutes logs k = ok r →
      ∀ (i : Nat) (hi : i < (RVal r).length), 0 ≤ (RVal r)[i]) := by
  sorry

/-- Under these preconditions, whenever the function returns a result r, for every i with 0 <= i < len(r), r[i] <= D, where D = |U| is the number of distinct user IDs occurring in logs.
  Preconditions: logs is a nonempty slice of vectors; for every i with 0 <= i < len(logs), logs[i] has length 2, 0 <= logs[i][0] <= 10^9, and 1 <= logs[i][1] <= 10^5; len(logs) <= 10^4; U is the set of all IDs u such that [u,t] occurs as a log entry for some t; for u in U, T(u) is the set of all times t such that [u,t] occurs as a log entry, and UAM(u) = |T(u)|; D = |U|; M = max_{u in U} UAM(u); and k is an integer with M <= k <= 10^5. -/
theorem spec_5 (logs : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hlogs : LogsValid logs) (hkM : (maxUam logs : Int) ≤ k.val) (hk : k.val ≤ 10 ^ 5) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.FindingUsersActiveMinutes.finding_users_active_minutes logs k = ok r →
      ∀ (i : Nat) (hi : i < (RVal r).length),
        (RVal r)[i] ≤ (distinctUsers logs : Int) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (logs : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hlogs : LogsValid logs) (hkM : (maxUam logs : Int) ≤ k.val) (hk : k.val ≤ 10 ^ 5), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.FindingUsersActiveMinutes.finding_users_active_minutes logs k = ok r →
      ∀ (i : Nat) (hi : i < (RVal r).length),
        (RVal r)[i] ≤ (distinctUsers logs : Int)) := by
  sorry

/-- Under these preconditions, whenever the function returns a result r, the sum of all entries of r equals D: sum_{i=0}^{len(r)-1} r[i] = D, where D is the number of distinct user IDs occurring in logs.
  Preconditions: logs is a nonempty slice of vectors; for every i with 0 <= i < len(logs), logs[i] has length 2, 0 <= logs[i][0] <= 10^9, and 1 <= logs[i][1] <= 10^5; len(logs) <= 10^4; U is the set of all IDs u such that [u,t] occurs as a log entry for some t; for u in U, T(u) is the set of all times t such that [u,t] occurs as a log entry, and UAM(u) = |T(u)|; D = |U|; M = max_{u in U} UAM(u); and k is an integer with M <= k <= 10^5. -/
theorem spec_6 (logs : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hlogs : LogsValid logs) (hkM : (maxUam logs : Int) ≤ k.val) (hk : k.val ≤ 10 ^ 5) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.FindingUsersActiveMinutes.finding_users_active_minutes logs k = ok r →
      (RVal r).sum = (distinctUsers logs : Int) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (logs : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hlogs : LogsValid logs) (hkM : (maxUam logs : Int) ≤ k.val) (hk : k.val ≤ 10 ^ 5), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.FindingUsersActiveMinutes.finding_users_active_minutes logs k = ok r →
      (RVal r).sum = (distinctUsers logs : Int)) := by
  sorry

/-- Under these preconditions, whenever the function returns a result r, for every j with 1 <= j <= k, r[j-1] > 0 if and only if there exists a user u in U with UAM(u) = j.
  Preconditions: logs is a nonempty slice of vectors; for every i with 0 <= i < len(logs), logs[i] has length 2, 0 <= logs[i][0] <= 10^9, and 1 <= logs[i][1] <= 10^5; len(logs) <= 10^4; U is the set of all IDs u such that [u,t] occurs as a log entry for some t; for u in U, T(u) is the set of all times t such that [u,t] occurs as a log entry, and UAM(u) = |T(u)|; D = |U|; M = max_{u in U} UAM(u); and k is an integer with M <= k <= 10^5. -/
theorem spec_7 (logs : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hlogs : LogsValid logs) (hkM : (maxUam logs : Int) ≤ k.val) (hk : k.val ≤ 10 ^ 5) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.FindingUsersActiveMinutes.finding_users_active_minutes logs k = ok r →
      ∀ j : Nat, 1 ≤ j → j ≤ k.val.toNat →
        (posAt r (j - 1) ↔ ∃ u : Int, IsUser logs u ∧ uam logs u = j) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (logs : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hlogs : LogsValid logs) (hkM : (maxUam logs : Int) ≤ k.val) (hk : k.val ≤ 10 ^ 5), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.FindingUsersActiveMinutes.finding_users_active_minutes logs k = ok r →
      ∀ j : Nat, 1 ≤ j → j ≤ k.val.toNat →
        (posAt r (j - 1) ↔ ∃ u : Int, IsUser logs u ∧ uam logs u = j)) := by
  sorry

/-- Under these preconditions, whenever the function returns a result r, for every j with 1 <= j <= k, j * r[j-1] <= len(logs).
  Preconditions: logs is a nonempty slice of vectors; for every i with 0 <= i < len(logs), logs[i] has length 2, 0 <= logs[i][0] <= 10^9, and 1 <= logs[i][1] <= 10^5; len(logs) <= 10^4; U is the set of all IDs u such that [u,t] occurs as a log entry for some t; for u in U, T(u) is the set of all times t such that [u,t] occurs as a log entry, and UAM(u) = |T(u)|; D = |U|; M = max_{u in U} UAM(u); and k is an integer with M <= k <= 10^5. -/
theorem spec_8 (logs : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hlogs : LogsValid logs) (hkM : (maxUam logs : Int) ≤ k.val) (hk : k.val ≤ 10 ^ 5) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.FindingUsersActiveMinutes.finding_users_active_minutes logs k = ok r →
      ∀ j : Nat, 1 ≤ j → j ≤ k.val.toNat → ∀ x : Int,
        (RVal r)[j - 1]? = some x → (j : Int) * x ≤ (logs.val.length : Int) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (logs : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hlogs : LogsValid logs) (hkM : (maxUam logs : Int) ≤ k.val) (hk : k.val ≤ 10 ^ 5), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.FindingUsersActiveMinutes.finding_users_active_minutes logs k = ok r →
      ∀ j : Nat, 1 ≤ j → j ≤ k.val.toNat → ∀ x : Int,
        (RVal r)[j - 1]? = some x → (j : Int) * x ≤ (logs.val.length : Int)) := by
  sorry

/-- Under these preconditions, whenever the function returns a result r, the greatest index i with 0 <= i < len(r) and r[i] > 0 is exactly M - 1; consequently r[M-1] > 0 and r[i] = 0 for every i with M <= i < len(r).
  Preconditions: logs is a nonempty slice of vectors; for every i with 0 <= i < len(logs), logs[i] has length 2, 0 <= logs[i][0] <= 10^9, and 1 <= logs[i][1] <= 10^5; len(logs) <= 10^4; U is the set of all IDs u such that [u,t] occurs as a log entry for some t; for u in U, T(u) is the set of all times t such that [u,t] occurs as a log entry, and UAM(u) = |T(u)|; D = |U|; M = max_{u in U} UAM(u); and k is an integer with M <= k <= 10^5. -/
theorem spec_9 (logs : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hlogs : LogsValid logs) (hkM : (maxUam logs : Int) ≤ k.val) (hk : k.val ≤ 10 ^ 5) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.FindingUsersActiveMinutes.finding_users_active_minutes logs k = ok r →
      greatestPosIndex r = some (maxUam logs - 1) ∧
        posAt r (maxUam logs - 1) ∧
        (∀ (i : Nat), maxUam logs ≤ i → ∀ (hi : i < (RVal r).length),
          (RVal r)[i] = 0) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (logs : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hlogs : LogsValid logs) (hkM : (maxUam logs : Int) ≤ k.val) (hk : k.val ≤ 10 ^ 5), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.FindingUsersActiveMinutes.finding_users_active_minutes logs k = ok r →
      greatestPosIndex r = some (maxUam logs - 1) ∧
        posAt r (maxUam logs - 1) ∧
        (∀ (i : Nat), maxUam logs ≤ i → ∀ (hi : i < (RVal r).length),
          (RVal r)[i] = 0)) := by
  sorry

/-- Under these preconditions, if the function returns r on logs and r' on logs' with the same k, then r = r'.
  Preconditions: logs is a nonempty slice of vectors; for every i with 0 <= i < len(logs), logs[i] has length 2, 0 <= logs[i][0] <= 10^9, and 1 <= logs[i][1] <= 10^5; len(logs) <= 10^4; U is the set of all IDs u such that [u,t] occurs as a log entry for some t; for u in U, T(u) is the set of all times t such that [u,t] occurs as a log entry, and UAM(u) = |T(u)|; D = |U|; M = max_{u in U} UAM(u); and k is an integer with M <= k <= 10^5. Additionally, logs' is a slice of vectors obtained by permuting the entries of logs, so it has the same length and the same multiset of [ID,time] pairs as logs. -/
theorem spec_10 (logs logs' : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hlogs : LogsValid logs) (hlogs' : LogsShape logs')
    (hperm : (entries logs).Perm (entries logs'))
    (hkM : (maxUam logs : Int) ≤ k.val) (hk : k.val ≤ 10 ^ 5) :
    ∀ r r' : alloc.vec.Vec Std.I64,
      Aegis.FindingUsersActiveMinutes.finding_users_active_minutes logs k = ok r →
      Aegis.FindingUsersActiveMinutes.finding_users_active_minutes logs' k = ok r' →
      r = r' := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (logs logs' : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hlogs : LogsValid logs) (hlogs' : LogsShape logs')
    (hperm : (entries logs).Perm (entries logs'))
    (hkM : (maxUam logs : Int) ≤ k.val) (hk : k.val ≤ 10 ^ 5), ∀ r r' : alloc.vec.Vec Std.I64,
      Aegis.FindingUsersActiveMinutes.finding_users_active_minutes logs k = ok r →
      Aegis.FindingUsersActiveMinutes.finding_users_active_minutes logs' k = ok r' →
      r = r') := by
  sorry

/-- Under these preconditions, if the function returns r on logs with k and returns r' on logs' with the same k, then r = r'.
  Preconditions: logs is a nonempty slice of vectors; for every i with 0 <= i < len(logs), logs[i] has length 2, 0 <= logs[i][0] <= 10^9, and 1 <= logs[i][1] <= 10^5; len(logs) <= 10^4; U is the set of all IDs u such that [u,t] occurs as a log entry for some t; for u in U, T(u) is the set of all times t such that [u,t] occurs as a log entry, and UAM(u) = |T(u)|; D = |U|; M = max_{u in U} UAM(u); and k is an integer with M <= k <= 10^5. Additionally, logs' is any slice such that the set of distinct entries [u,t] occurring in logs' equals the set of distinct entries occurring in logs; every entry of logs' has length 2 with 0 <= u <= 10^9 and 1 <= t <= 10^5; len(logs') <= 10^4; the maximum UAM for logs' is at most k; and the function is evaluated on logs' with the same k. -/
theorem spec_11 (logs logs' : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hlogs : LogsValid logs) (hlogs' : LogsShape logs')
    (hset : ∀ p : Int × Int, p ∈ entries logs' ↔ p ∈ entries logs)
    (hkM : (maxUam logs : Int) ≤ k.val)
    (hkM' : (maxUam logs' : Int) ≤ k.val) (hk : k.val ≤ 10 ^ 5) :
    ∀ r r' : alloc.vec.Vec Std.I64,
      Aegis.FindingUsersActiveMinutes.finding_users_active_minutes logs k = ok r →
      Aegis.FindingUsersActiveMinutes.finding_users_active_minutes logs' k = ok r' →
      r = r' := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (logs logs' : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hlogs : LogsValid logs) (hlogs' : LogsShape logs')
    (hset : ∀ p : Int × Int, p ∈ entries logs' ↔ p ∈ entries logs)
    (hkM : (maxUam logs : Int) ≤ k.val)
    (hkM' : (maxUam logs' : Int) ≤ k.val) (hk : k.val ≤ 10 ^ 5), ∀ r r' : alloc.vec.Vec Std.I64,
      Aegis.FindingUsersActiveMinutes.finding_users_active_minutes logs k = ok r →
      Aegis.FindingUsersActiveMinutes.finding_users_active_minutes logs' k = ok r' →
      r = r') := by
  sorry

end AegisSpec.FindingUsersActiveMinutes

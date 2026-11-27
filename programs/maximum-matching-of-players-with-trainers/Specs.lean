import Aegis.MatchPlayersAndTrainers.Code.Funs

/-!
# Specifications of `Aegis.MatchPlayersAndTrainers.match_players_and_trainers`

LeetCode problem `maximum-matching-of-players-with-trainers`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MatchPlayersAndTrainers

  def vals (s : Slice I64) : List ℤ := s.val.map (fun x => x.val)

  def listMax? : List ℤ → Option ℤ
    | [] => none
    | x :: xs => some (xs.foldl max x)

  def listMin? : List ℤ → Option ℤ
    | [] => none
    | x :: xs => some (xs.foldl min x)

  def IsValidMatching (P T : List I64) (M : Finset (Fin P.length × Fin T.length)) : Prop :=
    (∀ p ∈ M, (P.get p.1).val ≤ (T.get p.2).val) ∧
      (∀ p ∈ M, ∀ q ∈ M, p.1 = q.1 → p = q) ∧
        ∀ p ∈ M, ∀ q ∈ M, p.2 = q.2 → p = q

  def IsMaximumMatching (P T : List I64) (M : Finset (Fin P.length × Fin T.length)) : Prop :=
    IsValidMatching P T M ∧
      ∀ M' : Finset (Fin P.length × Fin T.length), IsValidMatching P T M' → M'.card ≤ M.card

  def IsSortedValues (s : Slice I64) (A : List ℤ) : Prop :=
    A.Pairwise (· ≤ ·) ∧ A.Perm (vals s)

  def PrefixLeSuffix (A B : List ℤ) (k : Nat) : Prop :=
    List.Forall₂ (· ≤ ·) (A.take k) (B.drop (B.length - k))

  /-- The function returns a result r, and r is the maximum cardinality of a valid matching M, where a valid matching is a set of pairs (i,j) such that 0 <= i < len(players), 0 <= j < len(trainers), players[i] <= trainers[j], no two pairs in M have the same first component, and no two pairs in M have the same second component. Thus r = max { |M| : M is a valid matching }.
    Preconditions: 1 <= len(players), len(trainers) <= 100000; for every i with 0 <= i < len(players), 1 <= players[i] <= 1000000000; for every j with 0 <= j < len(trainers), 1 <= trainers[j] <= 1000000000. -/
  theorem spec_1 (players trainers : Slice I64)
      (hPne : 1 ≤ players.val.length) (hTne : 1 ≤ trainers.val.length)
      (hPlen : players.val.length ≤ 100000) (hTlen : trainers.val.length ≤ 100000)
      (hPbound : ∀ i : Fin players.val.length, 1 ≤ (players.val.get i).val ∧ (players.val.get i).val ≤ 1000000000)
      (hTbound : ∀ j : Fin trainers.val.length, 1 ≤ (trainers.val.get j).val ∧ (trainers.val.get j).val ≤ 1000000000) :
      ∃ r, Aegis.MatchPlayersAndTrainers.match_players_and_trainers players trainers = ok r ∧
        ∃ M : Finset (Fin players.val.length × Fin trainers.val.length),
          IsMaximumMatching players.val trainers.val M ∧ (M.card : ℤ) = r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (players trainers : Slice I64)
        (hPne : 1 ≤ players.val.length) (hTne : 1 ≤ trainers.val.length)
        (hPlen : players.val.length ≤ 100000) (hTlen : trainers.val.length ≤ 100000)
        (hPbound : ∀ i : Fin players.val.length, 1 ≤ (players.val.get i).val ∧ (players.val.get i).val ≤ 1000000000)
        (hTbound : ∀ j : Fin trainers.val.length, 1 ≤ (trainers.val.get j).val ∧ (trainers.val.get j).val ≤ 1000000000), ∃ r, Aegis.MatchPlayersAndTrainers.match_players_and_trainers players trainers = ok r ∧
          ∃ M : Finset (Fin players.val.length × Fin trainers.val.length),
            IsMaximumMatching players.val trainers.val M ∧ (M.card : ℤ) = r.val) := by
    sorry

  /-- The function returns a result r and 0 <= r <= min(len(players), len(trainers)).
    Preconditions: 1 <= len(players), len(trainers) <= 100000; for every i with 0 <= i < len(players), 1 <= players[i] <= 1000000000; for every j with 0 <= j < len(trainers), 1 <= trainers[j] <= 1000000000. -/
  theorem spec_2 (players trainers : Slice I64)
      (hPne : 1 ≤ players.val.length) (hTne : 1 ≤ trainers.val.length)
      (hPlen : players.val.length ≤ 100000) (hTlen : trainers.val.length ≤ 100000)
      (hPbound : ∀ i : Fin players.val.length, 1 ≤ (players.val.get i).val ∧ (players.val.get i).val ≤ 1000000000)
      (hTbound : ∀ j : Fin trainers.val.length, 1 ≤ (trainers.val.get j).val ∧ (trainers.val.get j).val ≤ 1000000000) :
      ∃ r, Aegis.MatchPlayersAndTrainers.match_players_and_trainers players trainers = ok r ∧
        0 ≤ r.val ∧ r.val ≤ ((min players.val.length trainers.val.length : Nat) : ℤ) := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (players trainers : Slice I64)
        (hPne : 1 ≤ players.val.length) (hTne : 1 ≤ trainers.val.length)
        (hPlen : players.val.length ≤ 100000) (hTlen : trainers.val.length ≤ 100000)
        (hPbound : ∀ i : Fin players.val.length, 1 ≤ (players.val.get i).val ∧ (players.val.get i).val ≤ 1000000000)
        (hTbound : ∀ j : Fin trainers.val.length, 1 ≤ (trainers.val.get j).val ∧ (trainers.val.get j).val ≤ 1000000000), ∃ r, Aegis.MatchPlayersAndTrainers.match_players_and_trainers players trainers = ok r ∧
          0 ≤ r.val ∧ r.val ≤ ((min players.val.length trainers.val.length : Nat) : ℤ)) := by
    sorry

  /-- The function returns a result r; in particular, on every input satisfying the constraints it does not fail (no overflow, panic, or out-of-bounds failure).
    Preconditions: 1 <= len(players), len(trainers) <= 100000; for every i with 0 <= i < len(players), 1 <= players[i] <= 1000000000; for every j with 0 <= j < len(trainers), 1 <= trainers[j] <= 1000000000. -/
  theorem spec_3 (players trainers : Slice I64)
      (hPne : 1 ≤ players.val.length) (hTne : 1 ≤ trainers.val.length)
      (hPlen : players.val.length ≤ 100000) (hTlen : trainers.val.length ≤ 100000)
      (hPbound : ∀ i : Fin players.val.length, 1 ≤ (players.val.get i).val ∧ (players.val.get i).val ≤ 1000000000)
      (hTbound : ∀ j : Fin trainers.val.length, 1 ≤ (trainers.val.get j).val ∧ (trainers.val.get j).val ≤ 1000000000) :
      ∃ r, Aegis.MatchPlayersAndTrainers.match_players_and_trainers players trainers = ok r := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (players trainers : Slice I64)
        (hPne : 1 ≤ players.val.length) (hTne : 1 ≤ trainers.val.length)
        (hPlen : players.val.length ≤ 100000) (hTlen : trainers.val.length ≤ 100000)
        (hPbound : ∀ i : Fin players.val.length, 1 ≤ (players.val.get i).val ∧ (players.val.get i).val ≤ 1000000000)
        (hTbound : ∀ j : Fin trainers.val.length, 1 ≤ (trainers.val.get j).val ∧ (trainers.val.get j).val ≤ 1000000000), ∃ r, Aegis.MatchPlayersAndTrainers.match_players_and_trainers players trainers = ok r) := by
    sorry

  /-- Whenever the function returns a result r, there exist r distinct indices i_1,...,i_r with 0 <= i_k < len(players) and r distinct indices j_1,...,j_r with 0 <= j_k < len(trainers) such that players[i_k] <= trainers[j_k] for every k with 1 <= k <= r. For r = 0 this is the empty choice.
    Preconditions: 1 <= len(players), len(trainers) <= 100000; for every i with 0 <= i < len(players), 1 <= players[i] <= 1000000000; for every j with 0 <= j < len(trainers), 1 <= trainers[j] <= 1000000000. -/
  theorem spec_4 (players trainers : Slice I64)
      (hPne : 1 ≤ players.val.length) (hTne : 1 ≤ trainers.val.length)
      (hPlen : players.val.length ≤ 100000) (hTlen : trainers.val.length ≤ 100000)
      (hPbound : ∀ i : Fin players.val.length, 1 ≤ (players.val.get i).val ∧ (players.val.get i).val ≤ 1000000000)
      (hTbound : ∀ j : Fin trainers.val.length, 1 ≤ (trainers.val.get j).val ∧ (trainers.val.get j).val ≤ 1000000000) :
      ∀ r, Aegis.MatchPlayersAndTrainers.match_players_and_trainers players trainers = ok r →
        ∃ M : Finset (Fin players.val.length × Fin trainers.val.length),
          IsValidMatching players.val trainers.val M ∧ (M.card : ℤ) = r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (players trainers : Slice I64)
        (hPne : 1 ≤ players.val.length) (hTne : 1 ≤ trainers.val.length)
        (hPlen : players.val.length ≤ 100000) (hTlen : trainers.val.length ≤ 100000)
        (hPbound : ∀ i : Fin players.val.length, 1 ≤ (players.val.get i).val ∧ (players.val.get i).val ≤ 1000000000)
        (hTbound : ∀ j : Fin trainers.val.length, 1 ≤ (trainers.val.get j).val ∧ (trainers.val.get j).val ≤ 1000000000), ∀ r, Aegis.MatchPlayersAndTrainers.match_players_and_trainers players trainers = ok r →
          ∃ M : Finset (Fin players.val.length × Fin trainers.val.length),
            IsValidMatching players.val trainers.val M ∧ (M.card : ℤ) = r.val) := by
    sorry

  /-- Whenever the function returns a result r, there is no valid matching M, where a valid matching is a set of pairs (i,j) with 0 <= i < len(players), 0 <= j < len(trainers), players[i] <= trainers[j], and no two pairs sharing a first or second component, such that |M| > r.
    Preconditions: 1 <= len(players), len(trainers) <= 100000; for every i with 0 <= i < len(players), 1 <= players[i] <= 1000000000; for every j with 0 <= j < len(trainers), 1 <= trainers[j] <= 1000000000. -/
  theorem spec_5 (players trainers : Slice I64)
      (hPne : 1 ≤ players.val.length) (hTne : 1 ≤ trainers.val.length)
      (hPlen : players.val.length ≤ 100000) (hTlen : trainers.val.length ≤ 100000)
      (hPbound : ∀ i : Fin players.val.length, 1 ≤ (players.val.get i).val ∧ (players.val.get i).val ≤ 1000000000)
      (hTbound : ∀ j : Fin trainers.val.length, 1 ≤ (trainers.val.get j).val ∧ (trainers.val.get j).val ≤ 1000000000) :
      ∀ r, Aegis.MatchPlayersAndTrainers.match_players_and_trainers players trainers = ok r →
        ∀ M : Finset (Fin players.val.length × Fin trainers.val.length),
          IsValidMatching players.val trainers.val M → (M.card : ℤ) ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (players trainers : Slice I64)
        (hPne : 1 ≤ players.val.length) (hTne : 1 ≤ trainers.val.length)
        (hPlen : players.val.length ≤ 100000) (hTlen : trainers.val.length ≤ 100000)
        (hPbound : ∀ i : Fin players.val.length, 1 ≤ (players.val.get i).val ∧ (players.val.get i).val ≤ 1000000000)
        (hTbound : ∀ j : Fin trainers.val.length, 1 ≤ (trainers.val.get j).val ∧ (trainers.val.get j).val ≤ 1000000000), ∀ r, Aegis.MatchPlayersAndTrainers.match_players_and_trainers players trainers = ok r →
          ∀ M : Finset (Fin players.val.length × Fin trainers.val.length),
            IsValidMatching players.val trainers.val M → (M.card : ℤ) ≤ r.val) := by
    sorry

  /-- The function returns a result r, and r = 0 if and only if players[i] > trainers[j] for every i with 0 <= i < len(players) and every j with 0 <= j < len(trainers).
    Preconditions: 1 <= len(players), len(trainers) <= 100000; for every i with 0 <= i < len(players), 1 <= players[i] <= 1000000000; for every j with 0 <= j < len(trainers), 1 <= trainers[j] <= 1000000000. -/
  theorem spec_6 (players trainers : Slice I64)
      (hPne : 1 ≤ players.val.length) (hTne : 1 ≤ trainers.val.length)
      (hPlen : players.val.length ≤ 100000) (hTlen : trainers.val.length ≤ 100000)
      (hPbound : ∀ i : Fin players.val.length, 1 ≤ (players.val.get i).val ∧ (players.val.get i).val ≤ 1000000000)
      (hTbound : ∀ j : Fin trainers.val.length, 1 ≤ (trainers.val.get j).val ∧ (trainers.val.get j).val ≤ 1000000000) :
      ∃ r, Aegis.MatchPlayersAndTrainers.match_players_and_trainers players trainers = ok r ∧
        (r.val = 0 ↔
          ∀ i : Fin players.val.length, ∀ j : Fin trainers.val.length,
            (players.val.get i).val > (trainers.val.get j).val) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (players trainers : Slice I64)
        (hPne : 1 ≤ players.val.length) (hTne : 1 ≤ trainers.val.length)
        (hPlen : players.val.length ≤ 100000) (hTlen : trainers.val.length ≤ 100000)
        (hPbound : ∀ i : Fin players.val.length, 1 ≤ (players.val.get i).val ∧ (players.val.get i).val ≤ 1000000000)
        (hTbound : ∀ j : Fin trainers.val.length, 1 ≤ (trainers.val.get j).val ∧ (trainers.val.get j).val ≤ 1000000000), ∃ r, Aegis.MatchPlayersAndTrainers.match_players_and_trainers players trainers = ok r ∧
          (r.val = 0 ↔
            ∀ i : Fin players.val.length, ∀ j : Fin trainers.val.length,
              (players.val.get i).val > (trainers.val.get j).val)) := by
    sorry

  /-- The function returns a result r and r = min(len(players), len(trainers)).
    Preconditions: 1 <= len(players), len(trainers) <= 100000; for every i with 0 <= i < len(players), 1 <= players[i] <= 1000000000; for every j with 0 <= j < len(trainers), 1 <= trainers[j] <= 1000000000; max_{0 <= i < len(players)} players[i] <= min_{0 <= j < len(trainers)} trainers[j]. -/
  theorem spec_7 (players trainers : Slice I64)
      (hPne : 1 ≤ players.val.length) (hTne : 1 ≤ trainers.val.length)
      (hPlen : players.val.length ≤ 100000) (hTlen : trainers.val.length ≤ 100000)
      (hPbound : ∀ i : Fin players.val.length, 1 ≤ (players.val.get i).val ∧ (players.val.get i).val ≤ 1000000000)
      (hTbound : ∀ j : Fin trainers.val.length, 1 ≤ (trainers.val.get j).val ∧ (trainers.val.get j).val ≤ 1000000000)
      (hmaxmin : ∃ a b, listMax? (vals players) = some a ∧ listMin? (vals trainers) = some b ∧ a ≤ b) :
      ∃ r, Aegis.MatchPlayersAndTrainers.match_players_and_trainers players trainers = ok r ∧
        r.val = ((min players.val.length trainers.val.length : Nat) : ℤ) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (players trainers : Slice I64)
        (hPne : 1 ≤ players.val.length) (hTne : 1 ≤ trainers.val.length)
        (hPlen : players.val.length ≤ 100000) (hTlen : trainers.val.length ≤ 100000)
        (hPbound : ∀ i : Fin players.val.length, 1 ≤ (players.val.get i).val ∧ (players.val.get i).val ≤ 1000000000)
        (hTbound : ∀ j : Fin trainers.val.length, 1 ≤ (trainers.val.get j).val ∧ (trainers.val.get j).val ≤ 1000000000)
        (hmaxmin : ∃ a b, listMax? (vals players) = some a ∧ listMin? (vals trainers) = some b ∧ a ≤ b), ∃ r, Aegis.MatchPlayersAndTrainers.match_players_and_trainers players trainers = ok r ∧
          r.val = ((min players.val.length trainers.val.length : Nat) : ℤ)) := by
    sorry

  /-- Whenever the function returns r on (players, trainers) and r' on (P', T'), we have r = r'.
    Preconditions: 1 <= len(players), len(trainers) <= 100000; for every i with 0 <= i < len(players), 1 <= players[i] <= 1000000000; for every j with 0 <= j < len(trainers), 1 <= trainers[j] <= 1000000000. P' is any reordering of players (same multiset of values) and T' is any reordering of trainers (same multiset of values). -/
  theorem spec_8 (players trainers players' trainers' : Slice I64)
      (hPne : 1 ≤ players.val.length) (hTne : 1 ≤ trainers.val.length)
      (hPlen : players.val.length ≤ 100000) (hTlen : trainers.val.length ≤ 100000)
      (hPbound : ∀ i : Fin players.val.length, 1 ≤ (players.val.get i).val ∧ (players.val.get i).val ≤ 1000000000)
      (hTbound : ∀ j : Fin trainers.val.length, 1 ≤ (trainers.val.get j).val ∧ (trainers.val.get j).val ≤ 1000000000)
      (hPperm : players'.val.Perm players.val) (hTperm : trainers'.val.Perm trainers.val) :
      ∀ r r', Aegis.MatchPlayersAndTrainers.match_players_and_trainers players trainers = ok r →
        Aegis.MatchPlayersAndTrainers.match_players_and_trainers players' trainers' = ok r' →
          r = r' := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (players trainers players' trainers' : Slice I64)
        (hPne : 1 ≤ players.val.length) (hTne : 1 ≤ trainers.val.length)
        (hPlen : players.val.length ≤ 100000) (hTlen : trainers.val.length ≤ 100000)
        (hPbound : ∀ i : Fin players.val.length, 1 ≤ (players.val.get i).val ∧ (players.val.get i).val ≤ 1000000000)
        (hTbound : ∀ j : Fin trainers.val.length, 1 ≤ (trainers.val.get j).val ∧ (trainers.val.get j).val ≤ 1000000000)
        (hPperm : players'.val.Perm players.val) (hTperm : trainers'.val.Perm trainers.val), ∀ r r', Aegis.MatchPlayersAndTrainers.match_players_and_trainers players trainers = ok r →
          Aegis.MatchPlayersAndTrainers.match_players_and_trainers players' trainers' = ok r' →
            r = r') := by
    sorry

  /-- Whenever the function returns r on (players, trainers) and r' on (players, trainers'), we have r' >= r.
    Preconditions: 1 <= len(players), len(trainers) <= 100000; for every i with 0 <= i < len(players), 1 <= players[i] <= 1000000000; for every j with 0 <= j < len(trainers), 1 <= trainers[j] <= 1000000000. For some j with 0 <= j < len(trainers), trainers' is an array of the same length as trainers such that trainers'[k] = trainers[k] for every k != j and trainers[j] <= trainers'[j] <= 1000000000. -/
  theorem spec_9 (players trainers trainers' : Slice I64)
      (hPne : 1 ≤ players.val.length) (hTne : 1 ≤ trainers.val.length)
      (hPlen : players.val.length ≤ 100000) (hTlen : trainers.val.length ≤ 100000)
      (hPbound : ∀ i : Fin players.val.length, 1 ≤ (players.val.get i).val ∧ (players.val.get i).val ≤ 1000000000)
      (hTbound : ∀ j : Fin trainers.val.length, 1 ≤ (trainers.val.get j).val ∧ (trainers.val.get j).val ≤ 1000000000)
      (j : Nat) (hj : j < trainers.val.length) (hj' : j < trainers'.val.length)
      (hlen : trainers'.val.length = trainers.val.length)
      (hagree : ∀ (k : Nat) (hk : k < trainers.val.length) (hk' : k < trainers'.val.length),
        k ≠ j → trainers'.val.get ⟨k, hk'⟩ = trainers.val.get ⟨k, hk⟩)
      (hmono : (trainers.val.get ⟨j, hj⟩).val ≤ (trainers'.val.get ⟨j, hj'⟩).val ∧
        (trainers'.val.get ⟨j, hj'⟩).val ≤ 1000000000) :
      ∀ r r', Aegis.MatchPlayersAndTrainers.match_players_and_trainers players trainers = ok r →
        Aegis.MatchPlayersAndTrainers.match_players_and_trainers players trainers' = ok r' →
          r.val ≤ r'.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (players trainers trainers' : Slice I64)
        (hPne : 1 ≤ players.val.length) (hTne : 1 ≤ trainers.val.length)
        (hPlen : players.val.length ≤ 100000) (hTlen : trainers.val.length ≤ 100000)
        (hPbound : ∀ i : Fin players.val.length, 1 ≤ (players.val.get i).val ∧ (players.val.get i).val ≤ 1000000000)
        (hTbound : ∀ j : Fin trainers.val.length, 1 ≤ (trainers.val.get j).val ∧ (trainers.val.get j).val ≤ 1000000000)
        (j : Nat) (hj : j < trainers.val.length) (hj' : j < trainers'.val.length)
        (hlen : trainers'.val.length = trainers.val.length)
        (hagree : ∀ (k : Nat) (hk : k < trainers.val.length) (hk' : k < trainers'.val.length),
          k ≠ j → trainers'.val.get ⟨k, hk'⟩ = trainers.val.get ⟨k, hk⟩)
        (hmono : (trainers.val.get ⟨j, hj⟩).val ≤ (trainers'.val.get ⟨j, hj'⟩).val ∧
          (trainers'.val.get ⟨j, hj'⟩).val ≤ 1000000000), ∀ r r', Aegis.MatchPlayersAndTrainers.match_players_and_trainers players trainers = ok r →
          Aegis.MatchPlayersAndTrainers.match_players_and_trainers players trainers' = ok r' →
            r.val ≤ r'.val) := by
    sorry

  /-- Whenever the function returns r on (players, trainers) and r' on (players', trainers), we have r' <= r.
    Preconditions: 1 <= len(players), len(trainers) <= 100000; for every i with 0 <= i < len(players), 1 <= players[i] <= 1000000000; for every j with 0 <= j < len(trainers), 1 <= trainers[j] <= 1000000000. For some i with 0 <= i < len(players), players' is an array of the same length as players such that players'[k] = players[k] for every k != i and players[i] <= players'[i] <= 1000000000. -/
  theorem spec_10 (players players' trainers : Slice I64)
      (hPne : 1 ≤ players.val.length) (hTne : 1 ≤ trainers.val.length)
      (hPlen : players.val.length ≤ 100000) (hTlen : trainers.val.length ≤ 100000)
      (hPbound : ∀ i : Fin players.val.length, 1 ≤ (players.val.get i).val ∧ (players.val.get i).val ≤ 1000000000)
      (hTbound : ∀ j : Fin trainers.val.length, 1 ≤ (trainers.val.get j).val ∧ (trainers.val.get j).val ≤ 1000000000)
      (i : Nat) (hi : i < players.val.length) (hi' : i < players'.val.length)
      (hlen : players'.val.length = players.val.length)
      (hagree : ∀ (k : Nat) (hk : k < players.val.length) (hk' : k < players'.val.length),
        k ≠ i → players'.val.get ⟨k, hk'⟩ = players.val.get ⟨k, hk⟩)
      (hmono : (players.val.get ⟨i, hi⟩).val ≤ (players'.val.get ⟨i, hi'⟩).val ∧
        (players'.val.get ⟨i, hi'⟩).val ≤ 1000000000) :
      ∀ r r', Aegis.MatchPlayersAndTrainers.match_players_and_trainers players trainers = ok r →
        Aegis.MatchPlayersAndTrainers.match_players_and_trainers players' trainers = ok r' →
          r'.val ≤ r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (players players' trainers : Slice I64)
        (hPne : 1 ≤ players.val.length) (hTne : 1 ≤ trainers.val.length)
        (hPlen : players.val.length ≤ 100000) (hTlen : trainers.val.length ≤ 100000)
        (hPbound : ∀ i : Fin players.val.length, 1 ≤ (players.val.get i).val ∧ (players.val.get i).val ≤ 1000000000)
        (hTbound : ∀ j : Fin trainers.val.length, 1 ≤ (trainers.val.get j).val ∧ (trainers.val.get j).val ≤ 1000000000)
        (i : Nat) (hi : i < players.val.length) (hi' : i < players'.val.length)
        (hlen : players'.val.length = players.val.length)
        (hagree : ∀ (k : Nat) (hk : k < players.val.length) (hk' : k < players'.val.length),
          k ≠ i → players'.val.get ⟨k, hk'⟩ = players.val.get ⟨k, hk⟩)
        (hmono : (players.val.get ⟨i, hi⟩).val ≤ (players'.val.get ⟨i, hi'⟩).val ∧
          (players'.val.get ⟨i, hi'⟩).val ≤ 1000000000), ∀ r r', Aegis.MatchPlayersAndTrainers.match_players_and_trainers players trainers = ok r →
          Aegis.MatchPlayersAndTrainers.match_players_and_trainers players' trainers = ok r' →
            r'.val ≤ r.val) := by
    sorry

  /-- Whenever the function returns r on (players, trainers) and r' on (players, trainers'), we have r = r'.
    Preconditions: 1 <= len(players), len(trainers) <= 100000; for every i with 0 <= i < len(players), 1 <= players[i] <= 1000000000; for every j with 0 <= j < len(trainers), 1 <= trainers[j] <= 1000000000; len(trainers) >= 2; for some j with 0 <= j < len(trainers), trainers[j] < min_{0 <= i < len(players)} players[i]. Let trainers' be trainers with the entry at index j removed. -/
  theorem spec_11 (players trainers trainers' : Slice I64)
      (hPne : 1 ≤ players.val.length) (hTne : 1 ≤ trainers.val.length)
      (hPlen : players.val.length ≤ 100000) (hTlen : trainers.val.length ≤ 100000)
      (hPbound : ∀ i : Fin players.val.length, 1 ≤ (players.val.get i).val ∧ (players.val.get i).val ≤ 1000000000)
      (hTbound : ∀ j : Fin trainers.val.length, 1 ≤ (trainers.val.get j).val ∧ (trainers.val.get j).val ≤ 1000000000)
      (hTtwo : 2 ≤ trainers.val.length)
      (j : Nat) (hj : j < trainers.val.length)
      (hsmall : ∃ mn, listMin? (vals players) = some mn ∧ (trainers.val.get ⟨j, hj⟩).val < mn)
      (hdel : trainers'.val = trainers.val.eraseIdx j) :
      ∀ r r', Aegis.MatchPlayersAndTrainers.match_players_and_trainers players trainers = ok r →
        Aegis.MatchPlayersAndTrainers.match_players_and_trainers players trainers' = ok r' →
          r = r' := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (players trainers trainers' : Slice I64)
        (hPne : 1 ≤ players.val.length) (hTne : 1 ≤ trainers.val.length)
        (hPlen : players.val.length ≤ 100000) (hTlen : trainers.val.length ≤ 100000)
        (hPbound : ∀ i : Fin players.val.length, 1 ≤ (players.val.get i).val ∧ (players.val.get i).val ≤ 1000000000)
        (hTbound : ∀ j : Fin trainers.val.length, 1 ≤ (trainers.val.get j).val ∧ (trainers.val.get j).val ≤ 1000000000)
        (hTtwo : 2 ≤ trainers.val.length)
        (j : Nat) (hj : j < trainers.val.length)
        (hsmall : ∃ mn, listMin? (vals players) = some mn ∧ (trainers.val.get ⟨j, hj⟩).val < mn)
        (hdel : trainers'.val = trainers.val.eraseIdx j), ∀ r r', Aegis.MatchPlayersAndTrainers.match_players_and_trainers players trainers = ok r →
          Aegis.MatchPlayersAndTrainers.match_players_and_trainers players trainers' = ok r' →
            r = r') := by
    sorry

  /-- Whenever the function returns r on (players, trainers) and r' on (players', trainers), we have r = r'.
    Preconditions: 1 <= len(players), len(trainers) <= 100000; for every i with 0 <= i < len(players), 1 <= players[i] <= 1000000000; for every j with 0 <= j < len(trainers), 1 <= trainers[j] <= 1000000000; len(players) >= 2; for some i with 0 <= i < len(players), players[i] > max_{0 <= j < len(trainers)} trainers[j]. Let players' be players with the entry at index i removed. -/
  theorem spec_12 (players players' trainers : Slice I64)
      (hPne : 1 ≤ players.val.length) (hTne : 1 ≤ trainers.val.length)
      (hPlen : players.val.length ≤ 100000) (hTlen : trainers.val.length ≤ 100000)
      (hPbound : ∀ i : Fin players.val.length, 1 ≤ (players.val.get i).val ∧ (players.val.get i).val ≤ 1000000000)
      (hTbound : ∀ j : Fin trainers.val.length, 1 ≤ (trainers.val.get j).val ∧ (trainers.val.get j).val ≤ 1000000000)
      (hPtwo : 2 ≤ players.val.length)
      (i : Nat) (hi : i < players.val.length)
      (hlarge : ∃ mx, listMax? (vals trainers) = some mx ∧ mx < (players.val.get ⟨i, hi⟩).val)
      (hdel : players'.val = players.val.eraseIdx i) :
      ∀ r r', Aegis.MatchPlayersAndTrainers.match_players_and_trainers players trainers = ok r →
        Aegis.MatchPlayersAndTrainers.match_players_and_trainers players' trainers = ok r' →
          r = r' := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (players players' trainers : Slice I64)
        (hPne : 1 ≤ players.val.length) (hTne : 1 ≤ trainers.val.length)
        (hPlen : players.val.length ≤ 100000) (hTlen : trainers.val.length ≤ 100000)
        (hPbound : ∀ i : Fin players.val.length, 1 ≤ (players.val.get i).val ∧ (players.val.get i).val ≤ 1000000000)
        (hTbound : ∀ j : Fin trainers.val.length, 1 ≤ (trainers.val.get j).val ∧ (trainers.val.get j).val ≤ 1000000000)
        (hPtwo : 2 ≤ players.val.length)
        (i : Nat) (hi : i < players.val.length)
        (hlarge : ∃ mx, listMax? (vals trainers) = some mx ∧ mx < (players.val.get ⟨i, hi⟩).val)
        (hdel : players'.val = players.val.eraseIdx i), ∀ r r', Aegis.MatchPlayersAndTrainers.match_players_and_trainers players trainers = ok r →
          Aegis.MatchPlayersAndTrainers.match_players_and_trainers players' trainers = ok r' →
            r = r') := by
    sorry

  /-- Let A_1 <= A_2 <= ... <= A_n be the entries of players sorted into nondecreasing order, where n = len(players), and let B_1 <= B_2 <= ... <= B_m be the entries of trainers sorted into nondecreasing order, where m = len(trainers). The function returns a result r, and r is the largest integer k with 0 <= k <= min(n,m) such that for every q with 1 <= q <= k, A_q <= B_{m-k+q}.
    Preconditions: 1 <= len(players), len(trainers) <= 100000; for every i with 0 <= i < len(players), 1 <= players[i] <= 1000000000; for every j with 0 <= j < len(trainers), 1 <= trainers[j] <= 1000000000. -/
  theorem spec_13 (players trainers : Slice I64)
      (hPne : 1 ≤ players.val.length) (hTne : 1 ≤ trainers.val.length)
      (hPlen : players.val.length ≤ 100000) (hTlen : trainers.val.length ≤ 100000)
      (hPbound : ∀ i : Fin players.val.length, 1 ≤ (players.val.get i).val ∧ (players.val.get i).val ≤ 1000000000)
      (hTbound : ∀ j : Fin trainers.val.length, 1 ≤ (trainers.val.get j).val ∧ (trainers.val.get j).val ≤ 1000000000)
      (A B : List ℤ)
      (hA : IsSortedValues players A) (hB : IsSortedValues trainers B) :
      ∃ r k, Aegis.MatchPlayersAndTrainers.match_players_and_trainers players trainers = ok r ∧
        k ≤ min players.val.length trainers.val.length ∧ r.val = (k : ℤ) ∧
          PrefixLeSuffix A B k ∧
            ∀ k', k' ≤ min players.val.length trainers.val.length → PrefixLeSuffix A B k' → k' ≤ k := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (players trainers : Slice I64)
        (hPne : 1 ≤ players.val.length) (hTne : 1 ≤ trainers.val.length)
        (hPlen : players.val.length ≤ 100000) (hTlen : trainers.val.length ≤ 100000)
        (hPbound : ∀ i : Fin players.val.length, 1 ≤ (players.val.get i).val ∧ (players.val.get i).val ≤ 1000000000)
        (hTbound : ∀ j : Fin trainers.val.length, 1 ≤ (trainers.val.get j).val ∧ (trainers.val.get j).val ≤ 1000000000)
        (A B : List ℤ)
        (hA : IsSortedValues players A) (hB : IsSortedValues trainers B), ∃ r k, Aegis.MatchPlayersAndTrainers.match_players_and_trainers players trainers = ok r ∧
          k ≤ min players.val.length trainers.val.length ∧ r.val = (k : ℤ) ∧
            PrefixLeSuffix A B k ∧
              ∀ k', k' ≤ min players.val.length trainers.val.length → PrefixLeSuffix A B k' → k' ≤ k) := by
    sorry

  /-- The function returns a result r and r = min(len(players), c), where c is the number of indices j with 0 <= j < len(trainers) and trainers[j] >= a.
    Preconditions: 1 <= len(players), len(trainers) <= 100000; for every i with 0 <= i < len(players), 1 <= players[i] <= 1000000000; for every j with 0 <= j < len(trainers), 1 <= trainers[j] <= 1000000000; there is a value a such that players[i] = a for every i with 0 <= i < len(players). -/
  theorem spec_14 (players trainers : Slice I64)
      (hPne : 1 ≤ players.val.length) (hTne : 1 ≤ trainers.val.length)
      (hPlen : players.val.length ≤ 100000) (hTlen : trainers.val.length ≤ 100000)
      (hPbound : ∀ i : Fin players.val.length, 1 ≤ (players.val.get i).val ∧ (players.val.get i).val ≤ 1000000000)
      (hTbound : ∀ j : Fin trainers.val.length, 1 ≤ (trainers.val.get j).val ∧ (trainers.val.get j).val ≤ 1000000000)
      (a : ℤ) (hconst : ∀ i : Fin players.val.length, (players.val.get i).val = a) :
      ∃ r, Aegis.MatchPlayersAndTrainers.match_players_and_trainers players trainers = ok r ∧
        r.val = ((min players.val.length
          ((Finset.univ : Finset (Fin trainers.val.length)).filter
            (fun j => a ≤ (trainers.val.get j).val)).card : Nat) : ℤ) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (players trainers : Slice I64)
        (hPne : 1 ≤ players.val.length) (hTne : 1 ≤ trainers.val.length)
        (hPlen : players.val.length ≤ 100000) (hTlen : trainers.val.length ≤ 100000)
        (hPbound : ∀ i : Fin players.val.length, 1 ≤ (players.val.get i).val ∧ (players.val.get i).val ≤ 1000000000)
        (hTbound : ∀ j : Fin trainers.val.length, 1 ≤ (trainers.val.get j).val ∧ (trainers.val.get j).val ≤ 1000000000)
        (a : ℤ) (hconst : ∀ i : Fin players.val.length, (players.val.get i).val = a), ∃ r, Aegis.MatchPlayersAndTrainers.match_players_and_trainers players trainers = ok r ∧
          r.val = ((min players.val.length
            ((Finset.univ : Finset (Fin trainers.val.length)).filter
              (fun j => a ≤ (trainers.val.get j).val)).card : Nat) : ℤ)) := by
    sorry

  /-- The function returns a result r and r = min(len(trainers), c), where c is the number of indices i with 0 <= i < len(players) and players[i] <= b.
    Preconditions: 1 <= len(players), len(trainers) <= 100000; for every i with 0 <= i < len(players), 1 <= players[i] <= 1000000000; for every j with 0 <= j < len(trainers), 1 <= trainers[j] <= 1000000000; there is a value b such that trainers[j] = b for every j with 0 <= j < len(trainers). -/
  theorem spec_15 (players trainers : Slice I64)
      (hPne : 1 ≤ players.val.length) (hTne : 1 ≤ trainers.val.length)
      (hPlen : players.val.length ≤ 100000) (hTlen : trainers.val.length ≤ 100000)
      (hPbound : ∀ i : Fin players.val.length, 1 ≤ (players.val.get i).val ∧ (players.val.get i).val ≤ 1000000000)
      (hTbound : ∀ j : Fin trainers.val.length, 1 ≤ (trainers.val.get j).val ∧ (trainers.val.get j).val ≤ 1000000000)
      (b : ℤ) (hconst : ∀ j : Fin trainers.val.length, (trainers.val.get j).val = b) :
      ∃ r, Aegis.MatchPlayersAndTrainers.match_players_and_trainers players trainers = ok r ∧
        r.val = ((min trainers.val.length
          ((Finset.univ : Finset (Fin players.val.length)).filter
            (fun i => (players.val.get i).val ≤ b)).card : Nat) : ℤ) := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (players trainers : Slice I64)
        (hPne : 1 ≤ players.val.length) (hTne : 1 ≤ trainers.val.length)
        (hPlen : players.val.length ≤ 100000) (hTlen : trainers.val.length ≤ 100000)
        (hPbound : ∀ i : Fin players.val.length, 1 ≤ (players.val.get i).val ∧ (players.val.get i).val ≤ 1000000000)
        (hTbound : ∀ j : Fin trainers.val.length, 1 ≤ (trainers.val.get j).val ∧ (trainers.val.get j).val ≤ 1000000000)
        (b : ℤ) (hconst : ∀ j : Fin trainers.val.length, (trainers.val.get j).val = b), ∃ r, Aegis.MatchPlayersAndTrainers.match_players_and_trainers players trainers = ok r ∧
          r.val = ((min trainers.val.length
            ((Finset.univ : Finset (Fin players.val.length)).filter
              (fun i => (players.val.get i).val ≤ b)).card : Nat) : ℤ)) := by
    sorry

  end AegisSpec.MatchPlayersAndTrainers

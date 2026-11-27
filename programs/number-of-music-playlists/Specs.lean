import Aegis.NumMusicPlaylists.Code.Funs

/-!
# Specifications of `Aegis.NumMusicPlaylists.num_music_playlists`

LeetCode problem `number-of-music-playlists`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.NumMusicPlaylists

  open Aegis.NumMusicPlaylists (num_music_playlists)

  def M : Int := 1000000007

  def valNat (x : Std.I64) : Nat := x.val.toNat

  abbrev Playlist (n goal : Nat) : Type := Fin goal → Fin n

  def IsPlaylist (n goal k : Nat) (p : Playlist n goal) : Prop :=
    (∀ s : Fin n, ∃ i : Fin goal, p i = s) ∧
      ∀ i j : Fin goal, i < j → p i = p j → k < (j : Nat) - (i : Nat)

  noncomputable def playlistCount (n goal k : Nat) : Nat :=
    Nat.card { p : Playlist n goal // IsPlaylist n goal k p }

  noncomputable def surjectiveCount (n goal : Nat) : Nat :=
    Nat.card { p : Playlist n goal // ∀ s : Fin n, ∃ i : Fin goal, p i = s }

  noncomputable def validPairCount (n k : Nat) : Nat :=
    Nat.card { x : Fin (n + 1) × Fin (n + 1) //
      x.1 < x.2 ∧ k < (x.2 : Nat) - (x.1 : Nat) }

  def inclExcl (n goal : Nat) : Int :=
    ∑ j ∈ Finset.range (n + 1),
      (-1 : Int) ^ j * (Nat.choose n j : Int) * ((n - j : Nat) : Int) ^ goal

  def inclExclSucc (n goal : Nat) : Int :=
    ∑ j ∈ Finset.range (n + 1),
      (-1 : Int) ^ j * (Nat.choose n j : Int) * ((n - j : Nat) : Int) *
        (((n - j - 1 : Nat)) : Int) ^ (goal - 1)

  def WitnessSeq (n goal : Nat) (p : Playlist n goal) : Prop :=
    ∃ hn : 0 < n, p = fun i => ⟨(i : Nat) % n, Nat.mod_lt _ hn⟩

  /-- Let M = 1000000007. Let P be the set of all sequences p = (p_0, ..., p_{goal-1}) with p_i in {1, ..., n} for each 0 <= i < goal, such that (1) for every song s in {1, ..., n} there exists an index i with 0 <= i < goal and p_i = s, and (2) for every pair of indices i, j with 0 <= i < j < goal and p_i = p_j, we have j - i > k. Then the function returns a result r and r = |P| mod M, where |P| mod M is the unique integer in [0, M-1] congruent to |P| modulo M.
    Preconditions: n, goal, and k are integers satisfying 0 <= k < n <= goal <= 100. Thus n >= 1 and goal >= 1. -/
  theorem spec_1 (n goal k : Std.I64)
      (hk0 : 0 ≤ k.val) (hkn : k.val < n.val) (hng : n.val ≤ goal.val)
      (hg : goal.val ≤ 100) :
      ∃ r : Std.I64,
        num_music_playlists n goal k = ok r ∧
          r.val =
            (playlistCount (valNat n) (valNat goal) (valNat k) : Int) % M := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n goal k : Std.I64)
        (hk0 : 0 ≤ k.val) (hkn : k.val < n.val) (hng : n.val ≤ goal.val)
        (hg : goal.val ≤ 100), ∃ r : Std.I64,
          num_music_playlists n goal k = ok r ∧
            r.val =
              (playlistCount (valNat n) (valNat goal) (valNat k) : Int) % M) := by
    sorry

  /-- For every n, goal, and k satisfying the preconditions, the function returns a result r; it does not fail, panic, or hit an integer overflow.
    Preconditions: n, goal, and k are integers satisfying 0 <= k < n <= goal <= 100. -/
  theorem spec_2 (n goal k : Std.I64)
      (hk0 : 0 ≤ k.val) (hkn : k.val < n.val) (hng : n.val ≤ goal.val)
      (hg : goal.val ≤ 100) :
      ∃ r : Std.I64, num_music_playlists n goal k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n goal k : Std.I64)
        (hk0 : 0 ≤ k.val) (hkn : k.val < n.val) (hng : n.val ≤ goal.val)
        (hg : goal.val ≤ 100), ∃ r : Std.I64, num_music_playlists n goal k = ok r) := by
    sorry

  /-- Whenever the function returns a result r for an input satisfying the preconditions, 0 <= r < M, where M = 1000000007.
    Preconditions: n, goal, and k are integers satisfying 0 <= k < n <= goal <= 100. -/
  theorem spec_3 (n goal k : Std.I64)
      (hk0 : 0 ≤ k.val) (hkn : k.val < n.val) (hng : n.val ≤ goal.val)
      (hg : goal.val ≤ 100) :
      ∀ r : Std.I64, num_music_playlists n goal k = ok r → 0 ≤ r.val ∧ r.val < M := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n goal k : Std.I64)
        (hk0 : 0 ≤ k.val) (hkn : k.val < n.val) (hng : n.val ≤ goal.val)
        (hg : goal.val ≤ 100), ∀ r : Std.I64, num_music_playlists n goal k = ok r → 0 ≤ r.val ∧ r.val < M) := by
    sorry

  /-- If n = goal, then the function returns a result r and r = n! mod M, where M = 1000000007 and n! = 1 * 2 * ... * n (so 1! = 1).
    Preconditions: n, goal, and k satisfy 0 <= k < n <= goal <= 100 and n = goal. -/
  theorem spec_4 (n goal k : Std.I64)
      (hk0 : 0 ≤ k.val) (hkn : k.val < n.val) (hng : n.val ≤ goal.val)
      (hg : goal.val ≤ 100) (hng_eq : n = goal) :
      ∃ r : Std.I64,
        num_music_playlists n goal k = ok r ∧
          r.val = (Nat.factorial (valNat n) : Int) % M := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n goal k : Std.I64)
        (hk0 : 0 ≤ k.val) (hkn : k.val < n.val) (hng : n.val ≤ goal.val)
        (hg : goal.val ≤ 100) (hng_eq : n = goal), ∃ r : Std.I64,
          num_music_playlists n goal k = ok r ∧
            r.val = (Nat.factorial (valNat n) : Int) % M) := by
    sorry

  /-- If k = 0, then the function returns a result r and r = T mod M, where M = 1000000007 and T is the number of sequences of length goal over the n song labels in which every one of the n labels occurs at least once. Equivalently, r is the least nonnegative residue modulo M of sum_{j=0}^{n} (-1)^j * C(n,j) * (n-j)^goal, where C(n,j) is the binomial coefficient.
    Preconditions: n, goal, and k satisfy 0 <= k < n <= goal <= 100 and k = 0. -/
  theorem spec_5 (n goal k : Std.I64)
      (hk0 : 0 ≤ k.val) (hkn : k.val < n.val) (hng : n.val ≤ goal.val)
      (hg : goal.val ≤ 100) (hk : k.val = 0) :
      ∃ r : Std.I64,
        num_music_playlists n goal k = ok r ∧
          r.val = (surjectiveCount (valNat n) (valNat goal) : Int) % M ∧
          r.val = inclExcl (valNat n) (valNat goal) % M := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n goal k : Std.I64)
        (hk0 : 0 ≤ k.val) (hkn : k.val < n.val) (hng : n.val ≤ goal.val)
        (hg : goal.val ≤ 100) (hk : k.val = 0), ∃ r : Std.I64,
          num_music_playlists n goal k = ok r ∧
            r.val = (surjectiveCount (valNat n) (valNat goal) : Int) % M ∧
            r.val = inclExcl (valNat n) (valNat goal) % M) := by
    sorry

  /-- If k = n - 1, then for every valid goal the function returns a result r and r = n! mod M, where M = 1000000007 and n! = 1 * 2 * ... * n.
    Preconditions: n, goal, and k satisfy 0 <= k < n <= goal <= 100 and k = n - 1. -/
  theorem spec_6 (n goal k : Std.I64)
      (hk0 : 0 ≤ k.val) (hkn : k.val < n.val) (hng : n.val ≤ goal.val)
      (hg : goal.val ≤ 100) (hk : k.val = n.val - 1) :
      ∃ r : Std.I64,
        num_music_playlists n goal k = ok r ∧
          r.val = (Nat.factorial (valNat n) : Int) % M := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n goal k : Std.I64)
        (hk0 : 0 ≤ k.val) (hkn : k.val < n.val) (hng : n.val ≤ goal.val)
        (hg : goal.val ≤ 100) (hk : k.val = n.val - 1), ∃ r : Std.I64,
          num_music_playlists n goal k = ok r ∧
            r.val = (Nat.factorial (valNat n) : Int) % M) := by
    sorry

  /-- If k = 1, then the function returns a result r and r is the least nonnegative residue modulo M = 1000000007 of sum_{j=0}^{n} (-1)^j * C(n,j) * (n-j) * (n-j-1)^{goal-1}, where C(n,j) is the binomial coefficient and the usual integer exponent convention applies (the term is zero whenever n-j = 0, and also whenever n-j = 1 because the exponent goal-1 is positive).
    Preconditions: n, goal, and k satisfy 0 <= k < n <= goal <= 100 and k = 1. Thus n >= 2 and goal >= 2, so goal - 1 >= 1. -/
  theorem spec_7 (n goal k : Std.I64)
      (hk0 : 0 ≤ k.val) (hkn : k.val < n.val) (hng : n.val ≤ goal.val)
      (hg : goal.val ≤ 100) (hk : k.val = 1) :
      ∃ r : Std.I64,
        num_music_playlists n goal k = ok r ∧
          r.val = inclExclSucc (valNat n) (valNat goal) % M := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n goal k : Std.I64)
        (hk0 : 0 ≤ k.val) (hkn : k.val < n.val) (hng : n.val ≤ goal.val)
        (hg : goal.val ≤ 100) (hk : k.val = 1), ∃ r : Std.I64,
          num_music_playlists n goal k = ok r ∧
            r.val = inclExclSucc (valNat n) (valNat goal) % M) := by
    sorry

  /-- If goal = n + 1, then the function returns a result r and r = (n! * P) mod M, where M = 1000000007, n! = 1 * 2 * ... * n, and P is the number of pairs of indices (i,j) with 0 <= i < j <= n and j - i > k.
    Preconditions: n, goal, and k satisfy 0 <= k < n <= goal <= 100 and goal = n + 1. -/
  theorem spec_8 (n goal k : Std.I64)
      (hk0 : 0 ≤ k.val) (hkn : k.val < n.val) (hng : n.val ≤ goal.val)
      (hg : goal.val ≤ 100) (hgoal : goal.val = n.val + 1) :
      ∃ r : Std.I64,
        num_music_playlists n goal k = ok r ∧
          r.val =
            ((Nat.factorial (valNat n) * validPairCount (valNat n) (valNat k) : Nat) : Int) %
              M := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n goal k : Std.I64)
        (hk0 : 0 ≤ k.val) (hkn : k.val < n.val) (hng : n.val ≤ goal.val)
        (hg : goal.val ≤ 100) (hgoal : goal.val = n.val + 1), ∃ r : Std.I64,
          num_music_playlists n goal k = ok r ∧
            r.val =
              ((Nat.factorial (valNat n) * validPairCount (valNat n) (valNat k) : Nat) : Int) %
                M) := by
    sorry

  /-- For every input satisfying the preconditions, the set P of valid playlists defined in S1 is nonempty; for example, the sequence p_i = 1 + (i mod n) for i = 0, ..., goal-1 is valid. Consequently, the exact number T = |P| is a positive integer, and whenever the function returns a result r, r = T mod M with M = 1000000007.
    Preconditions: n, goal, and k are integers satisfying 0 <= k < n <= goal <= 100. -/
  theorem spec_9 (n goal k : Std.I64)
      (hk0 : 0 ≤ k.val) (hkn : k.val < n.val) (hng : n.val ≤ goal.val)
      (hg : goal.val ≤ 100) :
      (∃ p : Playlist (valNat n) (valNat goal),
          WitnessSeq (valNat n) (valNat goal) p ∧
            IsPlaylist (valNat n) (valNat goal) (valNat k) p) ∧
        0 < playlistCount (valNat n) (valNat goal) (valNat k) ∧
          ∀ r : Std.I64,
            num_music_playlists n goal k = ok r →
              r.val =
                (playlistCount (valNat n) (valNat goal) (valNat k) : Int) % M := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n goal k : Std.I64)
        (hk0 : 0 ≤ k.val) (hkn : k.val < n.val) (hng : n.val ≤ goal.val)
        (hg : goal.val ≤ 100), (∃ p : Playlist (valNat n) (valNat goal),
            WitnessSeq (valNat n) (valNat goal) p ∧
              IsPlaylist (valNat n) (valNat goal) (valNat k) p) ∧
          0 < playlistCount (valNat n) (valNat goal) (valNat k) ∧
            ∀ r : Std.I64,
              num_music_playlists n goal k = ok r →
                r.val =
                  (playlistCount (valNat n) (valNat goal) (valNat k) : Int) % M) := by
    sorry

  /-- Let P1 be the set of valid playlists for (n, goal, k1) and P2 the set for (n, goal, k2), using the definition in spec_1. Then P2 is a subset of P1, so |P1| >= |P2|. If the function returns r1 on (n, goal, k1) and r2 on (n, goal, k2), then r1 = |P1| mod M and r2 = |P2| mod M, with M = 1000000007 and both residues in [0, M-1].
    Preconditions: n, goal, k1, and k2 are integers satisfying 0 <= k1 <= k2 < n <= goal <= 100. Each of the two calls (n, goal, k1) and (n, goal, k2) satisfies the original constraints. -/
  theorem spec_10 (n goal k1 k2 : Std.I64)
      (h10 : 0 ≤ k1.val) (h12 : k1.val ≤ k2.val) (h2n : k2.val < n.val)
      (hng : n.val ≤ goal.val) (hg : goal.val ≤ 100) :
      (∀ p : Playlist (valNat n) (valNat goal),
          IsPlaylist (valNat n) (valNat goal) (valNat k2) p →
            IsPlaylist (valNat n) (valNat goal) (valNat k1) p) ∧
        playlistCount (valNat n) (valNat goal) (valNat k1) ≥
          playlistCount (valNat n) (valNat goal) (valNat k2) ∧
          ∀ r1 r2 : Std.I64,
            num_music_playlists n goal k1 = ok r1 →
              num_music_playlists n goal k2 = ok r2 →
                0 ≤ r1.val ∧ r1.val < M ∧
                  r1.val =
                    (playlistCount (valNat n) (valNat goal) (valNat k1) : Int) % M ∧
                    0 ≤ r2.val ∧ r2.val < M ∧
                      r2.val =
                        (playlistCount (valNat n) (valNat goal) (valNat k2) : Int) %
                          M := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n goal k1 k2 : Std.I64)
        (h10 : 0 ≤ k1.val) (h12 : k1.val ≤ k2.val) (h2n : k2.val < n.val)
        (hng : n.val ≤ goal.val) (hg : goal.val ≤ 100), (∀ p : Playlist (valNat n) (valNat goal),
            IsPlaylist (valNat n) (valNat goal) (valNat k2) p →
              IsPlaylist (valNat n) (valNat goal) (valNat k1) p) ∧
          playlistCount (valNat n) (valNat goal) (valNat k1) ≥
            playlistCount (valNat n) (valNat goal) (valNat k2) ∧
            ∀ r1 r2 : Std.I64,
              num_music_playlists n goal k1 = ok r1 →
                num_music_playlists n goal k2 = ok r2 →
                  0 ≤ r1.val ∧ r1.val < M ∧
                    r1.val =
                      (playlistCount (valNat n) (valNat goal) (valNat k1) : Int) % M ∧
                      0 ≤ r2.val ∧ r2.val < M ∧
                        r2.val =
                          (playlistCount (valNat n) (valNat goal) (valNat k2) : Int) %
                            M) := by
    sorry

  end AegisSpec.NumMusicPlaylists

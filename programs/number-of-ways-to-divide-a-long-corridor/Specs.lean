import Aegis.NumberOfWays.Code.Funs

/-!
# Specifications of `Aegis.NumberOfWays.number_of_ways`

LeetCode problem `number-of-ways-to-divide-a-long-corridor`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aeneas.Std.Result

  namespace AegisSpec.NumberOfWays

  abbrev Byte : Type := Aeneas.Std.U8

  abbrev Corridor : Type := Aeneas.Std.Slice Aeneas.Std.U8

  abbrev I64 : Type := Aeneas.Std.I64

  def MOD : ℤ := 1000000007

  def P_BYTE : Byte := 80#u8

  def S_BYTE : Byte := 83#u8

  def bytes (corridor : Corridor) : List ℕ := corridor.val.map (fun b => b.val)

  def AllPOrS (corridor : Corridor) : Prop :=
    ∀ b ∈ corridor.val, b.val = 80 ∨ b.val = 83

  def seatPositions (corridor : Corridor) : List ℕ :=
    (corridor.val.zipIdx).filterMap (fun (b, i) => if b.val = 83 then some i else none)

  def seatCount (corridor : Corridor) : ℕ := (seatPositions corridor).length

  def countSeatsIn (corridor : Corridor) (a b : ℕ) : ℕ :=
    ((seatPositions corridor).filter (fun i => decide (a ≤ i ∧ i < b))).length

  def pairGap (p : List ℕ) (j : ℕ) : ℤ := (p.getD (2 * j) 0 : ℤ) - (p.getD (2 * j - 1) 0 : ℤ)

  def pairGaps (p : List ℕ) : List ℤ :=
    (List.range (p.length / 2 - 1)).map (fun i => pairGap p (i + 1))

  def waysProduct (p : List ℕ) : ℤ := (pairGaps p).prod

  def modInv (d : ℤ) : ℤ := (d ^ 1000000005) % MOD

  def cutPoints (D : List ℕ) (n : ℕ) : List ℕ := 0 :: (D ++ [n])

  def SegmentsHaveTwoSeats (corridor : Corridor) (cuts : List ℕ) : Prop :=
    ∀ a b : ℕ, (a, b) ∈ cuts.zip cuts.tail → countSeatsIn corridor a b = 2

  def trimP (l : List ℕ) : List ℕ := (l.dropWhile (· = 80)).reverse.dropWhile (· = 80) |>.reverse

  def trimmedBytes (corridor : Corridor) : List ℕ := trimP (bytes corridor)

  /-- The function returns a result r and does not fail. Let m be the number of indices i with 0 <= i < len(corridor) and corridor[i] = 83, and let p_0 < p_1 < ... < p_{m-1} be those indices in increasing order. Let MOD = 1000000007. If m = 0 or m is odd, then r = 0. If m is even and m >= 2, then r is the unique integer with 0 <= r < MOD and r is congruent modulo MOD to the product over j = 1 to m/2 - 1 of (p_{2j} - p_{2j-1}); the empty product, when m = 2, is 1.
    Preconditions: The input is a valid corridor: 1 <= len(corridor) <= 100000, and for every i with 0 <= i < len(corridor), corridor[i] = 80 ('P') or corridor[i] = 83 ('S'). -/
  theorem spec_1 (corridor : Corridor)
      (hlen : 1 ≤ corridor.val.length) (hlen_max : corridor.val.length ≤ 100000)
      (hbytes : AllPOrS corridor) :
      ∃ r : I64,
        Aegis.NumberOfWays.number_of_ways corridor = ok r ∧
        ((seatCount corridor = 0 ∨ Odd (seatCount corridor)) → r.val = 0) ∧
        (Even (seatCount corridor) → 2 ≤ seatCount corridor →
          0 ≤ r.val ∧ r.val < MOD ∧
            Int.ModEq MOD r.val (waysProduct (seatPositions corridor))) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (corridor : Corridor)
        (hlen : 1 ≤ corridor.val.length) (hlen_max : corridor.val.length ≤ 100000)
        (hbytes : AllPOrS corridor), ∃ r : I64,
          Aegis.NumberOfWays.number_of_ways corridor = ok r ∧
          ((seatCount corridor = 0 ∨ Odd (seatCount corridor)) → r.val = 0) ∧
          (Even (seatCount corridor) → 2 ≤ seatCount corridor →
            0 ≤ r.val ∧ r.val < MOD ∧
              Int.ModEq MOD r.val (waysProduct (seatPositions corridor)))) := by
    sorry

  /-- The function returns a result r for every input satisfying the preconditions; it does not fail by arithmetic overflow, panic, or out-of-bounds access.
    Preconditions: The input is a valid corridor: 1 <= len(corridor) <= 100000, and for every i with 0 <= i < len(corridor), corridor[i] = 80 ('P') or corridor[i] = 83 ('S'). -/
  theorem spec_2 (corridor : Corridor)
      (hlen : 1 ≤ corridor.val.length) (hlen_max : corridor.val.length ≤ 100000)
      (hbytes : AllPOrS corridor) :
      ∃ r : I64, Aegis.NumberOfWays.number_of_ways corridor = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (corridor : Corridor)
        (hlen : 1 ≤ corridor.val.length) (hlen_max : corridor.val.length ≤ 100000)
        (hbytes : AllPOrS corridor), ∃ r : I64, Aegis.NumberOfWays.number_of_ways corridor = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r < 1000000007.
    Preconditions: The input is a valid corridor: 1 <= len(corridor) <= 100000, and for every i with 0 <= i < len(corridor), corridor[i] = 80 ('P') or corridor[i] = 83 ('S'). -/
  theorem spec_3 (corridor : Corridor)
      (hlen : 1 ≤ corridor.val.length) (hlen_max : corridor.val.length ≤ 100000)
      (hbytes : AllPOrS corridor) :
      ∀ r : I64, Aegis.NumberOfWays.number_of_ways corridor = ok r → 0 ≤ r.val ∧ r.val < MOD := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (corridor : Corridor)
        (hlen : 1 ≤ corridor.val.length) (hlen_max : corridor.val.length ≤ 100000)
        (hbytes : AllPOrS corridor), ∀ r : I64, Aegis.NumberOfWays.number_of_ways corridor = ok r → 0 ≤ r.val ∧ r.val < MOD) := by
    sorry

  /-- The function returns a result r and r = 0.
    Preconditions: The input is a valid corridor: 1 <= len(corridor) <= 100000, every corridor[i] is 80 ('P') or 83 ('S'), and the number m of indices i with corridor[i] = 83 is odd. -/
  theorem spec_4 (corridor : Corridor)
      (hlen : 1 ≤ corridor.val.length) (hlen_max : corridor.val.length ≤ 100000)
      (hbytes : AllPOrS corridor) (hodd : Odd (seatCount corridor)) :
      ∃ r : I64, Aegis.NumberOfWays.number_of_ways corridor = ok r ∧ r.val = 0 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (corridor : Corridor)
        (hlen : 1 ≤ corridor.val.length) (hlen_max : corridor.val.length ≤ 100000)
        (hbytes : AllPOrS corridor) (hodd : Odd (seatCount corridor)), ∃ r : I64, Aegis.NumberOfWays.number_of_ways corridor = ok r ∧ r.val = 0) := by
    sorry

  /-- The function returns a result r and r >= 1.
    Preconditions: The input is a valid corridor: 1 <= len(corridor) <= 100000, every corridor[i] is 80 ('P') or 83 ('S'), and the number m of indices i with corridor[i] = 83 is positive and even. -/
  theorem spec_5 (corridor : Corridor)
      (hlen : 1 ≤ corridor.val.length) (hlen_max : corridor.val.length ≤ 100000)
      (hbytes : AllPOrS corridor)
      (hpos : 0 < seatCount corridor) (heven : Even (seatCount corridor)) :
      ∃ r : I64, Aegis.NumberOfWays.number_of_ways corridor = ok r ∧ 1 ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (corridor : Corridor)
        (hlen : 1 ≤ corridor.val.length) (hlen_max : corridor.val.length ≤ 100000)
        (hbytes : AllPOrS corridor)
        (hpos : 0 < seatCount corridor) (heven : Even (seatCount corridor)), ∃ r : I64, Aegis.NumberOfWays.number_of_ways corridor = ok r ∧ 1 ≤ r.val) := by
    sorry

  /-- The function returns a result r and r = 1.
    Preconditions: The input is a valid corridor: 1 <= len(corridor) <= 100000, every corridor[i] is 80 ('P') or 83 ('S'), and the number m of indices i with corridor[i] = 83 is exactly 2. -/
  theorem spec_6 (corridor : Corridor)
      (hlen : 1 ≤ corridor.val.length) (hlen_max : corridor.val.length ≤ 100000)
      (hbytes : AllPOrS corridor) (htwo : seatCount corridor = 2) :
      ∃ r : I64, Aegis.NumberOfWays.number_of_ways corridor = ok r ∧ r.val = 1 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (corridor : Corridor)
        (hlen : 1 ≤ corridor.val.length) (hlen_max : corridor.val.length ≤ 100000)
        (hbytes : AllPOrS corridor) (htwo : seatCount corridor = 2), ∃ r : I64, Aegis.NumberOfWays.number_of_ways corridor = ok r ∧ r.val = 1) := by
    sorry

  /-- For every j with 1 <= j <= m/2 - 1, let d = p_{2j} - p_{2j-1}, and let corridor' be obtained by inserting one byte 80 ('P') at a position k with p_{2j-1} < k <= p_{2j} (insertion before the old index k). If number_of_ways(corridor) returns r and number_of_ways(corridor') returns r', then r' is congruent modulo 1000000007 to r * (d + 1) * d^{-1}, where d^{-1} denotes the inverse of d modulo 1000000007.
    Preconditions: The input corridor is valid: 1 <= len(corridor) < 100000, every byte is 80 ('P') or 83 ('S'), and the number m of seats is positive even with m >= 4. Let p_0 < ... < p_{m-1} be the seat positions. -/
  theorem spec_7 (corridor : Corridor)
      (hlen : 1 ≤ corridor.val.length) (hlen_max : corridor.val.length < 100000)
      (hbytes : AllPOrS corridor)
      (hpos : 0 < seatCount corridor) (heven : Even (seatCount corridor))
      (hfour : 4 ≤ seatCount corridor) :
      ∀ j : ℕ, 1 ≤ j → j ≤ seatCount corridor / 2 - 1 →
        ∀ k : ℕ, (seatPositions corridor).getD (2 * j - 1) 0 < k →
          k ≤ (seatPositions corridor).getD (2 * j) 0 →
            ∀ corridor' : Corridor,
              corridor'.val = corridor.val.take k ++ [P_BYTE] ++ corridor.val.drop k →
                ∀ r r' : I64,
                  Aegis.NumberOfWays.number_of_ways corridor = ok r →
                  Aegis.NumberOfWays.number_of_ways corridor' = ok r' →
                  Int.ModEq MOD r'.val
                    (r.val * (pairGap (seatPositions corridor) j + 1)
                      * modInv (pairGap (seatPositions corridor) j)) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (corridor : Corridor)
        (hlen : 1 ≤ corridor.val.length) (hlen_max : corridor.val.length < 100000)
        (hbytes : AllPOrS corridor)
        (hpos : 0 < seatCount corridor) (heven : Even (seatCount corridor))
        (hfour : 4 ≤ seatCount corridor), ∀ j : ℕ, 1 ≤ j → j ≤ seatCount corridor / 2 - 1 →
          ∀ k : ℕ, (seatPositions corridor).getD (2 * j - 1) 0 < k →
            k ≤ (seatPositions corridor).getD (2 * j) 0 →
              ∀ corridor' : Corridor,
                corridor'.val = corridor.val.take k ++ [P_BYTE] ++ corridor.val.drop k →
                  ∀ r r' : I64,
                    Aegis.NumberOfWays.number_of_ways corridor = ok r →
                    Aegis.NumberOfWays.number_of_ways corridor' = ok r' →
                    Int.ModEq MOD r'.val
                      (r.val * (pairGap (seatPositions corridor) j + 1)
                        * modInv (pairGap (seatPositions corridor) j))) := by
    sorry

  /-- Whenever the function returns a result r, r > 0 if and only if there exists a set D subset of {1, 2, ..., len(corridor) - 1} such that, writing the elements of D union {0, len(corridor)} in increasing order as d_0 < d_1 < ... < d_t with d_0 = 0 and d_t = len(corridor), for every k with 0 <= k < t the segment of indices i satisfying d_k <= i < d_{k+1} contains exactly two indices i with corridor[i] = 83.
    Preconditions: The input is a valid corridor: 1 <= len(corridor) <= 100000, and for every i with 0 <= i < len(corridor), corridor[i] = 80 ('P') or corridor[i] = 83 ('S'). -/
  theorem spec_8 (corridor : Corridor)
      (hlen : 1 ≤ corridor.val.length) (hlen_max : corridor.val.length ≤ 100000)
      (hbytes : AllPOrS corridor) :
      ∀ r : I64, Aegis.NumberOfWays.number_of_ways corridor = ok r →
        (0 < r.val ↔
          ∃ D : List ℕ,
            D.Pairwise (· < ·) ∧
            (∀ d ∈ D, 1 ≤ d ∧ d < corridor.val.length) ∧
            SegmentsHaveTwoSeats corridor (cutPoints D corridor.val.length)) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (corridor : Corridor)
        (hlen : 1 ≤ corridor.val.length) (hlen_max : corridor.val.length ≤ 100000)
        (hbytes : AllPOrS corridor), ∀ r : I64, Aegis.NumberOfWays.number_of_ways corridor = ok r →
          (0 < r.val ↔
            ∃ D : List ℕ,
              D.Pairwise (· < ·) ∧
              (∀ d ∈ D, 1 ≤ d ∧ d < corridor.val.length) ∧
              SegmentsHaveTwoSeats corridor (cutPoints D corridor.val.length))) := by
    sorry

  /-- Whenever number_of_ways(corridor) returns r and number_of_ways(corridor') returns r', we have r = r'.
    Preconditions: corridor and corridor' are valid inputs: each has length between 1 and 100000 and every byte is 80 ('P') or 83 ('S'). Deleting all leading bytes equal to 80 and all trailing bytes equal to 80 from corridor yields the same byte sequence as deleting all leading bytes equal to 80 and all trailing bytes equal to 80 from corridor'. -/
  theorem spec_9 (corridor corridor' : Corridor)
      (hlen : 1 ≤ corridor.val.length) (hlen_max : corridor.val.length ≤ 100000)
      (hbytes : AllPOrS corridor)
      (hlen' : 1 ≤ corridor'.val.length) (hlen_max' : corridor'.val.length ≤ 100000)
      (hbytes' : AllPOrS corridor')
      (htrim : trimmedBytes corridor = trimmedBytes corridor') :
      ∀ r r' : I64,
        Aegis.NumberOfWays.number_of_ways corridor = ok r →
        Aegis.NumberOfWays.number_of_ways corridor' = ok r' → r.val = r'.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (corridor corridor' : Corridor)
        (hlen : 1 ≤ corridor.val.length) (hlen_max : corridor.val.length ≤ 100000)
        (hbytes : AllPOrS corridor)
        (hlen' : 1 ≤ corridor'.val.length) (hlen_max' : corridor'.val.length ≤ 100000)
        (hbytes' : AllPOrS corridor')
        (htrim : trimmedBytes corridor = trimmedBytes corridor'), ∀ r r' : I64,
          Aegis.NumberOfWays.number_of_ways corridor = ok r →
          Aegis.NumberOfWays.number_of_ways corridor' = ok r' → r.val = r'.val) := by
    sorry

  end AegisSpec.NumberOfWays

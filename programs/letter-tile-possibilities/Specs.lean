import Aegis.NumTilePossibilities.Code.Funs

/-!
# Specifications of `Aegis.NumTilePossibilities.num_tile_possibilities`

LeetCode problem `letter-tile-possibilities`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.NumTilePossibilities

  def IsUpperByte (b : Aeneas.Std.U8) : Prop := 65 ≤ b.val ∧ b.val ≤ 90

  def IsUpperList (tiles : List Aeneas.Std.U8) : Prop :=
    ∀ i : Fin tiles.length, IsUpperByte (tiles.get i)

  def occ (c : Aeneas.Std.U8) (x : List Aeneas.Std.U8) : ℕ :=
    (x.filter (fun b => b = c)).length

  def IsValidSeq (tiles s : List Aeneas.Std.U8) : Prop :=
    1 ≤ s.length ∧ ∀ c : Aeneas.Std.U8, occ c s ≤ occ c tiles

  def listsUpTo (alpha : Finset Aeneas.Std.U8) : ℕ → Finset (List Aeneas.Std.U8)
    | 0 => {[]}
    | k + 1 => listsUpTo alpha k ∪ (listsUpTo alpha k).biUnion fun s => alpha.image fun c => c :: s

  noncomputable def nbValidSeqs (tiles : List Aeneas.Std.U8) : ℕ :=
    letI := Classical.decPred (fun s : List Aeneas.Std.U8 => IsValidSeq tiles s)
    ((listsUpTo tiles.toFinset tiles.length).filter fun s => IsValidSeq tiles s).card

  def nbDistinctBytes (tiles : List Aeneas.Std.U8) : ℕ := tiles.toFinset.card

  def sumFallingFactorial (n : ℕ) : ℕ := ∑ k ∈ Finset.Icc 1 n, n.factorial / (n - k).factorial

  /-- Let occ(c, x) denote the number of indices i with 0 <= i < len(x) and x[i] = c. Call a finite list s of bytes a valid sequence for tiles if len(s) >= 1 and for every byte c, occ(c, s) <= occ(c, tiles). Then whenever num_tile_possibilities(tiles) returns a result r, r equals the number of distinct valid sequences for tiles, where two sequences are distinct exactly when they differ in length or in some position.
    Preconditions: len(tiles) >= 1 and len(tiles) <= 7 and for every i with 0 <= i < len(tiles), 65 <= tiles[i] <= 90 (so tiles[i] is an uppercase English letter in ASCII). -/
  theorem spec_1 (tiles : Aeneas.Std.Slice Aeneas.Std.U8)
      (hlen_lower : 1 ≤ tiles.val.length) (hlen_upper : tiles.val.length ≤ 7)
      (hletters : IsUpperList tiles.val) :
      ∀ r : Aeneas.Std.I64,
        Aegis.NumTilePossibilities.num_tile_possibilities tiles = ok r →
        r.val = (nbValidSeqs tiles.val : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (tiles : Aeneas.Std.Slice Aeneas.Std.U8)
        (hlen_lower : 1 ≤ tiles.val.length) (hlen_upper : tiles.val.length ≤ 7)
        (hletters : IsUpperList tiles.val), ∀ r : Aeneas.Std.I64,
          Aegis.NumTilePossibilities.num_tile_possibilities tiles = ok r →
          r.val = (nbValidSeqs tiles.val : ℤ)) := by
    sorry

  /-- For every slice tiles satisfying the preconditions, num_tile_possibilities(tiles) returns a result r (i.e., it does not fail with an error, overflow, out-of-bounds access, or panic).
    Preconditions: len(tiles) >= 1 and len(tiles) <= 7 and for every i with 0 <= i < len(tiles), 65 <= tiles[i] <= 90. -/
  theorem spec_2 (tiles : Aeneas.Std.Slice Aeneas.Std.U8)
      (hlen_lower : 1 ≤ tiles.val.length) (hlen_upper : tiles.val.length ≤ 7)
      (hletters : IsUpperList tiles.val) :
      ∃ r : Aeneas.Std.I64, Aegis.NumTilePossibilities.num_tile_possibilities tiles = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (tiles : Aeneas.Std.Slice Aeneas.Std.U8)
        (hlen_lower : 1 ≤ tiles.val.length) (hlen_upper : tiles.val.length ≤ 7)
        (hletters : IsUpperList tiles.val), ∃ r : Aeneas.Std.I64, Aegis.NumTilePossibilities.num_tile_possibilities tiles = ok r) := by
    sorry

  /-- Let occ(c, x) denote the number of indices i with 0 <= i < len(x) and x[i] = c. For every slice tiles satisfying the preconditions, whenever num_tile_possibilities(tiles) returns a result r, r >= d, where d is the number of distinct bytes c such that occ(c, tiles) >= 1 (i.e., the number of distinct letters appearing in tiles).
    Preconditions: len(tiles) >= 1 and len(tiles) <= 7 and for every i with 0 <= i < len(tiles), 65 <= tiles[i] <= 90. -/
  theorem spec_3 (tiles : Aeneas.Std.Slice Aeneas.Std.U8)
      (hlen_lower : 1 ≤ tiles.val.length) (hlen_upper : tiles.val.length ≤ 7)
      (hletters : IsUpperList tiles.val) :
      ∀ r : Aeneas.Std.I64,
        Aegis.NumTilePossibilities.num_tile_possibilities tiles = ok r →
        (nbDistinctBytes tiles.val : ℤ) ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (tiles : Aeneas.Std.Slice Aeneas.Std.U8)
        (hlen_lower : 1 ≤ tiles.val.length) (hlen_upper : tiles.val.length ≤ 7)
        (hletters : IsUpperList tiles.val), ∀ r : Aeneas.Std.I64,
          Aegis.NumTilePossibilities.num_tile_possibilities tiles = ok r →
          (nbDistinctBytes tiles.val : ℤ) ≤ r.val) := by
    sorry

  /-- For every slice tiles satisfying the preconditions, whenever num_tile_possibilities(tiles) returns a result r, r <= sum_{k=1}^{len(tiles)} (len(tiles))! / (len(tiles)-k)!, where m! denotes the factorial of the natural number m and the sum is over integers k from 1 to len(tiles).
    Preconditions: len(tiles) >= 1 and len(tiles) <= 7 and for every i with 0 <= i < len(tiles), 65 <= tiles[i] <= 90. -/
  theorem spec_4 (tiles : Aeneas.Std.Slice Aeneas.Std.U8)
      (hlen_lower : 1 ≤ tiles.val.length) (hlen_upper : tiles.val.length ≤ 7)
      (hletters : IsUpperList tiles.val) :
      ∀ r : Aeneas.Std.I64,
        Aegis.NumTilePossibilities.num_tile_possibilities tiles = ok r →
        r.val ≤ (sumFallingFactorial tiles.val.length : ℤ) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (tiles : Aeneas.Std.Slice Aeneas.Std.U8)
        (hlen_lower : 1 ≤ tiles.val.length) (hlen_upper : tiles.val.length ≤ 7)
        (hletters : IsUpperList tiles.val), ∀ r : Aeneas.Std.I64,
          Aegis.NumTilePossibilities.num_tile_possibilities tiles = ok r →
          r.val ≤ (sumFallingFactorial tiles.val.length : ℤ)) := by
    sorry

  /-- For every slice tiles satisfying the preconditions, if len(tiles) = 1, then whenever num_tile_possibilities(tiles) returns a result r, r = 1.
    Preconditions: len(tiles) >= 1 and len(tiles) <= 7 and for every i with 0 <= i < len(tiles), 65 <= tiles[i] <= 90. -/
  theorem spec_5 (tiles : Aeneas.Std.Slice Aeneas.Std.U8)
      (hlen_lower : 1 ≤ tiles.val.length) (hlen_upper : tiles.val.length ≤ 7)
      (hletters : IsUpperList tiles.val)
      (hlen : tiles.val.length = 1) :
      ∀ r : Aeneas.Std.I64,
        Aegis.NumTilePossibilities.num_tile_possibilities tiles = ok r → r.val = 1 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (tiles : Aeneas.Std.Slice Aeneas.Std.U8)
        (hlen_lower : 1 ≤ tiles.val.length) (hlen_upper : tiles.val.length ≤ 7)
        (hletters : IsUpperList tiles.val)
        (hlen : tiles.val.length = 1), ∀ r : Aeneas.Std.I64,
          Aegis.NumTilePossibilities.num_tile_possibilities tiles = ok r → r.val = 1) := by
    sorry

  /-- For every slice tiles satisfying the preconditions, if all bytes in tiles are equal (i.e., there exists a byte c such that for every i with 0 <= i < len(tiles), tiles[i] = c), then whenever num_tile_possibilities(tiles) returns a result r, r = len(tiles).
    Preconditions: len(tiles) >= 1 and len(tiles) <= 7 and for every i with 0 <= i < len(tiles), 65 <= tiles[i] <= 90. -/
  theorem spec_6 (tiles : Aeneas.Std.Slice Aeneas.Std.U8)
      (hlen_lower : 1 ≤ tiles.val.length) (hlen_upper : tiles.val.length ≤ 7)
      (hletters : IsUpperList tiles.val)
      (hall : ∃ c : Aeneas.Std.U8, ∀ i : Fin tiles.val.length, tiles.val.get i = c) :
      ∀ r : Aeneas.Std.I64,
        Aegis.NumTilePossibilities.num_tile_possibilities tiles = ok r →
        r.val = (tiles.val.length : ℤ) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (tiles : Aeneas.Std.Slice Aeneas.Std.U8)
        (hlen_lower : 1 ≤ tiles.val.length) (hlen_upper : tiles.val.length ≤ 7)
        (hletters : IsUpperList tiles.val)
        (hall : ∃ c : Aeneas.Std.U8, ∀ i : Fin tiles.val.length, tiles.val.get i = c), ∀ r : Aeneas.Std.I64,
          Aegis.NumTilePossibilities.num_tile_possibilities tiles = ok r →
          r.val = (tiles.val.length : ℤ)) := by
    sorry

  /-- For every slice tiles satisfying the preconditions, if all bytes in tiles are pairwise distinct (i.e., for every i,j with 0 <= i < j < len(tiles), tiles[i] != tiles[j]), then whenever num_tile_possibilities(tiles) returns a result r, r = sum_{k=1}^{len(tiles)} (len(tiles))! / (len(tiles)-k)!, where m! denotes the factorial of the natural number m.
    Preconditions: len(tiles) >= 1 and len(tiles) <= 7 and for every i with 0 <= i < len(tiles), 65 <= tiles[i] <= 90. -/
  theorem spec_7 (tiles : Aeneas.Std.Slice Aeneas.Std.U8)
      (hlen_lower : 1 ≤ tiles.val.length) (hlen_upper : tiles.val.length ≤ 7)
      (hletters : IsUpperList tiles.val)
      (hdistinct : ∀ i j : Fin tiles.val.length, i < j → tiles.val.get i ≠ tiles.val.get j) :
      ∀ r : Aeneas.Std.I64,
        Aegis.NumTilePossibilities.num_tile_possibilities tiles = ok r →
        r.val = (sumFallingFactorial tiles.val.length : ℤ) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (tiles : Aeneas.Std.Slice Aeneas.Std.U8)
        (hlen_lower : 1 ≤ tiles.val.length) (hlen_upper : tiles.val.length ≤ 7)
        (hletters : IsUpperList tiles.val)
        (hdistinct : ∀ i j : Fin tiles.val.length, i < j → tiles.val.get i ≠ tiles.val.get j), ∀ r : Aeneas.Std.I64,
          Aegis.NumTilePossibilities.num_tile_possibilities tiles = ok r →
          r.val = (sumFallingFactorial tiles.val.length : ℤ)) := by
    sorry

  /-- Let occ(c, x) denote the number of indices i with 0 <= i < len(x) and x[i] = c. For every two slices tiles1 and tiles2 satisfying the preconditions, if for every byte c, occ(c, tiles1) = occ(c, tiles2) (i.e., tiles2 is a permutation of tiles1), then whenever num_tile_possibilities(tiles1) returns r1 and num_tile_possibilities(tiles2) returns r2, r1 = r2.
    Preconditions: Both tiles1 and tiles2 satisfy: len >= 1 and len <= 7 and every byte is an uppercase English letter (65..90). -/
  theorem spec_8 (tiles1 tiles2 : Aeneas.Std.Slice Aeneas.Std.U8)
      (hlen_lower1 : 1 ≤ tiles1.val.length) (hlen_upper1 : tiles1.val.length ≤ 7)
      (hletters1 : IsUpperList tiles1.val)
      (hlen_lower2 : 1 ≤ tiles2.val.length) (hlen_upper2 : tiles2.val.length ≤ 7)
      (hletters2 : IsUpperList tiles2.val)
      (hocc : ∀ c : Aeneas.Std.U8, occ c tiles1.val = occ c tiles2.val) :
      ∀ r1 r2 : Aeneas.Std.I64,
        Aegis.NumTilePossibilities.num_tile_possibilities tiles1 = ok r1 →
        Aegis.NumTilePossibilities.num_tile_possibilities tiles2 = ok r2 → r1 = r2 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (tiles1 tiles2 : Aeneas.Std.Slice Aeneas.Std.U8)
        (hlen_lower1 : 1 ≤ tiles1.val.length) (hlen_upper1 : tiles1.val.length ≤ 7)
        (hletters1 : IsUpperList tiles1.val)
        (hlen_lower2 : 1 ≤ tiles2.val.length) (hlen_upper2 : tiles2.val.length ≤ 7)
        (hletters2 : IsUpperList tiles2.val)
        (hocc : ∀ c : Aeneas.Std.U8, occ c tiles1.val = occ c tiles2.val), ∀ r1 r2 : Aeneas.Std.I64,
          Aegis.NumTilePossibilities.num_tile_possibilities tiles1 = ok r1 →
          Aegis.NumTilePossibilities.num_tile_possibilities tiles2 = ok r2 → r1 = r2) := by
    sorry

  /-- Let occ(c, x) denote the number of indices i with 0 <= i < len(x) and x[i] = c. For every two slices tiles1 and tiles2 satisfying the preconditions, if for every byte c, occ(c, tiles1) <= occ(c, tiles2) (i.e., the multiset of tiles1 is a sub-multiset of the multiset of tiles2), then whenever num_tile_possibilities(tiles1) returns r1 and num_tile_possibilities(tiles2) returns r2, r1 <= r2.
    Preconditions: Both tiles1 and tiles2 satisfy: len >= 1 and len <= 7 and every byte is an uppercase English letter (65..90). -/
  theorem spec_9 (tiles1 tiles2 : Aeneas.Std.Slice Aeneas.Std.U8)
      (hlen_lower1 : 1 ≤ tiles1.val.length) (hlen_upper1 : tiles1.val.length ≤ 7)
      (hletters1 : IsUpperList tiles1.val)
      (hlen_lower2 : 1 ≤ tiles2.val.length) (hlen_upper2 : tiles2.val.length ≤ 7)
      (hletters2 : IsUpperList tiles2.val)
      (hocc : ∀ c : Aeneas.Std.U8, occ c tiles1.val ≤ occ c tiles2.val) :
      ∀ r1 r2 : Aeneas.Std.I64,
        Aegis.NumTilePossibilities.num_tile_possibilities tiles1 = ok r1 →
        Aegis.NumTilePossibilities.num_tile_possibilities tiles2 = ok r2 → r1.val ≤ r2.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (tiles1 tiles2 : Aeneas.Std.Slice Aeneas.Std.U8)
        (hlen_lower1 : 1 ≤ tiles1.val.length) (hlen_upper1 : tiles1.val.length ≤ 7)
        (hletters1 : IsUpperList tiles1.val)
        (hlen_lower2 : 1 ≤ tiles2.val.length) (hlen_upper2 : tiles2.val.length ≤ 7)
        (hletters2 : IsUpperList tiles2.val)
        (hocc : ∀ c : Aeneas.Std.U8, occ c tiles1.val ≤ occ c tiles2.val), ∀ r1 r2 : Aeneas.Std.I64,
          Aegis.NumTilePossibilities.num_tile_possibilities tiles1 = ok r1 →
          Aegis.NumTilePossibilities.num_tile_possibilities tiles2 = ok r2 → r1.val ≤ r2.val) := by
    sorry

  /-- Let tiles' be the slice of the same length as tiles such that for every i with 0 <= i < len(tiles), tiles'[i] = f(tiles[i]). Then whenever num_tile_possibilities(tiles) returns r and num_tile_possibilities(tiles') returns r', we have r = r'.
    Preconditions: tiles satisfies len >= 1 and len <= 7 and every byte is an uppercase English letter (65..90). f is a bijection from the set of uppercase English letters (ASCII codes 65..90) to itself. -/
  theorem spec_10 (tiles tiles' : Aeneas.Std.Slice Aeneas.Std.U8) (f : Aeneas.Std.U8 → Aeneas.Std.U8)
      (hlen_lower : 1 ≤ tiles.val.length) (hlen_upper : tiles.val.length ≤ 7)
      (hletters : IsUpperList tiles.val)
      (hmap : ∀ c : Aeneas.Std.U8, IsUpperByte c → IsUpperByte (f c))
      (hinj : ∀ c d : Aeneas.Std.U8, IsUpperByte c → IsUpperByte d → f c = f d → c = d)
      (htiles' : tiles'.val = tiles.val.map f) :
      ∀ r r' : Aeneas.Std.I64,
        Aegis.NumTilePossibilities.num_tile_possibilities tiles = ok r →
        Aegis.NumTilePossibilities.num_tile_possibilities tiles' = ok r' → r = r' := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (tiles tiles' : Aeneas.Std.Slice Aeneas.Std.U8) (f : Aeneas.Std.U8 → Aeneas.Std.U8)
        (hlen_lower : 1 ≤ tiles.val.length) (hlen_upper : tiles.val.length ≤ 7)
        (hletters : IsUpperList tiles.val)
        (hmap : ∀ c : Aeneas.Std.U8, IsUpperByte c → IsUpperByte (f c))
        (hinj : ∀ c d : Aeneas.Std.U8, IsUpperByte c → IsUpperByte d → f c = f d → c = d)
        (htiles' : tiles'.val = tiles.val.map f), ∀ r r' : Aeneas.Std.I64,
          Aegis.NumTilePossibilities.num_tile_possibilities tiles = ok r →
          Aegis.NumTilePossibilities.num_tile_possibilities tiles' = ok r' → r = r') := by
    sorry

  /-- Let occ(c, x) denote the number of indices i with 0 <= i < len(x) and x[i] = c. Let c and d be the two distinct bytes appearing in tiles, and let a = occ(c, tiles) and b = occ(d, tiles). Then whenever num_tile_possibilities(tiles) returns a result r, r = (sum_{i=0}^{a} sum_{j=0}^{b} (i+j)! / (i! * j!)) - 1, where m! denotes the factorial of the natural number m.
    Preconditions: tiles satisfies len >= 1 and len <= 7 and every byte is an uppercase English letter (65..90), and the set of bytes appearing in tiles has exactly two elements. -/
  theorem spec_11 (tiles : Aeneas.Std.Slice Aeneas.Std.U8)
      (hlen_lower : 1 ≤ tiles.val.length) (hlen_upper : tiles.val.length ≤ 7)
      (hletters : IsUpperList tiles.val)
      (c d : Aeneas.Std.U8) (hc : c ∈ tiles.val) (hd : d ∈ tiles.val) (hcd : c ≠ d)
      (htwo : ∀ b : Aeneas.Std.U8, b ∈ tiles.val → b = c ∨ b = d) :
      ∀ r : Aeneas.Std.I64,
        Aegis.NumTilePossibilities.num_tile_possibilities tiles = ok r →
        r.val = ((∑ i ∈ Finset.range (occ c tiles.val + 1),
                    ∑ j ∈ Finset.range (occ d tiles.val + 1),
                      (i + j).factorial / (i.factorial * j.factorial) : ℕ) : ℤ) - 1 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (tiles : Aeneas.Std.Slice Aeneas.Std.U8)
        (hlen_lower : 1 ≤ tiles.val.length) (hlen_upper : tiles.val.length ≤ 7)
        (hletters : IsUpperList tiles.val)
        (c d : Aeneas.Std.U8) (hc : c ∈ tiles.val) (hd : d ∈ tiles.val) (hcd : c ≠ d)
        (htwo : ∀ b : Aeneas.Std.U8, b ∈ tiles.val → b = c ∨ b = d), ∀ r : Aeneas.Std.I64,
          Aegis.NumTilePossibilities.num_tile_possibilities tiles = ok r →
          r.val = ((∑ i ∈ Finset.range (occ c tiles.val + 1),
                      ∑ j ∈ Finset.range (occ d tiles.val + 1),
                        (i + j).factorial / (i.factorial * j.factorial) : ℕ) : ℤ) - 1) := by
    sorry

  end AegisSpec.NumTilePossibilities

import Aegis.MinimumRecolors.Code.Funs

/-!
# Specifications of `Aegis.MinimumRecolors.minimum_recolors`

LeetCode problem `minimum-recolors-to-get-k-consecutive-black-blocks`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinimumRecolors

  open Aegis.MinimumRecolors

  abbrev Byte : Type := Aeneas.Std.U8

  abbrev ByteSlice : Type := Aeneas.Std.Slice Aeneas.Std.U8

  def isWhite (b : Byte) : Prop := b.val = 87

  def isBlack (b : Byte) : Prop := b.val = 66

  def bytesBW (blocks : ByteSlice) : Prop :=
    ∀ i : ℕ, i < blocks.val.length → isWhite (blocks.val[i]!) ∨ isBlack (blocks.val[i]!)

  def whitesInWindow (blocks : ByteSlice) (j kk : ℕ) : ℕ :=
    ((blocks.val.drop j).take kk).countP (fun b => b.val = 87)

  def totalWhites (blocks : ByteSlice) : ℕ :=
    blocks.val.countP (fun b => b.val = 87)

  def ValidInput (blocks : ByteSlice) (k : Aeneas.Std.I64) : Prop :=
    1 ≤ blocks.val.length ∧ blocks.val.length ≤ 100 ∧ bytesBW blocks ∧
      1 ≤ k.val ∧ k.val ≤ (blocks.val.length : ℤ)

  /-- The function returns a result r, and r = min { W(j) | 0 <= j <= len(blocks)-k }, where W(j) is the number of indices i with j <= i < j+k and blocks[i] = 87 (ASCII 'W'). Equivalently, for every j with 0 <= j <= len(blocks)-k we have r <= W(j), and there exists at least one j with 0 <= j <= len(blocks)-k such that W(j) = r.
    Preconditions: `blocks` is a slice of bytes with 1 <= len(blocks) <= 100; for every i with 0 <= i < len(blocks), blocks[i] is either 87 (the ASCII code of 'W') or 66 (the ASCII code of 'B'); and k, viewed as an integer, satisfies 1 <= k <= len(blocks). -/
  theorem spec_1 (blocks : ByteSlice) (k : Aeneas.Std.I64)
      (hlen_lb : 1 ≤ blocks.val.length) (hlen_ub : blocks.val.length ≤ 100)
      (hbytes : bytesBW blocks)
      (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ (blocks.val.length : ℤ)) :
      ∃ r : Aeneas.Std.I64,
        Aegis.MinimumRecolors.minimum_recolors blocks k = Aeneas.Std.Result.ok r ∧
        (∀ j : ℕ, j ≤ blocks.val.length - k.val.toNat →
          r.val ≤ (whitesInWindow blocks j k.val.toNat : ℤ)) ∧
        (∃ j : ℕ, j ≤ blocks.val.length - k.val.toNat ∧
          (whitesInWindow blocks j k.val.toNat : ℤ) = r.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (blocks : ByteSlice) (k : Aeneas.Std.I64)
        (hlen_lb : 1 ≤ blocks.val.length) (hlen_ub : blocks.val.length ≤ 100)
        (hbytes : bytesBW blocks)
        (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ (blocks.val.length : ℤ)), ∃ r : Aeneas.Std.I64,
          Aegis.MinimumRecolors.minimum_recolors blocks k = Aeneas.Std.Result.ok r ∧
          (∀ j : ℕ, j ≤ blocks.val.length - k.val.toNat →
            r.val ≤ (whitesInWindow blocks j k.val.toNat : ℤ)) ∧
          (∃ j : ℕ, j ≤ blocks.val.length - k.val.toNat ∧
            (whitesInWindow blocks j k.val.toNat : ℤ) = r.val)) := by
    sorry

  /-- The function returns a result r for some i64 r; in particular, on these inputs it does not fail, panic, or overflow.
    Preconditions: `blocks` is a slice of bytes with 1 <= len(blocks) <= 100; for every i with 0 <= i < len(blocks), blocks[i] is either 87 (the ASCII code of 'W') or 66 (the ASCII code of 'B'); and k, viewed as an integer, satisfies 1 <= k <= len(blocks). -/
  theorem spec_2 (blocks : ByteSlice) (k : Aeneas.Std.I64)
      (hlen_lb : 1 ≤ blocks.val.length) (hlen_ub : blocks.val.length ≤ 100)
      (hbytes : bytesBW blocks)
      (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ (blocks.val.length : ℤ)) :
      ∃ r : Aeneas.Std.I64,
        Aegis.MinimumRecolors.minimum_recolors blocks k = Aeneas.Std.Result.ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (blocks : ByteSlice) (k : Aeneas.Std.I64)
        (hlen_lb : 1 ≤ blocks.val.length) (hlen_ub : blocks.val.length ≤ 100)
        (hbytes : bytesBW blocks)
        (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ (blocks.val.length : ℤ)), ∃ r : Aeneas.Std.I64,
          Aegis.MinimumRecolors.minimum_recolors blocks k = Aeneas.Std.Result.ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r <= k.
    Preconditions: `blocks` is a slice of bytes with 1 <= len(blocks) <= 100; for every i with 0 <= i < len(blocks), blocks[i] is either 87 (the ASCII code of 'W') or 66 (the ASCII code of 'B'); and k, viewed as an integer, satisfies 1 <= k <= len(blocks). -/
  theorem spec_3 (blocks : ByteSlice) (k : Aeneas.Std.I64)
      (hlen_lb : 1 ≤ blocks.val.length) (hlen_ub : blocks.val.length ≤ 100)
      (hbytes : bytesBW blocks)
      (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ (blocks.val.length : ℤ))
      (r : Aeneas.Std.I64)
      (hr : Aegis.MinimumRecolors.minimum_recolors blocks k = Aeneas.Std.Result.ok r) :
      0 ≤ r.val ∧ r.val ≤ k.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (blocks : ByteSlice) (k : Aeneas.Std.I64)
        (hlen_lb : 1 ≤ blocks.val.length) (hlen_ub : blocks.val.length ≤ 100)
        (hbytes : bytesBW blocks)
        (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ (blocks.val.length : ℤ))
        (r : Aeneas.Std.I64)
        (hr : Aegis.MinimumRecolors.minimum_recolors blocks k = Aeneas.Std.Result.ok r), 0 ≤ r.val ∧ r.val ≤ k.val) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if there exists a start index j with 0 <= j <= len(blocks)-k such that blocks[i] = 66 (ASCII 'B') for every i with j <= i < j+k.
    Preconditions: `blocks` is a slice of bytes with 1 <= len(blocks) <= 100; for every i with 0 <= i < len(blocks), blocks[i] is either 87 (the ASCII code of 'W') or 66 (the ASCII code of 'B'); and k, viewed as an integer, satisfies 1 <= k <= len(blocks). -/
  theorem spec_4 (blocks : ByteSlice) (k : Aeneas.Std.I64)
      (hlen_lb : 1 ≤ blocks.val.length) (hlen_ub : blocks.val.length ≤ 100)
      (hbytes : bytesBW blocks)
      (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ (blocks.val.length : ℤ))
      (r : Aeneas.Std.I64)
      (hr : Aegis.MinimumRecolors.minimum_recolors blocks k = Aeneas.Std.Result.ok r) :
      r.val = 0 ↔ ∃ j : ℕ, j ≤ blocks.val.length - k.val.toNat ∧
        ∀ i : ℕ, j ≤ i → i < j + k.val.toNat → isBlack (blocks.val[i]!) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (blocks : ByteSlice) (k : Aeneas.Std.I64)
        (hlen_lb : 1 ≤ blocks.val.length) (hlen_ub : blocks.val.length ≤ 100)
        (hbytes : bytesBW blocks)
        (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ (blocks.val.length : ℤ))
        (r : Aeneas.Std.I64)
        (hr : Aegis.MinimumRecolors.minimum_recolors blocks k = Aeneas.Std.Result.ok r), r.val = 0 ↔ ∃ j : ℕ, j ≤ blocks.val.length - k.val.toNat ∧
          ∀ i : ℕ, j ≤ i → i < j + k.val.toNat → isBlack (blocks.val[i]!)) := by
    sorry

  /-- Whenever the function returns a result r, there exists a start index j with 0 <= j <= len(blocks)-k such that exactly r of the indices i with j <= i < j+k satisfy blocks[i] = 87 (ASCII 'W'); consequently, recoloring exactly those r white blocks to black makes the k blocks j, j+1, ..., j+k-1 all black.
    Preconditions: `blocks` is a slice of bytes with 1 <= len(blocks) <= 100; for every i with 0 <= i < len(blocks), blocks[i] is either 87 (the ASCII code of 'W') or 66 (the ASCII code of 'B'); and k, viewed as an integer, satisfies 1 <= k <= len(blocks). -/
  theorem spec_5 (blocks : ByteSlice) (k : Aeneas.Std.I64)
      (hlen_lb : 1 ≤ blocks.val.length) (hlen_ub : blocks.val.length ≤ 100)
      (hbytes : bytesBW blocks)
      (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ (blocks.val.length : ℤ))
      (r : Aeneas.Std.I64)
      (hr : Aegis.MinimumRecolors.minimum_recolors blocks k = Aeneas.Std.Result.ok r) :
      ∃ j : ℕ, j ≤ blocks.val.length - k.val.toNat ∧
        (whitesInWindow blocks j k.val.toNat : ℤ) = r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (blocks : ByteSlice) (k : Aeneas.Std.I64)
        (hlen_lb : 1 ≤ blocks.val.length) (hlen_ub : blocks.val.length ≤ 100)
        (hbytes : bytesBW blocks)
        (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ (blocks.val.length : ℤ))
        (r : Aeneas.Std.I64)
        (hr : Aegis.MinimumRecolors.minimum_recolors blocks k = Aeneas.Std.Result.ok r), ∃ j : ℕ, j ≤ blocks.val.length - k.val.toNat ∧
          (whitesInWindow blocks j k.val.toNat : ℤ) = r.val) := by
    sorry

  /-- Whenever the function returns a result r, for every start index j with 0 <= j <= len(blocks)-k, at least r of the indices i with j <= i < j+k satisfy blocks[i] = 87 (ASCII 'W').
    Preconditions: `blocks` is a slice of bytes with 1 <= len(blocks) <= 100; for every i with 0 <= i < len(blocks), blocks[i] is either 87 (the ASCII code of 'W') or 66 (the ASCII code of 'B'); and k, viewed as an integer, satisfies 1 <= k <= len(blocks). -/
  theorem spec_6 (blocks : ByteSlice) (k : Aeneas.Std.I64)
      (hlen_lb : 1 ≤ blocks.val.length) (hlen_ub : blocks.val.length ≤ 100)
      (hbytes : bytesBW blocks)
      (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ (blocks.val.length : ℤ))
      (r : Aeneas.Std.I64)
      (hr : Aegis.MinimumRecolors.minimum_recolors blocks k = Aeneas.Std.Result.ok r) :
      ∀ j : ℕ, j ≤ blocks.val.length - k.val.toNat →
        r.val ≤ (whitesInWindow blocks j k.val.toNat : ℤ) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (blocks : ByteSlice) (k : Aeneas.Std.I64)
        (hlen_lb : 1 ≤ blocks.val.length) (hlen_ub : blocks.val.length ≤ 100)
        (hbytes : bytesBW blocks)
        (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ (blocks.val.length : ℤ))
        (r : Aeneas.Std.I64)
        (hr : Aegis.MinimumRecolors.minimum_recolors blocks k = Aeneas.Std.Result.ok r), ∀ j : ℕ, j ≤ blocks.val.length - k.val.toNat →
          r.val ≤ (whitesInWindow blocks j k.val.toNat : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r is at most the total number of indices i with 0 <= i < len(blocks) and blocks[i] = 87 (ASCII 'W').
    Preconditions: `blocks` is a slice of bytes with 1 <= len(blocks) <= 100; for every i with 0 <= i < len(blocks), blocks[i] is either 87 (the ASCII code of 'W') or 66 (the ASCII code of 'B'); and k, viewed as an integer, satisfies 1 <= k <= len(blocks). -/
  theorem spec_7 (blocks : ByteSlice) (k : Aeneas.Std.I64)
      (hlen_lb : 1 ≤ blocks.val.length) (hlen_ub : blocks.val.length ≤ 100)
      (hbytes : bytesBW blocks)
      (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ (blocks.val.length : ℤ))
      (r : Aeneas.Std.I64)
      (hr : Aegis.MinimumRecolors.minimum_recolors blocks k = Aeneas.Std.Result.ok r) :
      r.val ≤ (totalWhites blocks : ℤ) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (blocks : ByteSlice) (k : Aeneas.Std.I64)
        (hlen_lb : 1 ≤ blocks.val.length) (hlen_ub : blocks.val.length ≤ 100)
        (hbytes : bytesBW blocks)
        (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ (blocks.val.length : ℤ))
        (r : Aeneas.Std.I64)
        (hr : Aegis.MinimumRecolors.minimum_recolors blocks k = Aeneas.Std.Result.ok r), r.val ≤ (totalWhites blocks : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r = k if and only if blocks[i] = 87 (ASCII 'W') for every i with 0 <= i < len(blocks).
    Preconditions: `blocks` is a slice of bytes with 1 <= len(blocks) <= 100; for every i with 0 <= i < len(blocks), blocks[i] is either 87 (the ASCII code of 'W') or 66 (the ASCII code of 'B'); and k, viewed as an integer, satisfies 1 <= k <= len(blocks). -/
  theorem spec_8 (blocks : ByteSlice) (k : Aeneas.Std.I64)
      (hlen_lb : 1 ≤ blocks.val.length) (hlen_ub : blocks.val.length ≤ 100)
      (hbytes : bytesBW blocks)
      (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ (blocks.val.length : ℤ))
      (r : Aeneas.Std.I64)
      (hr : Aegis.MinimumRecolors.minimum_recolors blocks k = Aeneas.Std.Result.ok r) :
      r.val = k.val ↔ ∀ i : ℕ, i < blocks.val.length → isWhite (blocks.val[i]!) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (blocks : ByteSlice) (k : Aeneas.Std.I64)
        (hlen_lb : 1 ≤ blocks.val.length) (hlen_ub : blocks.val.length ≤ 100)
        (hbytes : bytesBW blocks)
        (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ (blocks.val.length : ℤ))
        (r : Aeneas.Std.I64)
        (hr : Aegis.MinimumRecolors.minimum_recolors blocks k = Aeneas.Std.Result.ok r), r.val = k.val ↔ ∀ i : ℕ, i < blocks.val.length → isWhite (blocks.val[i]!)) := by
    sorry

  end AegisSpec.MinimumRecolors

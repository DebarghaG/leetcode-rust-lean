import Aegis.MinStickers.Code.Funs

/-!
# Specifications of `Aegis.MinStickers.min_stickers`

LeetCode problem `stickers-to-spell-word`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

  namespace AegisSpec.MinStickers

  def isLowerByte (b : Std.U8) : Prop := 97 ≤ b.val ∧ b.val ≤ 122

  def cnt (x : List Std.U8) (c : Std.U8) : ℕ := x.countP (fun b => decide (b = c))

  def ceilDiv (a m : ℕ) : ℕ := (a + m - 1) / m

  def stickerAt (stickers : Slice (alloc.vec.Vec Std.U8)) (j : ℕ) : List Std.U8 :=
    (stickers.val.map (fun v => v.val)).getD j []

  def maxCnt (stickers : Slice (alloc.vec.Vec Std.U8)) (n : ℕ) (c : Std.U8) : ℕ :=
    (Finset.range n).sup (fun j => cnt (stickerAt stickers j) c)

  def maxLen (stickers : Slice (alloc.vec.Vec Std.U8)) (n : ℕ) : ℕ :=
    (Finset.range n).sup (fun j => (stickerAt stickers j).length)

  def spells (stickers : Slice (alloc.vec.Vec Std.U8)) (n : ℕ) (target : Slice Std.U8)
      (m : List ℕ) : Prop :=
    m.length = n ∧
      ∀ c : Std.U8, cnt target.val c ≤
        (Finset.range n).sum (fun j => m.getD j 0 * cnt (stickerAt stickers j) c)

  def spellable (stickers : Slice (alloc.vec.Vec Std.U8)) (n : ℕ)
      (target : Slice Std.U8) : Prop :=
    ∃ m : List ℕ, spells stickers n target m

  def dropOne (m : List ℕ) (j : ℕ) : List ℕ := m.set j (m.getD j 0 - 1)

  /-- Let cnt(x,c) be the number of indices i with 0 <= i < len(x) and x[i] = c. Call a sticker multiset any tuple (m_0,...,m_{n-1}) of nonnegative integers; its size is sum_{j=0}^{n-1} m_j, and it spells target if for every byte c, cnt(target,c) <= sum_{j=0}^{n-1} m_j * cnt(stickers[j],c). Whenever the function returns a result r, the following holds: if no sticker multiset spells target, then r = -1; otherwise r >= 0 and r is the minimum size of a sticker multiset that spells target, i.e., there exists a sticker multiset of size r that spells target, and every sticker multiset that spells target has size at least r.
    Preconditions: n = len(stickers); 1 <= n <= 50; for every j with 0 <= j < n, 1 <= len(stickers[j]) <= 10; 1 <= len(target) <= 15; every byte of every stickers[j] and every byte of target is an ASCII lowercase English letter ('a'..'z'). -/
  theorem spec_1
      (stickers : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8) (n : ℕ)
      (hn : n = stickers.val.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
      (hstickers : ∀ s ∈ stickers.val, 1 ≤ s.val.length ∧ s.val.length ≤ 10)
      (hstickers_byte : ∀ s ∈ stickers.val, ∀ b ∈ s.val, isLowerByte b)
      (htarget : 1 ≤ target.val.length ∧ target.val.length ≤ 15)
      (htarget_byte : ∀ b ∈ target.val, isLowerByte b) :
      ∀ r, Aegis.MinStickers.min_stickers stickers target = ok r →
        ((¬ spellable stickers n target) → r.val = -1) ∧
        (spellable stickers n target →
          0 ≤ r.val ∧
          (∃ m : List ℕ, spells stickers n target m ∧ (m.sum : ℤ) = r.val) ∧
          (∀ m : List ℕ, spells stickers n target m → r.val ≤ (m.sum : ℤ))) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (stickers : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8) (n : ℕ)
        (hn : n = stickers.val.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
        (hstickers : ∀ s ∈ stickers.val, 1 ≤ s.val.length ∧ s.val.length ≤ 10)
        (hstickers_byte : ∀ s ∈ stickers.val, ∀ b ∈ s.val, isLowerByte b)
        (htarget : 1 ≤ target.val.length ∧ target.val.length ≤ 15)
        (htarget_byte : ∀ b ∈ target.val, isLowerByte b), ∀ r, Aegis.MinStickers.min_stickers stickers target = ok r →
          ((¬ spellable stickers n target) → r.val = -1) ∧
          (spellable stickers n target →
            0 ≤ r.val ∧
            (∃ m : List ℕ, spells stickers n target m ∧ (m.sum : ℤ) = r.val) ∧
            (∀ m : List ℕ, spells stickers n target m → r.val ≤ (m.sum : ℤ)))) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result (some Std.I64 value); it does not fail, panic, overflow, or read out of bounds.
    Preconditions: n = len(stickers); 1 <= n <= 50; for every j with 0 <= j < n, 1 <= len(stickers[j]) <= 10; 1 <= len(target) <= 15; every byte of every stickers[j] and every byte of target is an ASCII lowercase English letter ('a'..'z'). -/
  theorem spec_2
      (stickers : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8) (n : ℕ)
      (hn : n = stickers.val.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
      (hstickers : ∀ s ∈ stickers.val, 1 ≤ s.val.length ∧ s.val.length ≤ 10)
      (hstickers_byte : ∀ s ∈ stickers.val, ∀ b ∈ s.val, isLowerByte b)
      (htarget : 1 ≤ target.val.length ∧ target.val.length ≤ 15)
      (htarget_byte : ∀ b ∈ target.val, isLowerByte b) :
      ∃ r : Std.I64, Aegis.MinStickers.min_stickers stickers target = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (stickers : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8) (n : ℕ)
        (hn : n = stickers.val.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
        (hstickers : ∀ s ∈ stickers.val, 1 ≤ s.val.length ∧ s.val.length ≤ 10)
        (hstickers_byte : ∀ s ∈ stickers.val, ∀ b ∈ s.val, isLowerByte b)
        (htarget : 1 ≤ target.val.length ∧ target.val.length ≤ 15)
        (htarget_byte : ∀ b ∈ target.val, isLowerByte b), ∃ r : Std.I64, Aegis.MinStickers.min_stickers stickers target = ok r) := by
    sorry

  /-- Let cnt(x,c) be the number of indices i with 0 <= i < len(x) and x[i] = c. Whenever the function returns a result r, r = -1 if and only if there exists a byte c such that cnt(target,c) > 0 and for every j with 0 <= j < n, cnt(stickers[j],c) = 0.
    Preconditions: n = len(stickers); 1 <= n <= 50; for every j with 0 <= j < n, 1 <= len(stickers[j]) <= 10; 1 <= len(target) <= 15; every byte of every stickers[j] and every byte of target is an ASCII lowercase English letter ('a'..'z'). -/
  theorem spec_3
      (stickers : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8) (n : ℕ)
      (hn : n = stickers.val.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
      (hstickers : ∀ s ∈ stickers.val, 1 ≤ s.val.length ∧ s.val.length ≤ 10)
      (hstickers_byte : ∀ s ∈ stickers.val, ∀ b ∈ s.val, isLowerByte b)
      (htarget : 1 ≤ target.val.length ∧ target.val.length ≤ 15)
      (htarget_byte : ∀ b ∈ target.val, isLowerByte b) :
      ∀ r, Aegis.MinStickers.min_stickers stickers target = ok r →
        (r.val = -1 ↔
          ∃ c : Std.U8, 0 < cnt target.val c ∧ ∀ j, j < n → cnt (stickerAt stickers j) c = 0) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (stickers : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8) (n : ℕ)
        (hn : n = stickers.val.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
        (hstickers : ∀ s ∈ stickers.val, 1 ≤ s.val.length ∧ s.val.length ≤ 10)
        (hstickers_byte : ∀ s ∈ stickers.val, ∀ b ∈ s.val, isLowerByte b)
        (htarget : 1 ≤ target.val.length ∧ target.val.length ≤ 15)
        (htarget_byte : ∀ b ∈ target.val, isLowerByte b), ∀ r, Aegis.MinStickers.min_stickers stickers target = ok r →
          (r.val = -1 ↔
            ∃ c : Std.U8, 0 < cnt target.val c ∧ ∀ j, j < n → cnt (stickerAt stickers j) c = 0)) := by
    sorry

  /-- Whenever the function returns a result r, either r = -1 or 1 <= r <= len(target).
    Preconditions: n = len(stickers); 1 <= n <= 50; for every j with 0 <= j < n, 1 <= len(stickers[j]) <= 10; 1 <= len(target) <= 15; every byte of every stickers[j] and every byte of target is an ASCII lowercase English letter ('a'..'z'). -/
  theorem spec_4
      (stickers : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8) (n : ℕ)
      (hn : n = stickers.val.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
      (hstickers : ∀ s ∈ stickers.val, 1 ≤ s.val.length ∧ s.val.length ≤ 10)
      (hstickers_byte : ∀ s ∈ stickers.val, ∀ b ∈ s.val, isLowerByte b)
      (htarget : 1 ≤ target.val.length ∧ target.val.length ≤ 15)
      (htarget_byte : ∀ b ∈ target.val, isLowerByte b) :
      ∀ r, Aegis.MinStickers.min_stickers stickers target = ok r →
        r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ (target.val.length : ℤ)) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (stickers : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8) (n : ℕ)
        (hn : n = stickers.val.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
        (hstickers : ∀ s ∈ stickers.val, 1 ≤ s.val.length ∧ s.val.length ≤ 10)
        (hstickers_byte : ∀ s ∈ stickers.val, ∀ b ∈ s.val, isLowerByte b)
        (htarget : 1 ≤ target.val.length ∧ target.val.length ≤ 15)
        (htarget_byte : ∀ b ∈ target.val, isLowerByte b), ∀ r, Aegis.MinStickers.min_stickers stickers target = ok r →
          r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ (target.val.length : ℤ))) := by
    sorry

  /-- Let cnt(x,c) be the number of indices i with 0 <= i < len(x) and x[i] = c. Whenever the function returns a result r, r = 1 if and only if there exists j with 0 <= j < n such that for every byte c, cnt(target,c) <= cnt(stickers[j],c).
    Preconditions: n = len(stickers); 1 <= n <= 50; for every j with 0 <= j < n, 1 <= len(stickers[j]) <= 10; 1 <= len(target) <= 15; every byte of every stickers[j] and every byte of target is an ASCII lowercase English letter ('a'..'z'). -/
  theorem spec_5
      (stickers : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8) (n : ℕ)
      (hn : n = stickers.val.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
      (hstickers : ∀ s ∈ stickers.val, 1 ≤ s.val.length ∧ s.val.length ≤ 10)
      (hstickers_byte : ∀ s ∈ stickers.val, ∀ b ∈ s.val, isLowerByte b)
      (htarget : 1 ≤ target.val.length ∧ target.val.length ≤ 15)
      (htarget_byte : ∀ b ∈ target.val, isLowerByte b) :
      ∀ r, Aegis.MinStickers.min_stickers stickers target = ok r →
        (r.val = 1 ↔
          ∃ j, j < n ∧ ∀ c : Std.U8, cnt target.val c ≤ cnt (stickerAt stickers j) c) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (stickers : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8) (n : ℕ)
        (hn : n = stickers.val.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
        (hstickers : ∀ s ∈ stickers.val, 1 ≤ s.val.length ∧ s.val.length ≤ 10)
        (hstickers_byte : ∀ s ∈ stickers.val, ∀ b ∈ s.val, isLowerByte b)
        (htarget : 1 ≤ target.val.length ∧ target.val.length ≤ 15)
        (htarget_byte : ∀ b ∈ target.val, isLowerByte b), ∀ r, Aegis.MinStickers.min_stickers stickers target = ok r →
          (r.val = 1 ↔
            ∃ j, j < n ∧ ∀ c : Std.U8, cnt target.val c ≤ cnt (stickerAt stickers j) c)) := by
    sorry

  /-- Let cnt(x,c) be the number of indices i with 0 <= i < len(x) and x[i] = c. Whenever the function returns a result r, if there is a byte c such that target[i] = c for every i with 0 <= i < len(target), then the following holds. Let M = max_{0 <= j < n} cnt(stickers[j],c). If M = 0 then r = -1; otherwise r = ceil(cnt(target,c)/M), equivalently r = (cnt(target,c) + M - 1) div M.
    Preconditions: n = len(stickers); 1 <= n <= 50; for every j with 0 <= j < n, 1 <= len(stickers[j]) <= 10; 1 <= len(target) <= 15; every byte of every stickers[j] and every byte of target is an ASCII lowercase English letter ('a'..'z'). -/
  theorem spec_6
      (stickers : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8) (n : ℕ)
      (hn : n = stickers.val.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
      (hstickers : ∀ s ∈ stickers.val, 1 ≤ s.val.length ∧ s.val.length ≤ 10)
      (hstickers_byte : ∀ s ∈ stickers.val, ∀ b ∈ s.val, isLowerByte b)
      (htarget : 1 ≤ target.val.length ∧ target.val.length ≤ 15)
      (htarget_byte : ∀ b ∈ target.val, isLowerByte b) :
      ∀ r, Aegis.MinStickers.min_stickers stickers target = ok r →
        ∀ c : Std.U8, (∀ b ∈ target.val, b = c) →
          (maxCnt stickers n c = 0 → r.val = -1) ∧
          (maxCnt stickers n c ≠ 0 →
            r.val = ↑(ceilDiv (cnt target.val c) (maxCnt stickers n c))) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (stickers : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8) (n : ℕ)
        (hn : n = stickers.val.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
        (hstickers : ∀ s ∈ stickers.val, 1 ≤ s.val.length ∧ s.val.length ≤ 10)
        (hstickers_byte : ∀ s ∈ stickers.val, ∀ b ∈ s.val, isLowerByte b)
        (htarget : 1 ≤ target.val.length ∧ target.val.length ≤ 15)
        (htarget_byte : ∀ b ∈ target.val, isLowerByte b), ∀ r, Aegis.MinStickers.min_stickers stickers target = ok r →
          ∀ c : Std.U8, (∀ b ∈ target.val, b = c) →
            (maxCnt stickers n c = 0 → r.val = -1) ∧
            (maxCnt stickers n c ≠ 0 →
              r.val = ↑(ceilDiv (cnt target.val c) (maxCnt stickers n c)))) := by
    sorry

  /-- Let cnt(x,c) be the number of indices i with 0 <= i < len(x) and x[i] = c. Whenever the function returns a result r with r != -1, for every byte c such that cnt(target,c) > 0, let M_c = max_{0 <= j < n} cnt(stickers[j],c). Then M_c > 0 and r * M_c >= cnt(target,c).
    Preconditions: n = len(stickers); 1 <= n <= 50; for every j with 0 <= j < n, 1 <= len(stickers[j]) <= 10; 1 <= len(target) <= 15; every byte of every stickers[j] and every byte of target is an ASCII lowercase English letter ('a'..'z'). -/
  theorem spec_7
      (stickers : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8) (n : ℕ)
      (hn : n = stickers.val.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
      (hstickers : ∀ s ∈ stickers.val, 1 ≤ s.val.length ∧ s.val.length ≤ 10)
      (hstickers_byte : ∀ s ∈ stickers.val, ∀ b ∈ s.val, isLowerByte b)
      (htarget : 1 ≤ target.val.length ∧ target.val.length ≤ 15)
      (htarget_byte : ∀ b ∈ target.val, isLowerByte b) :
      ∀ r, Aegis.MinStickers.min_stickers stickers target = ok r → r.val ≠ -1 →
        ∀ c : Std.U8, 0 < cnt target.val c →
          0 < maxCnt stickers n c ∧
          (cnt target.val c : ℤ) ≤ r.val * (maxCnt stickers n c : ℤ) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (stickers : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8) (n : ℕ)
        (hn : n = stickers.val.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
        (hstickers : ∀ s ∈ stickers.val, 1 ≤ s.val.length ∧ s.val.length ≤ 10)
        (hstickers_byte : ∀ s ∈ stickers.val, ∀ b ∈ s.val, isLowerByte b)
        (htarget : 1 ≤ target.val.length ∧ target.val.length ≤ 15)
        (htarget_byte : ∀ b ∈ target.val, isLowerByte b), ∀ r, Aegis.MinStickers.min_stickers stickers target = ok r → r.val ≠ -1 →
          ∀ c : Std.U8, 0 < cnt target.val c →
            0 < maxCnt stickers n c ∧
            (cnt target.val c : ℤ) ≤ r.val * (maxCnt stickers n c : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r with r != -1, let L = max_{0 <= j < n} len(stickers[j]); then r * L >= len(target).
    Preconditions: n = len(stickers); 1 <= n <= 50; for every j with 0 <= j < n, 1 <= len(stickers[j]) <= 10; 1 <= len(target) <= 15; every byte of every stickers[j] and every byte of target is an ASCII lowercase English letter ('a'..'z'). -/
  theorem spec_8
      (stickers : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8) (n : ℕ)
      (hn : n = stickers.val.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
      (hstickers : ∀ s ∈ stickers.val, 1 ≤ s.val.length ∧ s.val.length ≤ 10)
      (hstickers_byte : ∀ s ∈ stickers.val, ∀ b ∈ s.val, isLowerByte b)
      (htarget : 1 ≤ target.val.length ∧ target.val.length ≤ 15)
      (htarget_byte : ∀ b ∈ target.val, isLowerByte b) :
      ∀ r, Aegis.MinStickers.min_stickers stickers target = ok r → r.val ≠ -1 →
        (target.val.length : ℤ) ≤ r.val * (maxLen stickers n : ℤ) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (stickers : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8) (n : ℕ)
        (hn : n = stickers.val.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
        (hstickers : ∀ s ∈ stickers.val, 1 ≤ s.val.length ∧ s.val.length ≤ 10)
        (hstickers_byte : ∀ s ∈ stickers.val, ∀ b ∈ s.val, isLowerByte b)
        (htarget : 1 ≤ target.val.length ∧ target.val.length ≤ 15)
        (htarget_byte : ∀ b ∈ target.val, isLowerByte b), ∀ r, Aegis.MinStickers.min_stickers stickers target = ok r → r.val ≠ -1 →
          (target.val.length : ℤ) ≤ r.val * (maxLen stickers n : ℤ)) := by
    sorry

  /-- Let cnt(x,c) be the number of indices i with 0 <= i < len(x) and x[i] = c. Whenever the function returns a result r with r >= 0, there exist nonnegative integers m_0,...,m_{n-1} such that sum_{j=0}^{n-1} m_j = r, and for every byte c, cnt(target,c) <= sum_{j=0}^{n-1} m_j * cnt(stickers[j],c); moreover, for every j with m_j > 0, decreasing m_j by 1 while leaving all other m_k unchanged gives a multiset that does not spell target (i.e., some byte c then violates the displayed inequality).
    Preconditions: n = len(stickers); 1 <= n <= 50; for every j with 0 <= j < n, 1 <= len(stickers[j]) <= 10; 1 <= len(target) <= 15; every byte of every stickers[j] and every byte of target is an ASCII lowercase English letter ('a'..'z'). -/
  theorem spec_9
      (stickers : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8) (n : ℕ)
      (hn : n = stickers.val.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
      (hstickers : ∀ s ∈ stickers.val, 1 ≤ s.val.length ∧ s.val.length ≤ 10)
      (hstickers_byte : ∀ s ∈ stickers.val, ∀ b ∈ s.val, isLowerByte b)
      (htarget : 1 ≤ target.val.length ∧ target.val.length ≤ 15)
      (htarget_byte : ∀ b ∈ target.val, isLowerByte b) :
      ∀ r, Aegis.MinStickers.min_stickers stickers target = ok r → 0 ≤ r.val →
        ∃ m : List ℕ, spells stickers n target m ∧ (m.sum : ℤ) = r.val ∧
          ∀ j, j < n → 0 < m.getD j 0 → ¬ spells stickers n target (dropOne m j) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (stickers : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8) (n : ℕ)
        (hn : n = stickers.val.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
        (hstickers : ∀ s ∈ stickers.val, 1 ≤ s.val.length ∧ s.val.length ≤ 10)
        (hstickers_byte : ∀ s ∈ stickers.val, ∀ b ∈ s.val, isLowerByte b)
        (htarget : 1 ≤ target.val.length ∧ target.val.length ≤ 15)
        (htarget_byte : ∀ b ∈ target.val, isLowerByte b), ∀ r, Aegis.MinStickers.min_stickers stickers target = ok r → 0 ≤ r.val →
          ∃ m : List ℕ, spells stickers n target m ∧ (m.sum : ℤ) = r.val ∧
            ∀ j, j < n → 0 < m.getD j 0 → ¬ spells stickers n target (dropOne m j)) := by
    sorry

  /-- Whenever min_stickers(stickers,target) returns a result r and min_stickers(stickers',target) returns a result r', we have r = r'.
    Preconditions: n = len(stickers); 1 <= n <= 50; for every j with 0 <= j < n, 1 <= len(stickers[j]) <= 10; 1 <= len(target) <= 15; every byte of every stickers[j] and every byte of target is an ASCII lowercase English letter ('a'..'z'). Also let stickers' be any slice of length n such that there is a permutation pi of {0,...,n-1} with stickers'[i] = stickers[pi(i)] for all i. -/
  theorem spec_10
      (stickers : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8) (n : ℕ)
      (hn : n = stickers.val.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
      (hstickers : ∀ s ∈ stickers.val, 1 ≤ s.val.length ∧ s.val.length ≤ 10)
      (hstickers_byte : ∀ s ∈ stickers.val, ∀ b ∈ s.val, isLowerByte b)
      (htarget : 1 ≤ target.val.length ∧ target.val.length ≤ 15)
      (htarget_byte : ∀ b ∈ target.val, isLowerByte b)
      (stickers' : Slice (alloc.vec.Vec Std.U8))
      (hperm : stickers'.val.Perm stickers.val) :
      ∀ r r', Aegis.MinStickers.min_stickers stickers target = ok r →
        Aegis.MinStickers.min_stickers stickers' target = ok r' → r.val = r'.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (stickers : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8) (n : ℕ)
        (hn : n = stickers.val.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
        (hstickers : ∀ s ∈ stickers.val, 1 ≤ s.val.length ∧ s.val.length ≤ 10)
        (hstickers_byte : ∀ s ∈ stickers.val, ∀ b ∈ s.val, isLowerByte b)
        (htarget : 1 ≤ target.val.length ∧ target.val.length ≤ 15)
        (htarget_byte : ∀ b ∈ target.val, isLowerByte b)
        (stickers' : Slice (alloc.vec.Vec Std.U8))
        (hperm : stickers'.val.Perm stickers.val), ∀ r r', Aegis.MinStickers.min_stickers stickers target = ok r →
          Aegis.MinStickers.min_stickers stickers' target = ok r' → r.val = r'.val) := by
    sorry

  /-- Whenever min_stickers(stickers,target) returns a result r and min_stickers(stickers'',target) returns a result r'', we have r = r''.
    Preconditions: n = len(stickers); 1 <= n <= 50; for every j with 0 <= j < n, 1 <= len(stickers[j]) <= 10; 1 <= len(target) <= 15; every byte of every stickers[j] and every byte of target is an ASCII lowercase English letter ('a'..'z'). Suppose n >= 2 and there exist distinct indices j,k with 0 <= j < n, 0 <= k < n, and stickers[j] = stickers[k]. Let stickers'' be the slice of length n-1 obtained by deleting index k from stickers. -/
  theorem spec_11
      (stickers : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8) (n : ℕ)
      (hn : n = stickers.val.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
      (hstickers : ∀ s ∈ stickers.val, 1 ≤ s.val.length ∧ s.val.length ≤ 10)
      (hstickers_byte : ∀ s ∈ stickers.val, ∀ b ∈ s.val, isLowerByte b)
      (htarget : 1 ≤ target.val.length ∧ target.val.length ≤ 15)
      (htarget_byte : ∀ b ∈ target.val, isLowerByte b)
      (hn_ge_two : 2 ≤ n) (j k : ℕ) (hj : j < n) (hk : k < n) (hjk : j ≠ k)
      (hdup : stickerAt stickers j = stickerAt stickers k)
      (stickers'' : Slice (alloc.vec.Vec Std.U8))
      (hdel : stickers''.val = stickers.val.eraseIdx k) :
      ∀ r r'', Aegis.MinStickers.min_stickers stickers target = ok r →
        Aegis.MinStickers.min_stickers stickers'' target = ok r'' → r.val = r''.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (stickers : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8) (n : ℕ)
        (hn : n = stickers.val.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
        (hstickers : ∀ s ∈ stickers.val, 1 ≤ s.val.length ∧ s.val.length ≤ 10)
        (hstickers_byte : ∀ s ∈ stickers.val, ∀ b ∈ s.val, isLowerByte b)
        (htarget : 1 ≤ target.val.length ∧ target.val.length ≤ 15)
        (htarget_byte : ∀ b ∈ target.val, isLowerByte b)
        (hn_ge_two : 2 ≤ n) (j k : ℕ) (hj : j < n) (hk : k < n) (hjk : j ≠ k)
        (hdup : stickerAt stickers j = stickerAt stickers k)
        (stickers'' : Slice (alloc.vec.Vec Std.U8))
        (hdel : stickers''.val = stickers.val.eraseIdx k), ∀ r r'', Aegis.MinStickers.min_stickers stickers target = ok r →
          Aegis.MinStickers.min_stickers stickers'' target = ok r'' → r.val = r''.val) := by
    sorry

  /-- Whenever min_stickers(stickers,target) returns a result r and min_stickers(stickers+,target) returns a result r+, if r >= 0 then r+ >= 0 and r+ <= r.
    Preconditions: n = len(stickers); 1 <= n <= 50; for every j with 0 <= j < n, 1 <= len(stickers[j]) <= 10; 1 <= len(target) <= 15; every byte of every stickers[j] and every byte of target is an ASCII lowercase English letter ('a'..'z'). Suppose n <= 49. Let w be any byte sequence of ASCII lowercase English letters with 1 <= len(w) <= 10, and let stickers+ be any slice of length n+1 whose entries are exactly the entries of stickers together with one extra entry w. -/
  theorem spec_12
      (stickers : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8) (n : ℕ)
      (hn : n = stickers.val.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
      (hstickers : ∀ s ∈ stickers.val, 1 ≤ s.val.length ∧ s.val.length ≤ 10)
      (hstickers_byte : ∀ s ∈ stickers.val, ∀ b ∈ s.val, isLowerByte b)
      (htarget : 1 ≤ target.val.length ∧ target.val.length ≤ 15)
      (htarget_byte : ∀ b ∈ target.val, isLowerByte b)
      (hn49 : n ≤ 49) (w : alloc.vec.Vec Std.U8)
      (hw : 1 ≤ w.val.length ∧ w.val.length ≤ 10)
      (hw_byte : ∀ b ∈ w.val, isLowerByte b)
      (stickersPlus : Slice (alloc.vec.Vec Std.U8))
      (hplus : stickersPlus.val.Perm (w :: stickers.val)) :
      ∀ r rPlus, Aegis.MinStickers.min_stickers stickers target = ok r →
        Aegis.MinStickers.min_stickers stickersPlus target = ok rPlus →
        0 ≤ r.val → 0 ≤ rPlus.val ∧ rPlus.val ≤ r.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (stickers : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8) (n : ℕ)
        (hn : n = stickers.val.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
        (hstickers : ∀ s ∈ stickers.val, 1 ≤ s.val.length ∧ s.val.length ≤ 10)
        (hstickers_byte : ∀ s ∈ stickers.val, ∀ b ∈ s.val, isLowerByte b)
        (htarget : 1 ≤ target.val.length ∧ target.val.length ≤ 15)
        (htarget_byte : ∀ b ∈ target.val, isLowerByte b)
        (hn49 : n ≤ 49) (w : alloc.vec.Vec Std.U8)
        (hw : 1 ≤ w.val.length ∧ w.val.length ≤ 10)
        (hw_byte : ∀ b ∈ w.val, isLowerByte b)
        (stickersPlus : Slice (alloc.vec.Vec Std.U8))
        (hplus : stickersPlus.val.Perm (w :: stickers.val)), ∀ r rPlus, Aegis.MinStickers.min_stickers stickers target = ok r →
          Aegis.MinStickers.min_stickers stickersPlus target = ok rPlus →
          0 ≤ r.val → 0 ≤ rPlus.val ∧ rPlus.val ≤ r.val) := by
    sorry

  /-- Let cnt(x,c) be the number of indices i with 0 <= i < len(x) and x[i] = c. Suppose cnt(t,c) <= cnt(t',c) for every byte c. Whenever min_stickers(stickers,t') returns a result r' with r' != -1, the call min_stickers(stickers,t) returns a result r with r != -1 and r <= r'.
    Preconditions: n = len(stickers); 1 <= n <= 50; for every j with 0 <= j < n, 1 <= len(stickers[j]) <= 10; every byte of every stickers[j] is an ASCII lowercase English letter ('a'..'z'). Let t and t' be two target byte sequences, each of length between 1 and 15 and consisting entirely of ASCII lowercase English letters. -/
  theorem spec_13
      (stickers : Slice (alloc.vec.Vec Std.U8)) (n : ℕ)
      (hn : n = stickers.val.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
      (hstickers : ∀ s ∈ stickers.val, 1 ≤ s.val.length ∧ s.val.length ≤ 10)
      (hstickers_byte : ∀ s ∈ stickers.val, ∀ b ∈ s.val, isLowerByte b)
      (t t' : Slice Std.U8)
      (ht : 1 ≤ t.val.length ∧ t.val.length ≤ 15)
      (ht_byte : ∀ b ∈ t.val, isLowerByte b)
      (ht' : 1 ≤ t'.val.length ∧ t'.val.length ≤ 15)
      (ht'_byte : ∀ b ∈ t'.val, isLowerByte b)
      (hcnt : ∀ c : Std.U8, cnt t.val c ≤ cnt t'.val c) :
      ∀ r', Aegis.MinStickers.min_stickers stickers t' = ok r' → r'.val ≠ -1 →
        ∃ r, Aegis.MinStickers.min_stickers stickers t = ok r ∧ r.val ≠ -1 ∧ r.val ≤ r'.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (stickers : Slice (alloc.vec.Vec Std.U8)) (n : ℕ)
        (hn : n = stickers.val.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
        (hstickers : ∀ s ∈ stickers.val, 1 ≤ s.val.length ∧ s.val.length ≤ 10)
        (hstickers_byte : ∀ s ∈ stickers.val, ∀ b ∈ s.val, isLowerByte b)
        (t t' : Slice Std.U8)
        (ht : 1 ≤ t.val.length ∧ t.val.length ≤ 15)
        (ht_byte : ∀ b ∈ t.val, isLowerByte b)
        (ht' : 1 ≤ t'.val.length ∧ t'.val.length ≤ 15)
        (ht'_byte : ∀ b ∈ t'.val, isLowerByte b)
        (hcnt : ∀ c : Std.U8, cnt t.val c ≤ cnt t'.val c), ∀ r', Aegis.MinStickers.min_stickers stickers t' = ok r' → r'.val ≠ -1 →
          ∃ r, Aegis.MinStickers.min_stickers stickers t = ok r ∧ r.val ≠ -1 ∧ r.val ≤ r'.val) := by
    sorry

  /-- Whenever min_stickers(stickers,target) returns a result r and min_stickers(stickers,target') returns a result r', we have r = r'.
    Preconditions: n = len(stickers); 1 <= n <= 50; for every j with 0 <= j < n, 1 <= len(stickers[j]) <= 10; 1 <= len(target) <= 15; every byte of every stickers[j] and every byte of target is an ASCII lowercase English letter ('a'..'z'). Let target' be any byte sequence of ASCII lowercase English letters with 1 <= len(target') <= 15 such that for every byte c, cnt(target',c) = cnt(target,c), where cnt(x,c) is the number of indices i with 0 <= i < len(x) and x[i] = c. -/
  theorem spec_14
      (stickers : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8) (n : ℕ)
      (hn : n = stickers.val.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
      (hstickers : ∀ s ∈ stickers.val, 1 ≤ s.val.length ∧ s.val.length ≤ 10)
      (hstickers_byte : ∀ s ∈ stickers.val, ∀ b ∈ s.val, isLowerByte b)
      (htarget : 1 ≤ target.val.length ∧ target.val.length ≤ 15)
      (htarget_byte : ∀ b ∈ target.val, isLowerByte b)
      (target' : Slice Std.U8)
      (htarget' : 1 ≤ target'.val.length ∧ target'.val.length ≤ 15)
      (htarget'_byte : ∀ b ∈ target'.val, isLowerByte b)
      (hcnt : ∀ c : Std.U8, cnt target'.val c = cnt target.val c) :
      ∀ r r', Aegis.MinStickers.min_stickers stickers target = ok r →
        Aegis.MinStickers.min_stickers stickers target' = ok r' → r.val = r'.val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (stickers : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8) (n : ℕ)
        (hn : n = stickers.val.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
        (hstickers : ∀ s ∈ stickers.val, 1 ≤ s.val.length ∧ s.val.length ≤ 10)
        (hstickers_byte : ∀ s ∈ stickers.val, ∀ b ∈ s.val, isLowerByte b)
        (htarget : 1 ≤ target.val.length ∧ target.val.length ≤ 15)
        (htarget_byte : ∀ b ∈ target.val, isLowerByte b)
        (target' : Slice Std.U8)
        (htarget' : 1 ≤ target'.val.length ∧ target'.val.length ≤ 15)
        (htarget'_byte : ∀ b ∈ target'.val, isLowerByte b)
        (hcnt : ∀ c : Std.U8, cnt target'.val c = cnt target.val c), ∀ r r', Aegis.MinStickers.min_stickers stickers target = ok r →
          Aegis.MinStickers.min_stickers stickers target' = ok r' → r.val = r'.val) := by
    sorry

  end AegisSpec.MinStickers

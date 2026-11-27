import Aegis.MinimumWhiteTiles.Code.Funs

/-!
# Specifications of `Aegis.MinimumWhiteTiles.minimum_white_tiles`

LeetCode problem `minimum-white-tiles-after-covering-with-carpets`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MinimumWhiteTiles

namespace AegisSpec.MinimumWhiteTiles

def IsWhiteByte (b : Std.U8) : Bool := b.val == 49

def FloorBytes (f : List Std.U8) : Prop := ∀ b ∈ f, b.val = 48 ∨ b.val = 49

def WhiteCount (f : List Std.U8) : ℕ := (f.filter IsWhiteByte).length

def IsWhiteAt (f : List Std.U8) (i : ℕ) : Bool := (f[i]?).map (fun b => b.val) == some 49

def Covers (L s i : ℕ) : Prop := s ≤ i ∧ i < s + L

def coversB (L s i : ℕ) : Bool := decide (s ≤ i) && decide (i < s + L)

def uncoveredB (L : ℕ) (starts : List ℕ) (i : ℕ) : Bool := starts.all (fun s => !coversB L s i)

def RemainingWhite (f : List Std.U8) (L : ℕ) (starts : List ℕ) : ℕ :=
  ((List.range f.length).filter (fun i => IsWhiteAt f i && uncoveredB L starts i)).length

def IsPlacement (f : List Std.U8) (k L : ℕ) (starts : List ℕ) : Prop :=
  starts.length ≤ k ∧ ∀ s ∈ starts, s + L ≤ f.length

def Achievable (f : List Std.U8) (k L : ℕ) (v : ℤ) : Prop :=
  ∃ starts : List ℕ, IsPlacement f k L starts ∧ v = (RemainingWhite f L starts : ℤ)

def WindowWhite (f : List Std.U8) (L s : ℕ) : ℕ :=
  ((List.range f.length).filter (fun i => IsWhiteAt f i && coversB L s i)).length

def MaxWindowWhite (f : List Std.U8) (L : ℕ) : ℕ :=
  (List.range (f.length + 1)).foldr
    (fun s acc => if s + L ≤ f.length then Nat.max (WindowWhite f L s) acc else acc) 0

def RevFloor (f : List Std.U8) : List Std.U8 := f.reverse

/-- The function returns a result r and r is the minimum, over all finite sequences of starts s_1,...,s_m with 0 <= m <= numCarpets and 0 <= s_j <= n - carpetLen for every j, of the number of indices i with 0 <= i < n, floor[i] = 49, and i not in [s_j, s_j + carpetLen) for every j. Equivalently, r is the minimum number of white tiles visible after covering tiles by at most numCarpets carpets, each covering carpetLen consecutive tiles, with overlaps allowed; a carpet with start s covers indices s through s + carpetLen - 1.
  Preconditions: Let n = len(floor). 1 <= carpetLen <= n <= 1000, 1 <= numCarpets <= 1000, and for every i with 0 <= i < n, floor[i] is either 48 (the byte '0') or 49 (the byte '1'). -/
theorem spec_1 (floor : Slice Std.U8) (numCarpets carpetLen : Std.I64)
    (hLpos : 1 ≤ carpetLen.val) (hLlen : carpetLen.val ≤ (floor.val.length : ℤ))
    (hlen : floor.val.length ≤ 1000)
    (hkpos : 1 ≤ numCarpets.val) (hkle : numCarpets.val ≤ 1000)
    (hbytes : FloorBytes floor.val) :
    ∃ r : Std.I64,
      minimum_white_tiles floor numCarpets carpetLen = ok r ∧
        Achievable floor.val numCarpets.val.toNat carpetLen.val.toNat r.val ∧
        (∀ v : ℤ,
          Achievable floor.val numCarpets.val.toNat carpetLen.val.toNat v → r.val ≤ v) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (floor : Slice Std.U8) (numCarpets carpetLen : Std.I64)
    (hLpos : 1 ≤ carpetLen.val) (hLlen : carpetLen.val ≤ (floor.val.length : ℤ))
    (hlen : floor.val.length ≤ 1000)
    (hkpos : 1 ≤ numCarpets.val) (hkle : numCarpets.val ≤ 1000)
    (hbytes : FloorBytes floor.val), ∃ r : Std.I64,
      minimum_white_tiles floor numCarpets carpetLen = ok r ∧
        Achievable floor.val numCarpets.val.toNat carpetLen.val.toNat r.val ∧
        (∀ v : ℤ,
          Achievable floor.val numCarpets.val.toNat carpetLen.val.toNat v → r.val ≤ v)) := by
  sorry

/-- The function returns a result r; it does not fail, overflow, or panic.
  Preconditions: Let n = len(floor). 1 <= carpetLen <= n <= 1000, 1 <= numCarpets <= 1000, and for every i with 0 <= i < n, floor[i] is either 48 (the byte '0') or 49 (the byte '1'). -/
theorem spec_2 (floor : Slice Std.U8) (numCarpets carpetLen : Std.I64)
    (hLpos : 1 ≤ carpetLen.val) (hLlen : carpetLen.val ≤ (floor.val.length : ℤ))
    (hlen : floor.val.length ≤ 1000)
    (hkpos : 1 ≤ numCarpets.val) (hkle : numCarpets.val ≤ 1000)
    (hbytes : FloorBytes floor.val) :
    ∃ r : Std.I64, minimum_white_tiles floor numCarpets carpetLen = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (floor : Slice Std.U8) (numCarpets carpetLen : Std.I64)
    (hLpos : 1 ≤ carpetLen.val) (hLlen : carpetLen.val ≤ (floor.val.length : ℤ))
    (hlen : floor.val.length ≤ 1000)
    (hkpos : 1 ≤ numCarpets.val) (hkle : numCarpets.val ≤ 1000)
    (hbytes : FloorBytes floor.val), ∃ r : Std.I64, minimum_white_tiles floor numCarpets carpetLen = ok r) := by
  sorry

/-- The function returns a result r and 0 <= r <= W, where W is the number of indices i with 0 <= i < n and floor[i] = 49.
  Preconditions: Let n = len(floor). 1 <= carpetLen <= n <= 1000, 1 <= numCarpets <= 1000, and for every i with 0 <= i < n, floor[i] is either 48 (the byte '0') or 49 (the byte '1'). -/
theorem spec_3 (floor : Slice Std.U8) (numCarpets carpetLen : Std.I64)
    (hLpos : 1 ≤ carpetLen.val) (hLlen : carpetLen.val ≤ (floor.val.length : ℤ))
    (hlen : floor.val.length ≤ 1000)
    (hkpos : 1 ≤ numCarpets.val) (hkle : numCarpets.val ≤ 1000)
    (hbytes : FloorBytes floor.val) :
    ∃ r : Std.I64,
      minimum_white_tiles floor numCarpets carpetLen = ok r ∧
        0 ≤ r.val ∧ r.val ≤ (WhiteCount floor.val : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (floor : Slice Std.U8) (numCarpets carpetLen : Std.I64)
    (hLpos : 1 ≤ carpetLen.val) (hLlen : carpetLen.val ≤ (floor.val.length : ℤ))
    (hlen : floor.val.length ≤ 1000)
    (hkpos : 1 ≤ numCarpets.val) (hkle : numCarpets.val ≤ 1000)
    (hbytes : FloorBytes floor.val), ∃ r : Std.I64,
      minimum_white_tiles floor numCarpets carpetLen = ok r ∧
        0 ≤ r.val ∧ r.val ≤ (WhiteCount floor.val : ℤ)) := by
  sorry

/-- The function returns a result r and r >= max(0, W - numCarpets * carpetLen), where W is the number of indices i with 0 <= i < n and floor[i] = 49, and numCarpets * carpetLen is mathematical integer multiplication.
  Preconditions: Let n = len(floor). 1 <= carpetLen <= n <= 1000, 1 <= numCarpets <= 1000, and for every i with 0 <= i < n, floor[i] is either 48 (the byte '0') or 49 (the byte '1'). -/
theorem spec_4 (floor : Slice Std.U8) (numCarpets carpetLen : Std.I64)
    (hLpos : 1 ≤ carpetLen.val) (hLlen : carpetLen.val ≤ (floor.val.length : ℤ))
    (hlen : floor.val.length ≤ 1000)
    (hkpos : 1 ≤ numCarpets.val) (hkle : numCarpets.val ≤ 1000)
    (hbytes : FloorBytes floor.val) :
    ∃ r : Std.I64,
      minimum_white_tiles floor numCarpets carpetLen = ok r ∧
        max 0 ((WhiteCount floor.val : ℤ) - numCarpets.val * carpetLen.val) ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (floor : Slice Std.U8) (numCarpets carpetLen : Std.I64)
    (hLpos : 1 ≤ carpetLen.val) (hLlen : carpetLen.val ≤ (floor.val.length : ℤ))
    (hlen : floor.val.length ≤ 1000)
    (hkpos : 1 ≤ numCarpets.val) (hkle : numCarpets.val ≤ 1000)
    (hbytes : FloorBytes floor.val), ∃ r : Std.I64,
      minimum_white_tiles floor numCarpets carpetLen = ok r ∧
        max 0 ((WhiteCount floor.val : ℤ) - numCarpets.val * carpetLen.val) ≤ r.val) := by
  sorry

/-- The function returns a result r and r <= W - M, where W is the number of indices i with 0 <= i < n and floor[i] = 49, and M is the maximum, over all starts s with 0 <= s <= n - carpetLen, of the number of indices i with s <= i < s + carpetLen and floor[i] = 49.
  Preconditions: Let n = len(floor). 1 <= carpetLen <= n <= 1000, 1 <= numCarpets <= 1000, and for every i with 0 <= i < n, floor[i] is either 48 (the byte '0') or 49 (the byte '1'). -/
theorem spec_5 (floor : Slice Std.U8) (numCarpets carpetLen : Std.I64)
    (hLpos : 1 ≤ carpetLen.val) (hLlen : carpetLen.val ≤ (floor.val.length : ℤ))
    (hlen : floor.val.length ≤ 1000)
    (hkpos : 1 ≤ numCarpets.val) (hkle : numCarpets.val ≤ 1000)
    (hbytes : FloorBytes floor.val) :
    ∃ r : Std.I64,
      minimum_white_tiles floor numCarpets carpetLen = ok r ∧
        r.val ≤ (WhiteCount floor.val : ℤ) - (MaxWindowWhite floor.val carpetLen.val.toNat : ℤ) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (floor : Slice Std.U8) (numCarpets carpetLen : Std.I64)
    (hLpos : 1 ≤ carpetLen.val) (hLlen : carpetLen.val ≤ (floor.val.length : ℤ))
    (hlen : floor.val.length ≤ 1000)
    (hkpos : 1 ≤ numCarpets.val) (hkle : numCarpets.val ≤ 1000)
    (hbytes : FloorBytes floor.val), ∃ r : Std.I64,
      minimum_white_tiles floor numCarpets carpetLen = ok r ∧
        r.val ≤ (WhiteCount floor.val : ℤ) - (MaxWindowWhite floor.val carpetLen.val.toNat : ℤ)) := by
  sorry

/-- The function returns a result r and r = 0.
  Preconditions: Let n = len(floor). 1 <= carpetLen <= n <= 1000, 1 <= numCarpets <= 1000, for every i with 0 <= i < n, floor[i] is either 48 (the byte '0') or 49 (the byte '1'), and numCarpets * carpetLen >= n for mathematical integer multiplication. -/
theorem spec_6 (floor : Slice Std.U8) (numCarpets carpetLen : Std.I64)
    (hLpos : 1 ≤ carpetLen.val) (hLlen : carpetLen.val ≤ (floor.val.length : ℤ))
    (hlen : floor.val.length ≤ 1000)
    (hkpos : 1 ≤ numCarpets.val) (hkle : numCarpets.val ≤ 1000)
    (hbytes : FloorBytes floor.val)
    (hcover : (floor.val.length : ℤ) ≤ numCarpets.val * carpetLen.val) :
    ∃ r : Std.I64,
      minimum_white_tiles floor numCarpets carpetLen = ok r ∧ r.val = 0 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (floor : Slice Std.U8) (numCarpets carpetLen : Std.I64)
    (hLpos : 1 ≤ carpetLen.val) (hLlen : carpetLen.val ≤ (floor.val.length : ℤ))
    (hlen : floor.val.length ≤ 1000)
    (hkpos : 1 ≤ numCarpets.val) (hkle : numCarpets.val ≤ 1000)
    (hbytes : FloorBytes floor.val)
    (hcover : (floor.val.length : ℤ) ≤ numCarpets.val * carpetLen.val), ∃ r : Std.I64,
      minimum_white_tiles floor numCarpets carpetLen = ok r ∧ r.val = 0) := by
  sorry

/-- The function returns a result r and r = W - M, where W is the number of indices i with 0 <= i < n and floor[i] = 49, and M is the maximum, over all starts s with 0 <= s <= n - carpetLen, of the number of indices i with s <= i < s + carpetLen and floor[i] = 49.
  Preconditions: Let n = len(floor). 1 <= carpetLen <= n <= 1000, numCarpets = 1, and for every i with 0 <= i < n, floor[i] is either 48 (the byte '0') or 49 (the byte '1'). -/
theorem spec_7 (floor : Slice Std.U8) (numCarpets carpetLen : Std.I64)
    (hLpos : 1 ≤ carpetLen.val) (hLlen : carpetLen.val ≤ (floor.val.length : ℤ))
    (hlen : floor.val.length ≤ 1000)
    (hk : numCarpets.val = 1)
    (hbytes : FloorBytes floor.val) :
    ∃ r : Std.I64,
      minimum_white_tiles floor numCarpets carpetLen = ok r ∧
        r.val = (WhiteCount floor.val : ℤ) - (MaxWindowWhite floor.val carpetLen.val.toNat : ℤ) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (floor : Slice Std.U8) (numCarpets carpetLen : Std.I64)
    (hLpos : 1 ≤ carpetLen.val) (hLlen : carpetLen.val ≤ (floor.val.length : ℤ))
    (hlen : floor.val.length ≤ 1000)
    (hk : numCarpets.val = 1)
    (hbytes : FloorBytes floor.val), ∃ r : Std.I64,
      minimum_white_tiles floor numCarpets carpetLen = ok r ∧
        r.val = (WhiteCount floor.val : ℤ) - (MaxWindowWhite floor.val carpetLen.val.toNat : ℤ)) := by
  sorry

/-- The function returns a result r and r = max(0, W - numCarpets), where W is the number of indices i with 0 <= i < n and floor[i] = 49.
  Preconditions: Let n = len(floor). carpetLen = 1, 1 <= n <= 1000, 1 <= numCarpets <= 1000, and for every i with 0 <= i < n, floor[i] is either 48 (the byte '0') or 49 (the byte '1'). -/
theorem spec_8 (floor : Slice Std.U8) (numCarpets carpetLen : Std.I64)
    (hL : carpetLen.val = 1) (hlen : 1 ≤ floor.val.length) (hlen' : floor.val.length ≤ 1000)
    (hkpos : 1 ≤ numCarpets.val) (hkle : numCarpets.val ≤ 1000)
    (hbytes : FloorBytes floor.val) :
    ∃ r : Std.I64,
      minimum_white_tiles floor numCarpets carpetLen = ok r ∧
        r.val = max 0 ((WhiteCount floor.val : ℤ) - numCarpets.val) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (floor : Slice Std.U8) (numCarpets carpetLen : Std.I64)
    (hL : carpetLen.val = 1) (hlen : 1 ≤ floor.val.length) (hlen' : floor.val.length ≤ 1000)
    (hkpos : 1 ≤ numCarpets.val) (hkle : numCarpets.val ≤ 1000)
    (hbytes : FloorBytes floor.val), ∃ r : Std.I64,
      minimum_white_tiles floor numCarpets carpetLen = ok r ∧
        r.val = max 0 ((WhiteCount floor.val : ℤ) - numCarpets.val)) := by
  sorry

/-- The function returns a result r and r = max(0, n - numCarpets * carpetLen), where numCarpets * carpetLen is mathematical integer multiplication.
  Preconditions: Let n = len(floor). 1 <= carpetLen <= n <= 1000, 1 <= numCarpets <= 1000, and floor[i] = 49 for every i with 0 <= i < n. -/
theorem spec_9 (floor : Slice Std.U8) (numCarpets carpetLen : Std.I64)
    (hLpos : 1 ≤ carpetLen.val) (hLlen : carpetLen.val ≤ (floor.val.length : ℤ))
    (hlen : floor.val.length ≤ 1000)
    (hkpos : 1 ≤ numCarpets.val) (hkle : numCarpets.val ≤ 1000)
    (hwhite : ∀ b ∈ floor.val, b.val = 49) :
    ∃ r : Std.I64,
      minimum_white_tiles floor numCarpets carpetLen = ok r ∧
        r.val = max 0 ((floor.val.length : ℤ) - numCarpets.val * carpetLen.val) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (floor : Slice Std.U8) (numCarpets carpetLen : Std.I64)
    (hLpos : 1 ≤ carpetLen.val) (hLlen : carpetLen.val ≤ (floor.val.length : ℤ))
    (hlen : floor.val.length ≤ 1000)
    (hkpos : 1 ≤ numCarpets.val) (hkle : numCarpets.val ≤ 1000)
    (hwhite : ∀ b ∈ floor.val, b.val = 49), ∃ r : Std.I64,
      minimum_white_tiles floor numCarpets carpetLen = ok r ∧
        r.val = max 0 ((floor.val.length : ℤ) - numCarpets.val * carpetLen.val)) := by
  sorry

/-- If r1 is the result returned by the function on (floor, k1, carpetLen) and r2 is the result returned by the function on (floor, k2, carpetLen), then r2 <= r1.
  Preconditions: Let n = len(floor). 1 <= carpetLen <= n <= 1000, for every i with 0 <= i < n, floor[i] is either 48 (the byte '0') or 49 (the byte '1'), and 1 <= k1 <= k2 <= 1000. -/
theorem spec_10 (floor : Slice Std.U8) (k1 k2 carpetLen : Std.I64)
    (hLpos : 1 ≤ carpetLen.val) (hLlen : carpetLen.val ≤ (floor.val.length : ℤ))
    (hlen : floor.val.length ≤ 1000)
    (hbytes : FloorBytes floor.val)
    (hk1 : 1 ≤ k1.val) (hk12 : k1.val ≤ k2.val) (hk2 : k2.val ≤ 1000) :
    ∀ r1 r2 : Std.I64,
      minimum_white_tiles floor k1 carpetLen = ok r1 →
        minimum_white_tiles floor k2 carpetLen = ok r2 → r2.val ≤ r1.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (floor : Slice Std.U8) (k1 k2 carpetLen : Std.I64)
    (hLpos : 1 ≤ carpetLen.val) (hLlen : carpetLen.val ≤ (floor.val.length : ℤ))
    (hlen : floor.val.length ≤ 1000)
    (hbytes : FloorBytes floor.val)
    (hk1 : 1 ≤ k1.val) (hk12 : k1.val ≤ k2.val) (hk2 : k2.val ≤ 1000), ∀ r1 r2 : Std.I64,
      minimum_white_tiles floor k1 carpetLen = ok r1 →
        minimum_white_tiles floor k2 carpetLen = ok r2 → r2.val ≤ r1.val) := by
  sorry

/-- If r1 is the result returned by the function on (floor, k, L1) and r2 is the result returned by the function on (floor, k, L2), then r2 <= r1.
  Preconditions: Let n = len(floor). 1 <= k <= 1000, 1 <= L1 <= L2 <= n <= 1000, and for every i with 0 <= i < n, floor[i] is either 48 (the byte '0') or 49 (the byte '1'). -/
theorem spec_11 (floor : Slice Std.U8) (k L1 L2 : Std.I64)
    (hkpos : 1 ≤ k.val) (hkle : k.val ≤ 1000)
    (hL1pos : 1 ≤ L1.val) (hL12 : L1.val ≤ L2.val)
    (hL2 : L2.val ≤ (floor.val.length : ℤ))
    (hlen : floor.val.length ≤ 1000)
    (hbytes : FloorBytes floor.val) :
    ∀ r1 r2 : Std.I64,
      minimum_white_tiles floor k L1 = ok r1 →
        minimum_white_tiles floor k L2 = ok r2 → r2.val ≤ r1.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (floor : Slice Std.U8) (k L1 L2 : Std.I64)
    (hkpos : 1 ≤ k.val) (hkle : k.val ≤ 1000)
    (hL1pos : 1 ≤ L1.val) (hL12 : L1.val ≤ L2.val)
    (hL2 : L2.val ≤ (floor.val.length : ℤ))
    (hlen : floor.val.length ≤ 1000)
    (hbytes : FloorBytes floor.val), ∀ r1 r2 : Std.I64,
      minimum_white_tiles floor k L1 = ok r1 →
        minimum_white_tiles floor k L2 = ok r2 → r2.val ≤ r1.val) := by
  sorry

/-- If r1 is the result returned by the function on (floor1, k, carpetLen) and r2 is the result returned by the function on (floor2, k, carpetLen), then r1 <= r2.
  Preconditions: Let n = len(floor). 1 <= carpetLen <= n <= 1000, 1 <= k <= 1000, and floor1 and floor2 are byte slices of length n with every entry either 48 or 49. For every i with 0 <= i < n, floor1[i] <= floor2[i] as integers, meaning floor2 is obtained from floor1 by changing zero or more bytes '0' to '1'. -/
theorem spec_12 (floor1 floor2 : Slice Std.U8) (k carpetLen : Std.I64)
    (hLpos : 1 ≤ carpetLen.val) (hLlen : carpetLen.val ≤ (floor1.val.length : ℤ))
    (hlen : floor1.val.length ≤ 1000)
    (hkpos : 1 ≤ k.val) (hkle : k.val ≤ 1000)
    (hbytes1 : FloorBytes floor1.val) (hbytes2 : FloorBytes floor2.val)
    (hlen2 : floor2.val.length = floor1.val.length)
    (hmono : ∀ (i : ℕ) (b1 b2 : Std.U8),
      floor1.val[i]? = some b1 → floor2.val[i]? = some b2 → (b1.val : ℤ) ≤ (b2.val : ℤ)) :
    ∀ r1 r2 : Std.I64,
      minimum_white_tiles floor1 k carpetLen = ok r1 →
        minimum_white_tiles floor2 k carpetLen = ok r2 → r1.val ≤ r2.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (floor1 floor2 : Slice Std.U8) (k carpetLen : Std.I64)
    (hLpos : 1 ≤ carpetLen.val) (hLlen : carpetLen.val ≤ (floor1.val.length : ℤ))
    (hlen : floor1.val.length ≤ 1000)
    (hkpos : 1 ≤ k.val) (hkle : k.val ≤ 1000)
    (hbytes1 : FloorBytes floor1.val) (hbytes2 : FloorBytes floor2.val)
    (hlen2 : floor2.val.length = floor1.val.length)
    (hmono : ∀ (i : ℕ) (b1 b2 : Std.U8),
      floor1.val[i]? = some b1 → floor2.val[i]? = some b2 → (b1.val : ℤ) ≤ (b2.val : ℤ)), ∀ r1 r2 : Std.I64,
      minimum_white_tiles floor1 k carpetLen = ok r1 →
        minimum_white_tiles floor2 k carpetLen = ok r2 → r1.val ≤ r2.val) := by
  sorry

/-- If r is the result returned by the function on (floor, numCarpets, carpetLen) and rrev is the result returned by the function on (rev, numCarpets, carpetLen), then rrev = r.
  Preconditions: Let n = len(floor). 1 <= carpetLen <= n <= 1000, 1 <= numCarpets <= 1000, and for every i with 0 <= i < n, floor[i] is either 48 (the byte '0') or 49 (the byte '1'). Let rev be the byte slice of length n defined by rev[i] = floor[n - 1 - i] for 0 <= i < n. -/
theorem spec_13 (floor rev : Slice Std.U8) (numCarpets carpetLen : Std.I64)
    (hLpos : 1 ≤ carpetLen.val) (hLlen : carpetLen.val ≤ (floor.val.length : ℤ))
    (hlen : floor.val.length ≤ 1000)
    (hkpos : 1 ≤ numCarpets.val) (hkle : numCarpets.val ≤ 1000)
    (hbytes : FloorBytes floor.val)
    (hrev : rev.val = RevFloor floor.val) :
    ∀ r rrev : Std.I64,
      minimum_white_tiles floor numCarpets carpetLen = ok r →
        minimum_white_tiles rev numCarpets carpetLen = ok rrev → rrev.val = r.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (floor rev : Slice Std.U8) (numCarpets carpetLen : Std.I64)
    (hLpos : 1 ≤ carpetLen.val) (hLlen : carpetLen.val ≤ (floor.val.length : ℤ))
    (hlen : floor.val.length ≤ 1000)
    (hkpos : 1 ≤ numCarpets.val) (hkle : numCarpets.val ≤ 1000)
    (hbytes : FloorBytes floor.val)
    (hrev : rev.val = RevFloor floor.val), ∀ r rrev : Std.I64,
      minimum_white_tiles floor numCarpets carpetLen = ok r →
        minimum_white_tiles rev numCarpets carpetLen = ok rrev → rrev.val = r.val) := by
  sorry

end AegisSpec.MinimumWhiteTiles

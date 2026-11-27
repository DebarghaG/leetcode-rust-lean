import Aegis.IpToCidr.Code.Funs

/-!
# Specifications of `Aegis.IpToCidr.ip_to_cidr`

LeetCode problem `ip-to-cidr`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.IpToCidr

namespace AegisSpec.IpToCidr

def byteOf (c : ℕ) : U8 := ⟨BitVec.ofNat 8 c⟩

def dotByte : U8 := byteOf 46

def slashByte : U8 := byteOf 47

structure IsCanonicalDecimal (s : List U8) (v : ℕ) : Prop where
  ne_nil : s ≠ []
  is_digit : ∀ c ∈ s, 48 ≤ c.val ∧ c.val ≤ 57
  no_leading_zero : ∀ (c : U8) (rest : List U8), s = c :: rest → rest ≠ [] → c.val ≠ 48
  value_eq : v = s.foldl (fun acc c => acc * 10 + (c.val - 48)) 0

def IsDottedDecimal (s : List U8) (I : ℕ) : Prop :=
  ∃ (a b c d : ℕ) (sa sb sc sd : List U8),
    IsCanonicalDecimal sa a ∧ IsCanonicalDecimal sb b ∧ IsCanonicalDecimal sc c ∧
      IsCanonicalDecimal sd d ∧
      a ≤ 255 ∧ b ≤ 255 ∧ c ≤ 255 ∧ d ≤ 255 ∧
      s = sa ++ dotByte :: sb ++ dotByte :: sc ++ dotByte :: sd ∧
      I = 256 ^ 3 * a + 256 ^ 2 * b + 256 * c + d

def Covers (b k x : ℕ) : Prop :=
  x < 2 ^ 32 ∧ x / 2 ^ (32 - k) = b / 2 ^ (32 - k)

def BlockSize (k : ℕ) : ℕ := 2 ^ (32 - k)

def InRange (I N x : ℕ) : Prop := I ≤ x ∧ x < I + N

structure EncodesBlock (s : List U8) (b k : ℕ) : Prop where
  base_lt : b < 2 ^ 32
  prefix_le : k ≤ 32
  decomp : ∃ sb sk : List U8,
    IsDottedDecimal sb b ∧ IsCanonicalDecimal sk k ∧ s = sb ++ slashByte :: sk

def CoversExactly (b k I N : ℕ) : Prop := ∀ x, Covers b k x ↔ InRange I N x

def UnionCovers (ss : List (List U8)) (x : ℕ) : Prop :=
  ∃ s ∈ ss, ∃ b k : ℕ, EncodesBlock s b k ∧ Covers b k x

def UnionEqRange (ss : List (List U8)) (I N : ℕ) : Prop :=
  ∀ x, UnionCovers ss x ↔ InRange I N x

def CoveredAt (ss : List (List U8)) (x j : ℕ) : Prop :=
  ∃ (hj : j < ss.length) (b k : ℕ), EncodesBlock (ss.get ⟨j, hj⟩) b k ∧ Covers b k x

def blockStrings (r : alloc.vec.Vec (alloc.vec.Vec U8)) : List (List U8) :=
  r.val.map (fun s => s.val)

def NVal (n : I64) : ℕ := n.val.toNat

/-- Let R = {x : I <= x < I+n}. The function returns a result r = [s_0,...,s_{m-1}] (m = len(r)) such that: (1) each s_j encodes exactly one CIDR block (b_j,k_j); (2) the union of C(b_j,k_j) over j with 0 <= j < m equals R; (3) m is minimal: for every finite list t of byte strings each encoding a CIDR block, if the union of the covered sets of the blocks encoded by t equals R, then m <= len(t). The order of the s_j is irrelevant.
  Preconditions: Let I be the 32-bit integer represented by ip: ip is a valid IPv4 ASCII byte slice of the form a.b.c.d with 0 <= a,b,c,d <= 255 and I = 256^3*a + 256^2*b + 256*c + d. Preconditions: 7 <= len(ip) <= 15; ip is a valid IPv4 address in this sense; 1 <= n <= 1000; I + n - 1 <= 2^32 - 1. For a CIDR block (b,k) with 0 <= b < 2^32 and 0 <= k <= 32, let C(b,k) = {x : 0 <= x < 2^32 and x / 2^(32-k) = b / 2^(32-k)} (integer division; k=0 gives all 32-bit x, k=32 gives {b}). A byte string encodes (b,k) iff it is the ASCII concatenation of the canonical dotted-decimal encoding of b, the byte '/', and the canonical decimal encoding of k. -/
theorem spec_1 (ip : Slice U8) (n : I64) (I : ℕ)
    (h_ip : IsDottedDecimal ip.val I)
    (h_len_lo : 7 ≤ ip.val.length) (h_len_hi : ip.val.length ≤ 15)
    (h_n_lo : 1 ≤ n.val) (h_n_hi : n.val ≤ 1000)
    (h_top : (I : ℤ) + n.val ≤ 2 ^ 32) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec U8),
      ip_to_cidr ip n = ok r ∧
        (∀ s ∈ blockStrings r, ∃ b k : ℕ, EncodesBlock s b k) ∧
        UnionEqRange (blockStrings r) I (NVal n) ∧
        (∀ t : List (List U8),
          UnionEqRange t I (NVal n) → (blockStrings r).length ≤ t.length) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (ip : Slice U8) (n : I64) (I : ℕ)
    (h_ip : IsDottedDecimal ip.val I)
    (h_len_lo : 7 ≤ ip.val.length) (h_len_hi : ip.val.length ≤ 15)
    (h_n_lo : 1 ≤ n.val) (h_n_hi : n.val ≤ 1000)
    (h_top : (I : ℤ) + n.val ≤ 2 ^ 32), ∃ r : alloc.vec.Vec (alloc.vec.Vec U8),
      ip_to_cidr ip n = ok r ∧
        (∀ s ∈ blockStrings r, ∃ b k : ℕ, EncodesBlock s b k) ∧
        UnionEqRange (blockStrings r) I (NVal n) ∧
        (∀ t : List (List U8),
          UnionEqRange t I (NVal n) → (blockStrings r).length ≤ t.length)) := by
  sorry

/-- The function returns a result r for every input satisfying the preconditions; it does not fail, panic, overflow, or go out of bounds.
  Preconditions: Let I be the 32-bit integer represented by ip: ip is a valid IPv4 ASCII byte slice of the form a.b.c.d with 0 <= a,b,c,d <= 255 and I = 256^3*a + 256^2*b + 256*c + d. Preconditions: 7 <= len(ip) <= 15; ip is a valid IPv4 address in this sense; 1 <= n <= 1000; I + n - 1 <= 2^32 - 1. -/
theorem spec_2 (ip : Slice U8) (n : I64) (I : ℕ)
    (h_ip : IsDottedDecimal ip.val I)
    (h_len_lo : 7 ≤ ip.val.length) (h_len_hi : ip.val.length ≤ 15)
    (h_n_lo : 1 ≤ n.val) (h_n_hi : n.val ≤ 1000)
    (h_top : (I : ℤ) + n.val ≤ 2 ^ 32) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec U8), ip_to_cidr ip n = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (ip : Slice U8) (n : I64) (I : ℕ)
    (h_ip : IsDottedDecimal ip.val I)
    (h_len_lo : 7 ≤ ip.val.length) (h_len_hi : ip.val.length ≤ 15)
    (h_n_lo : 1 ≤ n.val) (h_n_hi : n.val ≤ 1000)
    (h_top : (I : ℤ) + n.val ≤ 2 ^ 32), ∃ r : alloc.vec.Vec (alloc.vec.Vec U8), ip_to_cidr ip n = ok r) := by
  sorry

/-- Whenever the function returns a result r, for every j with 0 <= j < len(r), the byte vector r[j] is the ASCII concatenation of the canonical dotted-decimal encoding of some integer b_j with 0 <= b_j < 2^32, the byte '/', and the canonical decimal encoding of some integer k_j with 0 <= k_j <= 32. Canonical decimal means no leading zeros except for the single digit 0.
  Preconditions: Let I be the 32-bit integer represented by ip: ip is a valid IPv4 ASCII byte slice of the form a.b.c.d with 0 <= a,b,c,d <= 255 and I = 256^3*a + 256^2*b + 256*c + d. Preconditions: 7 <= len(ip) <= 15; ip is a valid IPv4 address in this sense; 1 <= n <= 1000; I + n - 1 <= 2^32 - 1. -/
theorem spec_3 (ip : Slice U8) (n : I64) (I : ℕ)
    (h_ip : IsDottedDecimal ip.val I)
    (h_len_lo : 7 ≤ ip.val.length) (h_len_hi : ip.val.length ≤ 15)
    (h_n_lo : 1 ≤ n.val) (h_n_hi : n.val ≤ 1000)
    (h_top : (I : ℤ) + n.val ≤ 2 ^ 32)
    (r : alloc.vec.Vec (alloc.vec.Vec U8)) (h_r : ip_to_cidr ip n = ok r) :
    ∀ (j : ℕ) (hj : j < (blockStrings r).length),
      ∃ b k : ℕ, EncodesBlock ((blockStrings r).get ⟨j, hj⟩) b k := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (ip : Slice U8) (n : I64) (I : ℕ)
    (h_ip : IsDottedDecimal ip.val I)
    (h_len_lo : 7 ≤ ip.val.length) (h_len_hi : ip.val.length ≤ 15)
    (h_n_lo : 1 ≤ n.val) (h_n_hi : n.val ≤ 1000)
    (h_top : (I : ℤ) + n.val ≤ 2 ^ 32)
    (r : alloc.vec.Vec (alloc.vec.Vec U8)) (h_r : ip_to_cidr ip n = ok r), ∀ (j : ℕ) (hj : j < (blockStrings r).length),
      ∃ b k : ℕ, EncodesBlock ((blockStrings r).get ⟨j, hj⟩) b k) := by
  sorry

/-- Whenever the function returns a result r, for every j with 0 <= j < len(r), if r[j] encodes the CIDR block (b_j,k_j), then C(b_j,k_j) is a subset of R = {x : I <= x < I+n}. Thus no returned block covers an IP address outside the required range.
  Preconditions: Let I be the 32-bit integer represented by ip: ip is a valid IPv4 ASCII byte slice of the form a.b.c.d with 0 <= a,b,c,d <= 255 and I = 256^3*a + 256^2*b + 256*c + d. Preconditions: 7 <= len(ip) <= 15; ip is a valid IPv4 address in this sense; 1 <= n <= 1000; I + n - 1 <= 2^32 - 1. For a CIDR block (b,k) with 0 <= b < 2^32 and 0 <= k <= 32, let C(b,k) = {x : 0 <= x < 2^32 and x / 2^(32-k) = b / 2^(32-k)} (integer division). A byte string encodes (b,k) iff it is the canonical dotted-decimal encoding of b followed by '/' and the canonical decimal encoding of k. -/
theorem spec_4 (ip : Slice U8) (n : I64) (I : ℕ)
    (h_ip : IsDottedDecimal ip.val I)
    (h_len_lo : 7 ≤ ip.val.length) (h_len_hi : ip.val.length ≤ 15)
    (h_n_lo : 1 ≤ n.val) (h_n_hi : n.val ≤ 1000)
    (h_top : (I : ℤ) + n.val ≤ 2 ^ 32)
    (r : alloc.vec.Vec (alloc.vec.Vec U8)) (h_r : ip_to_cidr ip n = ok r) :
    ∀ (j : ℕ) (hj : j < (blockStrings r).length) (b k : ℕ),
      EncodesBlock ((blockStrings r).get ⟨j, hj⟩) b k →
        ∀ x : ℕ, Covers b k x → InRange I (NVal n) x := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (ip : Slice U8) (n : I64) (I : ℕ)
    (h_ip : IsDottedDecimal ip.val I)
    (h_len_lo : 7 ≤ ip.val.length) (h_len_hi : ip.val.length ≤ 15)
    (h_n_lo : 1 ≤ n.val) (h_n_hi : n.val ≤ 1000)
    (h_top : (I : ℤ) + n.val ≤ 2 ^ 32)
    (r : alloc.vec.Vec (alloc.vec.Vec U8)) (h_r : ip_to_cidr ip n = ok r), ∀ (j : ℕ) (hj : j < (blockStrings r).length) (b k : ℕ),
      EncodesBlock ((blockStrings r).get ⟨j, hj⟩) b k →
        ∀ x : ℕ, Covers b k x → InRange I (NVal n) x) := by
  sorry

/-- Whenever the function returns a result r, for every address x with I <= x < I+n, there exists j with 0 <= j < len(r) such that x is in C(b_j,k_j), where r[j] encodes (b_j,k_j). Thus every required address is covered.
  Preconditions: Let I be the 32-bit integer represented by ip: ip is a valid IPv4 ASCII byte slice of the form a.b.c.d with 0 <= a,b,c,d <= 255 and I = 256^3*a + 256^2*b + 256*c + d. Preconditions: 7 <= len(ip) <= 15; ip is a valid IPv4 address in this sense; 1 <= n <= 1000; I + n - 1 <= 2^32 - 1. For a CIDR block (b,k) with 0 <= b < 2^32 and 0 <= k <= 32, let C(b,k) = {x : 0 <= x < 2^32 and x / 2^(32-k) = b / 2^(32-k)} (integer division). A byte string encodes (b,k) iff it is the canonical dotted-decimal encoding of b followed by '/' and the canonical decimal encoding of k. -/
theorem spec_5 (ip : Slice U8) (n : I64) (I : ℕ)
    (h_ip : IsDottedDecimal ip.val I)
    (h_len_lo : 7 ≤ ip.val.length) (h_len_hi : ip.val.length ≤ 15)
    (h_n_lo : 1 ≤ n.val) (h_n_hi : n.val ≤ 1000)
    (h_top : (I : ℤ) + n.val ≤ 2 ^ 32)
    (r : alloc.vec.Vec (alloc.vec.Vec U8)) (h_r : ip_to_cidr ip n = ok r) :
    ∀ x : ℕ, InRange I (NVal n) x → ∃ j : ℕ, CoveredAt (blockStrings r) x j := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (ip : Slice U8) (n : I64) (I : ℕ)
    (h_ip : IsDottedDecimal ip.val I)
    (h_len_lo : 7 ≤ ip.val.length) (h_len_hi : ip.val.length ≤ 15)
    (h_n_lo : 1 ≤ n.val) (h_n_hi : n.val ≤ 1000)
    (h_top : (I : ℤ) + n.val ≤ 2 ^ 32)
    (r : alloc.vec.Vec (alloc.vec.Vec U8)) (h_r : ip_to_cidr ip n = ok r), ∀ x : ℕ, InRange I (NVal n) x → ∃ j : ℕ, CoveredAt (blockStrings r) x j) := by
  sorry

/-- Whenever the function returns a result r, for every address x with I <= x < I+n, there is exactly one j with 0 <= j < len(r) such that x is in C(b_j,k_j), where r[j] encodes (b_j,k_j).
  Preconditions: Let I be the 32-bit integer represented by ip: ip is a valid IPv4 ASCII byte slice of the form a.b.c.d with 0 <= a,b,c,d <= 255 and I = 256^3*a + 256^2*b + 256*c + d. Preconditions: 7 <= len(ip) <= 15; ip is a valid IPv4 address in this sense; 1 <= n <= 1000; I + n - 1 <= 2^32 - 1. For a CIDR block (b,k) with 0 <= b < 2^32 and 0 <= k <= 32, let C(b,k) = {x : 0 <= x < 2^32 and x / 2^(32-k) = b / 2^(32-k)} (integer division). A byte string encodes (b,k) iff it is the canonical dotted-decimal encoding of b followed by '/' and the canonical decimal encoding of k. -/
theorem spec_6 (ip : Slice U8) (n : I64) (I : ℕ)
    (h_ip : IsDottedDecimal ip.val I)
    (h_len_lo : 7 ≤ ip.val.length) (h_len_hi : ip.val.length ≤ 15)
    (h_n_lo : 1 ≤ n.val) (h_n_hi : n.val ≤ 1000)
    (h_top : (I : ℤ) + n.val ≤ 2 ^ 32)
    (r : alloc.vec.Vec (alloc.vec.Vec U8)) (h_r : ip_to_cidr ip n = ok r) :
    ∀ x : ℕ, InRange I (NVal n) x → ∃! j : ℕ, CoveredAt (blockStrings r) x j := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (ip : Slice U8) (n : I64) (I : ℕ)
    (h_ip : IsDottedDecimal ip.val I)
    (h_len_lo : 7 ≤ ip.val.length) (h_len_hi : ip.val.length ≤ 15)
    (h_n_lo : 1 ≤ n.val) (h_n_hi : n.val ≤ 1000)
    (h_top : (I : ℤ) + n.val ≤ 2 ^ 32)
    (r : alloc.vec.Vec (alloc.vec.Vec U8)) (h_r : ip_to_cidr ip n = ok r), ∀ x : ℕ, InRange I (NVal n) x → ∃! j : ℕ, CoveredAt (blockStrings r) x j) := by
  sorry

/-- Whenever the function returns a result r, with r[j] encoding (b_j,k_j) for each j, the sum over j = 0 to len(r)-1 of 2^(32-k_j) equals n.
  Preconditions: Let I be the 32-bit integer represented by ip: ip is a valid IPv4 ASCII byte slice of the form a.b.c.d with 0 <= a,b,c,d <= 255 and I = 256^3*a + 256^2*b + 256*c + d. Preconditions: 7 <= len(ip) <= 15; ip is a valid IPv4 address in this sense; 1 <= n <= 1000; I + n - 1 <= 2^32 - 1. For a CIDR block (b,k) with 0 <= b < 2^32 and 0 <= k <= 32, let C(b,k) = {x : 0 <= x < 2^32 and x / 2^(32-k) = b / 2^(32-k)} (integer division). A byte string encodes (b,k) iff it is the canonical dotted-decimal encoding of b followed by '/' and the canonical decimal encoding of k. -/
theorem spec_7 (ip : Slice U8) (n : I64) (I : ℕ)
    (h_ip : IsDottedDecimal ip.val I)
    (h_len_lo : 7 ≤ ip.val.length) (h_len_hi : ip.val.length ≤ 15)
    (h_n_lo : 1 ≤ n.val) (h_n_hi : n.val ≤ 1000)
    (h_top : (I : ℤ) + n.val ≤ 2 ^ 32)
    (r : alloc.vec.Vec (alloc.vec.Vec U8)) (h_r : ip_to_cidr ip n = ok r) :
    ∀ (b k : ℕ → ℕ),
      (∀ (j : ℕ) (hj : j < (blockStrings r).length),
          EncodesBlock ((blockStrings r).get ⟨j, hj⟩) (b j) (k j)) →
        Finset.sum (Finset.range (blockStrings r).length) (fun j => BlockSize (k j)) =
          NVal n := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (ip : Slice U8) (n : I64) (I : ℕ)
    (h_ip : IsDottedDecimal ip.val I)
    (h_len_lo : 7 ≤ ip.val.length) (h_len_hi : ip.val.length ≤ 15)
    (h_n_lo : 1 ≤ n.val) (h_n_hi : n.val ≤ 1000)
    (h_top : (I : ℤ) + n.val ≤ 2 ^ 32)
    (r : alloc.vec.Vec (alloc.vec.Vec U8)) (h_r : ip_to_cidr ip n = ok r), ∀ (b k : ℕ → ℕ),
      (∀ (j : ℕ) (hj : j < (blockStrings r).length),
          EncodesBlock ((blockStrings r).get ⟨j, hj⟩) (b j) (k j)) →
        Finset.sum (Finset.range (blockStrings r).length) (fun j => BlockSize (k j)) =
          NVal n) := by
  sorry

/-- Whenever the function returns a result r, for every finite list t of byte strings each encoding a CIDR block, if the union of the covered sets of the blocks encoded by t equals R = {x : I <= x < I+n}, then len(r) <= len(t). Equivalently, len(r) is the minimum possible number of CIDR blocks whose covered sets have union R.
  Preconditions: Let I be the 32-bit integer represented by ip: ip is a valid IPv4 ASCII byte slice of the form a.b.c.d with 0 <= a,b,c,d <= 255 and I = 256^3*a + 256^2*b + 256*c + d. Preconditions: 7 <= len(ip) <= 15; ip is a valid IPv4 address in this sense; 1 <= n <= 1000; I + n - 1 <= 2^32 - 1. For a CIDR block (b,k) with 0 <= b < 2^32 and 0 <= k <= 32, let C(b,k) = {x : 0 <= x < 2^32 and x / 2^(32-k) = b / 2^(32-k)} (integer division). A byte string encodes (b,k) iff it is the canonical dotted-decimal encoding of b followed by '/' and the canonical decimal encoding of k. -/
theorem spec_8 (ip : Slice U8) (n : I64) (I : ℕ)
    (h_ip : IsDottedDecimal ip.val I)
    (h_len_lo : 7 ≤ ip.val.length) (h_len_hi : ip.val.length ≤ 15)
    (h_n_lo : 1 ≤ n.val) (h_n_hi : n.val ≤ 1000)
    (h_top : (I : ℤ) + n.val ≤ 2 ^ 32)
    (r : alloc.vec.Vec (alloc.vec.Vec U8)) (h_r : ip_to_cidr ip n = ok r) :
    ∀ t : List (List U8),
      UnionEqRange t I (NVal n) → (blockStrings r).length ≤ t.length := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (ip : Slice U8) (n : I64) (I : ℕ)
    (h_ip : IsDottedDecimal ip.val I)
    (h_len_lo : 7 ≤ ip.val.length) (h_len_hi : ip.val.length ≤ 15)
    (h_n_lo : 1 ≤ n.val) (h_n_hi : n.val ≤ 1000)
    (h_top : (I : ℤ) + n.val ≤ 2 ^ 32)
    (r : alloc.vec.Vec (alloc.vec.Vec U8)) (h_r : ip_to_cidr ip n = ok r), ∀ t : List (List U8),
      UnionEqRange t I (NVal n) → (blockStrings r).length ≤ t.length) := by
  sorry

/-- Whenever the function returns a result r, for every j with 0 <= j < len(r), removing the block r[j] leaves at least one address of R uncovered: the union of C(b_i,k_i) over all i with 0 <= i < len(r) and i != j is not equal to R = {x : I <= x < I+n}.
  Preconditions: Let I be the 32-bit integer represented by ip: ip is a valid IPv4 ASCII byte slice of the form a.b.c.d with 0 <= a,b,c,d <= 255 and I = 256^3*a + 256^2*b + 256*c + d. Preconditions: 7 <= len(ip) <= 15; ip is a valid IPv4 address in this sense; 1 <= n <= 1000; I + n - 1 <= 2^32 - 1. For a CIDR block (b,k) with 0 <= b < 2^32 and 0 <= k <= 32, let C(b,k) = {x : 0 <= x < 2^32 and x / 2^(32-k) = b / 2^(32-k)} (integer division). A byte string encodes (b,k) iff it is the canonical dotted-decimal encoding of b followed by '/' and the canonical decimal encoding of k. -/
theorem spec_9 (ip : Slice U8) (n : I64) (I : ℕ)
    (h_ip : IsDottedDecimal ip.val I)
    (h_len_lo : 7 ≤ ip.val.length) (h_len_hi : ip.val.length ≤ 15)
    (h_n_lo : 1 ≤ n.val) (h_n_hi : n.val ≤ 1000)
    (h_top : (I : ℤ) + n.val ≤ 2 ^ 32)
    (r : alloc.vec.Vec (alloc.vec.Vec U8)) (h_r : ip_to_cidr ip n = ok r) :
    ∀ (j : ℕ) (hj : j < (blockStrings r).length) (b k : ℕ → ℕ),
      (∀ (i : ℕ) (hi : i < (blockStrings r).length),
          EncodesBlock ((blockStrings r).get ⟨i, hi⟩) (b i) (k i)) →
        ¬ (∀ x : ℕ,
            (∃ (i : ℕ) (hi : i < (blockStrings r).length), i ≠ j ∧ Covers (b i) (k i) x) ↔
              InRange I (NVal n) x) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (ip : Slice U8) (n : I64) (I : ℕ)
    (h_ip : IsDottedDecimal ip.val I)
    (h_len_lo : 7 ≤ ip.val.length) (h_len_hi : ip.val.length ≤ 15)
    (h_n_lo : 1 ≤ n.val) (h_n_hi : n.val ≤ 1000)
    (h_top : (I : ℤ) + n.val ≤ 2 ^ 32)
    (r : alloc.vec.Vec (alloc.vec.Vec U8)) (h_r : ip_to_cidr ip n = ok r), ∀ (j : ℕ) (hj : j < (blockStrings r).length) (b k : ℕ → ℕ),
      (∀ (i : ℕ) (hi : i < (blockStrings r).length),
          EncodesBlock ((blockStrings r).get ⟨i, hi⟩) (b i) (k i)) →
        ¬ (∀ x : ℕ,
            (∃ (i : ℕ) (hi : i < (blockStrings r).length), i ≠ j ∧ Covers (b i) (k i) x) ↔
              InRange I (NVal n) x)) := by
  sorry

/-- Whenever the function returns a result r, for every j with 0 <= j < len(r), if r[j] encodes (b_j,k_j), then I <= b_j < I+n.
  Preconditions: Let I be the 32-bit integer represented by ip: ip is a valid IPv4 ASCII byte slice of the form a.b.c.d with 0 <= a,b,c,d <= 255 and I = 256^3*a + 256^2*b + 256*c + d. Preconditions: 7 <= len(ip) <= 15; ip is a valid IPv4 address in this sense; 1 <= n <= 1000; I + n - 1 <= 2^32 - 1. For a CIDR block (b,k) with 0 <= b < 2^32 and 0 <= k <= 32, let C(b,k) = {x : 0 <= x < 2^32 and x / 2^(32-k) = b / 2^(32-k)} (integer division). A byte string encodes (b,k) iff it is the canonical dotted-decimal encoding of b followed by '/' and the canonical decimal encoding of k. -/
theorem spec_10 (ip : Slice U8) (n : I64) (I : ℕ)
    (h_ip : IsDottedDecimal ip.val I)
    (h_len_lo : 7 ≤ ip.val.length) (h_len_hi : ip.val.length ≤ 15)
    (h_n_lo : 1 ≤ n.val) (h_n_hi : n.val ≤ 1000)
    (h_top : (I : ℤ) + n.val ≤ 2 ^ 32)
    (r : alloc.vec.Vec (alloc.vec.Vec U8)) (h_r : ip_to_cidr ip n = ok r) :
    ∀ (j : ℕ) (hj : j < (blockStrings r).length) (b k : ℕ),
      EncodesBlock ((blockStrings r).get ⟨j, hj⟩) b k → I ≤ b ∧ b < I + NVal n := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (ip : Slice U8) (n : I64) (I : ℕ)
    (h_ip : IsDottedDecimal ip.val I)
    (h_len_lo : 7 ≤ ip.val.length) (h_len_hi : ip.val.length ≤ 15)
    (h_n_lo : 1 ≤ n.val) (h_n_hi : n.val ≤ 1000)
    (h_top : (I : ℤ) + n.val ≤ 2 ^ 32)
    (r : alloc.vec.Vec (alloc.vec.Vec U8)) (h_r : ip_to_cidr ip n = ok r), ∀ (j : ℕ) (hj : j < (blockStrings r).length) (b k : ℕ),
      EncodesBlock ((blockStrings r).get ⟨j, hj⟩) b k → I ≤ b ∧ b < I + NVal n) := by
  sorry

/-- Whenever the function returns a result r, for every j with 0 <= j < len(r), if r[j] encodes (b_j,k_j), then 2^(32-k_j) <= n. Equivalently, the number of addresses covered by any single returned block is at most the total number n of addresses that must be covered.
  Preconditions: Let I be the 32-bit integer represented by ip: ip is a valid IPv4 ASCII byte slice of the form a.b.c.d with 0 <= a,b,c,d <= 255 and I = 256^3*a + 256^2*b + 256*c + d. Preconditions: 7 <= len(ip) <= 15; ip is a valid IPv4 address in this sense; 1 <= n <= 1000; I + n - 1 <= 2^32 - 1. For a CIDR block (b,k) with 0 <= b < 2^32 and 0 <= k <= 32, let C(b,k) = {x : 0 <= x < 2^32 and x / 2^(32-k) = b / 2^(32-k)} (integer division). A byte string encodes (b,k) iff it is the canonical dotted-decimal encoding of b followed by '/' and the canonical decimal encoding of k. -/
theorem spec_11 (ip : Slice U8) (n : I64) (I : ℕ)
    (h_ip : IsDottedDecimal ip.val I)
    (h_len_lo : 7 ≤ ip.val.length) (h_len_hi : ip.val.length ≤ 15)
    (h_n_lo : 1 ≤ n.val) (h_n_hi : n.val ≤ 1000)
    (h_top : (I : ℤ) + n.val ≤ 2 ^ 32)
    (r : alloc.vec.Vec (alloc.vec.Vec U8)) (h_r : ip_to_cidr ip n = ok r) :
    ∀ (j : ℕ) (hj : j < (blockStrings r).length) (b k : ℕ),
      EncodesBlock ((blockStrings r).get ⟨j, hj⟩) b k → BlockSize k ≤ NVal n := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (ip : Slice U8) (n : I64) (I : ℕ)
    (h_ip : IsDottedDecimal ip.val I)
    (h_len_lo : 7 ≤ ip.val.length) (h_len_hi : ip.val.length ≤ 15)
    (h_n_lo : 1 ≤ n.val) (h_n_hi : n.val ≤ 1000)
    (h_top : (I : ℤ) + n.val ≤ 2 ^ 32)
    (r : alloc.vec.Vec (alloc.vec.Vec U8)) (h_r : ip_to_cidr ip n = ok r), ∀ (j : ℕ) (hj : j < (blockStrings r).length) (b k : ℕ),
      EncodesBlock ((blockStrings r).get ⟨j, hj⟩) b k → BlockSize k ≤ NVal n) := by
  sorry

/-- Whenever the function returns a result r, len(r) <= 64.
  Preconditions: Let I be the 32-bit integer represented by ip: ip is a valid IPv4 ASCII byte slice of the form a.b.c.d with 0 <= a,b,c,d <= 255 and I = 256^3*a + 256^2*b + 256*c + d. Preconditions: 7 <= len(ip) <= 15; ip is a valid IPv4 address in this sense; 1 <= n <= 1000; I + n - 1 <= 2^32 - 1. -/
theorem spec_12 (ip : Slice U8) (n : I64) (I : ℕ)
    (h_ip : IsDottedDecimal ip.val I)
    (h_len_lo : 7 ≤ ip.val.length) (h_len_hi : ip.val.length ≤ 15)
    (h_n_lo : 1 ≤ n.val) (h_n_hi : n.val ≤ 1000)
    (h_top : (I : ℤ) + n.val ≤ 2 ^ 32)
    (r : alloc.vec.Vec (alloc.vec.Vec U8)) (h_r : ip_to_cidr ip n = ok r) :
    (blockStrings r).length ≤ 64 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (ip : Slice U8) (n : I64) (I : ℕ)
    (h_ip : IsDottedDecimal ip.val I)
    (h_len_lo : 7 ≤ ip.val.length) (h_len_hi : ip.val.length ≤ 15)
    (h_n_lo : 1 ≤ n.val) (h_n_hi : n.val ≤ 1000)
    (h_top : (I : ℤ) + n.val ≤ 2 ^ 32)
    (r : alloc.vec.Vec (alloc.vec.Vec U8)) (h_r : ip_to_cidr ip n = ok r), (blockStrings r).length ≤ 64) := by
  sorry

/-- Under these extra preconditions, whenever the function returns a result r, len(r) = 1. The unique block r[0] encodes some (b_0,k_0) with k_0 = 32-m and C(b_0,k_0) = R = {x : I <= x < I+n}. The base b_0 may be any address in R, not necessarily I.
  Preconditions: Let I be the 32-bit integer represented by ip: ip is a valid IPv4 ASCII byte slice of the form a.b.c.d with 0 <= a,b,c,d <= 255 and I = 256^3*a + 256^2*b + 256*c + d. Preconditions: 7 <= len(ip) <= 15; ip is a valid IPv4 address in this sense; 1 <= n <= 1000; I + n - 1 <= 2^32 - 1. Additionally, n = 2^m for some integer m with 0 <= m <= 32, and I is a multiple of n. For a CIDR block (b,k) with 0 <= b < 2^32 and 0 <= k <= 32, let C(b,k) = {x : 0 <= x < 2^32 and x / 2^(32-k) = b / 2^(32-k)} (integer division). A byte string encodes (b,k) iff it is the canonical dotted-decimal encoding of b followed by '/' and the canonical decimal encoding of k. -/
theorem spec_13 (ip : Slice U8) (n : I64) (I : ℕ)
    (h_ip : IsDottedDecimal ip.val I)
    (h_len_lo : 7 ≤ ip.val.length) (h_len_hi : ip.val.length ≤ 15)
    (h_n_lo : 1 ≤ n.val) (h_n_hi : n.val ≤ 1000)
    (h_top : (I : ℤ) + n.val ≤ 2 ^ 32)
    (m : ℕ) (h_m : m ≤ 32) (h_n_pow : NVal n = 2 ^ m) (h_I_mult : 2 ^ m ∣ I)
    (r : alloc.vec.Vec (alloc.vec.Vec U8)) (h_r : ip_to_cidr ip n = ok r) :
    (blockStrings r).length = 1 ∧
      ∃ (s : List U8) (b k : ℕ),
        blockStrings r = [s] ∧ EncodesBlock s b k ∧ k = 32 - m ∧
          CoversExactly b k I (NVal n) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (ip : Slice U8) (n : I64) (I : ℕ)
    (h_ip : IsDottedDecimal ip.val I)
    (h_len_lo : 7 ≤ ip.val.length) (h_len_hi : ip.val.length ≤ 15)
    (h_n_lo : 1 ≤ n.val) (h_n_hi : n.val ≤ 1000)
    (h_top : (I : ℤ) + n.val ≤ 2 ^ 32)
    (m : ℕ) (h_m : m ≤ 32) (h_n_pow : NVal n = 2 ^ m) (h_I_mult : 2 ^ m ∣ I)
    (r : alloc.vec.Vec (alloc.vec.Vec U8)) (h_r : ip_to_cidr ip n = ok r), (blockStrings r).length = 1 ∧
      ∃ (s : List U8) (b k : ℕ),
        blockStrings r = [s] ∧ EncodesBlock s b k ∧ k = 32 - m ∧
          CoversExactly b k I (NVal n)) := by
  sorry

/-- Whenever the function returns a result r with len(r) = 1, say r[0] encodes (b_0,k_0), then n is a power of two, n = 2^(32-k_0), and I is a multiple of n; equivalently, the required range R = {x : I <= x < I+n} is exactly one CIDR block C(b_0,k_0).
  Preconditions: Let I be the 32-bit integer represented by ip: ip is a valid IPv4 ASCII byte slice of the form a.b.c.d with 0 <= a,b,c,d <= 255 and I = 256^3*a + 256^2*b + 256*c + d. Preconditions: 7 <= len(ip) <= 15; ip is a valid IPv4 address in this sense; 1 <= n <= 1000; I + n - 1 <= 2^32 - 1. For a CIDR block (b,k) with 0 <= b < 2^32 and 0 <= k <= 32, let C(b,k) = {x : 0 <= x < 2^32 and x / 2^(32-k) = b / 2^(32-k)} (integer division). A byte string encodes (b,k) iff it is the canonical dotted-decimal encoding of b followed by '/' and the canonical decimal encoding of k. -/
theorem spec_14 (ip : Slice U8) (n : I64) (I : ℕ)
    (h_ip : IsDottedDecimal ip.val I)
    (h_len_lo : 7 ≤ ip.val.length) (h_len_hi : ip.val.length ≤ 15)
    (h_n_lo : 1 ≤ n.val) (h_n_hi : n.val ≤ 1000)
    (h_top : (I : ℤ) + n.val ≤ 2 ^ 32)
    (r : alloc.vec.Vec (alloc.vec.Vec U8)) (h_r : ip_to_cidr ip n = ok r)
    (h_len_1 : (blockStrings r).length = 1) :
    ∃ (s : List U8) (b k m : ℕ),
      blockStrings r = [s] ∧ EncodesBlock s b k ∧ m ≤ 32 ∧ NVal n = 2 ^ m ∧
        NVal n = 2 ^ (32 - k) ∧ 2 ^ m ∣ I ∧ CoversExactly b k I (NVal n) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (ip : Slice U8) (n : I64) (I : ℕ)
    (h_ip : IsDottedDecimal ip.val I)
    (h_len_lo : 7 ≤ ip.val.length) (h_len_hi : ip.val.length ≤ 15)
    (h_n_lo : 1 ≤ n.val) (h_n_hi : n.val ≤ 1000)
    (h_top : (I : ℤ) + n.val ≤ 2 ^ 32)
    (r : alloc.vec.Vec (alloc.vec.Vec U8)) (h_r : ip_to_cidr ip n = ok r)
    (h_len_1 : (blockStrings r).length = 1), ∃ (s : List U8) (b k m : ℕ),
      blockStrings r = [s] ∧ EncodesBlock s b k ∧ m ≤ 32 ∧ NVal n = 2 ^ m ∧
        NVal n = 2 ^ (32 - k) ∧ 2 ^ m ∣ I ∧ CoversExactly b k I (NVal n)) := by
  sorry

end AegisSpec.IpToCidr

import Aegis.NumberOfWays.Code.Funs

/-!
# Specifications of `Aegis.NumberOfWays.number_of_ways`

LeetCode problem `number-of-ways-to-reach-destination-in-the-grid`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.NumberOfWays

def MOD : ℤ := 1000000007

abbrev Cell : Type := ℤ × ℤ

def InGrid (n m : ℤ) (c : Cell) : Prop := 1 ≤ c.1 ∧ c.1 ≤ n ∧ 1 ≤ c.2 ∧ c.2 ≤ m

abbrev Adjacent (u v : Cell) : Prop := (u.1 = v.1 ∨ u.2 = v.2) ∧ u ≠ v

def gridCells (n m : ℤ) : Finset Cell :=
  ((Finset.range n.toNat).product (Finset.range m.toNat)).image
    (fun p : ℕ × ℕ => ((p.1 : ℤ) + 1, (p.2 : ℤ) + 1))

def walkCountAux (n m : ℤ) : ℕ → Cell → Cell → ℕ :=
  Nat.rec (motive := fun _ => Cell → Cell → ℕ)
    (fun a b => if a = b then 1 else 0)
    (fun _ F => fun a b => ∑ u ∈ gridCells n m, if Adjacent a u then F u b else 0)

def walkCount (n m : ℤ) (t : ℕ) (a b : Cell) : ℕ :=
  if a ∈ gridCells n m then walkCountAux n m t a b else 0

def reduce (N : ℕ) : ℤ := (N : ℤ) % MOD

def commonNeighbours (n m : ℤ) (a b : Cell) : Finset Cell :=
  (gridCells n m).filter (fun u => Adjacent u a ∧ Adjacent u b)

abbrev EvenZ (z : ℤ) : Prop := z % 2 = 0

def coordX (s : Slice I64) : ℤ :=
  match s.val with
  | [] => 0
  | a :: _ => a.val

def coordY (s : Slice I64) : ℤ :=
  match s.val with
  | _ :: b :: _ => b.val
  | _ => 0

def cellOf (s : Slice I64) : Cell := (coordX s, coordY s)

def IsCellOf (n m : ℤ) (s : Slice I64) : Prop := s.val.length = 2 ∧ InGrid n m (cellOf s)

/-- For every input satisfying the preconditions, the function returns a result r and r = N mod MOD, where N is the number of sequences (c_0, c_1, ..., c_k) such that: each c_t = (x_t, y_t) is a grid cell with 1 <= x_t <= n and 1 <= y_t <= m; c_0 = (source[0], source[1]); c_k = (dest[0], dest[1]); and for every t with 0 <= t < k, (x_t = x_{t+1} or y_t = y_{t+1}) and (x_t, y_t) != (x_{t+1}, y_{t+1}). The value N mod MOD is the unique integer in [0, MOD-1] congruent to N modulo MOD.
  Preconditions: Let MOD = 1000000007. len(source) = 2 and len(dest) = 2; 2 <= n <= 1000000000; 2 <= m <= 1000000000; 1 <= k <= 100000; 1 <= source[0] <= n; 1 <= dest[0] <= n; 1 <= source[1] <= m; 1 <= dest[1] <= m. The slices are 0-indexed in Lean: (source[0], source[1]) is the problem's 1-indexed cell [x, y], and similarly for dest. -/
theorem spec_1 (n m k : I64) (source dest : Slice I64)
    (hsrc_len : source.val.length = 2) (hdest_len : dest.val.length = 2)
    (hn : 2 ≤ n.val) (hn_max : n.val ≤ 1000000000)
    (hm : 2 ≤ m.val) (hm_max : m.val ≤ 1000000000)
    (hk : 1 ≤ k.val) (hk_max : k.val ≤ 100000)
    (hsx : 1 ≤ coordX source) (hsx_max : coordX source ≤ n.val)
    (hsy : 1 ≤ coordY source) (hsy_max : coordY source ≤ m.val)
    (hdx : 1 ≤ coordX dest) (hdx_max : coordX dest ≤ n.val)
    (hdy : 1 ≤ coordY dest) (hdy_max : coordY dest ≤ m.val) :
    ∃ r : I64, Aegis.NumberOfWays.number_of_ways n m k source dest = ok r ∧
      r.val = reduce (walkCount n.val m.val k.val.toNat (cellOf source) (cellOf dest)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n m k : I64) (source dest : Slice I64)
    (hsrc_len : source.val.length = 2) (hdest_len : dest.val.length = 2)
    (hn : 2 ≤ n.val) (hn_max : n.val ≤ 1000000000)
    (hm : 2 ≤ m.val) (hm_max : m.val ≤ 1000000000)
    (hk : 1 ≤ k.val) (hk_max : k.val ≤ 100000)
    (hsx : 1 ≤ coordX source) (hsx_max : coordX source ≤ n.val)
    (hsy : 1 ≤ coordY source) (hsy_max : coordY source ≤ m.val)
    (hdx : 1 ≤ coordX dest) (hdx_max : coordX dest ≤ n.val)
    (hdy : 1 ≤ coordY dest) (hdy_max : coordY dest ≤ m.val), ∃ r : I64, Aegis.NumberOfWays.number_of_ways n m k source dest = ok r ∧
      r.val = reduce (walkCount n.val m.val k.val.toNat (cellOf source) (cellOf dest))) := by
  sorry

/-- For every input satisfying the preconditions, the function does not fail: it returns a result r rather than an error, panic, out-of-bounds access, or integer-overflow failure.
  Preconditions: Let MOD = 1000000007. len(source) = 2 and len(dest) = 2; 2 <= n <= 1000000000; 2 <= m <= 1000000000; 1 <= k <= 100000; 1 <= source[0] <= n; 1 <= dest[0] <= n; 1 <= source[1] <= m; 1 <= dest[1] <= m. The slices are 0-indexed in Lean: (source[0], source[1]) is the problem's 1-indexed cell [x, y], and similarly for dest. -/
theorem spec_2 (n m k : I64) (source dest : Slice I64)
    (hsrc_len : source.val.length = 2) (hdest_len : dest.val.length = 2)
    (hn : 2 ≤ n.val) (hn_max : n.val ≤ 1000000000)
    (hm : 2 ≤ m.val) (hm_max : m.val ≤ 1000000000)
    (hk : 1 ≤ k.val) (hk_max : k.val ≤ 100000)
    (hsx : 1 ≤ coordX source) (hsx_max : coordX source ≤ n.val)
    (hsy : 1 ≤ coordY source) (hsy_max : coordY source ≤ m.val)
    (hdx : 1 ≤ coordX dest) (hdx_max : coordX dest ≤ n.val)
    (hdy : 1 ≤ coordY dest) (hdy_max : coordY dest ≤ m.val) :
    ∃ r : I64, Aegis.NumberOfWays.number_of_ways n m k source dest = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n m k : I64) (source dest : Slice I64)
    (hsrc_len : source.val.length = 2) (hdest_len : dest.val.length = 2)
    (hn : 2 ≤ n.val) (hn_max : n.val ≤ 1000000000)
    (hm : 2 ≤ m.val) (hm_max : m.val ≤ 1000000000)
    (hk : 1 ≤ k.val) (hk_max : k.val ≤ 100000)
    (hsx : 1 ≤ coordX source) (hsx_max : coordX source ≤ n.val)
    (hsy : 1 ≤ coordY source) (hsy_max : coordY source ≤ m.val)
    (hdx : 1 ≤ coordX dest) (hdx_max : coordX dest ≤ n.val)
    (hdy : 1 ≤ coordY dest) (hdy_max : coordY dest ≤ m.val), ∃ r : I64, Aegis.NumberOfWays.number_of_ways n m k source dest = ok r) := by
  sorry

/-- For every input satisfying the preconditions, whenever the function returns a result r, the integer r satisfies 0 <= r < MOD.
  Preconditions: Let MOD = 1000000007. len(source) = 2 and len(dest) = 2; 2 <= n <= 1000000000; 2 <= m <= 1000000000; 1 <= k <= 100000; 1 <= source[0] <= n; 1 <= dest[0] <= n; 1 <= source[1] <= m; 1 <= dest[1] <= m. The slices are 0-indexed in Lean: (source[0], source[1]) is the problem's 1-indexed cell [x, y], and similarly for dest. -/
theorem spec_3 (n m k : I64) (source dest : Slice I64)
    (hsrc_len : source.val.length = 2) (hdest_len : dest.val.length = 2)
    (hn : 2 ≤ n.val) (hn_max : n.val ≤ 1000000000)
    (hm : 2 ≤ m.val) (hm_max : m.val ≤ 1000000000)
    (hk : 1 ≤ k.val) (hk_max : k.val ≤ 100000)
    (hsx : 1 ≤ coordX source) (hsx_max : coordX source ≤ n.val)
    (hsy : 1 ≤ coordY source) (hsy_max : coordY source ≤ m.val)
    (hdx : 1 ≤ coordX dest) (hdx_max : coordX dest ≤ n.val)
    (hdy : 1 ≤ coordY dest) (hdy_max : coordY dest ≤ m.val) :
    ∀ r : I64, Aegis.NumberOfWays.number_of_ways n m k source dest = ok r →
      0 ≤ r.val ∧ r.val < MOD := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n m k : I64) (source dest : Slice I64)
    (hsrc_len : source.val.length = 2) (hdest_len : dest.val.length = 2)
    (hn : 2 ≤ n.val) (hn_max : n.val ≤ 1000000000)
    (hm : 2 ≤ m.val) (hm_max : m.val ≤ 1000000000)
    (hk : 1 ≤ k.val) (hk_max : k.val ≤ 100000)
    (hsx : 1 ≤ coordX source) (hsx_max : coordX source ≤ n.val)
    (hsy : 1 ≤ coordY source) (hsy_max : coordY source ≤ m.val)
    (hdx : 1 ≤ coordX dest) (hdx_max : coordX dest ≤ n.val)
    (hdy : 1 ≤ coordY dest) (hdy_max : coordY dest ≤ m.val), ∀ r : I64, Aegis.NumberOfWays.number_of_ways n m k source dest = ok r →
      0 ≤ r.val ∧ r.val < MOD) := by
  sorry

/-- For every input satisfying the preconditions, the result of number_of_ways n m k source dest equals the result of number_of_ways n m k dest source.
  Preconditions: Let MOD = 1000000007. len(source) = 2 and len(dest) = 2; 2 <= n <= 1000000000; 2 <= m <= 1000000000; 1 <= k <= 100000; 1 <= source[0] <= n; 1 <= dest[0] <= n; 1 <= source[1] <= m; 1 <= dest[1] <= m. The slices are 0-indexed in Lean: (source[0], source[1]) is the problem's 1-indexed cell [x, y], and similarly for dest. -/
theorem spec_4 (n m k : I64) (source dest : Slice I64)
    (hsrc_len : source.val.length = 2) (hdest_len : dest.val.length = 2)
    (hn : 2 ≤ n.val) (hn_max : n.val ≤ 1000000000)
    (hm : 2 ≤ m.val) (hm_max : m.val ≤ 1000000000)
    (hk : 1 ≤ k.val) (hk_max : k.val ≤ 100000)
    (hsx : 1 ≤ coordX source) (hsx_max : coordX source ≤ n.val)
    (hsy : 1 ≤ coordY source) (hsy_max : coordY source ≤ m.val)
    (hdx : 1 ≤ coordX dest) (hdx_max : coordX dest ≤ n.val)
    (hdy : 1 ≤ coordY dest) (hdy_max : coordY dest ≤ m.val) :
    Aegis.NumberOfWays.number_of_ways n m k source dest =
      Aegis.NumberOfWays.number_of_ways n m k dest source := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n m k : I64) (source dest : Slice I64)
    (hsrc_len : source.val.length = 2) (hdest_len : dest.val.length = 2)
    (hn : 2 ≤ n.val) (hn_max : n.val ≤ 1000000000)
    (hm : 2 ≤ m.val) (hm_max : m.val ≤ 1000000000)
    (hk : 1 ≤ k.val) (hk_max : k.val ≤ 100000)
    (hsx : 1 ≤ coordX source) (hsx_max : coordX source ≤ n.val)
    (hsy : 1 ≤ coordY source) (hsy_max : coordY source ≤ m.val)
    (hdx : 1 ≤ coordX dest) (hdx_max : coordX dest ≤ n.val)
    (hdy : 1 ≤ coordY dest) (hdy_max : coordY dest ≤ m.val), Aegis.NumberOfWays.number_of_ways n m k source dest =
      Aegis.NumberOfWays.number_of_ways n m k dest source) := by
  sorry

/-- For every input satisfying the preconditions, the result of number_of_ways n m k source dest equals the result of number_of_ways m n k source' dest', where source' is the length-2 slice with source'[0] = source[1] and source'[1] = source[0], and dest' is the length-2 slice with dest'[0] = dest[1] and dest'[1] = dest[0].
  Preconditions: Let MOD = 1000000007. len(source) = 2 and len(dest) = 2; 2 <= n <= 1000000000; 2 <= m <= 1000000000; 1 <= k <= 100000; 1 <= source[0] <= n; 1 <= dest[0] <= n; 1 <= source[1] <= m; 1 <= dest[1] <= m. The slices are 0-indexed in Lean: (source[0], source[1]) is the problem's 1-indexed cell [x, y], and similarly for dest. -/
theorem spec_5 (n m k : I64) (source dest source' dest' : Slice I64)
    (hsrc_len : source.val.length = 2) (hdest_len : dest.val.length = 2)
    (hn : 2 ≤ n.val) (hn_max : n.val ≤ 1000000000)
    (hm : 2 ≤ m.val) (hm_max : m.val ≤ 1000000000)
    (hk : 1 ≤ k.val) (hk_max : k.val ≤ 100000)
    (hsx : 1 ≤ coordX source) (hsx_max : coordX source ≤ n.val)
    (hsy : 1 ≤ coordY source) (hsy_max : coordY source ≤ m.val)
    (hdx : 1 ≤ coordX dest) (hdx_max : coordX dest ≤ n.val)
    (hdy : 1 ≤ coordY dest) (hdy_max : coordY dest ≤ m.val)
    (hsrc'_len : source'.val.length = 2) (hdest'_len : dest'.val.length = 2)
    (hsrc'x : coordX source' = coordY source) (hsrc'y : coordY source' = coordX source)
    (hdest'x : coordX dest' = coordY dest) (hdest'y : coordY dest' = coordX dest) :
    Aegis.NumberOfWays.number_of_ways n m k source dest =
      Aegis.NumberOfWays.number_of_ways m n k source' dest' := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n m k : I64) (source dest source' dest' : Slice I64)
    (hsrc_len : source.val.length = 2) (hdest_len : dest.val.length = 2)
    (hn : 2 ≤ n.val) (hn_max : n.val ≤ 1000000000)
    (hm : 2 ≤ m.val) (hm_max : m.val ≤ 1000000000)
    (hk : 1 ≤ k.val) (hk_max : k.val ≤ 100000)
    (hsx : 1 ≤ coordX source) (hsx_max : coordX source ≤ n.val)
    (hsy : 1 ≤ coordY source) (hsy_max : coordY source ≤ m.val)
    (hdx : 1 ≤ coordX dest) (hdx_max : coordX dest ≤ n.val)
    (hdy : 1 ≤ coordY dest) (hdy_max : coordY dest ≤ m.val)
    (hsrc'_len : source'.val.length = 2) (hdest'_len : dest'.val.length = 2)
    (hsrc'x : coordX source' = coordY source) (hsrc'y : coordY source' = coordX source)
    (hdest'x : coordX dest' = coordY dest) (hdest'y : coordY dest' = coordX dest), Aegis.NumberOfWays.number_of_ways n m k source dest =
      Aegis.NumberOfWays.number_of_ways m n k source' dest') := by
  sorry

/-- For every input satisfying the preconditions, every permutation pi of {1,...,n}, and every permutation sigma of {1,...,m}, if source' is the cell (pi(source[0]), sigma(source[1])) and dest' is the cell (pi(dest[0]), sigma(dest[1])) (represented by length-2 slices), then number_of_ways n m k source dest = number_of_ways n m k source' dest'.
  Preconditions: Let MOD = 1000000007. len(source) = 2 and len(dest) = 2; 2 <= n <= 1000000000; 2 <= m <= 1000000000; 1 <= k <= 100000; 1 <= source[0] <= n; 1 <= dest[0] <= n; 1 <= source[1] <= m; 1 <= dest[1] <= m. The slices are 0-indexed in Lean: (source[0], source[1]) is the problem's 1-indexed cell [x, y], and similarly for dest. -/
theorem spec_6 (n m k : I64) (source dest source' dest' : Slice I64)
    (hsrc_len : source.val.length = 2) (hdest_len : dest.val.length = 2)
    (hn : 2 ≤ n.val) (hn_max : n.val ≤ 1000000000)
    (hm : 2 ≤ m.val) (hm_max : m.val ≤ 1000000000)
    (hk : 1 ≤ k.val) (hk_max : k.val ≤ 100000)
    (hsx : 1 ≤ coordX source) (hsx_max : coordX source ≤ n.val)
    (hsy : 1 ≤ coordY source) (hsy_max : coordY source ≤ m.val)
    (hdx : 1 ≤ coordX dest) (hdx_max : coordX dest ≤ n.val)
    (hdy : 1 ≤ coordY dest) (hdy_max : coordY dest ≤ m.val)
    (pi sigma : ℤ ≃ ℤ)
    (hpi : ∀ x : ℤ, 1 ≤ x → x ≤ n.val → 1 ≤ pi x ∧ pi x ≤ n.val)
    (hsigma : ∀ y : ℤ, 1 ≤ y → y ≤ m.val → 1 ≤ sigma y ∧ sigma y ≤ m.val)
    (hsrc'_len : source'.val.length = 2) (hdest'_len : dest'.val.length = 2)
    (hsrc'x : coordX source' = pi (coordX source))
    (hsrc'y : coordY source' = sigma (coordY source))
    (hdest'x : coordX dest' = pi (coordX dest))
    (hdest'y : coordY dest' = sigma (coordY dest)) :
    Aegis.NumberOfWays.number_of_ways n m k source dest =
      Aegis.NumberOfWays.number_of_ways n m k source' dest' := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n m k : I64) (source dest source' dest' : Slice I64)
    (hsrc_len : source.val.length = 2) (hdest_len : dest.val.length = 2)
    (hn : 2 ≤ n.val) (hn_max : n.val ≤ 1000000000)
    (hm : 2 ≤ m.val) (hm_max : m.val ≤ 1000000000)
    (hk : 1 ≤ k.val) (hk_max : k.val ≤ 100000)
    (hsx : 1 ≤ coordX source) (hsx_max : coordX source ≤ n.val)
    (hsy : 1 ≤ coordY source) (hsy_max : coordY source ≤ m.val)
    (hdx : 1 ≤ coordX dest) (hdx_max : coordX dest ≤ n.val)
    (hdy : 1 ≤ coordY dest) (hdy_max : coordY dest ≤ m.val)
    (pi sigma : ℤ ≃ ℤ)
    (hpi : ∀ x : ℤ, 1 ≤ x → x ≤ n.val → 1 ≤ pi x ∧ pi x ≤ n.val)
    (hsigma : ∀ y : ℤ, 1 ≤ y → y ≤ m.val → 1 ≤ sigma y ∧ sigma y ≤ m.val)
    (hsrc'_len : source'.val.length = 2) (hdest'_len : dest'.val.length = 2)
    (hsrc'x : coordX source' = pi (coordX source))
    (hsrc'y : coordY source' = sigma (coordY source))
    (hdest'x : coordX dest' = pi (coordX dest))
    (hdest'y : coordY dest' = sigma (coordY dest)), Aegis.NumberOfWays.number_of_ways n m k source dest =
      Aegis.NumberOfWays.number_of_ways n m k source' dest') := by
  sorry

/-- For every input satisfying the preconditions, and any two valid cells s and s' (represented by length-2 slices with coordinates in the grid), if (s[0] = dest[0] iff s'[0] = dest[0]) and (s[1] = dest[1] iff s'[1] = dest[1]), then number_of_ways n m k s dest = number_of_ways n m k s' dest.
  Preconditions: Let MOD = 1000000007. len(source) = 2 and len(dest) = 2; 2 <= n <= 1000000000; 2 <= m <= 1000000000; 1 <= k <= 100000; 1 <= source[0] <= n; 1 <= dest[0] <= n; 1 <= source[1] <= m; 1 <= dest[1] <= m. The slices are 0-indexed in Lean: (source[0], source[1]) is the problem's 1-indexed cell [x, y], and similarly for dest. -/
theorem spec_7 (n m k : I64) (source dest s s' : Slice I64)
    (hsrc_len : source.val.length = 2) (hdest_len : dest.val.length = 2)
    (hn : 2 ≤ n.val) (hn_max : n.val ≤ 1000000000)
    (hm : 2 ≤ m.val) (hm_max : m.val ≤ 1000000000)
    (hk : 1 ≤ k.val) (hk_max : k.val ≤ 100000)
    (hsx : 1 ≤ coordX source) (hsx_max : coordX source ≤ n.val)
    (hsy : 1 ≤ coordY source) (hsy_max : coordY source ≤ m.val)
    (hdx : 1 ≤ coordX dest) (hdx_max : coordX dest ≤ n.val)
    (hdy : 1 ≤ coordY dest) (hdy_max : coordY dest ≤ m.val)
    (hs : IsCellOf n.val m.val s) (hs' : IsCellOf n.val m.val s')
    (hx : coordX s = coordX dest ↔ coordX s' = coordX dest)
    (hy : coordY s = coordY dest ↔ coordY s' = coordY dest) :
    Aegis.NumberOfWays.number_of_ways n m k s dest =
      Aegis.NumberOfWays.number_of_ways n m k s' dest := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n m k : I64) (source dest s s' : Slice I64)
    (hsrc_len : source.val.length = 2) (hdest_len : dest.val.length = 2)
    (hn : 2 ≤ n.val) (hn_max : n.val ≤ 1000000000)
    (hm : 2 ≤ m.val) (hm_max : m.val ≤ 1000000000)
    (hk : 1 ≤ k.val) (hk_max : k.val ≤ 100000)
    (hsx : 1 ≤ coordX source) (hsx_max : coordX source ≤ n.val)
    (hsy : 1 ≤ coordY source) (hsy_max : coordY source ≤ m.val)
    (hdx : 1 ≤ coordX dest) (hdx_max : coordX dest ≤ n.val)
    (hdy : 1 ≤ coordY dest) (hdy_max : coordY dest ≤ m.val)
    (hs : IsCellOf n.val m.val s) (hs' : IsCellOf n.val m.val s')
    (hx : coordX s = coordX dest ↔ coordX s' = coordX dest)
    (hy : coordY s = coordY dest ↔ coordY s' = coordY dest), Aegis.NumberOfWays.number_of_ways n m k s dest =
      Aegis.NumberOfWays.number_of_ways n m k s' dest) := by
  sorry

/-- For every input satisfying the preconditions, and any two valid cells c and c' (represented by length-2 slices with coordinates in the grid), number_of_ways n m k c c = number_of_ways n m k c' c'.
  Preconditions: Let MOD = 1000000007. len(source) = 2 and len(dest) = 2; 2 <= n <= 1000000000; 2 <= m <= 1000000000; 1 <= k <= 100000; 1 <= source[0] <= n; 1 <= dest[0] <= n; 1 <= source[1] <= m; 1 <= dest[1] <= m. The slices are 0-indexed in Lean: (source[0], source[1]) is the problem's 1-indexed cell [x, y], and similarly for dest. -/
theorem spec_8 (n m k : I64) (source dest c c' : Slice I64)
    (hsrc_len : source.val.length = 2) (hdest_len : dest.val.length = 2)
    (hn : 2 ≤ n.val) (hn_max : n.val ≤ 1000000000)
    (hm : 2 ≤ m.val) (hm_max : m.val ≤ 1000000000)
    (hk : 1 ≤ k.val) (hk_max : k.val ≤ 100000)
    (hsx : 1 ≤ coordX source) (hsx_max : coordX source ≤ n.val)
    (hsy : 1 ≤ coordY source) (hsy_max : coordY source ≤ m.val)
    (hdx : 1 ≤ coordX dest) (hdx_max : coordX dest ≤ n.val)
    (hdy : 1 ≤ coordY dest) (hdy_max : coordY dest ≤ m.val)
    (hc : IsCellOf n.val m.val c) (hc' : IsCellOf n.val m.val c') :
    Aegis.NumberOfWays.number_of_ways n m k c c =
      Aegis.NumberOfWays.number_of_ways n m k c' c' := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n m k : I64) (source dest c c' : Slice I64)
    (hsrc_len : source.val.length = 2) (hdest_len : dest.val.length = 2)
    (hn : 2 ≤ n.val) (hn_max : n.val ≤ 1000000000)
    (hm : 2 ≤ m.val) (hm_max : m.val ≤ 1000000000)
    (hk : 1 ≤ k.val) (hk_max : k.val ≤ 100000)
    (hsx : 1 ≤ coordX source) (hsx_max : coordX source ≤ n.val)
    (hsy : 1 ≤ coordY source) (hsy_max : coordY source ≤ m.val)
    (hdx : 1 ≤ coordX dest) (hdx_max : coordX dest ≤ n.val)
    (hdy : 1 ≤ coordY dest) (hdy_max : coordY dest ≤ m.val)
    (hc : IsCellOf n.val m.val c) (hc' : IsCellOf n.val m.val c'), Aegis.NumberOfWays.number_of_ways n m k c c =
      Aegis.NumberOfWays.number_of_ways n m k c' c') := by
  sorry

/-- For every input satisfying the preconditions, if k = 1, then the returned value r is 1 if (source[0] = dest[0] or source[1] = dest[1]) and (source[0] != dest[0] or source[1] != dest[1]); otherwise r = 0.
  Preconditions: Let MOD = 1000000007. len(source) = 2 and len(dest) = 2; 2 <= n <= 1000000000; 2 <= m <= 1000000000; 1 <= k <= 100000; 1 <= source[0] <= n; 1 <= dest[0] <= n; 1 <= source[1] <= m; 1 <= dest[1] <= m. The slices are 0-indexed in Lean: (source[0], source[1]) is the problem's 1-indexed cell [x, y], and similarly for dest. -/
theorem spec_9 (n m k : I64) (source dest : Slice I64)
    (hsrc_len : source.val.length = 2) (hdest_len : dest.val.length = 2)
    (hn : 2 ≤ n.val) (hn_max : n.val ≤ 1000000000)
    (hm : 2 ≤ m.val) (hm_max : m.val ≤ 1000000000)
    (hk : 1 ≤ k.val) (hk_max : k.val ≤ 100000)
    (hsx : 1 ≤ coordX source) (hsx_max : coordX source ≤ n.val)
    (hsy : 1 ≤ coordY source) (hsy_max : coordY source ≤ m.val)
    (hdx : 1 ≤ coordX dest) (hdx_max : coordX dest ≤ n.val)
    (hdy : 1 ≤ coordY dest) (hdy_max : coordY dest ≤ m.val)
    (hk1 : k.val = 1) :
    ∃ r : I64, Aegis.NumberOfWays.number_of_ways n m k source dest = ok r ∧
      r.val = if Adjacent (cellOf source) (cellOf dest) then 1 else 0 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n m k : I64) (source dest : Slice I64)
    (hsrc_len : source.val.length = 2) (hdest_len : dest.val.length = 2)
    (hn : 2 ≤ n.val) (hn_max : n.val ≤ 1000000000)
    (hm : 2 ≤ m.val) (hm_max : m.val ≤ 1000000000)
    (hk : 1 ≤ k.val) (hk_max : k.val ≤ 100000)
    (hsx : 1 ≤ coordX source) (hsx_max : coordX source ≤ n.val)
    (hsy : 1 ≤ coordY source) (hsy_max : coordY source ≤ m.val)
    (hdx : 1 ≤ coordX dest) (hdx_max : coordX dest ≤ n.val)
    (hdy : 1 ≤ coordY dest) (hdy_max : coordY dest ≤ m.val)
    (hk1 : k.val = 1), ∃ r : I64, Aegis.NumberOfWays.number_of_ways n m k source dest = ok r ∧
      r.val = if Adjacent (cellOf source) (cellOf dest) then 1 else 0) := by
  sorry

/-- For every input satisfying the preconditions, if k = 2, then the returned value r equals |I| mod MOD, where I is the set of all grid cells u = (u_x, u_y) with 1 <= u_x <= n and 1 <= u_y <= m such that u is adjacent to both source and dest. A cell u is adjacent to a cell v = (v_x, v_y) when (u_x = v_x or u_y = v_y) and (u_x, u_y) != (v_x, v_y).
  Preconditions: Let MOD = 1000000007. len(source) = 2 and len(dest) = 2; 2 <= n <= 1000000000; 2 <= m <= 1000000000; 1 <= k <= 100000; 1 <= source[0] <= n; 1 <= dest[0] <= n; 1 <= source[1] <= m; 1 <= dest[1] <= m. The slices are 0-indexed in Lean: (source[0], source[1]) is the problem's 1-indexed cell [x, y], and similarly for dest. -/
theorem spec_10 (n m k : I64) (source dest : Slice I64)
    (hsrc_len : source.val.length = 2) (hdest_len : dest.val.length = 2)
    (hn : 2 ≤ n.val) (hn_max : n.val ≤ 1000000000)
    (hm : 2 ≤ m.val) (hm_max : m.val ≤ 1000000000)
    (hk : 1 ≤ k.val) (hk_max : k.val ≤ 100000)
    (hsx : 1 ≤ coordX source) (hsx_max : coordX source ≤ n.val)
    (hsy : 1 ≤ coordY source) (hsy_max : coordY source ≤ m.val)
    (hdx : 1 ≤ coordX dest) (hdx_max : coordX dest ≤ n.val)
    (hdy : 1 ≤ coordY dest) (hdy_max : coordY dest ≤ m.val)
    (hk2 : k.val = 2) :
    ∃ r : I64, Aegis.NumberOfWays.number_of_ways n m k source dest = ok r ∧
      r.val = reduce (commonNeighbours n.val m.val (cellOf source) (cellOf dest)).card := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n m k : I64) (source dest : Slice I64)
    (hsrc_len : source.val.length = 2) (hdest_len : dest.val.length = 2)
    (hn : 2 ≤ n.val) (hn_max : n.val ≤ 1000000000)
    (hm : 2 ≤ m.val) (hm_max : m.val ≤ 1000000000)
    (hk : 1 ≤ k.val) (hk_max : k.val ≤ 100000)
    (hsx : 1 ≤ coordX source) (hsx_max : coordX source ≤ n.val)
    (hsy : 1 ≤ coordY source) (hsy_max : coordY source ≤ m.val)
    (hdx : 1 ≤ coordX dest) (hdx_max : coordX dest ≤ n.val)
    (hdy : 1 ≤ coordY dest) (hdy_max : coordY dest ≤ m.val)
    (hk2 : k.val = 2), ∃ r : I64, Aegis.NumberOfWays.number_of_ways n m k source dest = ok r ∧
      r.val = reduce (commonNeighbours n.val m.val (cellOf source) (cellOf dest)).card) := by
  sorry

/-- For every input satisfying the preconditions, if k = 2, then the returned value r is: (n + m - 2) mod MOD when source[0] = dest[0] and source[1] = dest[1]; (m - 2) mod MOD when source[0] = dest[0] and source[1] != dest[1]; (n - 2) mod MOD when source[0] != dest[0] and source[1] = dest[1]; and 2 mod MOD when source[0] != dest[0] and source[1] != dest[1].
  Preconditions: Let MOD = 1000000007. len(source) = 2 and len(dest) = 2; 2 <= n <= 1000000000; 2 <= m <= 1000000000; 1 <= k <= 100000; 1 <= source[0] <= n; 1 <= dest[0] <= n; 1 <= source[1] <= m; 1 <= dest[1] <= m. The slices are 0-indexed in Lean: (source[0], source[1]) is the problem's 1-indexed cell [x, y], and similarly for dest. -/
theorem spec_11 (n m k : I64) (source dest : Slice I64)
    (hsrc_len : source.val.length = 2) (hdest_len : dest.val.length = 2)
    (hn : 2 ≤ n.val) (hn_max : n.val ≤ 1000000000)
    (hm : 2 ≤ m.val) (hm_max : m.val ≤ 1000000000)
    (hk : 1 ≤ k.val) (hk_max : k.val ≤ 100000)
    (hsx : 1 ≤ coordX source) (hsx_max : coordX source ≤ n.val)
    (hsy : 1 ≤ coordY source) (hsy_max : coordY source ≤ m.val)
    (hdx : 1 ≤ coordX dest) (hdx_max : coordX dest ≤ n.val)
    (hdy : 1 ≤ coordY dest) (hdy_max : coordY dest ≤ m.val)
    (hk2 : k.val = 2) :
    ∃ r : I64, Aegis.NumberOfWays.number_of_ways n m k source dest = ok r ∧
      r.val =
        (if coordX source = coordX dest ∧ coordY source = coordY dest then
            reduce (n.val + m.val - 2).toNat
          else if coordX source = coordX dest then
            reduce (m.val - 2).toNat
          else if coordY source = coordY dest then
            reduce (n.val - 2).toNat
          else reduce 2) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n m k : I64) (source dest : Slice I64)
    (hsrc_len : source.val.length = 2) (hdest_len : dest.val.length = 2)
    (hn : 2 ≤ n.val) (hn_max : n.val ≤ 1000000000)
    (hm : 2 ≤ m.val) (hm_max : m.val ≤ 1000000000)
    (hk : 1 ≤ k.val) (hk_max : k.val ≤ 100000)
    (hsx : 1 ≤ coordX source) (hsx_max : coordX source ≤ n.val)
    (hsy : 1 ≤ coordY source) (hsy_max : coordY source ≤ m.val)
    (hdx : 1 ≤ coordX dest) (hdx_max : coordX dest ≤ n.val)
    (hdy : 1 ≤ coordY dest) (hdy_max : coordY dest ≤ m.val)
    (hk2 : k.val = 2), ∃ r : I64, Aegis.NumberOfWays.number_of_ways n m k source dest = ok r ∧
      r.val =
        (if coordX source = coordX dest ∧ coordY source = coordY dest then
            reduce (n.val + m.val - 2).toNat
          else if coordX source = coordX dest then
            reduce (m.val - 2).toNat
          else if coordY source = coordY dest then
            reduce (n.val - 2).toNat
          else reduce 2)) := by
  sorry

/-- For every input satisfying the preconditions, if n = 2 and m = 2, then the returned value r is determined as follows. Let sx = source[0], sy = source[1], dx = dest[0], dy = dest[1]. If k is even, then r = (2^(k-1)) mod MOD when (sx = dx and sy = dy) or (sx != dx and sy != dy), and r = 0 otherwise. If k is odd, then r = (2^(k-1)) mod MOD when (sx = dx and sy != dy) or (sx != dx and sy = dy), and r = 0 otherwise.
  Preconditions: Let MOD = 1000000007. len(source) = 2 and len(dest) = 2; 2 <= n <= 1000000000; 2 <= m <= 1000000000; 1 <= k <= 100000; 1 <= source[0] <= n; 1 <= dest[0] <= n; 1 <= source[1] <= m; 1 <= dest[1] <= m. The slices are 0-indexed in Lean: (source[0], source[1]) is the problem's 1-indexed cell [x, y], and similarly for dest. -/
theorem spec_12 (n m k : I64) (source dest : Slice I64)
    (hsrc_len : source.val.length = 2) (hdest_len : dest.val.length = 2)
    (hn : 2 ≤ n.val) (hn_max : n.val ≤ 1000000000)
    (hm : 2 ≤ m.val) (hm_max : m.val ≤ 1000000000)
    (hk : 1 ≤ k.val) (hk_max : k.val ≤ 100000)
    (hsx : 1 ≤ coordX source) (hsx_max : coordX source ≤ n.val)
    (hsy : 1 ≤ coordY source) (hsy_max : coordY source ≤ m.val)
    (hdx : 1 ≤ coordX dest) (hdx_max : coordX dest ≤ n.val)
    (hdy : 1 ≤ coordY dest) (hdy_max : coordY dest ≤ m.val)
    (hn2 : n.val = 2) (hm2 : m.val = 2) :
    ∃ r : I64, Aegis.NumberOfWays.number_of_ways n m k source dest = ok r ∧
      r.val =
        (if EvenZ k.val then
            (if (coordX source = coordX dest ∧ coordY source = coordY dest) ∨
                (coordX source ≠ coordX dest ∧ coordY source ≠ coordY dest) then
                reduce ((2 : ℕ) ^ (k.val.toNat - 1))
              else 0)
          else
            (if (coordX source = coordX dest ∧ coordY source ≠ coordY dest) ∨
                (coordX source ≠ coordX dest ∧ coordY source = coordY dest) then
                reduce ((2 : ℕ) ^ (k.val.toNat - 1))
              else 0)) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n m k : I64) (source dest : Slice I64)
    (hsrc_len : source.val.length = 2) (hdest_len : dest.val.length = 2)
    (hn : 2 ≤ n.val) (hn_max : n.val ≤ 1000000000)
    (hm : 2 ≤ m.val) (hm_max : m.val ≤ 1000000000)
    (hk : 1 ≤ k.val) (hk_max : k.val ≤ 100000)
    (hsx : 1 ≤ coordX source) (hsx_max : coordX source ≤ n.val)
    (hsy : 1 ≤ coordY source) (hsy_max : coordY source ≤ m.val)
    (hdx : 1 ≤ coordX dest) (hdx_max : coordX dest ≤ n.val)
    (hdy : 1 ≤ coordY dest) (hdy_max : coordY dest ≤ m.val)
    (hn2 : n.val = 2) (hm2 : m.val = 2), ∃ r : I64, Aegis.NumberOfWays.number_of_ways n m k source dest = ok r ∧
      r.val =
        (if EvenZ k.val then
            (if (coordX source = coordX dest ∧ coordY source = coordY dest) ∨
                (coordX source ≠ coordX dest ∧ coordY source ≠ coordY dest) then
                reduce ((2 : ℕ) ^ (k.val.toNat - 1))
              else 0)
          else
            (if (coordX source = coordX dest ∧ coordY source ≠ coordY dest) ∨
                (coordX source ≠ coordX dest ∧ coordY source = coordY dest) then
                reduce ((2 : ℕ) ^ (k.val.toNat - 1))
              else 0))) := by
  sorry

end AegisSpec.NumberOfWays

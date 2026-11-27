import Aegis.MaxSizeSlices.Code.Funs

/-!
# Specifications of `Aegis.MaxSizeSlices.max_size_slices`

LeetCode problem `pizza-with-3n-slices`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxSizeSlices

def i64OfInt (z : Int) : Std.I64 := ⟨BitVec.ofInt 64 z⟩

def mkSlice (l : List Std.I64) (h : l.length ≤ Usize.max) : Slice Std.I64 :=
  ⟨l.length, Aeneas.Data.ListN.ListN.fromList l, h⟩

def entry (s : Slice Std.I64) (i : Nat) : Int := (s.val.getD i (i64OfInt 0)).val

def groupCount (m : Nat) : Nat := m / 3

def selSum (s : Slice Std.I64) (S : Finset Nat) : Int := ∑ i ∈ S, entry s i

def IsValidSelection (m n : Nat) (S : Finset Nat) : Prop :=
  (∀ i ∈ S, i < m) ∧ S.card = n ∧ ∀ i ∈ S, (i + 1) % m ∉ S ∧ (i + m - 1) % m ∉ S

def selVals (s : Slice Std.I64) : Set Int :=
  {v | ∃ S : Finset Nat,
    IsValidSelection s.val.length (groupCount s.val.length) S ∧ v = selSum s S}

def topNSum (s : Slice Std.I64) (n : Nat) : Int :=
  (((s.val.map fun x => x.val).mergeSort fun a b => a ≥ b).take n).sum

def rotateSlice (s : Slice Std.I64) (k : Nat) : Slice Std.I64 :=
  mkSlice (s.val.rotate k)
    (by rw [List.length_rotate]; simpa [Slice.val, Aeneas.Data.ListN.ListN_length] using s.bound)

def reverseSlice (s : Slice Std.I64) : Slice Std.I64 :=
  mkSlice s.val.reverse (by simpa [Slice.val, Aeneas.Data.ListN.ListN_length] using s.bound)

def shiftSlice (s : Slice Std.I64) (c : Int) : Slice Std.I64 :=
  mkSlice (s.val.map fun x => i64OfInt (x.val + c))
    (by simpa [Slice.val, Aeneas.Data.ListN.ListN_length] using s.bound)

def scaleSlice (s : Slice Std.I64) (k : Int) : Slice Std.I64 :=
  mkSlice (s.val.map fun x => i64OfInt (k * x.val))
    (by simpa [Slice.val, Aeneas.Data.ListN.ListN_length] using s.bound)

theorem ListN.toList_fromList' (l : List Std.I64) :
    (Aeneas.Data.ListN.ListN.fromList l).toList = l := by
  induction l with
  | nil => rfl
  | cons h t ih =>
    simp [Aeneas.Data.ListN.ListN.fromList, Aeneas.Data.ListN.ListN.toList, ih]

theorem mkSlice_val (l : List Std.I64) (h : l.length ≤ Usize.max) : (mkSlice l h).val = l :=
  ListN.toList_fromList' l

theorem entry_eq_getElem {s : Slice Std.I64} {i : Nat} (h : i < s.val.length) :
    entry s i = (s.val[i]).val := by
  simp [entry, List.getD, List.getElem?_eq_getElem h]

/-- The function returns a result r such that r = max { sum_{i in S} slices[i] | S is a valid selection }, where a valid selection is a set S of indices {0,...,m-1} with |S| = n and for every i in S, neither (i+1) mod m nor (i-1) mod m is in S.
  Preconditions: Let m = len(slices) and n = m/3. Assume m is divisible by 3, m >= 3, m <= 500, and for every i with 0 <= i < m, 1 <= slices[i] <= 1000. -/
theorem spec_1 (slices : Slice Std.I64)
    (hdiv : 3 ∣ slices.val.length)
    (h3 : 3 ≤ slices.val.length)
    (h500 : slices.val.length ≤ 500)
    (hval : ∀ i, i < slices.val.length → 1 ≤ entry slices i ∧ entry slices i ≤ 1000) :
    ∃ r, Aegis.MaxSizeSlices.max_size_slices slices = ok r ∧ IsGreatest (selVals slices) r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (slices : Slice Std.I64)
    (hdiv : 3 ∣ slices.val.length)
    (h3 : 3 ≤ slices.val.length)
    (h500 : slices.val.length ≤ 500)
    (hval : ∀ i, i < slices.val.length → 1 ≤ entry slices i ∧ entry slices i ≤ 1000), ∃ r, Aegis.MaxSizeSlices.max_size_slices slices = ok r ∧ IsGreatest (selVals slices) r.val) := by
  sorry

/-- The function returns a result r (it does not panic, overflow, or fail) for every input satisfying the preconditions.
  Preconditions: Let m = len(slices) and n = m/3. Assume m is divisible by 3, m >= 3, m <= 500, and for every i with 0 <= i < m, 1 <= slices[i] <= 1000. -/
theorem spec_2 (slices : Slice Std.I64)
    (hdiv : 3 ∣ slices.val.length)
    (h3 : 3 ≤ slices.val.length)
    (h500 : slices.val.length ≤ 500)
    (hval : ∀ i, i < slices.val.length → 1 ≤ entry slices i ∧ entry slices i ≤ 1000) :
    ∃ r, Aegis.MaxSizeSlices.max_size_slices slices = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (slices : Slice Std.I64)
    (hdiv : 3 ∣ slices.val.length)
    (h3 : 3 ≤ slices.val.length)
    (h500 : slices.val.length ≤ 500)
    (hval : ∀ i, i < slices.val.length → 1 ≤ entry slices i ∧ entry slices i ≤ 1000), ∃ r, Aegis.MaxSizeSlices.max_size_slices slices = ok r) := by
  sorry

/-- Let Top be the sum of the n largest elements of the multiset { slices[i] | 0 <= i < m } (with multiplicity). Then the returned result r satisfies r <= Top.
  Preconditions: Let m = len(slices) and n = m/3. Assume m is divisible by 3, m >= 3, m <= 500, and for every i with 0 <= i < m, 1 <= slices[i] <= 1000. -/
theorem spec_3 (slices : Slice Std.I64)
    (hdiv : 3 ∣ slices.val.length)
    (h3 : 3 ≤ slices.val.length)
    (h500 : slices.val.length ≤ 500)
    (hval : ∀ i, i < slices.val.length → 1 ≤ entry slices i ∧ entry slices i ≤ 1000) :
    ∃ r, Aegis.MaxSizeSlices.max_size_slices slices = ok r ∧
      r.val ≤ topNSum slices (groupCount slices.val.length) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (slices : Slice Std.I64)
    (hdiv : 3 ∣ slices.val.length)
    (h3 : 3 ≤ slices.val.length)
    (h500 : slices.val.length ≤ 500)
    (hval : ∀ i, i < slices.val.length → 1 ≤ entry slices i ∧ entry slices i ≤ 1000), ∃ r, Aegis.MaxSizeSlices.max_size_slices slices = ok r ∧
      r.val ≤ topNSum slices (groupCount slices.val.length)) := by
  sorry

/-- The returned result r satisfies r >= max { slices[i] | 0 <= i < m }.
  Preconditions: Let m = len(slices) and n = m/3. Assume m is divisible by 3, m >= 3, m <= 500, and for every i with 0 <= i < m, 1 <= slices[i] <= 1000. -/
theorem spec_4 (slices : Slice Std.I64)
    (hdiv : 3 ∣ slices.val.length)
    (h3 : 3 ≤ slices.val.length)
    (h500 : slices.val.length ≤ 500)
    (hval : ∀ i, i < slices.val.length → 1 ≤ entry slices i ∧ entry slices i ≤ 1000) :
    ∃ r, Aegis.MaxSizeSlices.max_size_slices slices = ok r ∧
      ∀ i, i < slices.val.length → entry slices i ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (slices : Slice Std.I64)
    (hdiv : 3 ∣ slices.val.length)
    (h3 : 3 ≤ slices.val.length)
    (h500 : slices.val.length ≤ 500)
    (hval : ∀ i, i < slices.val.length → 1 ≤ entry slices i ∧ entry slices i ≤ 1000), ∃ r, Aegis.MaxSizeSlices.max_size_slices slices = ok r ∧
      ∀ i, i < slices.val.length → entry slices i ≤ r.val) := by
  sorry

/-- The returned result r satisfies r >= sum_{k=0}^{n-1} slices[3*k].
  Preconditions: Let m = len(slices) and n = m/3. Assume m is divisible by 3, m >= 3, m <= 500, and for every i with 0 <= i < m, 1 <= slices[i] <= 1000. -/
theorem spec_5 (slices : Slice Std.I64)
    (hdiv : 3 ∣ slices.val.length)
    (h3 : 3 ≤ slices.val.length)
    (h500 : slices.val.length ≤ 500)
    (hval : ∀ i, i < slices.val.length → 1 ≤ entry slices i ∧ entry slices i ≤ 1000) :
    ∃ r, Aegis.MaxSizeSlices.max_size_slices slices = ok r ∧
      (∑ k ∈ Finset.range (groupCount slices.val.length), entry slices (3 * k)) ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (slices : Slice Std.I64)
    (hdiv : 3 ∣ slices.val.length)
    (h3 : 3 ≤ slices.val.length)
    (h500 : slices.val.length ≤ 500)
    (hval : ∀ i, i < slices.val.length → 1 ≤ entry slices i ∧ entry slices i ≤ 1000), ∃ r, Aegis.MaxSizeSlices.max_size_slices slices = ok r ∧
      (∑ k ∈ Finset.range (groupCount slices.val.length), entry slices (3 * k)) ≤ r.val) := by
  sorry

/-- There exists a valid selection S (as defined in the main specification) such that r = sum_{i in S} slices[i].
  Preconditions: Let m = len(slices) and n = m/3. Assume m is divisible by 3, m >= 3, m <= 500, and for every i with 0 <= i < m, 1 <= slices[i] <= 1000. -/
theorem spec_6 (slices : Slice Std.I64)
    (hdiv : 3 ∣ slices.val.length)
    (h3 : 3 ≤ slices.val.length)
    (h500 : slices.val.length ≤ 500)
    (hval : ∀ i, i < slices.val.length → 1 ≤ entry slices i ∧ entry slices i ≤ 1000) :
    ∃ r, Aegis.MaxSizeSlices.max_size_slices slices = ok r ∧
      ∃ S : Finset Nat,
        IsValidSelection slices.val.length (groupCount slices.val.length) S ∧
          r.val = selSum slices S := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (slices : Slice Std.I64)
    (hdiv : 3 ∣ slices.val.length)
    (h3 : 3 ≤ slices.val.length)
    (h500 : slices.val.length ≤ 500)
    (hval : ∀ i, i < slices.val.length → 1 ≤ entry slices i ∧ entry slices i ≤ 1000), ∃ r, Aegis.MaxSizeSlices.max_size_slices slices = ok r ∧
      ∃ S : Finset Nat,
        IsValidSelection slices.val.length (groupCount slices.val.length) S ∧
          r.val = selSum slices S) := by
  sorry

/-- For every valid selection S, sum_{i in S} slices[i] <= r.
  Preconditions: Let m = len(slices) and n = m/3. Assume m is divisible by 3, m >= 3, m <= 500, and for every i with 0 <= i < m, 1 <= slices[i] <= 1000. -/
theorem spec_7 (slices : Slice Std.I64)
    (hdiv : 3 ∣ slices.val.length)
    (h3 : 3 ≤ slices.val.length)
    (h500 : slices.val.length ≤ 500)
    (hval : ∀ i, i < slices.val.length → 1 ≤ entry slices i ∧ entry slices i ≤ 1000) :
    ∃ r, Aegis.MaxSizeSlices.max_size_slices slices = ok r ∧
      ∀ S : Finset Nat,
        IsValidSelection slices.val.length (groupCount slices.val.length) S →
          selSum slices S ≤ r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (slices : Slice Std.I64)
    (hdiv : 3 ∣ slices.val.length)
    (h3 : 3 ≤ slices.val.length)
    (h500 : slices.val.length ≤ 500)
    (hval : ∀ i, i < slices.val.length → 1 ≤ entry slices i ∧ entry slices i ≤ 1000), ∃ r, Aegis.MaxSizeSlices.max_size_slices slices = ok r ∧
      ∀ S : Finset Nat,
        IsValidSelection slices.val.length (groupCount slices.val.length) S →
          selSum slices S ≤ r.val) := by
  sorry

/-- The function returns the same result on rot as on slices: max_size_slices(rot) = max_size_slices(slices).
  Preconditions: Let m = len(slices) and n = m/3. Assume m is divisible by 3, m >= 3, m <= 500, and for every i with 0 <= i < m, 1 <= slices[i] <= 1000. Let k be any integer with 0 <= k < m, and define the rotated slice rot of length m by rot[i] = slices[(i+k) mod m]. The slice rot also satisfies the preconditions. -/
theorem spec_8 (slices : Slice Std.I64) (k : Nat)
    (hk : k < slices.val.length)
    (hdiv : 3 ∣ slices.val.length)
    (h3 : 3 ≤ slices.val.length)
    (h500 : slices.val.length ≤ 500)
    (hval : ∀ i, i < slices.val.length → 1 ≤ entry slices i ∧ entry slices i ≤ 1000) :
    Aegis.MaxSizeSlices.max_size_slices (rotateSlice slices k) =
      Aegis.MaxSizeSlices.max_size_slices slices := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (slices : Slice Std.I64) (k : Nat)
    (hk : k < slices.val.length)
    (hdiv : 3 ∣ slices.val.length)
    (h3 : 3 ≤ slices.val.length)
    (h500 : slices.val.length ≤ 500)
    (hval : ∀ i, i < slices.val.length → 1 ≤ entry slices i ∧ entry slices i ≤ 1000), Aegis.MaxSizeSlices.max_size_slices (rotateSlice slices k) =
      Aegis.MaxSizeSlices.max_size_slices slices) := by
  sorry

/-- max_size_slices(rev) = max_size_slices(slices).
  Preconditions: Let m = len(slices) and n = m/3. Assume m is divisible by 3, m >= 3, m <= 500, and for every i with 0 <= i < m, 1 <= slices[i] <= 1000. Define the reversed slice rev of length m by rev[i] = slices[m-1-i]. -/
theorem spec_9 (slices : Slice Std.I64)
    (hdiv : 3 ∣ slices.val.length)
    (h3 : 3 ≤ slices.val.length)
    (h500 : slices.val.length ≤ 500)
    (hval : ∀ i, i < slices.val.length → 1 ≤ entry slices i ∧ entry slices i ≤ 1000) :
    Aegis.MaxSizeSlices.max_size_slices (reverseSlice slices) =
      Aegis.MaxSizeSlices.max_size_slices slices := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (slices : Slice Std.I64)
    (hdiv : 3 ∣ slices.val.length)
    (h3 : 3 ≤ slices.val.length)
    (h500 : slices.val.length ≤ 500)
    (hval : ∀ i, i < slices.val.length → 1 ≤ entry slices i ∧ entry slices i ≤ 1000), Aegis.MaxSizeSlices.max_size_slices (reverseSlice slices) =
      Aegis.MaxSizeSlices.max_size_slices slices) := by
  sorry

/-- max_size_slices(shifted) = max_size_slices(slices) + n * c.
  Preconditions: Let m = len(slices) and n = m/3. Assume m is divisible by 3, m >= 3, m <= 500, and for every i with 0 <= i < m, 1 <= slices[i] <= 1000. Let c be an integer such that for every i with 0 <= i < m, 1 <= slices[i] + c <= 1000. Define the shifted slice shifted[i] = slices[i] + c. -/
theorem spec_10 (slices : Slice Std.I64) (c : Int)
    (hdiv : 3 ∣ slices.val.length)
    (h3 : 3 ≤ slices.val.length)
    (h500 : slices.val.length ≤ 500)
    (hval : ∀ i, i < slices.val.length → 1 ≤ entry slices i ∧ entry slices i ≤ 1000)
    (hshift : ∀ i, i < slices.val.length →
      1 ≤ entry slices i + c ∧ entry slices i + c ≤ 1000) :
    ∃ r r', Aegis.MaxSizeSlices.max_size_slices (shiftSlice slices c) = ok r ∧
      Aegis.MaxSizeSlices.max_size_slices slices = ok r' ∧
        r.val = r'.val + (groupCount slices.val.length : Int) * c := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (slices : Slice Std.I64) (c : Int)
    (hdiv : 3 ∣ slices.val.length)
    (h3 : 3 ≤ slices.val.length)
    (h500 : slices.val.length ≤ 500)
    (hval : ∀ i, i < slices.val.length → 1 ≤ entry slices i ∧ entry slices i ≤ 1000)
    (hshift : ∀ i, i < slices.val.length →
      1 ≤ entry slices i + c ∧ entry slices i + c ≤ 1000), ∃ r r', Aegis.MaxSizeSlices.max_size_slices (shiftSlice slices c) = ok r ∧
      Aegis.MaxSizeSlices.max_size_slices slices = ok r' ∧
        r.val = r'.val + (groupCount slices.val.length : Int) * c) := by
  sorry

/-- max_size_slices(scaled) = k * max_size_slices(slices).
  Preconditions: Let m = len(slices) and n = m/3. Assume m is divisible by 3, m >= 3, m <= 500, and for every i with 0 <= i < m, 1 <= slices[i] <= 1000. Let k be an integer with k >= 1 such that for every i with 0 <= i < m, 1 <= k * slices[i] <= 1000. Define the scaled slice scaled[i] = k * slices[i]. -/
theorem spec_11 (slices : Slice Std.I64) (k : Int)
    (hk : 1 ≤ k)
    (hdiv : 3 ∣ slices.val.length)
    (h3 : 3 ≤ slices.val.length)
    (h500 : slices.val.length ≤ 500)
    (hval : ∀ i, i < slices.val.length → 1 ≤ entry slices i ∧ entry slices i ≤ 1000)
    (hscale : ∀ i, i < slices.val.length →
      1 ≤ k * entry slices i ∧ k * entry slices i ≤ 1000) :
    ∃ r r', Aegis.MaxSizeSlices.max_size_slices (scaleSlice slices k) = ok r ∧
      Aegis.MaxSizeSlices.max_size_slices slices = ok r' ∧ r.val = k * r'.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (slices : Slice Std.I64) (k : Int)
    (hk : 1 ≤ k)
    (hdiv : 3 ∣ slices.val.length)
    (h3 : 3 ≤ slices.val.length)
    (h500 : slices.val.length ≤ 500)
    (hval : ∀ i, i < slices.val.length → 1 ≤ entry slices i ∧ entry slices i ≤ 1000)
    (hscale : ∀ i, i < slices.val.length →
      1 ≤ k * entry slices i ∧ k * entry slices i ≤ 1000), ∃ r r', Aegis.MaxSizeSlices.max_size_slices (scaleSlice slices k) = ok r ∧
      Aegis.MaxSizeSlices.max_size_slices slices = ok r' ∧ r.val = k * r'.val) := by
  sorry

/-- max_size_slices(a) <= max_size_slices(b).
  Preconditions: Let m = 3n with n >= 1 and m <= 500. Let a and b be two slices of length m, both satisfying 1 <= a[i] <= 1000 and 1 <= b[i] <= 1000 for all i with 0 <= i < m, and assume a[i] <= b[i] for every i with 0 <= i < m. -/
theorem spec_12 (a b : Slice Std.I64)
    (hlen : b.val.length = a.val.length)
    (hdiv : 3 ∣ a.val.length)
    (h3 : 3 ≤ a.val.length)
    (h500 : a.val.length ≤ 500)
    (hvala : ∀ i, i < a.val.length → 1 ≤ entry a i ∧ entry a i ≤ 1000)
    (hvalb : ∀ i, i < b.val.length → 1 ≤ entry b i ∧ entry b i ≤ 1000)
    (hle : ∀ i, i < a.val.length → entry a i ≤ entry b i) :
    ∃ ra rb, Aegis.MaxSizeSlices.max_size_slices a = ok ra ∧
      Aegis.MaxSizeSlices.max_size_slices b = ok rb ∧ ra.val ≤ rb.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (a b : Slice Std.I64)
    (hlen : b.val.length = a.val.length)
    (hdiv : 3 ∣ a.val.length)
    (h3 : 3 ≤ a.val.length)
    (h500 : a.val.length ≤ 500)
    (hvala : ∀ i, i < a.val.length → 1 ≤ entry a i ∧ entry a i ≤ 1000)
    (hvalb : ∀ i, i < b.val.length → 1 ≤ entry b i ∧ entry b i ≤ 1000)
    (hle : ∀ i, i < a.val.length → entry a i ≤ entry b i), ∃ ra rb, Aegis.MaxSizeSlices.max_size_slices a = ok ra ∧
      Aegis.MaxSizeSlices.max_size_slices b = ok rb ∧ ra.val ≤ rb.val) := by
  sorry

end AegisSpec.MaxSizeSlices

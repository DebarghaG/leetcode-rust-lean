import Aegis.PyramidTransition.Code.Funs

/-!
# Specifications of `Aegis.PyramidTransition.pyramid_transition`

LeetCode problem `pyramid-transition-matrix`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.PyramidTransition

  namespace AegisSpec.PyramidTransition

  def IsHexLetter (b : U8) : Prop :=
    b.val = 65 ∨ b.val = 66 ∨ b.val = 67 ∨ b.val = 68 ∨ b.val = 69 ∨ b.val = 70

  def StartsWithPair (p : alloc.vec.Vec U8) (a b : U8) : Prop :=
    ∃ c : U8, p.val = [a, b, c]

  def TripleAllowed (allowed : List (alloc.vec.Vec U8)) (a b c : U8) : Prop :=
    ∃ p ∈ allowed, p.val = [a, b, c]

  def RowStep (allowed : List (alloc.vec.Vec U8)) (top bot : List U8) : Prop :=
    bot.length + 1 = top.length ∧
      ∀ (i : ℕ) (a b c : U8),
        top[i]? = some a → top[i + 1]? = some b → bot[i]? = some c →
          TripleAllowed allowed a b c

  def IsPyramidWitness (bottom : Slice U8) (allowed : Slice (alloc.vec.Vec U8))
      (R : ℕ → List U8) : Prop :=
    R 0 = bottom.val ∧
      (∀ k, k < bottom.val.length → (R k).length = bottom.val.length - k) ∧
        (∀ k, k + 1 < bottom.val.length → RowStep allowed.val (R k) (R (k + 1)))

  def triangleCount (n : ℕ) : ℕ :=
    ((List.range (n - 1)).map (fun k => n - k - 1)).sum

  /-- The function returns a result r (it does not fail). Let n = len(bottom). Then r = true if and only if there exist byte arrays R_0, R_1, ..., R_{n-1} such that R_0 = bottom, len(R_k) = n-k for every k with 0 <= k < n, and for every k with 0 <= k < n-1 and every i with 0 <= i < n-k-1, there exists p in allowed with p[0]=R_k[i], p[1]=R_k[i+1], and p[2]=R_{k+1}[i]. Equivalently, r = false if and only if no such sequence of rows exists.
    Preconditions: len(bottom) is between 2 and 6 inclusive; len(allowed) is between 0 and 216 inclusive; every element p of allowed has len(p)=3; every byte in bottom and in every p in allowed is one of the ASCII codes 65,66,67,68,69,70 ('A'..'F'); the elements of allowed are pairwise distinct. -/
  theorem spec_1 (bottom : Slice U8) (allowed : Slice (alloc.vec.Vec U8))
      (hbot_lo : 2 ≤ bottom.val.length) (hbot_hi : bottom.val.length ≤ 6)
      (hall_lo : 0 ≤ allowed.val.length) (hall_hi : allowed.val.length ≤ 216)
      (hlen : ∀ p ∈ allowed.val, p.val.length = 3)
      (hbot_bytes : ∀ b ∈ bottom.val, IsHexLetter b)
      (hall_bytes : ∀ p ∈ allowed.val, ∀ b ∈ p.val, IsHexLetter b)
      (hdistinct : allowed.val.Nodup) :
      ∃ r : Bool, pyramid_transition bottom allowed = ok r ∧
        (r = true ↔ ∃ R : ℕ → List U8, IsPyramidWitness bottom allowed R) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (bottom : Slice U8) (allowed : Slice (alloc.vec.Vec U8))
        (hbot_lo : 2 ≤ bottom.val.length) (hbot_hi : bottom.val.length ≤ 6)
        (hall_lo : 0 ≤ allowed.val.length) (hall_hi : allowed.val.length ≤ 216)
        (hlen : ∀ p ∈ allowed.val, p.val.length = 3)
        (hbot_bytes : ∀ b ∈ bottom.val, IsHexLetter b)
        (hall_bytes : ∀ p ∈ allowed.val, ∀ b ∈ p.val, IsHexLetter b)
        (hdistinct : allowed.val.Nodup), ∃ r : Bool, pyramid_transition bottom allowed = ok r ∧
          (r = true ↔ ∃ R : ℕ → List U8, IsPyramidWitness bottom allowed R)) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r; it does not fail, panic, or overflow.
    Preconditions: len(bottom) is between 2 and 6 inclusive; len(allowed) is between 0 and 216 inclusive; every element p of allowed has len(p)=3; every byte in bottom and in every p in allowed is one of the ASCII codes 65,66,67,68,69,70 ('A'..'F'); the elements of allowed are pairwise distinct. -/
  theorem spec_2 (bottom : Slice U8) (allowed : Slice (alloc.vec.Vec U8))
      (hbot_lo : 2 ≤ bottom.val.length) (hbot_hi : bottom.val.length ≤ 6)
      (hall_lo : 0 ≤ allowed.val.length) (hall_hi : allowed.val.length ≤ 216)
      (hlen : ∀ p ∈ allowed.val, p.val.length = 3)
      (hbot_bytes : ∀ b ∈ bottom.val, IsHexLetter b)
      (hall_bytes : ∀ p ∈ allowed.val, ∀ b ∈ p.val, IsHexLetter b)
      (hdistinct : allowed.val.Nodup) :
      ∃ r : Bool, pyramid_transition bottom allowed = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (bottom : Slice U8) (allowed : Slice (alloc.vec.Vec U8))
        (hbot_lo : 2 ≤ bottom.val.length) (hbot_hi : bottom.val.length ≤ 6)
        (hall_lo : 0 ≤ allowed.val.length) (hall_hi : allowed.val.length ≤ 216)
        (hlen : ∀ p ∈ allowed.val, p.val.length = 3)
        (hbot_bytes : ∀ b ∈ bottom.val, IsHexLetter b)
        (hall_bytes : ∀ p ∈ allowed.val, ∀ b ∈ p.val, IsHexLetter b)
        (hdistinct : allowed.val.Nodup), ∃ r : Bool, pyramid_transition bottom allowed = ok r) := by
    sorry

  /-- If there exists an index i with 0 <= i < len(bottom)-1 such that no p in allowed satisfies p[0]=bottom[i] and p[1]=bottom[i+1], then the function returns false.
    Preconditions: len(bottom) is between 2 and 6 inclusive; len(allowed) is between 0 and 216 inclusive; every element p of allowed has len(p)=3; every byte in bottom and in every p in allowed is one of the ASCII codes 65,66,67,68,69,70 ('A'..'F'); the elements of allowed are pairwise distinct. -/
  theorem spec_3 (bottom : Slice U8) (allowed : Slice (alloc.vec.Vec U8))
      (hbot_lo : 2 ≤ bottom.val.length) (hbot_hi : bottom.val.length ≤ 6)
      (hall_lo : 0 ≤ allowed.val.length) (hall_hi : allowed.val.length ≤ 216)
      (hlen : ∀ p ∈ allowed.val, p.val.length = 3)
      (hbot_bytes : ∀ b ∈ bottom.val, IsHexLetter b)
      (hall_bytes : ∀ p ∈ allowed.val, ∀ b ∈ p.val, IsHexLetter b)
      (hdistinct : allowed.val.Nodup)
      (hgap : ∃ (i : ℕ) (a b : U8),
        i + 1 < bottom.val.length ∧
          bottom.val[i]? = some a ∧ bottom.val[i + 1]? = some b ∧
            ∀ p ∈ allowed.val, ¬ StartsWithPair p a b) :
      pyramid_transition bottom allowed = ok false := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (bottom : Slice U8) (allowed : Slice (alloc.vec.Vec U8))
        (hbot_lo : 2 ≤ bottom.val.length) (hbot_hi : bottom.val.length ≤ 6)
        (hall_lo : 0 ≤ allowed.val.length) (hall_hi : allowed.val.length ≤ 216)
        (hlen : ∀ p ∈ allowed.val, p.val.length = 3)
        (hbot_bytes : ∀ b ∈ bottom.val, IsHexLetter b)
        (hall_bytes : ∀ p ∈ allowed.val, ∀ b ∈ p.val, IsHexLetter b)
        (hdistinct : allowed.val.Nodup)
        (hgap : ∃ (i : ℕ) (a b : U8),
          i + 1 < bottom.val.length ∧
            bottom.val[i]? = some a ∧ bottom.val[i + 1]? = some b ∧
              ∀ p ∈ allowed.val, ¬ StartsWithPair p a b), pyramid_transition bottom allowed = ok false) := by
    sorry

  /-- Let allowed2 be a superset of allowed as sets of triples, satisfying the stated constraints. If pyramid_transition bottom allowed returns true, then pyramid_transition bottom allowed2 returns true.
    Preconditions: len(bottom) is between 2 and 6 inclusive; len(allowed) and len(allowed2) are between 0 and 216 inclusive; every element of allowed and allowed2 has length 3; every byte in bottom and in every element of allowed and allowed2 is one of the ASCII codes 65,66,67,68,69,70 ('A'..'F'); the elements of allowed and of allowed2 are pairwise distinct; every element of allowed also occurs in allowed2. -/
  theorem spec_4 (bottom : Slice U8) (allowed allowed2 : Slice (alloc.vec.Vec U8))
      (hbot_lo : 2 ≤ bottom.val.length) (hbot_hi : bottom.val.length ≤ 6)
      (hall_lo : 0 ≤ allowed.val.length) (hall_hi : allowed.val.length ≤ 216)
      (hall2_lo : 0 ≤ allowed2.val.length) (hall2_hi : allowed2.val.length ≤ 216)
      (hlen : ∀ p ∈ allowed.val, p.val.length = 3)
      (hlen2 : ∀ p ∈ allowed2.val, p.val.length = 3)
      (hbot_bytes : ∀ b ∈ bottom.val, IsHexLetter b)
      (hall_bytes : ∀ p ∈ allowed.val, ∀ b ∈ p.val, IsHexLetter b)
      (hall2_bytes : ∀ p ∈ allowed2.val, ∀ b ∈ p.val, IsHexLetter b)
      (hdistinct : allowed.val.Nodup) (hdistinct2 : allowed2.val.Nodup)
      (hsub : ∀ p ∈ allowed.val, p ∈ allowed2.val) :
      pyramid_transition bottom allowed = ok true →
        pyramid_transition bottom allowed2 = ok true := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (bottom : Slice U8) (allowed allowed2 : Slice (alloc.vec.Vec U8))
        (hbot_lo : 2 ≤ bottom.val.length) (hbot_hi : bottom.val.length ≤ 6)
        (hall_lo : 0 ≤ allowed.val.length) (hall_hi : allowed.val.length ≤ 216)
        (hall2_lo : 0 ≤ allowed2.val.length) (hall2_hi : allowed2.val.length ≤ 216)
        (hlen : ∀ p ∈ allowed.val, p.val.length = 3)
        (hlen2 : ∀ p ∈ allowed2.val, p.val.length = 3)
        (hbot_bytes : ∀ b ∈ bottom.val, IsHexLetter b)
        (hall_bytes : ∀ p ∈ allowed.val, ∀ b ∈ p.val, IsHexLetter b)
        (hall2_bytes : ∀ p ∈ allowed2.val, ∀ b ∈ p.val, IsHexLetter b)
        (hdistinct : allowed.val.Nodup) (hdistinct2 : allowed2.val.Nodup)
        (hsub : ∀ p ∈ allowed.val, p ∈ allowed2.val), pyramid_transition bottom allowed = ok true →
          pyramid_transition bottom allowed2 = ok true) := by
    sorry

  /-- For any allowed' obtained by reordering the elements of allowed (same length and same multiset of triples), pyramid_transition bottom allowed' returns the same Bool result as pyramid_transition bottom allowed.
    Preconditions: len(bottom) is between 2 and 6 inclusive; len(allowed) is between 0 and 216 inclusive; every element p of allowed has len(p)=3; every byte in bottom and in every p in allowed is one of the ASCII codes 65,66,67,68,69,70 ('A'..'F'); the elements of allowed are pairwise distinct; allowed' is any permutation of the elements of allowed. -/
  theorem spec_5 (bottom : Slice U8) (allowed allowed' : Slice (alloc.vec.Vec U8))
      (hbot_lo : 2 ≤ bottom.val.length) (hbot_hi : bottom.val.length ≤ 6)
      (hall_lo : 0 ≤ allowed.val.length) (hall_hi : allowed.val.length ≤ 216)
      (hlen : ∀ p ∈ allowed.val, p.val.length = 3)
      (hbot_bytes : ∀ b ∈ bottom.val, IsHexLetter b)
      (hall_bytes : ∀ p ∈ allowed.val, ∀ b ∈ p.val, IsHexLetter b)
      (hdistinct : allowed.val.Nodup)
      (hperm : allowed.val.Perm allowed'.val) :
      pyramid_transition bottom allowed' = pyramid_transition bottom allowed := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (bottom : Slice U8) (allowed allowed' : Slice (alloc.vec.Vec U8))
        (hbot_lo : 2 ≤ bottom.val.length) (hbot_hi : bottom.val.length ≤ 6)
        (hall_lo : 0 ≤ allowed.val.length) (hall_hi : allowed.val.length ≤ 216)
        (hlen : ∀ p ∈ allowed.val, p.val.length = 3)
        (hbot_bytes : ∀ b ∈ bottom.val, IsHexLetter b)
        (hall_bytes : ∀ p ∈ allowed.val, ∀ b ∈ p.val, IsHexLetter b)
        (hdistinct : allowed.val.Nodup)
        (hperm : allowed.val.Perm allowed'.val), pyramid_transition bottom allowed' = pyramid_transition bottom allowed) := by
    sorry

  /-- Let pi be any bijection of the six ASCII codes 'A'..'F'. Let bottom' be obtained from bottom by replacing every byte b with pi(b), and let allowed' be obtained from allowed by replacing every byte b in every p with pi(b), preserving order. Then pyramid_transition bottom' allowed' returns the same Bool result as pyramid_transition bottom allowed.
    Preconditions: len(bottom) is between 2 and 6 inclusive; len(allowed) is between 0 and 216 inclusive; every element p of allowed has len(p)=3; every byte in bottom and in every p in allowed is one of the ASCII codes 65,66,67,68,69,70 ('A'..'F'); the elements of allowed are pairwise distinct; pi is any bijection from {65,66,67,68,69,70} to itself; bottom' and allowed' are the bytewise pi-images of bottom and allowed. -/
  theorem spec_6 (bottom : Slice U8) (allowed : Slice (alloc.vec.Vec U8))
      (π : U8 → U8) (bottom' : Slice U8) (allowed' : Slice (alloc.vec.Vec U8))
      (hbot_lo : 2 ≤ bottom.val.length) (hbot_hi : bottom.val.length ≤ 6)
      (hall_lo : 0 ≤ allowed.val.length) (hall_hi : allowed.val.length ≤ 216)
      (hlen : ∀ p ∈ allowed.val, p.val.length = 3)
      (hbot_bytes : ∀ b ∈ bottom.val, IsHexLetter b)
      (hall_bytes : ∀ p ∈ allowed.val, ∀ b ∈ p.val, IsHexLetter b)
      (hdistinct : allowed.val.Nodup)
      (hπ_maps : ∀ b, IsHexLetter b → IsHexLetter (π b))
      (hπ_inj : ∀ a b, IsHexLetter a → IsHexLetter b → π a = π b → a = b)
      (hbottom' : bottom'.val = bottom.val.map π)
      (hallowed' : allowed'.val.map (fun p => p.val) = allowed.val.map (fun p => p.val.map π)) :
      pyramid_transition bottom' allowed' = pyramid_transition bottom allowed := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (bottom : Slice U8) (allowed : Slice (alloc.vec.Vec U8))
        (π : U8 → U8) (bottom' : Slice U8) (allowed' : Slice (alloc.vec.Vec U8))
        (hbot_lo : 2 ≤ bottom.val.length) (hbot_hi : bottom.val.length ≤ 6)
        (hall_lo : 0 ≤ allowed.val.length) (hall_hi : allowed.val.length ≤ 216)
        (hlen : ∀ p ∈ allowed.val, p.val.length = 3)
        (hbot_bytes : ∀ b ∈ bottom.val, IsHexLetter b)
        (hall_bytes : ∀ p ∈ allowed.val, ∀ b ∈ p.val, IsHexLetter b)
        (hdistinct : allowed.val.Nodup)
        (hπ_maps : ∀ b, IsHexLetter b → IsHexLetter (π b))
        (hπ_inj : ∀ a b, IsHexLetter a → IsHexLetter b → π a = π b → a = b)
        (hbottom' : bottom'.val = bottom.val.map π)
        (hallowed' : allowed'.val.map (fun p => p.val) = allowed.val.map (fun p => p.val.map π)), pyramid_transition bottom' allowed' = pyramid_transition bottom allowed) := by
    sorry

  /-- Whenever the function returns true, there exists a valid pyramid witness R_0,...,R_{n-1} with n=len(bottom), R_0=bottom, len(R_k)=n-k for every k with 0 <= k < n, and for every k with 0 <= k < n-1 and every i with 0 <= i < n-k-1, the triple [R_k[i], R_k[i+1], R_{k+1}[i]] is an allowed pattern. Consequently the witness has exactly n rows and exactly n*(n-1)/2 triangular patterns.
    Preconditions: len(bottom) is between 2 and 6 inclusive; len(allowed) is between 0 and 216 inclusive; every element p of allowed has len(p)=3; every byte in bottom and in every p in allowed is one of the ASCII codes 65,66,67,68,69,70 ('A'..'F'); the elements of allowed are pairwise distinct. -/
  theorem spec_7 (bottom : Slice U8) (allowed : Slice (alloc.vec.Vec U8))
      (hbot_lo : 2 ≤ bottom.val.length) (hbot_hi : bottom.val.length ≤ 6)
      (hall_lo : 0 ≤ allowed.val.length) (hall_hi : allowed.val.length ≤ 216)
      (hlen : ∀ p ∈ allowed.val, p.val.length = 3)
      (hbot_bytes : ∀ b ∈ bottom.val, IsHexLetter b)
      (hall_bytes : ∀ p ∈ allowed.val, ∀ b ∈ p.val, IsHexLetter b)
      (hdistinct : allowed.val.Nodup) :
      pyramid_transition bottom allowed = ok true →
        (∃ R : ℕ → List U8, IsPyramidWitness bottom allowed R) ∧
          triangleCount bottom.val.length = bottom.val.length * (bottom.val.length - 1) / 2 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (bottom : Slice U8) (allowed : Slice (alloc.vec.Vec U8))
        (hbot_lo : 2 ≤ bottom.val.length) (hbot_hi : bottom.val.length ≤ 6)
        (hall_lo : 0 ≤ allowed.val.length) (hall_hi : allowed.val.length ≤ 216)
        (hlen : ∀ p ∈ allowed.val, p.val.length = 3)
        (hbot_bytes : ∀ b ∈ bottom.val, IsHexLetter b)
        (hall_bytes : ∀ p ∈ allowed.val, ∀ b ∈ p.val, IsHexLetter b)
        (hdistinct : allowed.val.Nodup), pyramid_transition bottom allowed = ok true →
          (∃ R : ℕ → List U8, IsPyramidWitness bottom allowed R) ∧
            triangleCount bottom.val.length = bottom.val.length * (bottom.val.length - 1) / 2) := by
    sorry

  end AegisSpec.PyramidTransition

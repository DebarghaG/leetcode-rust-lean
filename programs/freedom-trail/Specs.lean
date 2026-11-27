import Aegis.FindRotateSteps.Code.Funs

/-!
# Specifications of `Aegis.FindRotateSteps.find_rotate_steps`

LeetCode problem `freedom-trail`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.FindRotateSteps

  open Aegis.FindRotateSteps (find_rotate_steps)

  def ringDist (n a b : Nat) : Nat :=
    min (a - b + (b - a)) (n - (a - b + (b - a)))

  def occursAt (ring : List U8) (c : U8) (p : Nat) : Prop :=
    ∃ (h : p < ring.length), ring.get ⟨p, h⟩ = c

  def positions (ring : List U8) (c : U8) : List Nat :=
    ((List.range ring.length).zip ring).filterMap
      (fun pr => if pr.2 = c then some pr.1 else none)

  def IsPath (ring key : List U8) (ps : List Nat) : Prop :=
    List.Forall₂ (fun p c => occursAt ring c p) ps key

  def pathCost (n : Nat) (ps : List Nat) : Nat :=
    ps.length + (match ps with | [] => 0 | p0 :: _ => ringDist n 0 p0)
      + ((ps.zip ps.tail).map (fun pr => ringDist n pr.1 pr.2)).sum

  def listMin (l : List Nat) : Nat := (l.min?).getD 0

  def minInit (n : Nat) (ring : List U8) (c : U8) : Nat :=
    listMin ((positions ring c).map (fun p => ringDist n 0 p))

  def minStep (n : Nat) (ring : List U8) (c₁ c₂ : U8) : Nat :=
    listMin ((positions ring c₁).flatMap
      (fun p => (positions ring c₂).map (fun q => ringDist n p q)))

  def lowerBound (n : Nat) (ring key : List U8) : Nat :=
    (match key with | [] => 0 | c0 :: _ => minInit n ring c0)
      + ((key.zip key.tail).map (fun pr => minStep n ring pr.1 pr.2)).sum

  /-- Let n = len(ring) and m = len(key). For 0 <= a,b < n let dist(a,b) = min(|a-b|, n - |a-b|). The function returns a result r, and r is the minimum, over all sequences p_0,...,p_(m-1) of indices with 0 <= p_i < n and ring[p_i] = key[i] for every i, of the value m + dist(0,p_0) + sum_{i=1}^{m-1} dist(p_(i-1),p_i). The term m counts the m button presses; each dist term counts rotations between successive aligned positions; the initial aligned position is index 0.
    Preconditions: 1 <= len(ring) <= 100, 1 <= len(key) <= 100, every byte of ring and key is an ASCII lower-case letter (97..122), and for every i with 0 <= i < len(key) there exists p with 0 <= p < len(ring) and ring[p] = key[i] (so key is spellable). -/
  theorem spec_1 (ring key : Slice U8)
      (hring_len : 1 ≤ ring.val.length) (hring_len_ub : ring.val.length ≤ 100)
      (hkey_len : 1 ≤ key.val.length) (hkey_len_ub : key.val.length ≤ 100)
      (hring_lower : ∀ b ∈ ring.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hkey_lower : ∀ b ∈ key.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hspell : ∀ i (hi : i < key.val.length),
        ∃ p, occursAt ring.val (key.val.get ⟨i, hi⟩) p) :
      ∃ r, find_rotate_steps ring key = Result.ok r ∧
        (∀ ps, IsPath ring.val key.val ps →
          r.val ≤ (pathCost ring.val.length ps : Int)) ∧
        (∃ ps, IsPath ring.val key.val ps ∧ r.val = (pathCost ring.val.length ps : Int)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (ring key : Slice U8)
        (hring_len : 1 ≤ ring.val.length) (hring_len_ub : ring.val.length ≤ 100)
        (hkey_len : 1 ≤ key.val.length) (hkey_len_ub : key.val.length ≤ 100)
        (hring_lower : ∀ b ∈ ring.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hkey_lower : ∀ b ∈ key.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hspell : ∀ i (hi : i < key.val.length),
          ∃ p, occursAt ring.val (key.val.get ⟨i, hi⟩) p), ∃ r, find_rotate_steps ring key = Result.ok r ∧
          (∀ ps, IsPath ring.val key.val ps →
            r.val ≤ (pathCost ring.val.length ps : Int)) ∧
          (∃ ps, IsPath ring.val key.val ps ∧ r.val = (pathCost ring.val.length ps : Int))) := by
    sorry

  /-- For every ring and key satisfying the preconditions, the function returns a result r; it does not fail, panic, overflow, or access an index out of bounds.
    Preconditions: 1 <= len(ring) <= 100, 1 <= len(key) <= 100, every byte of ring and key is an ASCII lower-case letter (97..122), and for every i with 0 <= i < len(key) there exists p with 0 <= p < len(ring) and ring[p] = key[i]. -/
  theorem spec_2 (ring key : Slice U8)
      (hring_len : 1 ≤ ring.val.length) (hring_len_ub : ring.val.length ≤ 100)
      (hkey_len : 1 ≤ key.val.length) (hkey_len_ub : key.val.length ≤ 100)
      (hring_lower : ∀ b ∈ ring.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hkey_lower : ∀ b ∈ key.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hspell : ∀ i (hi : i < key.val.length),
        ∃ p, occursAt ring.val (key.val.get ⟨i, hi⟩) p) :
      ∃ r, find_rotate_steps ring key = Result.ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (ring key : Slice U8)
        (hring_len : 1 ≤ ring.val.length) (hring_len_ub : ring.val.length ≤ 100)
        (hkey_len : 1 ≤ key.val.length) (hkey_len_ub : key.val.length ≤ 100)
        (hring_lower : ∀ b ∈ ring.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hkey_lower : ∀ b ∈ key.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hspell : ∀ i (hi : i < key.val.length),
          ∃ p, occursAt ring.val (key.val.get ⟨i, hi⟩) p), ∃ r, find_rotate_steps ring key = Result.ok r) := by
    sorry

  /-- Let n = len(ring), m = len(key), and dist(a,b) = min(|a-b|, n - |a-b|) for 0 <= a,b < n. Whenever the function returns a result r, for every sequence q_0,...,q_(m-1) of indices with 0 <= q_i < n and ring[q_i] = key[i] for every i, we have r <= m + dist(0,q_0) + sum_{i=1}^{m-1} dist(q_(i-1),q_i).
    Preconditions: len(ring) >= 1, len(key) >= 1, every byte of ring and key is an ASCII lower-case letter (97..122), and for every i with 0 <= i < len(key) there exists p with 0 <= p < len(ring) and ring[p] = key[i]. -/
  theorem spec_3 (ring key : Slice U8)
      (hring_len : 1 ≤ ring.val.length)
      (hkey_len : 1 ≤ key.val.length)
      (hring_lower : ∀ b ∈ ring.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hkey_lower : ∀ b ∈ key.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hspell : ∀ i (hi : i < key.val.length),
        ∃ p, occursAt ring.val (key.val.get ⟨i, hi⟩) p) :
      ∀ r, find_rotate_steps ring key = Result.ok r →
        ∀ qs, IsPath ring.val key.val qs →
          r.val ≤ (pathCost ring.val.length qs : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (ring key : Slice U8)
        (hring_len : 1 ≤ ring.val.length)
        (hkey_len : 1 ≤ key.val.length)
        (hring_lower : ∀ b ∈ ring.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hkey_lower : ∀ b ∈ key.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hspell : ∀ i (hi : i < key.val.length),
          ∃ p, occursAt ring.val (key.val.get ⟨i, hi⟩) p), ∀ r, find_rotate_steps ring key = Result.ok r →
          ∀ qs, IsPath ring.val key.val qs →
            r.val ≤ (pathCost ring.val.length qs : Int)) := by
    sorry

  /-- Let n = len(ring), m = len(key), dist(a,b) = min(|a-b|, n - |a-b|) for 0 <= a,b < n, and Pos(i) = {p | 0 <= p < n and ring[p] = key[i]}. Whenever the function returns a result r, r >= m + min_{p in Pos(0)} dist(0,p) + sum_{i=1}^{m-1} min_{a in Pos(i-1), b in Pos(i)} dist(a,b).
    Preconditions: len(ring) >= 1, len(key) >= 1, every byte of ring and key is an ASCII lower-case letter (97..122), and for every i with 0 <= i < len(key) there exists p with 0 <= p < len(ring) and ring[p] = key[i]. -/
  theorem spec_4 (ring key : Slice U8)
      (hring_len : 1 ≤ ring.val.length)
      (hkey_len : 1 ≤ key.val.length)
      (hring_lower : ∀ b ∈ ring.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hkey_lower : ∀ b ∈ key.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hspell : ∀ i (hi : i < key.val.length),
        ∃ p, occursAt ring.val (key.val.get ⟨i, hi⟩) p) :
      ∀ r, find_rotate_steps ring key = Result.ok r →
        (key.val.length : Int) + (lowerBound ring.val.length ring.val key.val : Int) ≤ r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (ring key : Slice U8)
        (hring_len : 1 ≤ ring.val.length)
        (hkey_len : 1 ≤ key.val.length)
        (hring_lower : ∀ b ∈ ring.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hkey_lower : ∀ b ∈ key.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hspell : ∀ i (hi : i < key.val.length),
          ∃ p, occursAt ring.val (key.val.get ⟨i, hi⟩) p), ∀ r, find_rotate_steps ring key = Result.ok r →
          (key.val.length : Int) + (lowerBound ring.val.length ring.val key.val : Int) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r = len(key) + min_{p | 0 <= p < len(ring) and ring[p] = c} dist(0,p), where dist(a,b) = min(|a-b|, len(ring) - |a-b|).
    Preconditions: len(ring) >= 1, len(key) >= 1, every byte of ring and key is an ASCII lower-case letter (97..122), every key character equals one byte c, and c occurs in ring. -/
  theorem spec_5 (ring key : Slice U8) (c : U8)
      (hring_len : 1 ≤ ring.val.length)
      (hkey_len : 1 ≤ key.val.length)
      (hring_lower : ∀ b ∈ ring.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hkey_lower : ∀ b ∈ key.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hkey_const : ∀ b ∈ key.val, b = c)
      (hocc : ∃ p, occursAt ring.val c p) :
      ∀ r, find_rotate_steps ring key = Result.ok r →
        r.val = (key.val.length : Int) + (minInit ring.val.length ring.val c : Int) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (ring key : Slice U8) (c : U8)
        (hring_len : 1 ≤ ring.val.length)
        (hkey_len : 1 ≤ key.val.length)
        (hring_lower : ∀ b ∈ ring.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hkey_lower : ∀ b ∈ key.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hkey_const : ∀ b ∈ key.val, b = c)
        (hocc : ∃ p, occursAt ring.val c p), ∀ r, find_rotate_steps ring key = Result.ok r →
          r.val = (key.val.length : Int) + (minInit ring.val.length ring.val c : Int)) := by
    sorry

  /-- Let r1 be the result for (ring,key1) and r2 the result for (ring,key2). Whenever both functions return, r1 <= r2.
    Preconditions: len(ring) >= 1; key1 and key2 are nonempty spellable keys for the same ring; every byte of ring, key1, and key2 is an ASCII lower-case letter; key1 is a subsequence of key2, meaning len(key1) <= len(key2) and there exist indices 0 <= j_0 < j_1 < ... < j_(len(key1)-1) < len(key2) with key1[t] = key2[j_t] for all t. -/
  theorem spec_6 (ring key₁ key₂ : Slice U8)
      (hring_len : 1 ≤ ring.val.length)
      (hkey₁_len : 1 ≤ key₁.val.length)
      (hkey₂_len : 1 ≤ key₂.val.length)
      (hring_lower : ∀ b ∈ ring.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hkey₁_lower : ∀ b ∈ key₁.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hkey₂_lower : ∀ b ∈ key₂.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hspell₁ : ∀ i (hi : i < key₁.val.length),
        ∃ p, occursAt ring.val (key₁.val.get ⟨i, hi⟩) p)
      (hspell₂ : ∀ i (hi : i < key₂.val.length),
        ∃ p, occursAt ring.val (key₂.val.get ⟨i, hi⟩) p)
      (hsub : key₁.val.Sublist key₂.val) :
      ∀ r₁ r₂, find_rotate_steps ring key₁ = Result.ok r₁ →
        find_rotate_steps ring key₂ = Result.ok r₂ → r₁.val ≤ r₂.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (ring key₁ key₂ : Slice U8)
        (hring_len : 1 ≤ ring.val.length)
        (hkey₁_len : 1 ≤ key₁.val.length)
        (hkey₂_len : 1 ≤ key₂.val.length)
        (hring_lower : ∀ b ∈ ring.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hkey₁_lower : ∀ b ∈ key₁.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hkey₂_lower : ∀ b ∈ key₂.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hspell₁ : ∀ i (hi : i < key₁.val.length),
          ∃ p, occursAt ring.val (key₁.val.get ⟨i, hi⟩) p)
        (hspell₂ : ∀ i (hi : i < key₂.val.length),
          ∃ p, occursAt ring.val (key₂.val.get ⟨i, hi⟩) p)
        (hsub : key₁.val.Sublist key₂.val), ∀ r₁ r₂, find_rotate_steps ring key₁ = Result.ok r₁ →
          find_rotate_steps ring key₂ = Result.ok r₂ → r₁.val ≤ r₂.val) := by
    sorry

  /-- Let r be the result for (ring,key) and r' the result for (ring,key'). Whenever both functions return, r' <= r + 1 + floor(len(ring)/2).
    Preconditions: len(ring) >= 1, len(key) >= 1, key' is key with one extra byte c appended so len(key') = len(key)+1, key'[i] = key[i] for 0 <= i < len(key), and key'[len(key)] = c; ring, key, and key' use ASCII lower-case letters; key and key' are spellable. -/
  theorem spec_7 (ring key key' : Slice U8) (c : U8)
      (hring_len : 1 ≤ ring.val.length)
      (hkey_len : 1 ≤ key.val.length)
      (hkey'_eq : key'.val = key.val ++ [c])
      (hring_lower : ∀ b ∈ ring.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hkey_lower : ∀ b ∈ key.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hkey'_lower : ∀ b ∈ key'.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hspell : ∀ i (hi : i < key.val.length),
        ∃ p, occursAt ring.val (key.val.get ⟨i, hi⟩) p)
      (hspell' : ∀ i (hi : i < key'.val.length),
        ∃ p, occursAt ring.val (key'.val.get ⟨i, hi⟩) p) :
      ∀ r r', find_rotate_steps ring key = Result.ok r →
        find_rotate_steps ring key' = Result.ok r' →
          r'.val ≤ r.val + 1 + ((ring.val.length / 2 : Nat) : Int) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (ring key key' : Slice U8) (c : U8)
        (hring_len : 1 ≤ ring.val.length)
        (hkey_len : 1 ≤ key.val.length)
        (hkey'_eq : key'.val = key.val ++ [c])
        (hring_lower : ∀ b ∈ ring.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hkey_lower : ∀ b ∈ key.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hkey'_lower : ∀ b ∈ key'.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hspell : ∀ i (hi : i < key.val.length),
          ∃ p, occursAt ring.val (key.val.get ⟨i, hi⟩) p)
        (hspell' : ∀ i (hi : i < key'.val.length),
          ∃ p, occursAt ring.val (key'.val.get ⟨i, hi⟩) p), ∀ r r', find_rotate_steps ring key = Result.ok r →
          find_rotate_steps ring key' = Result.ok r' →
            r'.val ≤ r.val + 1 + ((ring.val.length / 2 : Nat) : Int)) := by
    sorry

  /-- Whenever the function returns results for both (ring,key) and (ring',key'), the two results are equal.
    Preconditions: len(ring) >= 1, len(key) >= 1, every byte of ring and key is an ASCII lower-case letter, key is spellable from ring, and f is an injective mapping from the 26 lower-case letters to lower-case letters. ring' and key' are obtained by ring'[i] = f(ring[i]) and key'[j] = f(key[j]). -/
  theorem spec_8 (ring key ring' key' : Slice U8) (f : U8 → U8)
      (hring_len : 1 ≤ ring.val.length)
      (hkey_len : 1 ≤ key.val.length)
      (hring_lower : ∀ b ∈ ring.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hkey_lower : ∀ b ∈ key.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hspell : ∀ i (hi : i < key.val.length),
        ∃ p, occursAt ring.val (key.val.get ⟨i, hi⟩) p)
      (hf_lower : ∀ b, 97 ≤ b.val → b.val ≤ 122 →
        97 ≤ (f b).val ∧ (f b).val ≤ 122)
      (hf_inj : ∀ a b, 97 ≤ a.val → a.val ≤ 122 → 97 ≤ b.val → b.val ≤ 122 →
        f a = f b → a = b)
      (hring' : ring'.val = ring.val.map f)
      (hkey' : key'.val = key.val.map f) :
      ∀ r r', find_rotate_steps ring key = Result.ok r →
        find_rotate_steps ring' key' = Result.ok r' → r.val = r'.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (ring key ring' key' : Slice U8) (f : U8 → U8)
        (hring_len : 1 ≤ ring.val.length)
        (hkey_len : 1 ≤ key.val.length)
        (hring_lower : ∀ b ∈ ring.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hkey_lower : ∀ b ∈ key.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hspell : ∀ i (hi : i < key.val.length),
          ∃ p, occursAt ring.val (key.val.get ⟨i, hi⟩) p)
        (hf_lower : ∀ b, 97 ≤ b.val → b.val ≤ 122 →
          97 ≤ (f b).val ∧ (f b).val ≤ 122)
        (hf_inj : ∀ a b, 97 ≤ a.val → a.val ≤ 122 → 97 ≤ b.val → b.val ≤ 122 →
          f a = f b → a = b)
        (hring' : ring'.val = ring.val.map f)
        (hkey' : key'.val = key.val.map f), ∀ r r', find_rotate_steps ring key = Result.ok r →
          find_rotate_steps ring' key' = Result.ok r' → r.val = r'.val) := by
    sorry

  /-- Let n = len(ring), m = len(key), and dist(a,b) = min(|a-b|, n - |a-b|). Whenever the function returns a result r, there exists a sequence p_0,...,p_(m-1) of indices with 0 <= p_i < n and ring[p_i] = key[i] for every i such that r = m + dist(0,p_0) + sum_{i=1}^{m-1} dist(p_(i-1),p_i).
    Preconditions: len(ring) >= 1, len(key) >= 1, every byte of ring and key is an ASCII lower-case letter (97..122), and for every i with 0 <= i < len(key) there exists p with 0 <= p < len(ring) and ring[p] = key[i]. -/
  theorem spec_9 (ring key : Slice U8)
      (hring_len : 1 ≤ ring.val.length) (hring_len_ub : ring.val.length ≤ 100)
      (hkey_len : 1 ≤ key.val.length) (hkey_len_ub : key.val.length ≤ 100)
      (hring_lower : ∀ b ∈ ring.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hkey_lower : ∀ b ∈ key.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hspell : ∀ i (hi : i < key.val.length),
        ∃ p, occursAt ring.val (key.val.get ⟨i, hi⟩) p) :
      ∀ r, find_rotate_steps ring key = Result.ok r →
        ∃ ps, IsPath ring.val key.val ps ∧
          r.val = (pathCost ring.val.length ps : Int) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (ring key : Slice U8)
        (hring_len : 1 ≤ ring.val.length) (hring_len_ub : ring.val.length ≤ 100)
        (hkey_len : 1 ≤ key.val.length) (hkey_len_ub : key.val.length ≤ 100)
        (hring_lower : ∀ b ∈ ring.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hkey_lower : ∀ b ∈ key.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hspell : ∀ i (hi : i < key.val.length),
          ∃ p, occursAt ring.val (key.val.get ⟨i, hi⟩) p), ∀ r, find_rotate_steps ring key = Result.ok r →
          ∃ ps, IsPath ring.val key.val ps ∧
            r.val = (pathCost ring.val.length ps : Int)) := by
    sorry

  end AegisSpec.FindRotateSteps

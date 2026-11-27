import Aegis.MaximumGain.Code.Funs

/-!
# Specifications of `Aegis.MaximumGain.maximum_gain`

LeetCode problem `maximum-score-from-removing-substrings`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MaximumGain

namespace AegisSpec.MaximumGain

def isAb (c : U8) : Prop := c.val = 97 ∨ c.val = 98

def allLower (l : List U8) : Prop := ∀ c ∈ l, 97 ≤ c.val ∧ c.val ≤ 122

def allAb (l : List U8) : Prop := ∀ c ∈ l, isAb c

def numA (l : List U8) : Nat := l.countP (fun c => c.val == 97)

def numB (l : List U8) : Nat := l.countP (fun c => c.val == 98)

def abBlocksAux (cur : List U8) (acc : List (List U8)) : List U8 → List (List U8)
  | [] => if cur = [] then acc.reverse else (cur.reverse :: acc).reverse
  | c :: rest =>
      if c.val = 97 ∨ c.val = 98 then abBlocksAux (c :: cur) acc rest
      else abBlocksAux [] (if cur = [] then acc else cur.reverse :: acc) rest

def abBlocks (l : List U8) : List (List U8) := abBlocksAux [] [] l

def blockMin (blk : List U8) : Nat := min (numA blk) (numB blk)

def Msum (l : List U8) : Nat := ((abBlocks l).map blockMin).sum

def covered (m : List (Nat × Nat)) : List Nat := m.map (fun p => p.1) ++ m.map (fun p => p.2)

def IsMatchingAb (l : List U8) (m : List (Nat × Nat)) : Prop :=
  (∀ p ∈ m, p.1 < p.2 ∧ l[p.1]? = some 97#u8 ∧ l[p.2]? = some 98#u8) ∧
    (covered m).Nodup

def IsMatchingBa (l : List U8) (m : List (Nat × Nat)) : Prop :=
  (∀ p ∈ m, p.1 < p.2 ∧ l[p.1]? = some 98#u8 ∧ l[p.2]? = some 97#u8) ∧
    (covered m).Nodup

noncomputable def KAb (l : List U8) : Nat := by
  classical
  exact (Finset.range (l.length + 1)).sup (fun n =>
    if ∃ m : List (Nat × Nat), m.length = n ∧ IsMatchingAb l m then n else 0)

noncomputable def KBa (l : List U8) : Nat := by
  classical
  exact (Finset.range (l.length + 1)).sup (fun n =>
    if ∃ m : List (Nat × Nat), m.length = n ∧ IsMatchingBa l m then n else 0)

noncomputable def KsumAb (l : List U8) : Nat := ((abBlocks l).map KAb).sum

noncomputable def KsumBa (l : List U8) : Nat := ((abBlocks l).map KBa).sum

inductive LegalStep (x y : ℤ) : List U8 → ℤ → List U8 → Prop where
  | ab (p q : List U8) : LegalStep x y (p ++ 97#u8 :: 98#u8 :: q) x (p ++ q)
  | ba (p q : List U8) : LegalStep x y (p ++ 98#u8 :: 97#u8 :: q) y (p ++ q)

inductive LegalSeq (x y : ℤ) : List U8 → ℤ → Nat → List U8 → Prop where
  | nil (u : List U8) : LegalSeq x y u 0 0 u
  | step {u v w : List U8} {g h : ℤ} {n : Nat} :
      LegalStep x y u g v → LegalSeq x y v h n w → LegalSeq x y u (g + h) (n + 1) w

/-- Define a block of s to be a maximal contiguous substring all of whose bytes are 'a' or 'b'. For a block t, let A(t) and B(t) be the numbers of 'a' and 'b' in t, let M(t)=min(A(t),B(t)), let K_ab(t) be the maximum cardinality of a set of pairwise disjoint pairs (i,j) of positions in t with i<j, t[i]='a', t[j]='b', and let K_ba(t) be the analogous maximum with t[i]='b', t[j]='a'. Let M=sum_t M(t), K_ab=sum_t K_ab(t), and K_ba=sum_t K_ba(t). Whenever the function returns a result r, r satisfies: if x>=y then r = x*K_ab + y*(M-K_ab); if y>=x then r = y*K_ba + x*(M-K_ba). When x=y both formulas reduce to x*M.
  Preconditions: 1 <= len(s) <= 100000; every byte of s is a lowercase English letter (ASCII codes 'a' through 'z'); 1 <= x <= 10000; 1 <= y <= 10000. -/
theorem spec_1 (s : Slice U8) (x y : I64)
    (hlen1 : 1 ≤ (s.val).length) (hlen2 : (s.val).length ≤ 100000)
    (hlower : allLower s.val)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10000)
    (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ 10000) :
    ∀ r : I64, maximum_gain s x y = ok r →
      (y.val ≤ x.val →
        r.val = x.val * (KsumAb s.val : ℤ) + y.val * ((Msum s.val : ℤ) - (KsumAb s.val : ℤ))) ∧
      (x.val ≤ y.val →
        r.val = y.val * (KsumBa s.val : ℤ) + x.val * ((Msum s.val : ℤ) - (KsumBa s.val : ℤ))) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice U8) (x y : I64)
    (hlen1 : 1 ≤ (s.val).length) (hlen2 : (s.val).length ≤ 100000)
    (hlower : allLower s.val)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10000)
    (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ 10000), ∀ r : I64, maximum_gain s x y = ok r →
      (y.val ≤ x.val →
        r.val = x.val * (KsumAb s.val : ℤ) + y.val * ((Msum s.val : ℤ) - (KsumAb s.val : ℤ))) ∧
      (x.val ≤ y.val →
        r.val = y.val * (KsumBa s.val : ℤ) + x.val * ((Msum s.val : ℤ) - (KsumBa s.val : ℤ)))) := by
  sorry

/-- For every s, x, and y satisfying the preconditions, the function returns a result r; it does not fail, panic, or overflow.
  Preconditions: 1 <= len(s) <= 100000; every byte of s is a lowercase English letter; 1 <= x <= 10000; 1 <= y <= 10000. -/
theorem spec_2 (s : Slice U8) (x y : I64)
    (hlen1 : 1 ≤ (s.val).length) (hlen2 : (s.val).length ≤ 100000)
    (hlower : allLower s.val)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10000)
    (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ 10000) :
    ∃ r : I64, maximum_gain s x y = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice U8) (x y : I64)
    (hlen1 : 1 ≤ (s.val).length) (hlen2 : (s.val).length ≤ 100000)
    (hlower : allLower s.val)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10000)
    (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ 10000), ∃ r : I64, maximum_gain s x y = ok r) := by
  sorry

/-- Whenever the function returns a result r, there exists a finite sequence of legal operations starting from s, where each operation removes a current adjacent occurrence of 'ab' and adds x or removes a current adjacent occurrence of 'ba' and adds y, such that the total added score is exactly r.
  Preconditions: 1 <= len(s) <= 100000; every byte of s is a lowercase English letter; 1 <= x <= 10000; 1 <= y <= 10000. -/
theorem spec_3 (s : Slice U8) (x y : I64)
    (hlen1 : 1 ≤ (s.val).length) (hlen2 : (s.val).length ≤ 100000)
    (hlower : allLower s.val)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10000)
    (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ 10000) :
    ∀ r : I64, maximum_gain s x y = ok r →
      ∃ (t : List U8) (n : Nat), LegalSeq x.val y.val s.val r.val n t := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice U8) (x y : I64)
    (hlen1 : 1 ≤ (s.val).length) (hlen2 : (s.val).length ≤ 100000)
    (hlower : allLower s.val)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10000)
    (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ 10000), ∀ r : I64, maximum_gain s x y = ok r →
      ∃ (t : List U8) (n : Nat), LegalSeq x.val y.val s.val r.val n t) := by
  sorry

/-- Whenever the function returns a result r, every finite sequence of legal operations starting from s has total score at most r.
  Preconditions: 1 <= len(s) <= 100000; every byte of s is a lowercase English letter; 1 <= x <= 10000; 1 <= y <= 10000. -/
theorem spec_4 (s : Slice U8) (x y : I64)
    (hlen1 : 1 ≤ (s.val).length) (hlen2 : (s.val).length ≤ 100000)
    (hlower : allLower s.val)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10000)
    (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ 10000) :
    ∀ r : I64, maximum_gain s x y = ok r →
      ∀ (t : List U8) (sc : ℤ) (n : Nat), LegalSeq x.val y.val s.val sc n t → sc ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice U8) (x y : I64)
    (hlen1 : 1 ≤ (s.val).length) (hlen2 : (s.val).length ≤ 100000)
    (hlower : allLower s.val)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10000)
    (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ 10000), ∀ r : I64, maximum_gain s x y = ok r →
      ∀ (t : List U8) (sc : ℤ) (n : Nat), LegalSeq x.val y.val s.val sc n t → sc ≤ r.val) := by
  sorry

/-- Let M be the sum, over all maximal contiguous substrings t of s containing only 'a' and 'b', of min(number of 'a' in t, number of 'b' in t). Whenever the function returns a result r, r is achieved by some legal sequence with exactly M removal operations; no legal sequence starting from s contains more than M removal operations.
  Preconditions: 1 <= len(s) <= 100000; every byte of s is a lowercase English letter; 1 <= x <= 10000; 1 <= y <= 10000. -/
theorem spec_5 (s : Slice U8) (x y : I64)
    (hlen1 : 1 ≤ (s.val).length) (hlen2 : (s.val).length ≤ 100000)
    (hlower : allLower s.val)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10000)
    (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ 10000) :
    ∀ r : I64, maximum_gain s x y = ok r →
      (∃ t : List U8, LegalSeq x.val y.val s.val r.val (Msum s.val) t) ∧
      (∀ (t : List U8) (sc : ℤ) (n : Nat), LegalSeq x.val y.val s.val sc n t → n ≤ Msum s.val) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice U8) (x y : I64)
    (hlen1 : 1 ≤ (s.val).length) (hlen2 : (s.val).length ≤ 100000)
    (hlower : allLower s.val)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10000)
    (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ 10000), ∀ r : I64, maximum_gain s x y = ok r →
      (∃ t : List U8, LegalSeq x.val y.val s.val r.val (Msum s.val) t) ∧
      (∀ (t : List U8) (sc : ℤ) (n : Nat), LegalSeq x.val y.val s.val sc n t → n ≤ Msum s.val)) := by
  sorry

/-- Let M be the sum, over all maximal contiguous substrings t of s containing only 'a' and 'b', of min(number of 'a' in t, number of 'b' in t). Whenever the function returns a result r, r >= M * min(x,y).
  Preconditions: 1 <= len(s) <= 100000; every byte of s is a lowercase English letter; 1 <= x <= 10000; 1 <= y <= 10000. -/
theorem spec_6 (s : Slice U8) (x y : I64)
    (hlen1 : 1 ≤ (s.val).length) (hlen2 : (s.val).length ≤ 100000)
    (hlower : allLower s.val)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10000)
    (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ 10000) :
    ∀ r : I64, maximum_gain s x y = ok r →
      (Msum s.val : ℤ) * min x.val y.val ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice U8) (x y : I64)
    (hlen1 : 1 ≤ (s.val).length) (hlen2 : (s.val).length ≤ 100000)
    (hlower : allLower s.val)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10000)
    (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ 10000), ∀ r : I64, maximum_gain s x y = ok r →
      (Msum s.val : ℤ) * min x.val y.val ≤ r.val) := by
  sorry

/-- Let M be the sum, over all maximal contiguous substrings t of s containing only 'a' and 'b', of min(number of 'a' in t, number of 'b' in t). Whenever the function returns a result r, r <= M * max(x,y).
  Preconditions: 1 <= len(s) <= 100000; every byte of s is a lowercase English letter; 1 <= x <= 10000; 1 <= y <= 10000. -/
theorem spec_7 (s : Slice U8) (x y : I64)
    (hlen1 : 1 ≤ (s.val).length) (hlen2 : (s.val).length ≤ 100000)
    (hlower : allLower s.val)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10000)
    (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ 10000) :
    ∀ r : I64, maximum_gain s x y = ok r →
      r.val ≤ (Msum s.val : ℤ) * max x.val y.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice U8) (x y : I64)
    (hlen1 : 1 ≤ (s.val).length) (hlen2 : (s.val).length ≤ 100000)
    (hlower : allLower s.val)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10000)
    (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ 10000), ∀ r : I64, maximum_gain s x y = ok r →
      r.val ≤ (Msum s.val : ℤ) * max x.val y.val) := by
  sorry

/-- Let s be the concatenation p ++ [c] ++ q. If the function returns r for s with x and y, r_p for p with the same x and y, and r_q for q with the same x and y, then r = r_p + r_q.
  Preconditions: 1 <= x <= 10000; 1 <= y <= 10000; p and q are nonempty byte strings all of whose bytes are lowercase English letters; c is a lowercase English letter with c not equal to 'a' and c not equal to 'b'; 1 <= len(p)+1+len(q) <= 100000. -/
theorem spec_8 (s p q : Slice U8) (c : U8) (x y : I64)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10000)
    (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ 10000)
    (hpne : p.val ≠ []) (hqne : q.val ≠ [])
    (hplower : allLower p.val) (hqlower : allLower q.val)
    (hclower : 97 ≤ c.val ∧ c.val ≤ 122)
    (hcne_a : c.val ≠ 97) (hcne_b : c.val ≠ 98)
    (hlen1 : 1 ≤ (p.val).length + 1 + (q.val).length)
    (hlen2 : (p.val).length + 1 + (q.val).length ≤ 100000)
    (hs : s.val = p.val ++ [c] ++ q.val) :
    ∀ r rp rq : I64, maximum_gain s x y = ok r → maximum_gain p x y = ok rp →
      maximum_gain q x y = ok rq → r.val = rp.val + rq.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s p q : Slice U8) (c : U8) (x y : I64)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10000)
    (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ 10000)
    (hpne : p.val ≠ []) (hqne : q.val ≠ [])
    (hplower : allLower p.val) (hqlower : allLower q.val)
    (hclower : 97 ≤ c.val ∧ c.val ≤ 122)
    (hcne_a : c.val ≠ 97) (hcne_b : c.val ≠ 98)
    (hlen1 : 1 ≤ (p.val).length + 1 + (q.val).length)
    (hlen2 : (p.val).length + 1 + (q.val).length ≤ 100000)
    (hs : s.val = p.val ++ [c] ++ q.val), ∀ r rp rq : I64, maximum_gain s x y = ok r → maximum_gain p x y = ok rp →
      maximum_gain q x y = ok rq → r.val = rp.val + rq.val) := by
  sorry

/-- If the function returns r for s and r' for s' with the same x and y, then r = r'.
  Preconditions: 1 <= x <= 10000; 1 <= y <= 10000; s and s' are byte strings of lowercase English letters with the same length n, 1 <= n <= 100000; for every i with 0 <= i < n, either s[i]=s'[i], or both s[i] and s'[i] are different from 'a' and 'b'. -/
theorem spec_9 (s s' : Slice U8) (x y : I64)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10000)
    (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ 10000)
    (hlen1 : 1 ≤ (s.val).length) (hlen2 : (s.val).length ≤ 100000)
    (hlower : allLower s.val) (hlower' : allLower s'.val)
    (hlen : (s.val).length = (s'.val).length)
    (hagree : ∀ (i : Nat) (a b : U8), i < (s.val).length → (s.val)[i]? = some a →
      (s'.val)[i]? = some b →
      a.val = b.val ∨ (a.val ≠ 97 ∧ a.val ≠ 98 ∧ b.val ≠ 97 ∧ b.val ≠ 98)) :
    ∀ r r' : I64, maximum_gain s x y = ok r → maximum_gain s' x y = ok r' → r.val = r'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s s' : Slice U8) (x y : I64)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10000)
    (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ 10000)
    (hlen1 : 1 ≤ (s.val).length) (hlen2 : (s.val).length ≤ 100000)
    (hlower : allLower s.val) (hlower' : allLower s'.val)
    (hlen : (s.val).length = (s'.val).length)
    (hagree : ∀ (i : Nat) (a b : U8), i < (s.val).length → (s.val)[i]? = some a →
      (s'.val)[i]? = some b →
      a.val = b.val ∨ (a.val ≠ 97 ∧ a.val ≠ 98 ∧ b.val ≠ 97 ∧ b.val ≠ 98)), ∀ r r' : I64, maximum_gain s x y = ok r → maximum_gain s' x y = ok r' → r.val = r'.val) := by
  sorry

/-- If the function returns r1 for (s, x1, y) and r2 for (s, x2, y), then r1 <= r2.
  Preconditions: s is a byte string of lowercase English letters with 1 <= len(s) <= 100000; 1 <= y <= 10000; 1 <= x1 <= x2 <= 10000. -/
theorem spec_10 (s : Slice U8) (x1 x2 y : I64)
    (hlen1 : 1 ≤ (s.val).length) (hlen2 : (s.val).length ≤ 100000)
    (hlower : allLower s.val)
    (hx1 : 1 ≤ x1.val) (hx12 : x1.val ≤ x2.val) (hx2 : x2.val ≤ 10000)
    (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ 10000) :
    ∀ r1 r2 : I64, maximum_gain s x1 y = ok r1 → maximum_gain s x2 y = ok r2 →
      r1.val ≤ r2.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : Slice U8) (x1 x2 y : I64)
    (hlen1 : 1 ≤ (s.val).length) (hlen2 : (s.val).length ≤ 100000)
    (hlower : allLower s.val)
    (hx1 : 1 ≤ x1.val) (hx12 : x1.val ≤ x2.val) (hx2 : x2.val ≤ 10000)
    (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ 10000), ∀ r1 r2 : I64, maximum_gain s x1 y = ok r1 → maximum_gain s x2 y = ok r2 →
      r1.val ≤ r2.val) := by
  sorry

/-- If the function returns r1 for (s, x, y1) and r2 for (s, x, y2), then r1 <= r2.
  Preconditions: s is a byte string of lowercase English letters with 1 <= len(s) <= 100000; 1 <= x <= 10000; 1 <= y1 <= y2 <= 10000. -/
theorem spec_11 (s : Slice U8) (x y1 y2 : I64)
    (hlen1 : 1 ≤ (s.val).length) (hlen2 : (s.val).length ≤ 100000)
    (hlower : allLower s.val)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10000)
    (hy1 : 1 ≤ y1.val) (hy12 : y1.val ≤ y2.val) (hy2 : y2.val ≤ 10000) :
    ∀ r1 r2 : I64, maximum_gain s x y1 = ok r1 → maximum_gain s x y2 = ok r2 →
      r1.val ≤ r2.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s : Slice U8) (x y1 y2 : I64)
    (hlen1 : 1 ≤ (s.val).length) (hlen2 : (s.val).length ≤ 100000)
    (hlower : allLower s.val)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10000)
    (hy1 : 1 ≤ y1.val) (hy12 : y1.val ≤ y2.val) (hy2 : y2.val ≤ 10000), ∀ r1 r2 : I64, maximum_gain s x y1 = ok r1 → maximum_gain s x y2 = ok r2 →
      r1.val ≤ r2.val) := by
  sorry

/-- Whenever the function returns a result r, r = 0.
  Preconditions: 1 <= len(s) <= 100000; every byte of s is a lowercase English letter; 1 <= x <= 10000; 1 <= y <= 10000; there is no index i with 0 <= i < len(s)-1 such that s[i]='a' and s[i+1]='b', or s[i]='b' and s[i+1]='a'. -/
theorem spec_12 (s : Slice U8) (x y : I64)
    (hlen1 : 1 ≤ (s.val).length) (hlen2 : (s.val).length ≤ 100000)
    (hlower : allLower s.val)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10000)
    (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ 10000)
    (hno_adj : ∀ i : Nat, i + 1 < (s.val).length →
      ¬ ((s.val)[i]? = some 97#u8 ∧ (s.val)[i + 1]? = some 98#u8) ∧
      ¬ ((s.val)[i]? = some 98#u8 ∧ (s.val)[i + 1]? = some 97#u8)) :
    ∀ r : I64, maximum_gain s x y = ok r → r.val = 0 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s : Slice U8) (x y : I64)
    (hlen1 : 1 ≤ (s.val).length) (hlen2 : (s.val).length ≤ 100000)
    (hlower : allLower s.val)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10000)
    (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ 10000)
    (hno_adj : ∀ i : Nat, i + 1 < (s.val).length →
      ¬ ((s.val)[i]? = some 97#u8 ∧ (s.val)[i + 1]? = some 98#u8) ∧
      ¬ ((s.val)[i]? = some 98#u8 ∧ (s.val)[i + 1]? = some 97#u8)), ∀ r : I64, maximum_gain s x y = ok r → r.val = 0) := by
  sorry

/-- Whenever the function returns a result r, r = x if s[0]='a' and s[1]='b'; r = y if s[0]='b' and s[1]='a'; and r = 0 otherwise.
  Preconditions: 1 <= len(s) <= 100000; every byte of s is a lowercase English letter; 1 <= x <= 10000; 1 <= y <= 10000; len(s)=2. -/
theorem spec_13 (s : Slice U8) (x y : I64)
    (hlen1 : 1 ≤ (s.val).length) (hlen2 : (s.val).length ≤ 100000)
    (hlower : allLower s.val)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10000)
    (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ 10000)
    (hlen : (s.val).length = 2) :
    ∀ r : I64, maximum_gain s x y = ok r →
      (∀ a b : U8, s.val = [a, b] → a.val = 97 → b.val = 98 → r.val = x.val) ∧
      (∀ a b : U8, s.val = [a, b] → a.val = 98 → b.val = 97 → r.val = y.val) ∧
      (∀ a b : U8, s.val = [a, b] → ¬(a.val = 97 ∧ b.val = 98) →
        ¬(a.val = 98 ∧ b.val = 97) → r.val = 0) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (s : Slice U8) (x y : I64)
    (hlen1 : 1 ≤ (s.val).length) (hlen2 : (s.val).length ≤ 100000)
    (hlower : allLower s.val)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10000)
    (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ 10000)
    (hlen : (s.val).length = 2), ∀ r : I64, maximum_gain s x y = ok r →
      (∀ a b : U8, s.val = [a, b] → a.val = 97 → b.val = 98 → r.val = x.val) ∧
      (∀ a b : U8, s.val = [a, b] → a.val = 98 → b.val = 97 → r.val = y.val) ∧
      (∀ a b : U8, s.val = [a, b] → ¬(a.val = 97 ∧ b.val = 98) →
        ¬(a.val = 98 ∧ b.val = 97) → r.val = 0)) := by
  sorry

/-- Let A be the number of 'a' bytes and B the number of 'b' bytes in s. Whenever the function returns a result r, r = x * min(A,B).
  Preconditions: 1 <= len(s) <= 100000; every byte of s is a lowercase English letter; 1 <= x <= 10000; 1 <= y <= 10000; s consists only of bytes 'a' and 'b'; there are no indices i<j with s[i]='b' and s[j]='a' (equivalently, s has the form a^A b^B). -/
theorem spec_14 (s : Slice U8) (x y : I64)
    (hlen1 : 1 ≤ (s.val).length) (hlen2 : (s.val).length ≤ 100000)
    (hlower : allLower s.val)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10000)
    (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ 10000)
    (hab : allAb s.val)
    (hsorted : ∀ i j : Nat, i < j → j < (s.val).length →
      ¬ ((s.val)[i]? = some 98#u8 ∧ (s.val)[j]? = some 97#u8)) :
    ∀ r : I64, maximum_gain s x y = ok r →
      r.val = x.val * (min (numA s.val) (numB s.val) : ℤ) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (s : Slice U8) (x y : I64)
    (hlen1 : 1 ≤ (s.val).length) (hlen2 : (s.val).length ≤ 100000)
    (hlower : allLower s.val)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10000)
    (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ 10000)
    (hab : allAb s.val)
    (hsorted : ∀ i j : Nat, i < j → j < (s.val).length →
      ¬ ((s.val)[i]? = some 98#u8 ∧ (s.val)[j]? = some 97#u8)), ∀ r : I64, maximum_gain s x y = ok r →
      r.val = x.val * (min (numA s.val) (numB s.val) : ℤ)) := by
  sorry

/-- Let A be the number of 'a' bytes and B the number of 'b' bytes in s. Whenever the function returns a result r, r = y * min(A,B).
  Preconditions: 1 <= len(s) <= 100000; every byte of s is a lowercase English letter; 1 <= x <= 10000; 1 <= y <= 10000; s consists only of bytes 'a' and 'b'; there are no indices i<j with s[i]='a' and s[j]='b' (equivalently, s has the form b^B a^A). -/
theorem spec_15 (s : Slice U8) (x y : I64)
    (hlen1 : 1 ≤ (s.val).length) (hlen2 : (s.val).length ≤ 100000)
    (hlower : allLower s.val)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10000)
    (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ 10000)
    (hab : allAb s.val)
    (hsorted : ∀ i j : Nat, i < j → j < (s.val).length →
      ¬ ((s.val)[i]? = some 97#u8 ∧ (s.val)[j]? = some 98#u8)) :
    ∀ r : I64, maximum_gain s x y = ok r →
      r.val = y.val * (min (numA s.val) (numB s.val) : ℤ) := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (s : Slice U8) (x y : I64)
    (hlen1 : 1 ≤ (s.val).length) (hlen2 : (s.val).length ≤ 100000)
    (hlower : allLower s.val)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10000)
    (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ 10000)
    (hab : allAb s.val)
    (hsorted : ∀ i j : Nat, i < j → j < (s.val).length →
      ¬ ((s.val)[i]? = some 97#u8 ∧ (s.val)[j]? = some 98#u8)), ∀ r : I64, maximum_gain s x y = ok r →
      r.val = y.val * (min (numA s.val) (numB s.val) : ℤ)) := by
  sorry

end AegisSpec.MaximumGain

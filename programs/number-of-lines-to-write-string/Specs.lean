import Aegis.NumberOfLines.Code.Funs

/-!
# Specifications of `Aegis.NumberOfLines.number_of_lines`

LeetCode problem `number-of-lines-to-write-string`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.NumberOfLines

def byteAt (s : Slice Std.U8) (t : ℕ) : ℕ :=
  ((s.val[t]?).map (fun b => b.val)).getD 0

def w (widths : Slice Std.I64) (c : ℕ) : ℤ :=
  ((widths.val[c - 97]?).map (fun x => x.val)).getD 0

def W (widths : Slice Std.I64) (s : Slice Std.U8) (l r : ℕ) : ℤ :=
  ((List.range (r - l)).map (fun j => w widths (byteAt s (l + j)))).sum

def totalWidth (widths : Slice Std.I64) (s : Slice Std.U8) : ℤ :=
  W widths s 0 s.val.length

def OccursIn (c : ℕ) (s : Slice Std.U8) : Prop :=
  ∃ t, t < s.val.length ∧ byteAt s t = c

def WidthsValid (widths : Slice Std.I64) : Prop :=
  widths.val.length = 26 ∧
    ∀ (i : ℕ) (x : Std.I64), widths.val[i]? = some x → 2 ≤ x.val ∧ x.val ≤ 10

def IsLowercase (s : Slice Std.U8) : Prop :=
  ∀ t, t < s.val.length → 97 ≤ byteAt s t ∧ byteAt s t ≤ 122

def Partition (widths : Slice Std.I64) (s : Slice Std.U8) (p : ℕ) : ℕ → Prop
  | 0 => p = 0
  | m + 1 => ∃ q, q < p ∧ W widths s q p ≤ 100 ∧ Partition widths s q m

def greedyStep (widths : Slice Std.I64) (s : Slice Std.U8) (p : ℕ) : ℕ :=
  Nat.findGreatest (fun q => p < q ∧ W widths s p q ≤ 100) s.val.length

def prefixEnd (widths : Slice Std.I64) (s : Slice Std.U8) (j : ℕ) : ℕ :=
  Nat.iterate (greedyStep widths s) j 0

/-- Let w(c)=widths[c-97] for a lowercase byte c, and for 0<=l<=r<=len(s) let W(l,r)=sum_{t=l}^{r-1} w(s[t]). Define p_0=0. For each j with p_j<len(s), let p_{j+1} be the largest integer q such that p_j<q<=len(s) and W(p_j,q)<=100. Let k be the least integer with p_k=len(s). Then the function returns a result r with len(r)=2, r[0]=k, and r[1]=W(p_{k-1},len(s)).
  Preconditions: len(widths)=26; for every i with 0<=i<26, 2<=widths[i]<=10; 1<=len(s)<=1000; and every byte s[t] with 0<=t<len(s) is a lowercase English letter (97<=s[t]<=122). -/
theorem spec_1 (widths : Slice Std.I64) (s : Slice Std.U8)
    (hw : WidthsValid widths) (hs : IsLowercase s)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 1000) :
    ∃ r : alloc.vec.Vec Std.I64, Aegis.NumberOfLines.number_of_lines widths s = Result.ok r ∧
      ∃ (a b : Std.I64) (k : ℕ), r.val = [a, b] ∧ a.val = (k : ℤ) ∧
        prefixEnd widths s k = s.val.length ∧
        (∀ j, j < k → prefixEnd widths s j ≠ s.val.length) ∧
        b.val = W widths s (prefixEnd widths s (k - 1)) s.val.length := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (widths : Slice Std.I64) (s : Slice Std.U8)
    (hw : WidthsValid widths) (hs : IsLowercase s)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 1000), ∃ r : alloc.vec.Vec Std.I64, Aegis.NumberOfLines.number_of_lines widths s = Result.ok r ∧
      ∃ (a b : Std.I64) (k : ℕ), r.val = [a, b] ∧ a.val = (k : ℤ) ∧
        prefixEnd widths s k = s.val.length ∧
        (∀ j, j < k → prefixEnd widths s j ≠ s.val.length) ∧
        b.val = W widths s (prefixEnd widths s (k - 1)) s.val.length) := by
  sorry

/-- The function returns a result r (it does not fail, panic, or overflow) for every input satisfying the preconditions.
  Preconditions: len(widths)=26; for every i with 0<=i<26, 2<=widths[i]<=10; 1<=len(s)<=1000; and every byte s[t] with 0<=t<len(s) is a lowercase English letter (97<=s[t]<=122). -/
theorem spec_2 (widths : Slice Std.I64) (s : Slice Std.U8)
    (hw : WidthsValid widths) (hs : IsLowercase s)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 1000) :
    ∃ r : alloc.vec.Vec Std.I64, Aegis.NumberOfLines.number_of_lines widths s = Result.ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (widths : Slice Std.I64) (s : Slice Std.U8)
    (hw : WidthsValid widths) (hs : IsLowercase s)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 1000), ∃ r : alloc.vec.Vec Std.I64, Aegis.NumberOfLines.number_of_lines widths s = Result.ok r) := by
  sorry

/-- Whenever the function returns a result r on an input satisfying the preconditions, len(r)=2.
  Preconditions: len(widths)=26; for every i with 0<=i<26, 2<=widths[i]<=10; 1<=len(s)<=1000; and every byte s[t] with 0<=t<len(s) is a lowercase English letter (97<=s[t]<=122). -/
theorem spec_3 (widths : Slice Std.I64) (s : Slice Std.U8)
    (hw : WidthsValid widths) (hs : IsLowercase s)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 1000) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.NumberOfLines.number_of_lines widths s = Result.ok r → r.val.length = 2 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (widths : Slice Std.I64) (s : Slice Std.U8)
    (hw : WidthsValid widths) (hs : IsLowercase s)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 1000), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.NumberOfLines.number_of_lines widths s = Result.ok r → r.val.length = 2) := by
  sorry

/-- Whenever the function returns a result r on an input satisfying the preconditions, 1<=r[0]<=len(s).
  Preconditions: len(widths)=26; for every i with 0<=i<26, 2<=widths[i]<=10; 1<=len(s)<=1000; and every byte s[t] with 0<=t<len(s) is a lowercase English letter (97<=s[t]<=122). -/
theorem spec_4 (widths : Slice Std.I64) (s : Slice Std.U8)
    (hw : WidthsValid widths) (hs : IsLowercase s)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 1000) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.NumberOfLines.number_of_lines widths s = Result.ok r →
      ∃ a b : Std.I64, r.val = [a, b] ∧ 1 ≤ a.val ∧ a.val ≤ (s.val.length : ℤ) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (widths : Slice Std.I64) (s : Slice Std.U8)
    (hw : WidthsValid widths) (hs : IsLowercase s)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 1000), ∀ r : alloc.vec.Vec Std.I64, Aegis.NumberOfLines.number_of_lines widths s = Result.ok r →
      ∃ a b : Std.I64, r.val = [a, b] ∧ 1 ≤ a.val ∧ a.val ≤ (s.val.length : ℤ)) := by
  sorry

/-- Whenever the function returns a result r on an input satisfying the preconditions, 2<=r[1]<=100.
  Preconditions: len(widths)=26; for every i with 0<=i<26, 2<=widths[i]<=10; 1<=len(s)<=1000; and every byte s[t] with 0<=t<len(s) is a lowercase English letter (97<=s[t]<=122). -/
theorem spec_5 (widths : Slice Std.I64) (s : Slice Std.U8)
    (hw : WidthsValid widths) (hs : IsLowercase s)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 1000) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.NumberOfLines.number_of_lines widths s = Result.ok r →
      ∃ a b : Std.I64, r.val = [a, b] ∧ 2 ≤ b.val ∧ b.val ≤ 100 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (widths : Slice Std.I64) (s : Slice Std.U8)
    (hw : WidthsValid widths) (hs : IsLowercase s)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 1000), ∀ r : alloc.vec.Vec Std.I64, Aegis.NumberOfLines.number_of_lines widths s = Result.ok r →
      ∃ a b : Std.I64, r.val = [a, b] ∧ 2 ≤ b.val ∧ b.val ≤ 100) := by
  sorry

/-- Whenever the function returns a result r on an input satisfying the preconditions, let T=sum_{t=0}^{len(s)-1} widths[s[t]-97]. Then r[0]=1 if and only if T<=100.
  Preconditions: len(widths)=26; for every i with 0<=i<26, 2<=widths[i]<=10; 1<=len(s)<=1000; and every byte s[t] with 0<=t<len(s) is a lowercase English letter (97<=s[t]<=122). -/
theorem spec_6 (widths : Slice Std.I64) (s : Slice Std.U8)
    (hw : WidthsValid widths) (hs : IsLowercase s)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 1000) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.NumberOfLines.number_of_lines widths s = Result.ok r →
      ∃ a b : Std.I64, r.val = [a, b] ∧ (a.val = 1 ↔ totalWidth widths s ≤ 100) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (widths : Slice Std.I64) (s : Slice Std.U8)
    (hw : WidthsValid widths) (hs : IsLowercase s)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 1000), ∀ r : alloc.vec.Vec Std.I64, Aegis.NumberOfLines.number_of_lines widths s = Result.ok r →
      ∃ a b : Std.I64, r.val = [a, b] ∧ (a.val = 1 ↔ totalWidth widths s ≤ 100)) := by
  sorry

/-- Whenever the function returns a result r on an input satisfying the preconditions, let w(c)=widths[c-97] and W(l,r)=sum_{t=l}^{r-1} w(s[t]). Then r[0] is the minimum integer m for which there exist indices 0=l_0<l_1<...<l_m=len(s) with W(l_j,l_{j+1})<=100 for every j with 0<=j<m.
  Preconditions: len(widths)=26; for every i with 0<=i<26, 2<=widths[i]<=10; 1<=len(s)<=1000; and every byte s[t] with 0<=t<len(s) is a lowercase English letter (97<=s[t]<=122). -/
theorem spec_7 (widths : Slice Std.I64) (s : Slice Std.U8)
    (hw : WidthsValid widths) (hs : IsLowercase s)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 1000) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.NumberOfLines.number_of_lines widths s = Result.ok r →
      ∃ a b : Std.I64, r.val = [a, b] ∧
        ∃ m : ℕ, a.val = (m : ℤ) ∧
          Partition widths s s.val.length m ∧
          ∀ m' : ℕ, Partition widths s s.val.length m' → m ≤ m' := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (widths : Slice Std.I64) (s : Slice Std.U8)
    (hw : WidthsValid widths) (hs : IsLowercase s)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 1000), ∀ r : alloc.vec.Vec Std.I64, Aegis.NumberOfLines.number_of_lines widths s = Result.ok r →
      ∃ a b : Std.I64, r.val = [a, b] ∧
        ∃ m : ℕ, a.val = (m : ℤ) ∧
          Partition widths s s.val.length m ∧
          ∀ m' : ℕ, Partition widths s s.val.length m' → m ≤ m') := by
  sorry

/-- Whenever the function returns a result r on an input satisfying the preconditions, let w(c)=widths[c-97] and W(l,r)=sum_{t=l}^{r-1} w(s[t]). There exists an index p with 0<=p<len(s) such that r[1]=W(p,len(s)) and the prefix s[0..p) can be partitioned into exactly r[0]-1 nonempty contiguous segments, each of width at most 100.
  Preconditions: len(widths)=26; for every i with 0<=i<26, 2<=widths[i]<=10; 1<=len(s)<=1000; and every byte s[t] with 0<=t<len(s) is a lowercase English letter (97<=s[t]<=122). -/
theorem spec_8 (widths : Slice Std.I64) (s : Slice Std.U8)
    (hw : WidthsValid widths) (hs : IsLowercase s)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 1000) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.NumberOfLines.number_of_lines widths s = Result.ok r →
      ∃ a b : Std.I64, r.val = [a, b] ∧
        ∃ p : ℕ, p < s.val.length ∧ b.val = W widths s p s.val.length ∧
          ∃ m : ℕ, a.val = (m : ℤ) + 1 ∧ Partition widths s p m := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (widths : Slice Std.I64) (s : Slice Std.U8)
    (hw : WidthsValid widths) (hs : IsLowercase s)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 1000), ∀ r : alloc.vec.Vec Std.I64, Aegis.NumberOfLines.number_of_lines widths s = Result.ok r →
      ∃ a b : Std.I64, r.val = [a, b] ∧
        ∃ p : ℕ, p < s.val.length ∧ b.val = W widths s p s.val.length ∧
          ∃ m : ℕ, a.val = (m : ℤ) + 1 ∧ Partition widths s p m) := by
  sorry

/-- Whenever the function returns a result r on an input satisfying the preconditions and r[0]>1, let w(c)=widths[c-97] and W(l,r)=sum_{t=l}^{r-1} w(s[t]). There exist indices q and p with 0<=q<p<len(s) such that W(q,p)<=100, W(q,p)+w(s[p])>100, r[1]=W(p,len(s)), and the prefix s[0..q) can be partitioned into exactly r[0]-2 nonempty contiguous segments, each of width at most 100.
  Preconditions: len(widths)=26; for every i with 0<=i<26, 2<=widths[i]<=10; 1<=len(s)<=1000; and every byte s[t] with 0<=t<len(s) is a lowercase English letter (97<=s[t]<=122). -/
theorem spec_9 (widths : Slice Std.I64) (s : Slice Std.U8)
    (hw : WidthsValid widths) (hs : IsLowercase s)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 1000) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.NumberOfLines.number_of_lines widths s = Result.ok r →
      ∃ a b : Std.I64, r.val = [a, b] ∧
        (1 < a.val →
          ∃ q p : ℕ, q < p ∧ p < s.val.length ∧
            W widths s q p ≤ 100 ∧
            W widths s q p + w widths (byteAt s p) > 100 ∧
            b.val = W widths s p s.val.length ∧
            ∃ m : ℕ, a.val = (m : ℤ) + 2 ∧ Partition widths s q m) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (widths : Slice Std.I64) (s : Slice Std.U8)
    (hw : WidthsValid widths) (hs : IsLowercase s)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 1000), ∀ r : alloc.vec.Vec Std.I64, Aegis.NumberOfLines.number_of_lines widths s = Result.ok r →
      ∃ a b : Std.I64, r.val = [a, b] ∧
        (1 < a.val →
          ∃ q p : ℕ, q < p ∧ p < s.val.length ∧
            W widths s q p ≤ 100 ∧
            W widths s q p + w widths (byteAt s p) > 100 ∧
            b.val = W widths s p s.val.length ∧
            ∃ m : ℕ, a.val = (m : ℤ) + 2 ∧ Partition widths s q m)) := by
  sorry

/-- Let widths' be any length-26 slice of i64 satisfying 2<=widths'[i]<=10 for every 0<=i<26 and widths'[i]=widths[i] whenever the letter with code i+97 occurs in s. If r and r' are the result vectors returned for (widths,s) and (widths',s) respectively, then r=r'.
  Preconditions: len(widths)=26; for every i with 0<=i<26, 2<=widths[i]<=10; 1<=len(s)<=1000; and every byte s[t] with 0<=t<len(s) is a lowercase English letter (97<=s[t]<=122). -/
theorem spec_10 (widths widths' : Slice Std.I64) (s : Slice Std.U8)
    (hw : WidthsValid widths) (hw' : WidthsValid widths') (hs : IsLowercase s)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 1000)
    (hagree : ∀ i : ℕ, i < 26 → OccursIn (i + 97) s → w widths (i + 97) = w widths' (i + 97)) :
    ∀ (r r' : alloc.vec.Vec Std.I64), Aegis.NumberOfLines.number_of_lines widths s = Result.ok r →
      Aegis.NumberOfLines.number_of_lines widths' s = Result.ok r' → r = r' := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (widths widths' : Slice Std.I64) (s : Slice Std.U8)
    (hw : WidthsValid widths) (hw' : WidthsValid widths') (hs : IsLowercase s)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 1000)
    (hagree : ∀ i : ℕ, i < 26 → OccursIn (i + 97) s → w widths (i + 97) = w widths' (i + 97)), ∀ (r r' : alloc.vec.Vec Std.I64), Aegis.NumberOfLines.number_of_lines widths s = Result.ok r →
      Aegis.NumberOfLines.number_of_lines widths' s = Result.ok r' → r = r') := by
  sorry

/-- Let s' be any byte slice of lowercase letters with len(s')=len(s) and such that for every t with 0<=t<len(s), widths[s'[t]-97]=widths[s[t]-97]. If r and r' are the result vectors returned for (widths,s) and (widths,s') respectively, then r=r'.
  Preconditions: len(widths)=26; for every i with 0<=i<26, 2<=widths[i]<=10; 1<=len(s)<=1000; and every byte s[t] with 0<=t<len(s) is a lowercase English letter (97<=s[t]<=122). -/
theorem spec_11 (widths : Slice Std.I64) (s s' : Slice Std.U8)
    (hw : WidthsValid widths) (hs : IsLowercase s) (hs' : IsLowercase s')
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 1000)
    (hlen_eq : s'.val.length = s.val.length)
    (hagree : ∀ t : ℕ, t < s.val.length → w widths (byteAt s' t) = w widths (byteAt s t)) :
    ∀ (r r' : alloc.vec.Vec Std.I64), Aegis.NumberOfLines.number_of_lines widths s = Result.ok r →
      Aegis.NumberOfLines.number_of_lines widths s' = Result.ok r' → r = r' := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (widths : Slice Std.I64) (s s' : Slice Std.U8)
    (hw : WidthsValid widths) (hs : IsLowercase s) (hs' : IsLowercase s')
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 1000)
    (hlen_eq : s'.val.length = s.val.length)
    (hagree : ∀ t : ℕ, t < s.val.length → w widths (byteAt s' t) = w widths (byteAt s t)), ∀ (r r' : alloc.vec.Vec Std.I64), Aegis.NumberOfLines.number_of_lines widths s = Result.ok r →
      Aegis.NumberOfLines.number_of_lines widths s' = Result.ok r' → r = r') := by
  sorry

/-- Whenever the function returns a result r on an input satisfying the preconditions and r[0]>1, let T=sum_{t=0}^{len(s)-1} widths[s[t]-97]. Then r[1]<T.
  Preconditions: len(widths)=26; for every i with 0<=i<26, 2<=widths[i]<=10; 1<=len(s)<=1000; and every byte s[t] with 0<=t<len(s) is a lowercase English letter (97<=s[t]<=122). -/
theorem spec_12 (widths : Slice Std.I64) (s : Slice Std.U8)
    (hw : WidthsValid widths) (hs : IsLowercase s)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 1000) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.NumberOfLines.number_of_lines widths s = Result.ok r →
      ∃ a b : Std.I64, r.val = [a, b] ∧ (1 < a.val → b.val < totalWidth widths s) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (widths : Slice Std.I64) (s : Slice Std.U8)
    (hw : WidthsValid widths) (hs : IsLowercase s)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 1000), ∀ r : alloc.vec.Vec Std.I64, Aegis.NumberOfLines.number_of_lines widths s = Result.ok r →
      ∃ a b : Std.I64, r.val = [a, b] ∧ (1 < a.val → b.val < totalWidth widths s)) := by
  sorry

end AegisSpec.NumberOfLines

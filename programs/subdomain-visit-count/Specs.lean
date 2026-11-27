import Aegis.SubdomainVisits.Code.Funs

/-!
# Specifications of `Aegis.SubdomainVisits.subdomain_visits`

LeetCode problem `subdomain-visit-count`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result Aeneas.Std.alloc.vec

namespace AegisSpec.SubdomainVisits

set_option maxHeartbeats 1000000

def digitByte (c : Nat) : U8 :=
  U8.ofNat (48 + c % 10) (by
    have h : UScalar.cMax UScalarTy.U8 = 255 := rfl
    have h2 : c % 10 < 10 := Nat.mod_lt c (by decide)
    omega)

def decRepr (c : Nat) : List U8 :=
  if c < 10 then [digitByte c] else decRepr (c / 10) ++ [digitByte c]
termination_by c

def IsLowerByte (b : U8) : Prop := 97 ≤ b.val ∧ b.val ≤ 122

def IsLabel (l : List U8) : Prop := l ≠ [] ∧ ∀ b ∈ l, IsLowerByte b

def joinLabels : List (List U8) → List U8
  | [] => []
  | [l] => l
  | l :: l' :: rest => l ++ 46#u8 :: joinLabels (l' :: rest)

def IsDomainWithLabels (k : Nat) (D : List U8) : Prop :=
  ∃ ls : List (List U8), k ≤ ls.length ∧ (∀ l ∈ ls, IsLabel l) ∧ D = joinLabels ls

def IsInputDomain (D : List U8) : Prop := IsDomainWithLabels 2 D

def IsDomain (D : List U8) : Prop := IsDomainWithLabels 1 D

def numLabels (D : List U8) : Nat := (D.filter (fun b => b == 46#u8)).length + 1

def IsLabelSuffix (D S : List U8) : Prop :=
  ∃ p : List U8, D = p ++ S ∧ (p = [] ∨ ∃ q : List U8, p = q ++ [46#u8])

def IsProperLabelSuffix (D S : List U8) : Prop :=
  ∃ q : List U8, D = (q ++ [46#u8]) ++ S

def entry (c : Nat) (D : List U8) : List U8 := decRepr c ++ [32#u8] ++ D

def NoLeadingZero (l : List U8) : Prop := l = [48#u8] ∨ l.head? ≠ some 48#u8

def GoodEntry (e : List U8) (c : Nat) (D : List U8) : Prop :=
  e = entry c D ∧ 1 ≤ c ∧ c ≤ 10000 ∧ IsInputDomain D ∧ e.length ≤ 100

def ValidInput (cpdomains : List (Vec U8)) (pcs : List (Nat × List U8)) : Prop :=
  ∃ (hlen : pcs.length = cpdomains.length),
    1 ≤ cpdomains.length ∧ cpdomains.length ≤ 100 ∧
      ∀ (i : Nat) (h : i < pcs.length),
        GoodEntry (cpdomains.get ⟨i, by omega⟩).val (pcs.get ⟨i, h⟩).1 (pcs.get ⟨i, h⟩).2

def SuffixOfSomeInput (pcs : List (Nat × List U8)) (S : List U8) : Prop :=
  ∃ p ∈ pcs, IsLabelSuffix p.2 S

noncomputable def visitSum (pcs : List (Nat × List U8)) (S : List U8) : Nat :=
  letI := Classical.propDecidable
  (pcs.map (fun p => if IsLabelSuffix p.2 S then p.1 else 0)).sum

def totalCount (pcs : List (Nat × List U8)) : Nat := (pcs.map (fun p => p.1)).sum

def weightedTotal (pcs : List (Nat × List U8)) : Nat :=
  (pcs.map (fun p => p.1 * numLabels p.2)).sum

def maxLabels (pcs : List (Nat × List U8)) : Nat :=
  (pcs.map (fun p => numLabels p.2)).foldr max 0

def countEntry (r : List (Vec U8)) (x : List U8) : Nat :=
  (r.filter (fun e => decide (e.val = x))).length

def Writes (r : List (Vec U8)) (ps : List (Nat × List U8)) : Prop :=
  ∃ (hlen : ps.length = r.length),
    ∀ (i : Nat) (h : i < r.length),
      (r.get ⟨i, h⟩).val = entry (ps.get ⟨i, by omega⟩).1 (ps.get ⟨i, by omega⟩).2

/-- Let visit_sum(S) = the sum of c_i over all i with 0 <= i < n such that S is a label-boundary suffix of D_i (a label-boundary suffix of a domain L1....Lk is L_j....Lk for some 1 <= j <= k). Let E be the set of byte strings decimal_repr(visit_sum(S)) ++ [32] ++ S, over all domain strings S that are a label-boundary suffix of at least one D_i. The function returns a result r and r is a permutation of E: len(r) = |E|, every entry of r belongs to E, and every member of E occurs exactly once as an entry of r. The order of entries is arbitrary.
  Preconditions: Let n = len(cpdomains). 1 <= n <= 100. For each i with 0 <= i < n, cpdomains[i] is the byte string decimal_repr(c_i) ++ [32] ++ D_i, where 1 <= c_i <= 10^4, decimal_repr(c_i) is the usual decimal representation with no leading zero, [32] is one ASCII space, D_i is a dot-separated domain string with at least 2 nonempty lowercase ASCII letter labels and no other bytes, and len(cpdomains[i]) <= 100. -/
theorem spec_1 (cpdomains : Slice (Vec U8)) (pcs : List (Nat × List U8))
    (hpre : ValidInput cpdomains.val pcs) :
    ∃ r : Vec (Vec U8),
      Aegis.SubdomainVisits.subdomain_visits cpdomains = ok r ∧
        ∃ Es : List (List U8),
          Es.Nodup ∧ (∀ S : List U8, S ∈ Es ↔ SuffixOfSomeInput pcs S) ∧
            r.val.length = Es.length ∧
            (∀ e ∈ r.val, ∃ S ∈ Es, e.val = entry (visitSum pcs S) S) ∧
            (∀ S ∈ Es, countEntry r.val (entry (visitSum pcs S) S) = 1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (cpdomains : Slice (Vec U8)) (pcs : List (Nat × List U8))
    (hpre : ValidInput cpdomains.val pcs), ∃ r : Vec (Vec U8),
      Aegis.SubdomainVisits.subdomain_visits cpdomains = ok r ∧
        ∃ Es : List (List U8),
          Es.Nodup ∧ (∀ S : List U8, S ∈ Es ↔ SuffixOfSomeInput pcs S) ∧
            r.val.length = Es.length ∧
            (∀ e ∈ r.val, ∃ S ∈ Es, e.val = entry (visitSum pcs S) S) ∧
            (∀ S ∈ Es, countEntry r.val (entry (visitSum pcs S) S) = 1)) := by
  sorry

/-- Whenever the function returns a result r, every entry e of r has the form decimal_repr(c) ++ [32] ++ D for a unique integer c >= 0 and a unique domain string D, and c = the sum of c_i over all i with 0 <= i < n such that D is a label-boundary suffix of D_i (a label-boundary suffix of L1....Lk is L_j....Lk for some 1 <= j <= k).
  Preconditions: Let n = len(cpdomains). 1 <= n <= 100. For each i with 0 <= i < n, cpdomains[i] is the byte string decimal_repr(c_i) ++ [32] ++ D_i, where 1 <= c_i <= 10^4, decimal_repr(c_i) is the usual decimal representation with no leading zero, [32] is one ASCII space, D_i is a dot-separated domain string with at least 2 nonempty lowercase ASCII letter labels and no other bytes, and len(cpdomains[i]) <= 100. -/
theorem spec_2 (cpdomains : Slice (Vec U8)) (pcs : List (Nat × List U8))
    (hpre : ValidInput cpdomains.val pcs) :
    ∀ r : Vec (Vec U8),
      Aegis.SubdomainVisits.subdomain_visits cpdomains = ok r →
        ∀ e ∈ r.val,
          ∃! c : Nat, ∃! D : List U8, e.val = entry c D ∧ c = visitSum pcs D := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (cpdomains : Slice (Vec U8)) (pcs : List (Nat × List U8))
    (hpre : ValidInput cpdomains.val pcs), ∀ r : Vec (Vec U8),
      Aegis.SubdomainVisits.subdomain_visits cpdomains = ok r →
        ∀ e ∈ r.val,
          ∃! c : Nat, ∃! D : List U8, e.val = entry c D ∧ c = visitSum pcs D) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < n and every label-boundary suffix S of D_i, there exists an integer c such that the byte string decimal_repr(c) ++ [32] ++ S is an entry of r.
  Preconditions: Let n = len(cpdomains). 1 <= n <= 100. For each i with 0 <= i < n, cpdomains[i] is the byte string decimal_repr(c_i) ++ [32] ++ D_i, where 1 <= c_i <= 10^4, decimal_repr(c_i) is the usual decimal representation with no leading zero, [32] is one ASCII space, D_i is a dot-separated domain string with at least 2 nonempty lowercase ASCII letter labels and no other bytes, and len(cpdomains[i]) <= 100. -/
theorem spec_3 (cpdomains : Slice (Vec U8)) (pcs : List (Nat × List U8))
    (hpre : ValidInput cpdomains.val pcs) :
    ∀ r : Vec (Vec U8),
      Aegis.SubdomainVisits.subdomain_visits cpdomains = ok r →
        ∀ (i : Nat) (h : i < pcs.length) (S : List U8),
          IsLabelSuffix (pcs.get ⟨i, h⟩).2 S →
            ∃ c : Nat, ∃ e ∈ r.val, e.val = entry c S := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (cpdomains : Slice (Vec U8)) (pcs : List (Nat × List U8))
    (hpre : ValidInput cpdomains.val pcs), ∀ r : Vec (Vec U8),
      Aegis.SubdomainVisits.subdomain_visits cpdomains = ok r →
        ∀ (i : Nat) (h : i < pcs.length) (S : List U8),
          IsLabelSuffix (pcs.get ⟨i, h⟩).2 S →
            ∃ c : Nat, ∃ e ∈ r.val, e.val = entry c S) := by
  sorry

/-- Whenever the function returns a result r, for every entry e of r that can be written as decimal_repr(c) ++ [32] ++ D with c an integer and D a domain string, D is a label-boundary suffix of at least one input domain D_i with 0 <= i < n.
  Preconditions: Let n = len(cpdomains). 1 <= n <= 100. For each i with 0 <= i < n, cpdomains[i] is the byte string decimal_repr(c_i) ++ [32] ++ D_i, where 1 <= c_i <= 10^4, decimal_repr(c_i) is the usual decimal representation with no leading zero, [32] is one ASCII space, D_i is a dot-separated domain string with at least 2 nonempty lowercase ASCII letter labels and no other bytes, and len(cpdomains[i]) <= 100. -/
theorem spec_4 (cpdomains : Slice (Vec U8)) (pcs : List (Nat × List U8))
    (hpre : ValidInput cpdomains.val pcs) :
    ∀ r : Vec (Vec U8),
      Aegis.SubdomainVisits.subdomain_visits cpdomains = ok r →
        ∀ e ∈ r.val, ∀ (c : Nat) (D : List U8),
          e.val = entry c D → SuffixOfSomeInput pcs D := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (cpdomains : Slice (Vec U8)) (pcs : List (Nat × List U8))
    (hpre : ValidInput cpdomains.val pcs), ∀ r : Vec (Vec U8),
      Aegis.SubdomainVisits.subdomain_visits cpdomains = ok r →
        ∀ e ∈ r.val, ∀ (c : Nat) (D : List U8),
          e.val = entry c D → SuffixOfSomeInput pcs D) := by
  sorry

/-- Whenever the function returns a result r, no two distinct entries of r have the same domain part: if e1 = decimal_repr(c1) ++ [32] ++ D and e2 = decimal_repr(c2) ++ [32] ++ D are entries of r with the same domain string D, then e1 = e2 and c1 = c2.
  Preconditions: Let n = len(cpdomains). 1 <= n <= 100. For each i with 0 <= i < n, cpdomains[i] is the byte string decimal_repr(c_i) ++ [32] ++ D_i, where 1 <= c_i <= 10^4, decimal_repr(c_i) is the usual decimal representation with no leading zero, [32] is one ASCII space, D_i is a dot-separated domain string with at least 2 nonempty lowercase ASCII letter labels and no other bytes, and len(cpdomains[i]) <= 100. -/
theorem spec_5 (cpdomains : Slice (Vec U8)) (pcs : List (Nat × List U8))
    (hpre : ValidInput cpdomains.val pcs) :
    ∀ r : Vec (Vec U8),
      Aegis.SubdomainVisits.subdomain_visits cpdomains = ok r →
        ∀ (c1 c2 : Nat) (D : List U8) (e1 e2 : Vec U8),
          e1 ∈ r.val → e2 ∈ r.val →
            e1.val = entry c1 D → e2.val = entry c2 D → e1 = e2 ∧ c1 = c2 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (cpdomains : Slice (Vec U8)) (pcs : List (Nat × List U8))
    (hpre : ValidInput cpdomains.val pcs), ∀ r : Vec (Vec U8),
      Aegis.SubdomainVisits.subdomain_visits cpdomains = ok r →
        ∀ (c1 c2 : Nat) (D : List U8) (e1 e2 : Vec U8),
          e1 ∈ r.val → e2 ∈ r.val →
            e1.val = entry c1 D → e2.val = entry c2 D → e1 = e2 ∧ c1 = c2) := by
  sorry

/-- Whenever the function returns a result r, every entry e of r is exactly decimal_repr(c) ++ [32] ++ D, where c is an integer with 1 <= c <= 1,000,000, decimal_repr(c) has no leading zero, and D is a domain string consisting of one or more nonempty labels of lowercase ASCII letters separated by single '.' bytes; e has no other bytes, so it contains exactly one ASCII space.
  Preconditions: Let n = len(cpdomains). 1 <= n <= 100. For each i with 0 <= i < n, cpdomains[i] is the byte string decimal_repr(c_i) ++ [32] ++ D_i, where 1 <= c_i <= 10^4, decimal_repr(c_i) is the usual decimal representation with no leading zero, [32] is one ASCII space, D_i is a dot-separated domain string with at least 2 nonempty lowercase ASCII letter labels and no other bytes, and len(cpdomains[i]) <= 100. -/
theorem spec_6 (cpdomains : Slice (Vec U8)) (pcs : List (Nat × List U8))
    (hpre : ValidInput cpdomains.val pcs) :
    ∀ r : Vec (Vec U8),
      Aegis.SubdomainVisits.subdomain_visits cpdomains = ok r →
        ∀ e ∈ r.val, ∃ (c : Nat) (D : List U8),
          e.val = entry c D ∧ 1 ≤ c ∧ c ≤ 1000000 ∧ NoLeadingZero (decRepr c) ∧
            IsDomain D ∧ (e.val.filter (fun b => b == 32#u8)).length = 1 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (cpdomains : Slice (Vec U8)) (pcs : List (Nat × List U8))
    (hpre : ValidInput cpdomains.val pcs), ∀ r : Vec (Vec U8),
      Aegis.SubdomainVisits.subdomain_visits cpdomains = ok r →
        ∀ e ∈ r.val, ∃ (c : Nat) (D : List U8),
          e.val = entry c D ∧ 1 ≤ c ∧ c ≤ 1000000 ∧ NoLeadingZero (decRepr c) ∧
            IsDomain D ∧ (e.val.filter (fun b => b == 32#u8)).length = 1) := by
  sorry

/-- Whenever the function returns a result r, len(r) equals the number of distinct domain strings S that are a label-boundary suffix of at least one input domain D_i with 0 <= i < n.
  Preconditions: Let n = len(cpdomains). 1 <= n <= 100. For each i with 0 <= i < n, cpdomains[i] is the byte string decimal_repr(c_i) ++ [32] ++ D_i, where 1 <= c_i <= 10^4, decimal_repr(c_i) is the usual decimal representation with no leading zero, [32] is one ASCII space, D_i is a dot-separated domain string with at least 2 nonempty lowercase ASCII letter labels and no other bytes, and len(cpdomains[i]) <= 100. -/
theorem spec_7 (cpdomains : Slice (Vec U8)) (pcs : List (Nat × List U8))
    (hpre : ValidInput cpdomains.val pcs) :
    ∀ r : Vec (Vec U8),
      Aegis.SubdomainVisits.subdomain_visits cpdomains = ok r →
        ∃ Es : List (List U8),
          Es.Nodup ∧ (∀ S : List U8, S ∈ Es ↔ SuffixOfSomeInput pcs S) ∧
            r.val.length = Es.length := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (cpdomains : Slice (Vec U8)) (pcs : List (Nat × List U8))
    (hpre : ValidInput cpdomains.val pcs), ∀ r : Vec (Vec U8),
      Aegis.SubdomainVisits.subdomain_visits cpdomains = ok r →
        ∃ Es : List (List U8),
          Es.Nodup ∧ (∀ S : List U8, S ∈ Es ↔ SuffixOfSomeInput pcs S) ∧
            r.val.length = Es.length) := by
  sorry

/-- Whenever the function returns a result r, for every entry e = decimal_repr(c) ++ [32] ++ D of r, 1 <= c <= the sum of c_i over all i with 0 <= i < n.
  Preconditions: Let n = len(cpdomains). 1 <= n <= 100. For each i with 0 <= i < n, cpdomains[i] is the byte string decimal_repr(c_i) ++ [32] ++ D_i, where 1 <= c_i <= 10^4, decimal_repr(c_i) is the usual decimal representation with no leading zero, [32] is one ASCII space, D_i is a dot-separated domain string with at least 2 nonempty lowercase ASCII letter labels and no other bytes, and len(cpdomains[i]) <= 100. -/
theorem spec_8 (cpdomains : Slice (Vec U8)) (pcs : List (Nat × List U8))
    (hpre : ValidInput cpdomains.val pcs) :
    ∀ r : Vec (Vec U8),
      Aegis.SubdomainVisits.subdomain_visits cpdomains = ok r →
        ∀ e ∈ r.val, ∀ (c : Nat) (D : List U8),
          e.val = entry c D → 1 ≤ c ∧ c ≤ totalCount pcs := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (cpdomains : Slice (Vec U8)) (pcs : List (Nat × List U8))
    (hpre : ValidInput cpdomains.val pcs), ∀ r : Vec (Vec U8),
      Aegis.SubdomainVisits.subdomain_visits cpdomains = ok r →
        ∀ e ∈ r.val, ∀ (c : Nat) (D : List U8),
          e.val = entry c D → 1 ≤ c ∧ c ≤ totalCount pcs) := by
  sorry

/-- Whenever the function returns a result r, if r contains entries decimal_repr(c1) ++ [32] ++ D1 and decimal_repr(c2) ++ [32] ++ D2, and D2 is a proper label-boundary suffix of D1 (that is, D2 = L_j....L_k for some j > 1 when D1 = L1....Lk), then c2 >= c1.
  Preconditions: Let n = len(cpdomains). 1 <= n <= 100. For each i with 0 <= i < n, cpdomains[i] is the byte string decimal_repr(c_i) ++ [32] ++ D_i, where 1 <= c_i <= 10^4, decimal_repr(c_i) is the usual decimal representation with no leading zero, [32] is one ASCII space, D_i is a dot-separated domain string with at least 2 nonempty lowercase ASCII letter labels and no other bytes, and len(cpdomains[i]) <= 100. -/
theorem spec_9 (cpdomains : Slice (Vec U8)) (pcs : List (Nat × List U8))
    (hpre : ValidInput cpdomains.val pcs) :
    ∀ r : Vec (Vec U8),
      Aegis.SubdomainVisits.subdomain_visits cpdomains = ok r →
        ∀ (c1 c2 : Nat) (D1 D2 : List U8),
          (∃ e ∈ r.val, e.val = entry c1 D1) →
            (∃ e ∈ r.val, e.val = entry c2 D2) →
              IsProperLabelSuffix D1 D2 → c1 ≤ c2 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (cpdomains : Slice (Vec U8)) (pcs : List (Nat × List U8))
    (hpre : ValidInput cpdomains.val pcs), ∀ r : Vec (Vec U8),
      Aegis.SubdomainVisits.subdomain_visits cpdomains = ok r →
        ∀ (c1 c2 : Nat) (D1 D2 : List U8),
          (∃ e ∈ r.val, e.val = entry c1 D1) →
            (∃ e ∈ r.val, e.val = entry c2 D2) →
              IsProperLabelSuffix D1 D2 → c1 ≤ c2) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r; it does not fail with overflow, out-of-bounds access, or panic.
  Preconditions: Let n = len(cpdomains). 1 <= n <= 100. For each i with 0 <= i < n, cpdomains[i] is the byte string decimal_repr(c_i) ++ [32] ++ D_i, where 1 <= c_i <= 10^4, decimal_repr(c_i) is the usual decimal representation with no leading zero, [32] is one ASCII space, D_i is a dot-separated domain string with at least 2 nonempty lowercase ASCII letter labels and no other bytes, and len(cpdomains[i]) <= 100. -/
theorem spec_10 (cpdomains : Slice (Vec U8)) (pcs : List (Nat × List U8))
    (hpre : ValidInput cpdomains.val pcs) :
    ∃ r : Vec (Vec U8), Aegis.SubdomainVisits.subdomain_visits cpdomains = ok r := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (cpdomains : Slice (Vec U8)) (pcs : List (Nat × List U8))
    (hpre : ValidInput cpdomains.val pcs), ∃ r : Vec (Vec U8), Aegis.SubdomainVisits.subdomain_visits cpdomains = ok r) := by
  sorry

/-- Whenever the function returns a result r, write each entry of r as decimal_repr(c_e) ++ [32] ++ D_e. Then the sum of c_e over all entries e of r equals the sum of c_i * k_i over all i with 0 <= i < n, where k_i is the number of labels in D_i.
  Preconditions: Let n = len(cpdomains). 1 <= n <= 100. For each i with 0 <= i < n, cpdomains[i] is the byte string decimal_repr(c_i) ++ [32] ++ D_i, where 1 <= c_i <= 10^4, decimal_repr(c_i) is the usual decimal representation with no leading zero, [32] is one ASCII space, D_i is a dot-separated domain string with at least 2 nonempty lowercase ASCII letter labels and no other bytes, and len(cpdomains[i]) <= 100. -/
theorem spec_11 (cpdomains : Slice (Vec U8)) (pcs : List (Nat × List U8))
    (hpre : ValidInput cpdomains.val pcs) :
    ∀ r : Vec (Vec U8),
      Aegis.SubdomainVisits.subdomain_visits cpdomains = ok r →
        ∀ ps : List (Nat × List U8),
          Writes r.val ps → (ps.map (fun p => p.1)).sum = weightedTotal pcs := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (cpdomains : Slice (Vec U8)) (pcs : List (Nat × List U8))
    (hpre : ValidInput cpdomains.val pcs), ∀ r : Vec (Vec U8),
      Aegis.SubdomainVisits.subdomain_visits cpdomains = ok r →
        ∀ ps : List (Nat × List U8),
          Writes r.val ps → (ps.map (fun p => p.1)).sum = weightedTotal pcs) := by
  sorry

/-- Let L be the maximum number of labels among all input domains D_i. Whenever the function returns a result r, for every entry e = decimal_repr(c) ++ [32] ++ D of r, the number of labels in D is between 1 and L inclusive.
  Preconditions: Let n = len(cpdomains). 1 <= n <= 100. For each i with 0 <= i < n, cpdomains[i] is the byte string decimal_repr(c_i) ++ [32] ++ D_i, where 1 <= c_i <= 10^4, decimal_repr(c_i) is the usual decimal representation with no leading zero, [32] is one ASCII space, D_i is a dot-separated domain string with at least 2 nonempty lowercase ASCII letter labels and no other bytes, and len(cpdomains[i]) <= 100. -/
theorem spec_12 (cpdomains : Slice (Vec U8)) (pcs : List (Nat × List U8))
    (hpre : ValidInput cpdomains.val pcs) :
    ∀ r : Vec (Vec U8),
      Aegis.SubdomainVisits.subdomain_visits cpdomains = ok r →
        ∀ e ∈ r.val, ∀ (c : Nat) (D : List U8),
          e.val = entry c D → 1 ≤ numLabels D ∧ numLabels D ≤ maxLabels pcs := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (cpdomains : Slice (Vec U8)) (pcs : List (Nat × List U8))
    (hpre : ValidInput cpdomains.val pcs), ∀ r : Vec (Vec U8),
      Aegis.SubdomainVisits.subdomain_visits cpdomains = ok r →
        ∀ e ∈ r.val, ∀ (c : Nat) (D : List U8),
          e.val = entry c D → 1 ≤ numLabels D ∧ numLabels D ≤ maxLabels pcs) := by
  sorry

end AegisSpec.SubdomainVisits

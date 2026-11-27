import Aegis.ValidateStackSequences.Code.Funs

/-!
# Specifications of `Aegis.ValidateStackSequences.validate_stack_sequences`

LeetCode problem `validate-stack-sequences`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.ValidateStackSequences

namespace AegisSpec.ValidateStackSequences

def vals (s : Slice Std.I64) : List Int := s.val.map (fun x => x.val)

abbrev StackState := List Int × List Int × List Int

inductive Step : StackState → StackState → Prop
  | push (v : Int) (todo pending stack : List Int) :
      Step (v :: todo, pending, stack) (todo, pending, v :: stack)
  | pop (v : Int) (todo pending stack : List Int) :
      Step (todo, v :: pending, v :: stack) (todo, pending, stack)

def IsStackPermutation (pushed popped : List Int) : Prop :=
  Relation.ReflTransGen Step (pushed, popped, []) ([], [], [])

def posOf (l : List Int) (v : Int) : Nat := l.idxOf v

/-- Whenever the function returns a result r, r = true if and only if there exists a finite sequence of operations starting from an empty stack such that: (1) the push operations push pushed[0], pushed[1], ..., pushed[n-1] exactly once each and in that order; (2) every operation is either the next push in that order or a pop of the current top of the stack, and a pop is performed only when the stack is nonempty; (3) the values removed by the successive pop operations are exactly popped[0], popped[1], ..., popped[n-1]; and (4) after all n pushes and all n pops the stack is empty. Equivalently, r is true exactly when popped is a valid stack permutation of pushed, and r is false otherwise.
  Preconditions: Let n = len(pushed). The inputs satisfy the problem constraints: len(popped) = n, 1 <= n <= 1000; every value pushed[i] is an integer in [0,1000]; the values in pushed are pairwise distinct; and popped is a permutation of pushed (each value occurring in pushed occurs exactly once in popped and vice versa). -/
theorem spec_1 (pushed popped : Slice Std.I64)
    (hlen : popped.val.length = pushed.val.length)
    (hn_pos : 1 ≤ pushed.val.length)
    (hn_le : pushed.val.length ≤ 1000)
    (hbounds : ∀ v ∈ pushed.val, 0 ≤ v.val ∧ v.val ≤ 1000)
    (hnodup : (vals pushed).Nodup)
    (hperm : (vals pushed).Perm (vals popped)) :
    ∀ r, validate_stack_sequences pushed popped = ok r →
      (r = true ↔ IsStackPermutation (vals pushed) (vals popped)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (pushed popped : Slice Std.I64)
    (hlen : popped.val.length = pushed.val.length)
    (hn_pos : 1 ≤ pushed.val.length)
    (hn_le : pushed.val.length ≤ 1000)
    (hbounds : ∀ v ∈ pushed.val, 0 ≤ v.val ∧ v.val ≤ 1000)
    (hnodup : (vals pushed).Nodup)
    (hperm : (vals pushed).Perm (vals popped)), ∀ r, validate_stack_sequences pushed popped = ok r →
      (r = true ↔ IsStackPermutation (vals pushed) (vals popped))) := by
  sorry

/-- The function does not fail on these inputs: for every pushed and popped satisfying the preconditions, it returns some Boolean result r, with no panic, arithmetic overflow, out-of-bounds slice access, or other failure.
  Preconditions: Let n = len(pushed). The inputs satisfy the problem constraints: len(popped) = n, 1 <= n <= 1000; every value pushed[i] is an integer in [0,1000]; the values in pushed are pairwise distinct; and popped is a permutation of pushed. -/
theorem spec_2 (pushed popped : Slice Std.I64)
    (hlen : popped.val.length = pushed.val.length)
    (hn_pos : 1 ≤ pushed.val.length)
    (hn_le : pushed.val.length ≤ 1000)
    (hbounds : ∀ v ∈ pushed.val, 0 ≤ v.val ∧ v.val ≤ 1000)
    (hnodup : (vals pushed).Nodup)
    (hperm : (vals pushed).Perm (vals popped)) :
    ∃ r, validate_stack_sequences pushed popped = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (pushed popped : Slice Std.I64)
    (hlen : popped.val.length = pushed.val.length)
    (hn_pos : 1 ≤ pushed.val.length)
    (hn_le : pushed.val.length ≤ 1000)
    (hbounds : ∀ v ∈ pushed.val, 0 ≤ v.val ∧ v.val ≤ 1000)
    (hnodup : (vals pushed).Nodup)
    (hperm : (vals pushed).Perm (vals popped)), ∃ r, validate_stack_sequences pushed popped = ok r) := by
  sorry

/-- Whenever the function returns false, there exist indices i, j, k with 0 <= i < j < k < n such that pos(popped[j]) < pos(popped[k]) < pos(popped[i]).
  Preconditions: Let n = len(pushed). The inputs satisfy the problem constraints: len(popped) = n, 1 <= n <= 1000; every value pushed[i] is an integer in [0,1000]; the values in pushed are pairwise distinct; and popped is a permutation of pushed. For a value v occurring in pushed, pos(v) denotes the unique index i with pushed[i] = v. -/
theorem spec_3 (pushed popped : Slice Std.I64)
    (hlen : popped.val.length = pushed.val.length)
    (hn_pos : 1 ≤ pushed.val.length)
    (hn_le : pushed.val.length ≤ 1000)
    (hbounds : ∀ v ∈ pushed.val, 0 ≤ v.val ∧ v.val ≤ 1000)
    (hnodup : (vals pushed).Nodup)
    (hperm : (vals pushed).Perm (vals popped)) :
    ∀ r, validate_stack_sequences pushed popped = ok r → r = false →
      ∃ (i j k : Nat) (hij : i < j) (hjk : j < k) (hkn : k < popped.val.length),
        posOf (vals pushed) ((popped.val.get ⟨j, hjk.trans hkn⟩).val) <
            posOf (vals pushed) ((popped.val.get ⟨k, hkn⟩).val) ∧
          posOf (vals pushed) ((popped.val.get ⟨k, hkn⟩).val) <
            posOf (vals pushed) ((popped.val.get ⟨i, (hij.trans hjk).trans hkn⟩).val) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (pushed popped : Slice Std.I64)
    (hlen : popped.val.length = pushed.val.length)
    (hn_pos : 1 ≤ pushed.val.length)
    (hn_le : pushed.val.length ≤ 1000)
    (hbounds : ∀ v ∈ pushed.val, 0 ≤ v.val ∧ v.val ≤ 1000)
    (hnodup : (vals pushed).Nodup)
    (hperm : (vals pushed).Perm (vals popped)), ∀ r, validate_stack_sequences pushed popped = ok r → r = false →
      ∃ (i j k : Nat) (hij : i < j) (hjk : j < k) (hkn : k < popped.val.length),
        posOf (vals pushed) ((popped.val.get ⟨j, hjk.trans hkn⟩).val) <
            posOf (vals pushed) ((popped.val.get ⟨k, hkn⟩).val) ∧
          posOf (vals pushed) ((popped.val.get ⟨k, hkn⟩).val) <
            posOf (vals pushed) ((popped.val.get ⟨i, (hij.trans hjk).trans hkn⟩).val)) := by
  sorry

/-- Whenever the function returns true, there do not exist indices i, j, k with 0 <= i < j < k < n such that pos(popped[j]) < pos(popped[k]) < pos(popped[i]).
  Preconditions: Let n = len(pushed). The inputs satisfy the problem constraints: len(popped) = n, 1 <= n <= 1000; every value pushed[i] is an integer in [0,1000]; the values in pushed are pairwise distinct; and popped is a permutation of pushed. For a value v occurring in pushed, pos(v) denotes the unique index i with pushed[i] = v. -/
theorem spec_4 (pushed popped : Slice Std.I64)
    (hlen : popped.val.length = pushed.val.length)
    (hn_pos : 1 ≤ pushed.val.length)
    (hn_le : pushed.val.length ≤ 1000)
    (hbounds : ∀ v ∈ pushed.val, 0 ≤ v.val ∧ v.val ≤ 1000)
    (hnodup : (vals pushed).Nodup)
    (hperm : (vals pushed).Perm (vals popped)) :
    ∀ r, validate_stack_sequences pushed popped = ok r → r = true →
      ¬ ∃ (i j k : Nat) (hij : i < j) (hjk : j < k) (hkn : k < popped.val.length),
        posOf (vals pushed) ((popped.val.get ⟨j, hjk.trans hkn⟩).val) <
            posOf (vals pushed) ((popped.val.get ⟨k, hkn⟩).val) ∧
          posOf (vals pushed) ((popped.val.get ⟨k, hkn⟩).val) <
            posOf (vals pushed) ((popped.val.get ⟨i, (hij.trans hjk).trans hkn⟩).val) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (pushed popped : Slice Std.I64)
    (hlen : popped.val.length = pushed.val.length)
    (hn_pos : 1 ≤ pushed.val.length)
    (hn_le : pushed.val.length ≤ 1000)
    (hbounds : ∀ v ∈ pushed.val, 0 ≤ v.val ∧ v.val ≤ 1000)
    (hnodup : (vals pushed).Nodup)
    (hperm : (vals pushed).Perm (vals popped)), ∀ r, validate_stack_sequences pushed popped = ok r → r = true →
      ¬ ∃ (i j k : Nat) (hij : i < j) (hjk : j < k) (hkn : k < popped.val.length),
        posOf (vals pushed) ((popped.val.get ⟨j, hjk.trans hkn⟩).val) <
            posOf (vals pushed) ((popped.val.get ⟨k, hkn⟩).val) ∧
          posOf (vals pushed) ((popped.val.get ⟨k, hkn⟩).val) <
            posOf (vals pushed) ((popped.val.get ⟨i, (hij.trans hjk).trans hkn⟩).val)) := by
  sorry

/-- The function returns true on (pushed', popped') if and only if it returns true on (pushed, popped).
  Preconditions: Let n = len(pushed). The inputs satisfy the problem constraints: len(popped) = n, 1 <= n <= 1000; every value pushed[i] is an integer in [0,1000]; the values in pushed are pairwise distinct; and popped is a permutation of pushed. Fix an integer x with 0 <= x <= 1000 such that x is not among the values in pushed, and n + 1 <= 1000. Let pushed' = pushed with x appended, and popped' = popped with x appended; these also satisfy the problem constraints. -/
theorem spec_5 (pushed popped : Slice Std.I64)
    (hlen : popped.val.length = pushed.val.length)
    (hn_pos : 1 ≤ pushed.val.length)
    (hn_le : pushed.val.length ≤ 1000)
    (hbounds : ∀ v ∈ pushed.val, 0 ≤ v.val ∧ v.val ≤ 1000)
    (hnodup : (vals pushed).Nodup)
    (hperm : (vals pushed).Perm (vals popped))
    (x : Int) (hx_lo : 0 ≤ x) (hx_hi : x ≤ 1000) (hx_fresh : x ∉ vals pushed)
    (hn_succ : pushed.val.length + 1 ≤ 1000)
    (pushed' popped' : Slice Std.I64)
    (hpushed' : vals pushed' = vals pushed ++ [x])
    (hpopped' : vals popped' = vals popped ++ [x]) :
    ∀ r r', validate_stack_sequences pushed popped = ok r →
      validate_stack_sequences pushed' popped' = ok r' → (r' = true ↔ r = true) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (pushed popped : Slice Std.I64)
    (hlen : popped.val.length = pushed.val.length)
    (hn_pos : 1 ≤ pushed.val.length)
    (hn_le : pushed.val.length ≤ 1000)
    (hbounds : ∀ v ∈ pushed.val, 0 ≤ v.val ∧ v.val ≤ 1000)
    (hnodup : (vals pushed).Nodup)
    (hperm : (vals pushed).Perm (vals popped))
    (x : Int) (hx_lo : 0 ≤ x) (hx_hi : x ≤ 1000) (hx_fresh : x ∉ vals pushed)
    (hn_succ : pushed.val.length + 1 ≤ 1000)
    (pushed' popped' : Slice Std.I64)
    (hpushed' : vals pushed' = vals pushed ++ [x])
    (hpopped' : vals popped' = vals popped ++ [x]), ∀ r r', validate_stack_sequences pushed popped = ok r →
      validate_stack_sequences pushed' popped' = ok r' → (r' = true ↔ r = true)) := by
  sorry

/-- The function returns true on (f(pushed), f(popped)) if and only if it returns true on (pushed, popped).
  Preconditions: Let n = len(pushed). The inputs satisfy the problem constraints: len(popped) = n, 1 <= n <= 1000; every value pushed[i] is an integer in [0,1000]; the values in pushed are pairwise distinct; and popped is a permutation of pushed. Let f be a function on integers that is injective on the set of values occurring in pushed and maps each of those values to an integer in [0,1000]. Let f(pushed) and f(popped) be the arrays obtained by applying f elementwise; these also satisfy the problem constraints. -/
theorem spec_6 (pushed popped : Slice Std.I64)
    (hlen : popped.val.length = pushed.val.length)
    (hn_pos : 1 ≤ pushed.val.length)
    (hn_le : pushed.val.length ≤ 1000)
    (hbounds : ∀ v ∈ pushed.val, 0 ≤ v.val ∧ v.val ≤ 1000)
    (hnodup : (vals pushed).Nodup)
    (hperm : (vals pushed).Perm (vals popped))
    (f : Int → Int)
    (hf_inj : ∀ a ∈ vals pushed, ∀ b ∈ vals pushed, f a = f b → a = b)
    (hf_bounds : ∀ a ∈ vals pushed, 0 ≤ f a ∧ f a ≤ 1000)
    (pushed' popped' : Slice Std.I64)
    (hpushed' : vals pushed' = (vals pushed).map f)
    (hpopped' : vals popped' = (vals popped).map f) :
    ∀ r r', validate_stack_sequences pushed popped = ok r →
      validate_stack_sequences pushed' popped' = ok r' → (r' = true ↔ r = true) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (pushed popped : Slice Std.I64)
    (hlen : popped.val.length = pushed.val.length)
    (hn_pos : 1 ≤ pushed.val.length)
    (hn_le : pushed.val.length ≤ 1000)
    (hbounds : ∀ v ∈ pushed.val, 0 ≤ v.val ∧ v.val ≤ 1000)
    (hnodup : (vals pushed).Nodup)
    (hperm : (vals pushed).Perm (vals popped))
    (f : Int → Int)
    (hf_inj : ∀ a ∈ vals pushed, ∀ b ∈ vals pushed, f a = f b → a = b)
    (hf_bounds : ∀ a ∈ vals pushed, 0 ≤ f a ∧ f a ≤ 1000)
    (pushed' popped' : Slice Std.I64)
    (hpushed' : vals pushed' = (vals pushed).map f)
    (hpopped' : vals popped' = (vals popped).map f), ∀ r r', validate_stack_sequences pushed popped = ok r →
      validate_stack_sequences pushed' popped' = ok r' → (r' = true ↔ r = true)) := by
  sorry

/-- If the function returns true on (pushed, popped), then it returns true on (pushed', popped').
  Preconditions: Let n = len(pushed). The inputs satisfy the problem constraints: len(popped) = n, 1 <= n <= 1000; every value pushed[i] is an integer in [0,1000]; the values in pushed are pairwise distinct; and popped is a permutation of pushed. Let S be any set of values contained in pushed such that at least one value remains, i.e., n - |S| >= 1. Let pushed' be pushed with all values in S deleted, and popped' be popped with all values in S deleted; these also satisfy the problem constraints. -/
theorem spec_7 (pushed popped : Slice Std.I64)
    (hlen : popped.val.length = pushed.val.length)
    (hn_pos : 1 ≤ pushed.val.length)
    (hn_le : pushed.val.length ≤ 1000)
    (hbounds : ∀ v ∈ pushed.val, 0 ≤ v.val ∧ v.val ≤ 1000)
    (hnodup : (vals pushed).Nodup)
    (hperm : (vals pushed).Perm (vals popped))
    (S : Finset Int) (hS : ∀ v ∈ S, v ∈ vals pushed)
    (hS_lt : 1 ≤ pushed.val.length - S.card)
    (pushed' popped' : Slice Std.I64)
    (hpushed' : vals pushed' = (vals pushed).filter (fun v => decide (v ∉ S)))
    (hpopped' : vals popped' = (vals popped).filter (fun v => decide (v ∉ S))) :
    ∀ r r', validate_stack_sequences pushed popped = ok r →
      validate_stack_sequences pushed' popped' = ok r' → (r = true → r' = true) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (pushed popped : Slice Std.I64)
    (hlen : popped.val.length = pushed.val.length)
    (hn_pos : 1 ≤ pushed.val.length)
    (hn_le : pushed.val.length ≤ 1000)
    (hbounds : ∀ v ∈ pushed.val, 0 ≤ v.val ∧ v.val ≤ 1000)
    (hnodup : (vals pushed).Nodup)
    (hperm : (vals pushed).Perm (vals popped))
    (S : Finset Int) (hS : ∀ v ∈ S, v ∈ vals pushed)
    (hS_lt : 1 ≤ pushed.val.length - S.card)
    (pushed' popped' : Slice Std.I64)
    (hpushed' : vals pushed' = (vals pushed).filter (fun v => decide (v ∉ S)))
    (hpopped' : vals popped' = (vals popped).filter (fun v => decide (v ∉ S))), ∀ r r', validate_stack_sequences pushed popped = ok r →
      validate_stack_sequences pushed' popped' = ok r' → (r = true → r' = true)) := by
  sorry

/-- Whenever the function returns true, for every i with 0 <= i < j, the value pushed[i] occurs in popped at some index k with 1 <= k < n (that is, after popped[0]).
  Preconditions: Let n = len(pushed). The inputs satisfy the problem constraints: len(popped) = n, 1 <= n <= 1000; every value pushed[i] is an integer in [0,1000]; the values in pushed are pairwise distinct; and popped is a permutation of pushed. Let j be the unique index with pushed[j] = popped[0]. -/
theorem spec_8 (pushed popped : Slice Std.I64)
    (hlen : popped.val.length = pushed.val.length)
    (hn_pos : 1 ≤ pushed.val.length)
    (hn_le : pushed.val.length ≤ 1000)
    (hbounds : ∀ v ∈ pushed.val, 0 ≤ v.val ∧ v.val ≤ 1000)
    (hnodup : (vals pushed).Nodup)
    (hperm : (vals pushed).Perm (vals popped))
    (j : Nat) (hj : j < pushed.val.length)
    (hjpos : (pushed.val.get ⟨j, hj⟩).val = (popped.val.get ⟨0, by omega⟩).val) :
    ∀ r, validate_stack_sequences pushed popped = ok r → r = true →
      ∀ (i : Nat) (hi : i < j),
        ∃ (k : Nat) (hk_ge : 1 ≤ k) (hk_lt : k < popped.val.length),
          (popped.val.get ⟨k, hk_lt⟩).val = (pushed.val.get ⟨i, hi.trans hj⟩).val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (pushed popped : Slice Std.I64)
    (hlen : popped.val.length = pushed.val.length)
    (hn_pos : 1 ≤ pushed.val.length)
    (hn_le : pushed.val.length ≤ 1000)
    (hbounds : ∀ v ∈ pushed.val, 0 ≤ v.val ∧ v.val ≤ 1000)
    (hnodup : (vals pushed).Nodup)
    (hperm : (vals pushed).Perm (vals popped))
    (j : Nat) (hj : j < pushed.val.length)
    (hjpos : (pushed.val.get ⟨j, hj⟩).val = (popped.val.get ⟨0, by omega⟩).val), ∀ r, validate_stack_sequences pushed popped = ok r → r = true →
      ∀ (i : Nat) (hi : i < j),
        ∃ (k : Nat) (hk_ge : 1 ≤ k) (hk_lt : k < popped.val.length),
          (popped.val.get ⟨k, hk_lt⟩).val = (pushed.val.get ⟨i, hi.trans hj⟩).val) := by
  sorry

/-- Whenever the function returns true, for every i with j < i < n, the value pushed[i] occurs in popped at some index k with 0 <= k < n-1 (that is, before popped[n-1]).
  Preconditions: Let n = len(pushed). The inputs satisfy the problem constraints: len(popped) = n, 1 <= n <= 1000; every value pushed[i] is an integer in [0,1000]; the values in pushed are pairwise distinct; and popped is a permutation of pushed. Let j be the unique index with pushed[j] = popped[n-1]. -/
theorem spec_9 (pushed popped : Slice Std.I64)
    (hlen : popped.val.length = pushed.val.length)
    (hn_pos : 1 ≤ pushed.val.length)
    (hn_le : pushed.val.length ≤ 1000)
    (hbounds : ∀ v ∈ pushed.val, 0 ≤ v.val ∧ v.val ≤ 1000)
    (hnodup : (vals pushed).Nodup)
    (hperm : (vals pushed).Perm (vals popped))
    (j : Nat) (hj : j < pushed.val.length)
    (hjpos : (pushed.val.get ⟨j, hj⟩).val =
      (popped.val.get ⟨popped.val.length - 1, by omega⟩).val) :
    ∀ r, validate_stack_sequences pushed popped = ok r → r = true →
      ∀ (i : Nat) (hji : j < i) (hin : i < pushed.val.length),
        ∃ (k : Nat) (hk_lt : k < popped.val.length - 1),
          (popped.val.get ⟨k, Nat.lt_of_lt_of_le hk_lt (Nat.sub_le _ _)⟩).val =
            (pushed.val.get ⟨i, hin⟩).val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (pushed popped : Slice Std.I64)
    (hlen : popped.val.length = pushed.val.length)
    (hn_pos : 1 ≤ pushed.val.length)
    (hn_le : pushed.val.length ≤ 1000)
    (hbounds : ∀ v ∈ pushed.val, 0 ≤ v.val ∧ v.val ≤ 1000)
    (hnodup : (vals pushed).Nodup)
    (hperm : (vals pushed).Perm (vals popped))
    (j : Nat) (hj : j < pushed.val.length)
    (hjpos : (pushed.val.get ⟨j, hj⟩).val =
      (popped.val.get ⟨popped.val.length - 1, by omega⟩).val), ∀ r, validate_stack_sequences pushed popped = ok r → r = true →
      ∀ (i : Nat) (hji : j < i) (hin : i < pushed.val.length),
        ∃ (k : Nat) (hk_lt : k < popped.val.length - 1),
          (popped.val.get ⟨k, Nat.lt_of_lt_of_le hk_lt (Nat.sub_le _ _)⟩).val =
            (pushed.val.get ⟨i, hin⟩).val) := by
  sorry

end AegisSpec.ValidateStackSequences

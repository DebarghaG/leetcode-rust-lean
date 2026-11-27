import Aegis.MaximumRequests.Code.Funs

/-!
# Specifications of `Aegis.MaximumRequests.maximum_requests`

LeetCode problem `maximum-number-of-achievable-transfer-requests`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MaximumRequests

  set_option autoImplicit false

  namespace AegisSpec.MaximumRequests

  def reqList (requests : Slice (alloc.vec.Vec Std.I64)) : List (List ℤ) :=
    requests.val.map (fun v => v.val)

  def reqAt (reqs : List (List ℤ)) (i : ℕ) : List ℤ := reqs.getD i []

  def fromAt (reqs : List (List ℤ)) (i : ℕ) : ℤ := (reqAt reqs i).getD 0 0

  def toAt (reqs : List (List ℤ)) (i : ℕ) : ℤ := (reqAt reqs i).getD 1 0

  def idxSet (reqs : List (List ℤ)) : Finset ℕ := Finset.range reqs.length

  def countFrom (reqs : List (List ℤ)) (S : Finset ℕ) (b : ℤ) : ℕ :=
    (S.filter fun i => fromAt reqs i = b).card

  def countTo (reqs : List (List ℤ)) (S : Finset ℕ) (b : ℤ) : ℕ :=
    (S.filter fun i => toAt reqs i = b).card

  def IsSelection (reqs : List (List ℤ)) (S : Finset ℕ) : Prop :=
    S ⊆ idxSet reqs

  def Balanced (n : ℤ) (reqs : List (List ℤ)) (S : Finset ℕ) : Prop :=
    ∀ b : ℤ, 0 ≤ b → b < n → countFrom reqs S b = countTo reqs S b

  def Feasible (n : ℤ) (reqs : List (List ℤ)) (S : Finset ℕ) : Prop :=
    IsSelection reqs S ∧ Balanced n reqs S

  def diagCount (reqs : List (List ℤ)) : ℕ :=
    ((idxSet reqs).filter fun i => fromAt reqs i = toAt reqs i).card

  def countPair (reqs : List (List ℤ)) (a b : ℤ) : ℕ :=
    ((idxSet reqs).filter fun i => fromAt reqs i = a ∧ toAt reqs i = b).card

  def IsMaxCard (n : ℤ) (reqs : List (List ℤ)) (r : ℤ) : Prop :=
    (∀ S : Finset ℕ, Feasible n reqs S → (S.card : ℤ) ≤ r) ∧
      ∃ S : Finset ℕ, Feasible n reqs S ∧ (S.card : ℤ) = r

  /-- The function returns a result r and r is the maximum, over all subsets S of the index set {0, 1, ..., m-1} where m = len(requests), of the cardinality |S| subject to: for every building b with 0 <= b < n, the number of indices i in S with requests[i][0] = b equals the number of indices i in S with requests[i][1] = b. The empty subset is allowed. Indices in S are selected requests; they need not be contiguous, and duplicate request entries are distinct indices.
    Preconditions: n is an i64 with 1 <= n <= 20. Let m = len(requests). requests is a slice with 1 <= m <= 16. For every i with 0 <= i < m, len(requests[i]) = 2. For every i with 0 <= i < m, 0 <= requests[i][0] < n and 0 <= requests[i][1] < n. -/
  theorem spec_1 (n : Std.I64) (requests : Slice (alloc.vec.Vec Std.I64))
      (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20)
      (hm1 : 1 ≤ requests.val.length) (hm2 : requests.val.length ≤ 16)
      (hlen : ∀ i, i < requests.val.length → (reqAt (reqList requests) i).length = 2)
      (hfrom : ∀ i, i < requests.val.length →
        0 ≤ fromAt (reqList requests) i ∧ fromAt (reqList requests) i < n.val)
      (hto : ∀ i, i < requests.val.length →
        0 ≤ toAt (reqList requests) i ∧ toAt (reqList requests) i < n.val) :
      ∃ r : Std.I64, maximum_requests n requests = ok r ∧
        IsMaxCard n.val (reqList requests) r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Std.I64) (requests : Slice (alloc.vec.Vec Std.I64))
        (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20)
        (hm1 : 1 ≤ requests.val.length) (hm2 : requests.val.length ≤ 16)
        (hlen : ∀ i, i < requests.val.length → (reqAt (reqList requests) i).length = 2)
        (hfrom : ∀ i, i < requests.val.length →
          0 ≤ fromAt (reqList requests) i ∧ fromAt (reqList requests) i < n.val)
        (hto : ∀ i, i < requests.val.length →
          0 ≤ toAt (reqList requests) i ∧ toAt (reqList requests) i < n.val), ∃ r : Std.I64, maximum_requests n requests = ok r ∧
          IsMaxCard n.val (reqList requests) r.val) := by
    sorry

  /-- The function returns a result r; under the preconditions it does not fail (no overflow, out-of-bounds access, or panic).
    Preconditions: n is an i64 with 1 <= n <= 20. Let m = len(requests). requests is a slice with 1 <= m <= 16. For every i with 0 <= i < m, len(requests[i]) = 2. For every i with 0 <= i < m, 0 <= requests[i][0] < n and 0 <= requests[i][1] < n. -/
  theorem spec_2 (n : Std.I64) (requests : Slice (alloc.vec.Vec Std.I64))
      (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20)
      (hm1 : 1 ≤ requests.val.length) (hm2 : requests.val.length ≤ 16)
      (hlen : ∀ i, i < requests.val.length → (reqAt (reqList requests) i).length = 2)
      (hfrom : ∀ i, i < requests.val.length →
        0 ≤ fromAt (reqList requests) i ∧ fromAt (reqList requests) i < n.val)
      (hto : ∀ i, i < requests.val.length →
        0 ≤ toAt (reqList requests) i ∧ toAt (reqList requests) i < n.val) :
      ∃ r : Std.I64, maximum_requests n requests = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64) (requests : Slice (alloc.vec.Vec Std.I64))
        (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20)
        (hm1 : 1 ≤ requests.val.length) (hm2 : requests.val.length ≤ 16)
        (hlen : ∀ i, i < requests.val.length → (reqAt (reqList requests) i).length = 2)
        (hfrom : ∀ i, i < requests.val.length →
          0 ≤ fromAt (reqList requests) i ∧ fromAt (reqList requests) i < n.val)
        (hto : ∀ i, i < requests.val.length →
          0 ≤ toAt (reqList requests) i ∧ toAt (reqList requests) i < n.val), ∃ r : Std.I64, maximum_requests n requests = ok r) := by
    sorry

  /-- The function returns a result r and 0 <= r <= len(requests).
    Preconditions: n is an i64 with 1 <= n <= 20. Let m = len(requests). requests is a slice with 1 <= m <= 16. For every i with 0 <= i < m, len(requests[i]) = 2. For every i with 0 <= i < m, 0 <= requests[i][0] < n and 0 <= requests[i][1] < n. -/
  theorem spec_3 (n : Std.I64) (requests : Slice (alloc.vec.Vec Std.I64))
      (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20)
      (hm1 : 1 ≤ requests.val.length) (hm2 : requests.val.length ≤ 16)
      (hlen : ∀ i, i < requests.val.length → (reqAt (reqList requests) i).length = 2)
      (hfrom : ∀ i, i < requests.val.length →
        0 ≤ fromAt (reqList requests) i ∧ fromAt (reqList requests) i < n.val)
      (hto : ∀ i, i < requests.val.length →
        0 ≤ toAt (reqList requests) i ∧ toAt (reqList requests) i < n.val) :
      ∃ r : Std.I64, maximum_requests n requests = ok r ∧
        0 ≤ r.val ∧ r.val ≤ (requests.val.length : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Std.I64) (requests : Slice (alloc.vec.Vec Std.I64))
        (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20)
        (hm1 : 1 ≤ requests.val.length) (hm2 : requests.val.length ≤ 16)
        (hlen : ∀ i, i < requests.val.length → (reqAt (reqList requests) i).length = 2)
        (hfrom : ∀ i, i < requests.val.length →
          0 ≤ fromAt (reqList requests) i ∧ fromAt (reqList requests) i < n.val)
        (hto : ∀ i, i < requests.val.length →
          0 ≤ toAt (reqList requests) i ∧ toAt (reqList requests) i < n.val), ∃ r : Std.I64, maximum_requests n requests = ok r ∧
          0 ≤ r.val ∧ r.val ≤ (requests.val.length : ℤ)) := by
    sorry

  /-- The function returns a result r and there exists a subset S of {0, 1, ..., m-1} such that |S| = r and, for every b with 0 <= b < n, the number of i in S with requests[i][0] = b equals the number of i in S with requests[i][1] = b.
    Preconditions: n is an i64 with 1 <= n <= 20. Let m = len(requests). requests is a slice with 1 <= m <= 16. For every i with 0 <= i < m, len(requests[i]) = 2. For every i with 0 <= i < m, 0 <= requests[i][0] < n and 0 <= requests[i][1] < n. -/
  theorem spec_4 (n : Std.I64) (requests : Slice (alloc.vec.Vec Std.I64))
      (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20)
      (hm1 : 1 ≤ requests.val.length) (hm2 : requests.val.length ≤ 16)
      (hlen : ∀ i, i < requests.val.length → (reqAt (reqList requests) i).length = 2)
      (hfrom : ∀ i, i < requests.val.length →
        0 ≤ fromAt (reqList requests) i ∧ fromAt (reqList requests) i < n.val)
      (hto : ∀ i, i < requests.val.length →
        0 ≤ toAt (reqList requests) i ∧ toAt (reqList requests) i < n.val) :
      ∃ r : Std.I64, maximum_requests n requests = ok r ∧
        ∃ S : Finset ℕ, Feasible n.val (reqList requests) S ∧ (S.card : ℤ) = r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Std.I64) (requests : Slice (alloc.vec.Vec Std.I64))
        (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20)
        (hm1 : 1 ≤ requests.val.length) (hm2 : requests.val.length ≤ 16)
        (hlen : ∀ i, i < requests.val.length → (reqAt (reqList requests) i).length = 2)
        (hfrom : ∀ i, i < requests.val.length →
          0 ≤ fromAt (reqList requests) i ∧ fromAt (reqList requests) i < n.val)
        (hto : ∀ i, i < requests.val.length →
          0 ≤ toAt (reqList requests) i ∧ toAt (reqList requests) i < n.val), ∃ r : Std.I64, maximum_requests n requests = ok r ∧
          ∃ S : Finset ℕ, Feasible n.val (reqList requests) S ∧ (S.card : ℤ) = r.val) := by
    sorry

  /-- The function returns a result r and for every subset S of {0, 1, ..., m-1}, if for every b with 0 <= b < n the number of i in S with requests[i][0] = b equals the number of i in S with requests[i][1] = b, then |S| <= r.
    Preconditions: n is an i64 with 1 <= n <= 20. Let m = len(requests). requests is a slice with 1 <= m <= 16. For every i with 0 <= i < m, len(requests[i]) = 2. For every i with 0 <= i < m, 0 <= requests[i][0] < n and 0 <= requests[i][1] < n. -/
  theorem spec_5 (n : Std.I64) (requests : Slice (alloc.vec.Vec Std.I64))
      (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20)
      (hm1 : 1 ≤ requests.val.length) (hm2 : requests.val.length ≤ 16)
      (hlen : ∀ i, i < requests.val.length → (reqAt (reqList requests) i).length = 2)
      (hfrom : ∀ i, i < requests.val.length →
        0 ≤ fromAt (reqList requests) i ∧ fromAt (reqList requests) i < n.val)
      (hto : ∀ i, i < requests.val.length →
        0 ≤ toAt (reqList requests) i ∧ toAt (reqList requests) i < n.val) :
      ∃ r : Std.I64, maximum_requests n requests = ok r ∧
        ∀ S : Finset ℕ, Feasible n.val (reqList requests) S → (S.card : ℤ) ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : Std.I64) (requests : Slice (alloc.vec.Vec Std.I64))
        (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20)
        (hm1 : 1 ≤ requests.val.length) (hm2 : requests.val.length ≤ 16)
        (hlen : ∀ i, i < requests.val.length → (reqAt (reqList requests) i).length = 2)
        (hfrom : ∀ i, i < requests.val.length →
          0 ≤ fromAt (reqList requests) i ∧ fromAt (reqList requests) i < n.val)
        (hto : ∀ i, i < requests.val.length →
          0 ≤ toAt (reqList requests) i ∧ toAt (reqList requests) i < n.val), ∃ r : Std.I64, maximum_requests n requests = ok r ∧
          ∀ S : Finset ℕ, Feasible n.val (reqList requests) S → (S.card : ℤ) ≤ r.val) := by
    sorry

  /-- The function returns a result r and r >= the number of indices i with 0 <= i < len(requests) and requests[i][0] = requests[i][1].
    Preconditions: n is an i64 with 1 <= n <= 20. Let m = len(requests). requests is a slice with 1 <= m <= 16. For every i with 0 <= i < m, len(requests[i]) = 2. For every i with 0 <= i < m, 0 <= requests[i][0] < n and 0 <= requests[i][1] < n. -/
  theorem spec_6 (n : Std.I64) (requests : Slice (alloc.vec.Vec Std.I64))
      (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20)
      (hm1 : 1 ≤ requests.val.length) (hm2 : requests.val.length ≤ 16)
      (hlen : ∀ i, i < requests.val.length → (reqAt (reqList requests) i).length = 2)
      (hfrom : ∀ i, i < requests.val.length →
        0 ≤ fromAt (reqList requests) i ∧ fromAt (reqList requests) i < n.val)
      (hto : ∀ i, i < requests.val.length →
        0 ≤ toAt (reqList requests) i ∧ toAt (reqList requests) i < n.val) :
      ∃ r : Std.I64, maximum_requests n requests = ok r ∧
        (diagCount (reqList requests) : ℤ) ≤ r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : Std.I64) (requests : Slice (alloc.vec.Vec Std.I64))
        (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20)
        (hm1 : 1 ≤ requests.val.length) (hm2 : requests.val.length ≤ 16)
        (hlen : ∀ i, i < requests.val.length → (reqAt (reqList requests) i).length = 2)
        (hfrom : ∀ i, i < requests.val.length →
          0 ≤ fromAt (reqList requests) i ∧ fromAt (reqList requests) i < n.val)
        (hto : ∀ i, i < requests.val.length →
          0 ≤ toAt (reqList requests) i ∧ toAt (reqList requests) i < n.val), ∃ r : Std.I64, maximum_requests n requests = ok r ∧
          (diagCount (reqList requests) : ℤ) ≤ r.val) := by
    sorry

  /-- The function returns a result r and r = 1 if requests[0][0] = requests[0][1], and r = 0 otherwise.
    Preconditions: n is an i64 with 1 <= n <= 20. Let m = len(requests). requests is a slice with m = 1. For i = 0, len(requests[i]) = 2, 0 <= requests[i][0] < n and 0 <= requests[i][1] < n. -/
  theorem spec_7 (n : Std.I64) (requests : Slice (alloc.vec.Vec Std.I64))
      (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20)
      (hm : requests.val.length = 1)
      (hlen : (reqAt (reqList requests) 0).length = 2)
      (hfrom : 0 ≤ fromAt (reqList requests) 0 ∧ fromAt (reqList requests) 0 < n.val)
      (hto : 0 ≤ toAt (reqList requests) 0 ∧ toAt (reqList requests) 0 < n.val) :
      ∃ r : Std.I64, maximum_requests n requests = ok r ∧
        r.val = (if fromAt (reqList requests) 0 = toAt (reqList requests) 0 then 1 else 0) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : Std.I64) (requests : Slice (alloc.vec.Vec Std.I64))
        (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20)
        (hm : requests.val.length = 1)
        (hlen : (reqAt (reqList requests) 0).length = 2)
        (hfrom : 0 ≤ fromAt (reqList requests) 0 ∧ fromAt (reqList requests) 0 < n.val)
        (hto : 0 ≤ toAt (reqList requests) 0 ∧ toAt (reqList requests) 0 < n.val), ∃ r : Std.I64, maximum_requests n requests = ok r ∧
          r.val = (if fromAt (reqList requests) 0 = toAt (reqList requests) 0 then 1 else 0)) := by
    sorry

  /-- The function returns a result r and r = 0.
    Preconditions: n is an i64 with 1 <= n <= 20. Let m = len(requests). requests is a slice with 1 <= m <= 16. For every i with 0 <= i < m, len(requests[i]) = 2. For every i with 0 <= i < m, 0 <= requests[i][0] < n and 0 <= requests[i][1] < n. There exist integers a and b with 0 <= a < n, 0 <= b < n, and a != b, such that for every i with 0 <= i < m, requests[i][0] = a and requests[i][1] = b. -/
  theorem spec_8 (n : Std.I64) (requests : Slice (alloc.vec.Vec Std.I64))
      (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20)
      (hm1 : 1 ≤ requests.val.length) (hm2 : requests.val.length ≤ 16)
      (hlen : ∀ i, i < requests.val.length → (reqAt (reqList requests) i).length = 2)
      (hfrom : ∀ i, i < requests.val.length →
        0 ≤ fromAt (reqList requests) i ∧ fromAt (reqList requests) i < n.val)
      (hto : ∀ i, i < requests.val.length →
        0 ≤ toAt (reqList requests) i ∧ toAt (reqList requests) i < n.val)
      (hall : ∃ a b : ℤ, 0 ≤ a ∧ a < n.val ∧ 0 ≤ b ∧ b < n.val ∧ a ≠ b ∧
        ∀ i, i < requests.val.length →
          fromAt (reqList requests) i = a ∧ toAt (reqList requests) i = b) :
      ∃ r : Std.I64, maximum_requests n requests = ok r ∧ r.val = 0 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : Std.I64) (requests : Slice (alloc.vec.Vec Std.I64))
        (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20)
        (hm1 : 1 ≤ requests.val.length) (hm2 : requests.val.length ≤ 16)
        (hlen : ∀ i, i < requests.val.length → (reqAt (reqList requests) i).length = 2)
        (hfrom : ∀ i, i < requests.val.length →
          0 ≤ fromAt (reqList requests) i ∧ fromAt (reqList requests) i < n.val)
        (hto : ∀ i, i < requests.val.length →
          0 ≤ toAt (reqList requests) i ∧ toAt (reqList requests) i < n.val)
        (hall : ∃ a b : ℤ, 0 ≤ a ∧ a < n.val ∧ 0 ≤ b ∧ b < n.val ∧ a ≠ b ∧
          ∀ i, i < requests.val.length →
            fromAt (reqList requests) i = a ∧ toAt (reqList requests) i = b), ∃ r : Std.I64, maximum_requests n requests = ok r ∧ r.val = 0) := by
    sorry

  /-- Whenever maximum_requests n requests returns r and maximum_requests n requests' returns r', we have r' = r + 1.
    Preconditions: n is an i64 with 1 <= n <= 20. Let m = len(requests). requests is a slice with 1 <= m <= 15. For every i with 0 <= i < m, len(requests[i]) = 2. For every i with 0 <= i < m, 0 <= requests[i][0] < n and 0 <= requests[i][1] < n. Let b be an integer with 0 <= b < n. Let requests' be the slice of length m+1 such that requests'[i] = requests[i] for 0 <= i < m and requests'[m] is the vector [b, b]. -/
  theorem spec_9 (n : Std.I64) (requests : Slice (alloc.vec.Vec Std.I64))
      (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20)
      (hm1 : 1 ≤ requests.val.length) (hm2 : requests.val.length ≤ 15)
      (hlen : ∀ i, i < requests.val.length → (reqAt (reqList requests) i).length = 2)
      (hfrom : ∀ i, i < requests.val.length →
        0 ≤ fromAt (reqList requests) i ∧ fromAt (reqList requests) i < n.val)
      (hto : ∀ i, i < requests.val.length →
        0 ≤ toAt (reqList requests) i ∧ toAt (reqList requests) i < n.val)
      (b : ℤ) (hb1 : 0 ≤ b) (hb2 : b < n.val)
      (requests' : Slice (alloc.vec.Vec Std.I64))
      (hlen' : requests'.val.length = requests.val.length + 1)
      (hval : reqList requests' = reqList requests ++ [[b, b]]) :
      ∀ r r' : Std.I64, maximum_requests n requests = ok r →
        maximum_requests n requests' = ok r' → r'.val = r.val + 1 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : Std.I64) (requests : Slice (alloc.vec.Vec Std.I64))
        (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20)
        (hm1 : 1 ≤ requests.val.length) (hm2 : requests.val.length ≤ 15)
        (hlen : ∀ i, i < requests.val.length → (reqAt (reqList requests) i).length = 2)
        (hfrom : ∀ i, i < requests.val.length →
          0 ≤ fromAt (reqList requests) i ∧ fromAt (reqList requests) i < n.val)
        (hto : ∀ i, i < requests.val.length →
          0 ≤ toAt (reqList requests) i ∧ toAt (reqList requests) i < n.val)
        (b : ℤ) (hb1 : 0 ≤ b) (hb2 : b < n.val)
        (requests' : Slice (alloc.vec.Vec Std.I64))
        (hlen' : requests'.val.length = requests.val.length + 1)
        (hval : reqList requests' = reqList requests ++ [[b, b]]), ∀ r r' : Std.I64, maximum_requests n requests = ok r →
          maximum_requests n requests' = ok r' → r'.val = r.val + 1) := by
    sorry

  /-- Whenever maximum_requests n requests returns r and maximum_requests n requests' returns r', we have r = r'.
    Preconditions: n is an i64 with 1 <= n <= 20. Let m = len(requests) and let len(requests') = m. We have 1 <= m <= 16. For every i with 0 <= i < m, len(requests[i]) = 2 and len(requests'[i]) = 2. For every i with 0 <= i < m, 0 <= requests[i][0] < n, 0 <= requests[i][1] < n, 0 <= requests'[i][0] < n, and 0 <= requests'[i][1] < n. There exists a permutation sigma of {0, 1, ..., m-1} such that for every i with 0 <= i < m, requests'[i][0] = requests[sigma(i)][0] and requests'[i][1] = requests[sigma(i)][1]. -/
  theorem spec_10 (n : Std.I64) (requests : Slice (alloc.vec.Vec Std.I64))
      (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20)
      (hm1 : 1 ≤ requests.val.length) (hm2 : requests.val.length ≤ 16)
      (requests' : Slice (alloc.vec.Vec Std.I64))
      (hlen : requests'.val.length = requests.val.length)
      (hlen0 : ∀ i, i < requests.val.length → (reqAt (reqList requests) i).length = 2)
      (hlen1 : ∀ i, i < requests'.val.length → (reqAt (reqList requests') i).length = 2)
      (hfrom0 : ∀ i, i < requests.val.length →
        0 ≤ fromAt (reqList requests) i ∧ fromAt (reqList requests) i < n.val)
      (hto0 : ∀ i, i < requests.val.length →
        0 ≤ toAt (reqList requests) i ∧ toAt (reqList requests) i < n.val)
      (hfrom1 : ∀ i, i < requests'.val.length →
        0 ≤ fromAt (reqList requests') i ∧ fromAt (reqList requests') i < n.val)
      (hto1 : ∀ i, i < requests'.val.length →
        0 ≤ toAt (reqList requests') i ∧ toAt (reqList requests') i < n.val)
      (hperm : List.Perm (reqList requests') (reqList requests)) :
      ∀ r r' : Std.I64, maximum_requests n requests = ok r →
        maximum_requests n requests' = ok r' → r = r' := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n : Std.I64) (requests : Slice (alloc.vec.Vec Std.I64))
        (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20)
        (hm1 : 1 ≤ requests.val.length) (hm2 : requests.val.length ≤ 16)
        (requests' : Slice (alloc.vec.Vec Std.I64))
        (hlen : requests'.val.length = requests.val.length)
        (hlen0 : ∀ i, i < requests.val.length → (reqAt (reqList requests) i).length = 2)
        (hlen1 : ∀ i, i < requests'.val.length → (reqAt (reqList requests') i).length = 2)
        (hfrom0 : ∀ i, i < requests.val.length →
          0 ≤ fromAt (reqList requests) i ∧ fromAt (reqList requests) i < n.val)
        (hto0 : ∀ i, i < requests.val.length →
          0 ≤ toAt (reqList requests) i ∧ toAt (reqList requests) i < n.val)
        (hfrom1 : ∀ i, i < requests'.val.length →
          0 ≤ fromAt (reqList requests') i ∧ fromAt (reqList requests') i < n.val)
        (hto1 : ∀ i, i < requests'.val.length →
          0 ≤ toAt (reqList requests') i ∧ toAt (reqList requests') i < n.val)
        (hperm : List.Perm (reqList requests') (reqList requests)), ∀ r r' : Std.I64, maximum_requests n requests = ok r →
          maximum_requests n requests' = ok r' → r = r') := by
    sorry

  /-- The function returns a result r and r = len(requests).
    Preconditions: n is an i64 with 1 <= n <= 20. Let m = len(requests). requests is a slice with 1 <= m <= 16. For every i with 0 <= i < m, len(requests[i]) = 2. For every i with 0 <= i < m, 0 <= requests[i][0] < n and 0 <= requests[i][1] < n. For every b with 0 <= b < n, the number of i with requests[i][0] = b equals the number of i with requests[i][1] = b. -/
  theorem spec_11 (n : Std.I64) (requests : Slice (alloc.vec.Vec Std.I64))
      (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20)
      (hm1 : 1 ≤ requests.val.length) (hm2 : requests.val.length ≤ 16)
      (hlen : ∀ i, i < requests.val.length → (reqAt (reqList requests) i).length = 2)
      (hfrom : ∀ i, i < requests.val.length →
        0 ≤ fromAt (reqList requests) i ∧ fromAt (reqList requests) i < n.val)
      (hto : ∀ i, i < requests.val.length →
        0 ≤ toAt (reqList requests) i ∧ toAt (reqList requests) i < n.val)
      (hbal : ∀ b : ℤ, 0 ≤ b → b < n.val →
        countFrom (reqList requests) (idxSet (reqList requests)) b =
          countTo (reqList requests) (idxSet (reqList requests)) b) :
      ∃ r : Std.I64, maximum_requests n requests = ok r ∧
        r.val = (requests.val.length : ℤ) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n : Std.I64) (requests : Slice (alloc.vec.Vec Std.I64))
        (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20)
        (hm1 : 1 ≤ requests.val.length) (hm2 : requests.val.length ≤ 16)
        (hlen : ∀ i, i < requests.val.length → (reqAt (reqList requests) i).length = 2)
        (hfrom : ∀ i, i < requests.val.length →
          0 ≤ fromAt (reqList requests) i ∧ fromAt (reqList requests) i < n.val)
        (hto : ∀ i, i < requests.val.length →
          0 ≤ toAt (reqList requests) i ∧ toAt (reqList requests) i < n.val)
        (hbal : ∀ b : ℤ, 0 ≤ b → b < n.val →
          countFrom (reqList requests) (idxSet (reqList requests)) b =
            countTo (reqList requests) (idxSet (reqList requests)) b), ∃ r : Std.I64, maximum_requests n requests = ok r ∧
          r.val = (requests.val.length : ℤ)) := by
    sorry

  /-- The function returns a result r and r = C + 2 * min(A, B), where A is the number of indices i with requests[i][0] = 0 and requests[i][1] = 1, B is the number of indices i with requests[i][0] = 1 and requests[i][1] = 0, and C is the number of indices i with requests[i][0] = requests[i][1].
    Preconditions: n is an i64 with n = 2. Let m = len(requests). requests is a slice with 1 <= m <= 16. For every i with 0 <= i < m, len(requests[i]) = 2. For every i with 0 <= i < m, 0 <= requests[i][0] < n and 0 <= requests[i][1] < n. -/
  theorem spec_12 (n : Std.I64) (requests : Slice (alloc.vec.Vec Std.I64))
      (hn : n.val = 2)
      (hm1 : 1 ≤ requests.val.length) (hm2 : requests.val.length ≤ 16)
      (hlen : ∀ i, i < requests.val.length → (reqAt (reqList requests) i).length = 2)
      (hfrom : ∀ i, i < requests.val.length →
        0 ≤ fromAt (reqList requests) i ∧ fromAt (reqList requests) i < n.val)
      (hto : ∀ i, i < requests.val.length →
        0 ≤ toAt (reqList requests) i ∧ toAt (reqList requests) i < n.val) :
      ∃ r : Std.I64, maximum_requests n requests = ok r ∧
        r.val = (diagCount (reqList requests) : ℤ) +
          2 * (min (countPair (reqList requests) 0 1)
            (countPair (reqList requests) 1 0) : ℤ) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (n : Std.I64) (requests : Slice (alloc.vec.Vec Std.I64))
        (hn : n.val = 2)
        (hm1 : 1 ≤ requests.val.length) (hm2 : requests.val.length ≤ 16)
        (hlen : ∀ i, i < requests.val.length → (reqAt (reqList requests) i).length = 2)
        (hfrom : ∀ i, i < requests.val.length →
          0 ≤ fromAt (reqList requests) i ∧ fromAt (reqList requests) i < n.val)
        (hto : ∀ i, i < requests.val.length →
          0 ≤ toAt (reqList requests) i ∧ toAt (reqList requests) i < n.val), ∃ r : Std.I64, maximum_requests n requests = ok r ∧
          r.val = (diagCount (reqList requests) : ℤ) +
            2 * (min (countPair (reqList requests) 0 1)
              (countPair (reqList requests) 1 0) : ℤ)) := by
    sorry

  /-- Whenever maximum_requests n requests returns r and maximum_requests n requests' returns r', we have r <= r' <= r + 1.
    Preconditions: n is an i64 with 1 <= n <= 20. Let m = len(requests). requests is a slice with 1 <= m <= 15. For every i with 0 <= i < m, len(requests[i]) = 2 and 0 <= requests[i][0] < n and 0 <= requests[i][1] < n. Let a and b be integers with 0 <= a < n and 0 <= b < n. Let requests' be the slice of length m+1 such that requests'[i] = requests[i] for 0 <= i < m and requests'[m] is the vector [a, b]. -/
  theorem spec_13 (n : Std.I64) (requests : Slice (alloc.vec.Vec Std.I64))
      (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20)
      (hm1 : 1 ≤ requests.val.length) (hm2 : requests.val.length ≤ 15)
      (hlen : ∀ i, i < requests.val.length → (reqAt (reqList requests) i).length = 2)
      (hfrom : ∀ i, i < requests.val.length →
        0 ≤ fromAt (reqList requests) i ∧ fromAt (reqList requests) i < n.val)
      (hto : ∀ i, i < requests.val.length →
        0 ≤ toAt (reqList requests) i ∧ toAt (reqList requests) i < n.val)
      (a b : ℤ) (ha1 : 0 ≤ a) (ha2 : a < n.val) (hb1 : 0 ≤ b) (hb2 : b < n.val)
      (requests' : Slice (alloc.vec.Vec Std.I64))
      (hlen' : requests'.val.length = requests.val.length + 1)
      (hval : reqList requests' = reqList requests ++ [[a, b]]) :
      ∀ r r' : Std.I64, maximum_requests n requests = ok r →
        maximum_requests n requests' = ok r' → r.val ≤ r'.val ∧ r'.val ≤ r.val + 1 := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (n : Std.I64) (requests : Slice (alloc.vec.Vec Std.I64))
        (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 20)
        (hm1 : 1 ≤ requests.val.length) (hm2 : requests.val.length ≤ 15)
        (hlen : ∀ i, i < requests.val.length → (reqAt (reqList requests) i).length = 2)
        (hfrom : ∀ i, i < requests.val.length →
          0 ≤ fromAt (reqList requests) i ∧ fromAt (reqList requests) i < n.val)
        (hto : ∀ i, i < requests.val.length →
          0 ≤ toAt (reqList requests) i ∧ toAt (reqList requests) i < n.val)
        (a b : ℤ) (ha1 : 0 ≤ a) (ha2 : a < n.val) (hb1 : 0 ≤ b) (hb2 : b < n.val)
        (requests' : Slice (alloc.vec.Vec Std.I64))
        (hlen' : requests'.val.length = requests.val.length + 1)
        (hval : reqList requests' = reqList requests ++ [[a, b]]), ∀ r r' : Std.I64, maximum_requests n requests = ok r →
          maximum_requests n requests' = ok r' → r.val ≤ r'.val ∧ r'.val ≤ r.val + 1) := by
    sorry

  /-- Whenever maximum_requests n requests returns r and maximum_requests n' requests returns r', we have r = r'.
    Preconditions: n and n' are i64 values with 1 <= n <= n' <= 20. Let m = len(requests). requests is a slice with 1 <= m <= 16. For every i with 0 <= i < m, len(requests[i]) = 2 and 0 <= requests[i][0] < n and 0 <= requests[i][1] < n. -/
  theorem spec_14 (n n' : Std.I64) (requests : Slice (alloc.vec.Vec Std.I64))
      (hn1 : 1 ≤ n.val) (hnn' : n.val ≤ n'.val) (hn'2 : n'.val ≤ 20)
      (hm1 : 1 ≤ requests.val.length) (hm2 : requests.val.length ≤ 16)
      (hlen : ∀ i, i < requests.val.length → (reqAt (reqList requests) i).length = 2)
      (hfrom : ∀ i, i < requests.val.length →
        0 ≤ fromAt (reqList requests) i ∧ fromAt (reqList requests) i < n.val)
      (hto : ∀ i, i < requests.val.length →
        0 ≤ toAt (reqList requests) i ∧ toAt (reqList requests) i < n.val) :
      ∀ r r' : Std.I64, maximum_requests n requests = ok r →
        maximum_requests n' requests = ok r' → r = r' := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (n n' : Std.I64) (requests : Slice (alloc.vec.Vec Std.I64))
        (hn1 : 1 ≤ n.val) (hnn' : n.val ≤ n'.val) (hn'2 : n'.val ≤ 20)
        (hm1 : 1 ≤ requests.val.length) (hm2 : requests.val.length ≤ 16)
        (hlen : ∀ i, i < requests.val.length → (reqAt (reqList requests) i).length = 2)
        (hfrom : ∀ i, i < requests.val.length →
          0 ≤ fromAt (reqList requests) i ∧ fromAt (reqList requests) i < n.val)
        (hto : ∀ i, i < requests.val.length →
          0 ≤ toAt (reqList requests) i ∧ toAt (reqList requests) i < n.val), ∀ r r' : Std.I64, maximum_requests n requests = ok r →
          maximum_requests n' requests = ok r' → r = r') := by
    sorry

  end AegisSpec.MaximumRequests

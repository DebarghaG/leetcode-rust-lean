import Aegis.Str2tree.Code.Funs

/-!
# Specifications of `Aegis.Str2tree.str2tree`

LeetCode problem `construct-binary-tree-from-string`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.Str2tree

  namespace AegisSpec.Str2tree

  def IsDigit (c : Std.U8) : Prop := 48 ≤ c.val ∧ c.val ≤ 57

  instance instDecidableIsDigit (c : Std.U8) : Decidable (IsDigit c) := by
    unfold IsDigit
    infer_instance

  def isDig (c : Std.U8) : Bool := decide (IsDigit c)

  theorem isDig_iff (c : Std.U8) : isDig c = true ↔ IsDigit c := by
    simp [isDig]

  def readDigits : List Std.U8 → Nat → Nat × List Std.U8
    | [], acc => (acc, [])
    | c :: rest, acc =>
      if isDig c then readDigits rest (acc * 10 + (c.val - 48))
      else (acc, c :: rest)

  theorem readDigits_rest_len :
      ∀ (l : List Std.U8) (acc : Nat), (readDigits l acc).2.length ≤ l.length
    | [], acc => by simp [readDigits]
    | c :: rest, acc => by
      rw [readDigits]
      split
      · have h := readDigits_rest_len rest (acc * 10 + (c.val - 48))
        simp only [List.length_cons] at h ⊢
        omega
      · simp

  def parseInt : List Std.U8 → Option (Int × List Std.U8)
    | [] => none
    | c :: rest =>
      if c.val = 45 then
        match rest with
        | [] => none
        | d :: _ =>
          if isDig d then
            let p := readDigits rest 0
            some (-(p.1 : Int), p.2)
          else none
      else if isDig c then
        let p := readDigits (c :: rest) 0
        some ((p.1 : Int), p.2)
      else none

  inductive IntTree where
    | null : IntTree
    | node : Int → IntTree → IntTree → IntTree

  namespace IntTree

  def preorder : IntTree → List Int
    | null => []
    | node v l r => v :: (l.preorder ++ r.preorder)

  def size : IntTree → Nat
    | null => 0
    | node _ l r => 1 + l.size + r.size

  def childNulls : IntTree → List (Bool × Bool)
    | null => []
    | node _ l r =>
      ((match l with | null => true | node _ _ _ => false),
       (match r with | null => true | node _ _ _ => false)) ::
        (l.childNulls ++ r.childNulls)

  def annotAux : Nat → IntTree → List (Nat × Int)
    | _, null => []
    | d, node v l r => (d, v) :: (annotAux (d + 1) l ++ annotAux (d + 1) r)

  def annotated (t : IntTree) : List (Nat × Int) := annotAux 0 t

  end IntTree

  def toIntTree : Tree → IntTree
    | Tree.Null => IntTree.null
    | Tree.Node v l r => IntTree.node v.val (toIntTree l) (toIntTree r)

  inductive GroupInfo where
    | absent : GroupInfo
    | empty : GroupInfo
    | nonempty : GroupInfo
    deriving DecidableEq

  namespace GroupInfo

  def childIsNull : GroupInfo → Bool
    | absent => true
    | empty => true
    | nonempty => false

  end GroupInfo

  structure Rec where
    value : Int
    leftGroup : GroupInfo
    rightGroup : GroupInfo

  def Rec.childNulls (r : Rec) : Bool × Bool :=
    (r.leftGroup.childIsNull, r.rightGroup.childIsNull)

  def parseSub : Nat → List Std.U8 → Option (IntTree × List Rec × List Std.U8)
    | 0, _ => none
    | _ + 1, [] => some (IntTree.null, [], [])
    | fuel + 1, l =>
      match parseInt l with
      | none => none
      | some (v, rest) =>
        match rest with
        | [] =>
          some (IntTree.node v IntTree.null IntTree.null,
            [⟨v, GroupInfo.absent, GroupInfo.absent⟩], [])
        | c1 :: s1 =>
          if c1.val = 40 then
            match s1 with
            | [] => none
            | c2 :: s2 =>
              if c2.val = 41 then
                match s2 with
                | [] =>
                  some (IntTree.node v IntTree.null IntTree.null,
                    [⟨v, GroupInfo.empty, GroupInfo.absent⟩], [])
                | c3 :: s3 =>
                  if c3.val = 40 then
                    match s3 with
                    | [] => none
                    | c4 :: _ =>
                      if c4.val = 41 then
                        some (IntTree.node v IntTree.null IntTree.null,
                          [⟨v, GroupInfo.empty, GroupInfo.empty⟩], s3.tail)
                      else
                        match parseSub fuel s3 with
                        | none => none
                        | some (t2, recs2, r3) =>
                          match r3 with
                          | [] => none
                          | c5 :: s5 =>
                            if c5.val = 41 then
                              some (IntTree.node v IntTree.null t2,
                                ⟨v, GroupInfo.empty, GroupInfo.nonempty⟩ :: recs2, s5)
                            else none
                  else
                    some (IntTree.node v IntTree.null IntTree.null,
                      [⟨v, GroupInfo.empty, GroupInfo.absent⟩], s2)
              else
                match parseSub fuel s1 with
                | none => none
                | some (t1, recs1, r1) =>
                  match r1 with
                  | [] => none
                  | c3 :: s3 =>
                    if c3.val = 41 then
                      match s3 with
                      | [] =>
                        some (IntTree.node v t1 IntTree.null,
                          ⟨v, GroupInfo.nonempty, GroupInfo.absent⟩ :: recs1, [])
                      | c4 :: s4 =>
                        if c4.val = 40 then
                          match s4 with
                          | [] => none
                          | c5 :: _ =>
                            if c5.val = 41 then
                              some (IntTree.node v t1 IntTree.null,
                                ⟨v, GroupInfo.nonempty, GroupInfo.empty⟩ :: recs1, s4.tail)
                            else
                              match parseSub fuel s4 with
                              | none => none
                              | some (t2, recs2, r5) =>
                                match r5 with
                                | [] => none
                                | c6 :: s6 =>
                                  if c6.val = 41 then
                                    some (IntTree.node v t1 t2,
                                      ⟨v, GroupInfo.nonempty, GroupInfo.nonempty⟩ ::
                                        (recs1 ++ recs2), s6)
                                  else none
                        else
                          some (IntTree.node v t1 IntTree.null,
                            ⟨v, GroupInfo.nonempty, GroupInfo.absent⟩ :: recs1, s3)
                    else none
          else
            some (IntTree.node v IntTree.null IntTree.null,
              [⟨v, GroupInfo.absent, GroupInfo.absent⟩], rest)

  def parseStr (l : List Std.U8) : Option (IntTree × List Rec × List Std.U8) :=
    parseSub (l.length + 1) l

  def decode (l : List Std.U8) : Option IntTree :=
    match parseStr l with
    | some (t, _, []) => some t
    | _ => none

  def strRecords (l : List Std.U8) : Option (List Rec) :=
    match parseStr l with
    | some (_, recs, []) => some recs
    | _ => none

  def Valid (l : List Std.U8) : Prop := ∃ t, decode l = some t

  structure NumSt where
    run : Option (Nat × Nat)
    acc : List Int

  def numsStep (c : Std.U8) (st : NumSt) : NumSt :=
    if isDig c then
      { st with run := some (match st.run with
          | none => (10, c.val - 48)
          | some (p, v) => (p * 10, v + p * (c.val - 48))) }
    else if c.val = 45 then
      { st with
        run := none
        acc := (match st.run with
          | none => st.acc
          | some (_, v) => (-(v : Int)) :: st.acc) }
    else
      { st with
        run := none
        acc := (match st.run with
          | none => st.acc
          | some (_, v) => (v : Int) :: st.acc) }

  def nums (l : List Std.U8) : List Int :=
    let st := List.foldr numsStep ⟨none, []⟩ l
    match st.run with
    | none => st.acc
    | some (_, v) => (v : Int) :: st.acc

  def NumsBounded (l : List Std.U8) : Prop := ∀ v, v ∈ nums l → v.natAbs ≤ 2 ^ 30

  def HasEmptyGroup (l : List Std.U8) : Prop :=
    ∃ pre post, l = pre ++ 40#u8 :: 41#u8 :: post

  structure DepSt where
    run : Option (Nat × Nat)
    acc : List (Nat × Int)
    cright : Int

  def depStep (dtot : Int) (c : Std.U8) (st : DepSt) : DepSt :=
    if isDig c then
      { st with run := some (match st.run with
          | none => (10, c.val - 48)
          | some (p, v) => (p * 10, v + p * (c.val - 48))) }
    else if c.val = 45 then
      { st with
        run := none
        acc := (match st.run with
          | none => st.acc
          | some (_, v) => (Int.toNat (dtot + st.cright), -(v : Int)) :: st.acc) }
    else
      { st with
        run := none
        acc := (match st.run with
          | none => st.acc
          | some (_, v) => (Int.toNat (dtot + st.cright), (v : Int)) :: st.acc)
        cright := (if c.val = 40 then st.cright - 1
                   else if c.val = 41 then st.cright + 1 else st.cright) }

  def scanDepths (l : List Std.U8) : List (Nat × Int) :=
    let dtot : Int := (l.countP (fun c => decide (c.val = 40)) : Int) -
      (l.countP (fun c => decide (c.val = 41)) : Int)
    let st := List.foldr (depStep dtot) ⟨none, [], 0⟩ l
    match st.run with
    | none => st.acc
    | some (_, v) => (Int.toNat (dtot + st.cright), (v : Int)) :: st.acc

  /-- The function returns a result r = ok T where T is the unique tree encoded by s according to the recursive rules: (1) if s is empty, T = Null; (2) if s = n with no parentheses, T = Node(n, Null, Null); (3) if s = n(g1), T = Node(n, T1, Null) where T1 is the tree encoded by g1; (4) if s = n(g1)(g2), T = Node(n, T1, T2) where T1 and T2 are the trees encoded by g1 and g2 respectively. Here n denotes the integer value of the literal.
    Preconditions: s is a byte slice representing a string of ASCII characters from the set {'0'-'9', '-', '(', ')'}. The string is a valid serialization of a binary tree: either s is empty, or s has the form n, n(g1), or n(g1)(g2), where n is an optional '-' followed by one or more decimal digits (the integer value has absolute value at most 2^30), and g1, g2 are themselves valid serializations (possibly empty). The length of s is at most 30000. The parentheses are balanced and the decomposition is unique. -/
  theorem spec_1 (s : Slice Std.U8) (hvalid : Valid s.val)
      (hlen : s.val.length ≤ 30000) (hbounds : NumsBounded s.val) :
      ∃ (T : Tree) (U : IntTree),
        str2tree s = ok T ∧ decode s.val = some U ∧ toIntTree T = U := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice Std.U8) (hvalid : Valid s.val)
        (hlen : s.val.length ≤ 30000) (hbounds : NumsBounded s.val), ∃ (T : Tree) (U : IntTree),
          str2tree s = ok T ∧ decode s.val = some U ∧ toIntTree T = U) := by
    sorry

  /-- The function returns a result (i.e., it does not fail, panic, or overflow) for every valid s.
    Preconditions: Same as spec_1: s is a valid tree string (length ≤ 30000, all numbers have absolute value ≤ 2^30, and s conforms to the grammar in spec_1). -/
  theorem spec_2 (s : Slice Std.U8) (hvalid : Valid s.val)
      (hlen : s.val.length ≤ 30000) (hbounds : NumsBounded s.val) :
      ∃ T : Tree, str2tree s = ok T := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice Std.U8) (hvalid : Valid s.val)
        (hlen : s.val.length ≤ 30000) (hbounds : NumsBounded s.val), ∃ T : Tree, str2tree s = ok T) := by
    sorry

  /-- Let nums(s) be the list of integers appearing in s from left to right, where each integer is the maximal substring consisting of an optional '-' followed by one or more decimal digits. Then the preorder traversal (root, then left subtree, then right subtree) of the returned tree T (from r = ok T) yields exactly nums(s).
    Preconditions: Same as spec_1. -/
  theorem spec_3 (s : Slice Std.U8) (hvalid : Valid s.val)
      (hlen : s.val.length ≤ 30000) (hbounds : NumsBounded s.val) :
      ∃ T : Tree, str2tree s = ok T ∧ IntTree.preorder (toIntTree T) = nums s.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice Std.U8) (hvalid : Valid s.val)
        (hlen : s.val.length ≤ 30000) (hbounds : NumsBounded s.val), ∃ T : Tree, str2tree s = ok T ∧ IntTree.preorder (toIntTree T) = nums s.val) := by
    sorry

  /-- The number of nodes in the returned tree T (from r = ok T) equals the number of integer literals in s.
    Preconditions: Same as spec_1. -/
  theorem spec_4 (s : Slice Std.U8) (hvalid : Valid s.val)
      (hlen : s.val.length ≤ 30000) (hbounds : NumsBounded s.val) :
      ∃ T : Tree, str2tree s = ok T ∧ IntTree.size (toIntTree T) = (nums s.val).length := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice Std.U8) (hvalid : Valid s.val)
        (hlen : s.val.length ≤ 30000) (hbounds : NumsBounded s.val), ∃ T : Tree, str2tree s = ok T ∧ IntTree.size (toIntTree T) = (nums s.val).length) := by
    sorry

  /-- Every node value in the returned tree T (from r = ok T) equals the integer value of some integer literal occurring in s. Consequently, its absolute value is at most 2^30 and it fits in the i64 range.
    Preconditions: Same as spec_1: s is a valid serialization of a binary tree, with length at most 30000 and every integer literal having absolute value at most 2^30. -/
  theorem spec_5 (s : Slice Std.U8) (hvalid : Valid s.val)
      (hlen : s.val.length ≤ 30000) (hbounds : NumsBounded s.val) :
      ∃ T : Tree, str2tree s = ok T ∧
        (∀ v, v ∈ IntTree.preorder (toIntTree T) → v ∈ nums s.val) ∧
        (∀ v, v ∈ IntTree.preorder (toIntTree T) → v.natAbs ≤ 2 ^ 30) ∧
        (∀ v, v ∈ IntTree.preorder (toIntTree T) → -(2 : Int) ^ 63 ≤ v ∧ v < (2 : Int) ^ 63) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice Std.U8) (hvalid : Valid s.val)
        (hlen : s.val.length ≤ 30000) (hbounds : NumsBounded s.val), ∃ T : Tree, str2tree s = ok T ∧
          (∀ v, v ∈ IntTree.preorder (toIntTree T) → v ∈ nums s.val) ∧
          (∀ v, v ∈ IntTree.preorder (toIntTree T) → v.natAbs ≤ 2 ^ 30) ∧
          (∀ v, v ∈ IntTree.preorder (toIntTree T) → -(2 : Int) ^ 63 ≤ v ∧ v < (2 : Int) ^ 63)) := by
    sorry

  /-- The root value of the returned tree T (from r = ok T) equals the integer value of the longest prefix of s that is an integer literal (an optional '-' followed by one or more decimal digits).
    Preconditions: Same as spec_1 and s is non-empty. -/
  theorem spec_6 (s : Slice Std.U8) (hvalid : Valid s.val)
      (hlen : s.val.length ≤ 30000) (hbounds : NumsBounded s.val)
      (hne : s.val ≠ []) (v : Int) (rest : List Std.U8)
      (hprefix : parseInt s.val = some (v, rest)) :
      ∃ (T : Tree) (l r : IntTree), str2tree s = ok T ∧ toIntTree T = IntTree.node v l r := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Slice Std.U8) (hvalid : Valid s.val)
        (hlen : s.val.length ≤ 30000) (hbounds : NumsBounded s.val)
        (hne : s.val ≠ []) (v : Int) (rest : List Std.U8)
        (hprefix : parseInt s.val = some (v, rest)), ∃ (T : Tree) (l r : IntTree), str2tree s = ok T ∧ toIntTree T = IntTree.node v l r) := by
    sorry

  /-- The function returns r = ok (Node(n, Null, Null)) where n is the integer value of s.
    Preconditions: s is a non-empty valid tree string that contains no '(' or ')' characters. -/
  theorem spec_7 (s : Slice Std.U8) (hvalid : Valid s.val) (hne : s.val ≠ [])
      (hnopar : ∀ c, c ∈ s.val → c.val ≠ 40 ∧ c.val ≠ 41) :
      ∃ (n : Std.I64) (v : Int),
        str2tree s = ok (Tree.Node n Tree.Null Tree.Null) ∧ nums s.val = [v] ∧ n.val = v := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s : Slice Std.U8) (hvalid : Valid s.val) (hne : s.val ≠ [])
        (hnopar : ∀ c, c ∈ s.val → c.val ≠ 40 ∧ c.val ≠ 41), ∃ (n : Std.I64) (v : Int),
          str2tree s = ok (Tree.Node n Tree.Null Tree.Null) ∧ nums s.val = [v] ∧ n.val = v) := by
    sorry

  /-- For every maximal integer literal in s that begins with '-', the corresponding node in the returned tree T (from r = ok T) has the integer value of that literal. In particular, if the first integer literal in s has a leading '-' and its value is nonzero, then the root value is negative.
    Preconditions: Same as spec_1: s is a valid serialization of a binary tree, with length at most 30000 and every integer literal having absolute value at most 2^30. -/
  theorem spec_8 (s : Slice Std.U8) (hvalid : Valid s.val)
      (hlen : s.val.length ≤ 30000) (hbounds : NumsBounded s.val) :
      ∃ T : Tree, str2tree s = ok T ∧
        (∀ v, v ∈ nums s.val → v < 0 → v ∈ IntTree.preorder (toIntTree T)) ∧
        (∀ v, (nums s.val).head? = some v → v < 0 →
          ∃ (v0 : Int) (l r : IntTree),
            toIntTree T = IntTree.node v0 l r ∧ v0 < 0) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s : Slice Std.U8) (hvalid : Valid s.val)
        (hlen : s.val.length ≤ 30000) (hbounds : NumsBounded s.val), ∃ T : Tree, str2tree s = ok T ∧
          (∀ v, v ∈ nums s.val → v < 0 → v ∈ IntTree.preorder (toIntTree T)) ∧
          (∀ v, (nums s.val).head? = some v → v < 0 →
            ∃ (v0 : Int) (l r : IntTree),
              toIntTree T = IntTree.node v0 l r ∧ v0 < 0)) := by
    sorry

  /-- Let v be the integer value of n. The function returns r = ok (Node(v, T1, Null)), where T1 is the tree encoded by g (possibly Null when g is empty).
    Preconditions: s is a valid tree string of the form n(g), where n is an integer literal and g is a valid tree string (possibly empty). That is, there is exactly one top-level parenthesized group after the initial integer. The length of s is at most 30000 and every literal has absolute value at most 2^30. -/
  theorem spec_9 (s : Slice Std.U8) (v : Int) (g : List Std.U8)
      (hvalid : Valid s.val) (hlen : s.val.length ≤ 30000) (hbounds : NumsBounded s.val)
      (hform : parseInt s.val = some (v, 40#u8 :: (g ++ [41#u8]))) (hg : Valid g) :
      ∃ (T : Tree) (T1 : IntTree),
        str2tree s = ok T ∧ decode g = some T1 ∧
          toIntTree T = IntTree.node v T1 IntTree.null := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s : Slice Std.U8) (v : Int) (g : List Std.U8)
        (hvalid : Valid s.val) (hlen : s.val.length ≤ 30000) (hbounds : NumsBounded s.val)
        (hform : parseInt s.val = some (v, 40#u8 :: (g ++ [41#u8]))) (hg : Valid g), ∃ (T : Tree) (T1 : IntTree),
          str2tree s = ok T ∧ decode g = some T1 ∧
            toIntTree T = IntTree.node v T1 IntTree.null) := by
    sorry

  /-- Let v be the integer value of n. The function returns r = ok (Node(v, T1, T2)), where T1 is the tree encoded by g1 and T2 is the tree encoded by g2 (each may be Null when the corresponding group is empty).
    Preconditions: s is a valid tree string of the form n(g1)(g2), where n is an integer literal and g1, g2 are valid tree strings (possibly empty). That is, there are exactly two top-level parenthesized groups after the initial integer. The length of s is at most 30000 and every literal has absolute value at most 2^30. -/
  theorem spec_10 (s : Slice Std.U8) (v : Int) (g1 g2 : List Std.U8)
      (hvalid : Valid s.val) (hlen : s.val.length ≤ 30000) (hbounds : NumsBounded s.val)
      (hform : parseInt s.val = some (v, 40#u8 :: (g1 ++ 41#u8 :: 40#u8 :: (g2 ++ [41#u8]))))
      (hg1 : Valid g1) (hg2 : Valid g2) :
      ∃ (T : Tree) (T1 T2 : IntTree),
        str2tree s = ok T ∧ decode g1 = some T1 ∧ decode g2 = some T2 ∧
          toIntTree T = IntTree.node v T1 T2 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s : Slice Std.U8) (v : Int) (g1 g2 : List Std.U8)
        (hvalid : Valid s.val) (hlen : s.val.length ≤ 30000) (hbounds : NumsBounded s.val)
        (hform : parseInt s.val = some (v, 40#u8 :: (g1 ++ 41#u8 :: 40#u8 :: (g2 ++ [41#u8]))))
        (hg1 : Valid g1) (hg2 : Valid g2), ∃ (T : Tree) (T1 T2 : IntTree),
          str2tree s = ok T ∧ decode g1 = some T1 ∧ decode g2 = some T2 ∧
            toIntTree T = IntTree.node v T1 T2) := by
    sorry

  /-- Whenever a parenthesized group in s is empty, the corresponding child subtree in the returned tree T (from r = ok T) is Null. More generally, the empty string encodes the Null tree, so any empty child group yields a Null child.
    Preconditions: Same as spec_1. Additionally, s contains a parenthesized group that is empty, i.e., the substring "()" appears as a child group. -/
  theorem spec_11 (s : Slice Std.U8) (hvalid : Valid s.val)
      (hlen : s.val.length ≤ 30000) (hbounds : NumsBounded s.val)
      (hempty : HasEmptyGroup s.val) :
      ∃ (T : Tree) (R : List Rec), str2tree s = ok T ∧ strRecords s.val = some R ∧
        ∀ (i : Nat) (r : Rec) (b : Bool × Bool),
          R[i]? = some r → (IntTree.childNulls (toIntTree T))[i]? = some b →
          (r.leftGroup = GroupInfo.empty → b.1 = true) ∧
            (r.rightGroup = GroupInfo.empty → b.2 = true) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (s : Slice Std.U8) (hvalid : Valid s.val)
        (hlen : s.val.length ≤ 30000) (hbounds : NumsBounded s.val)
        (hempty : HasEmptyGroup s.val), ∃ (T : Tree) (R : List Rec), str2tree s = ok T ∧ strRecords s.val = some R ∧
          ∀ (i : Nat) (r : Rec) (b : Bool × Bool),
            R[i]? = some r → (IntTree.childNulls (toIntTree T))[i]? = some b →
            (r.leftGroup = GroupInfo.empty → b.1 = true) ∧
              (r.rightGroup = GroupInfo.empty → b.2 = true)) := by
    sorry

  /-- For every node in the returned tree T (from r = ok T), its left child (if present) corresponds to the first parenthesized group immediately following the node's integer literal in s, and its right child (if present) corresponds to the second parenthesized group. If a group is missing, the corresponding child is Null.
    Preconditions: Same as spec_1. -/
  theorem spec_12 (s : Slice Std.U8) (hvalid : Valid s.val)
      (hlen : s.val.length ≤ 30000) (hbounds : NumsBounded s.val) :
      ∃ (T : Tree) (R : List Rec), str2tree s = ok T ∧ strRecords s.val = some R ∧
        IntTree.preorder (toIntTree T) = R.map (fun r => r.value) ∧
        IntTree.childNulls (toIntTree T) = R.map Rec.childNulls := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (s : Slice Std.U8) (hvalid : Valid s.val)
        (hlen : s.val.length ≤ 30000) (hbounds : NumsBounded s.val), ∃ (T : Tree) (R : List Rec), str2tree s = ok T ∧ strRecords s.val = some R ∧
          IntTree.preorder (toIntTree T) = R.map (fun r => r.value) ∧
          IntTree.childNulls (toIntTree T) = R.map Rec.childNulls) := by
    sorry

  /-- For every node in the returned tree T (from r = ok T), the depth of the node (root at depth 0) equals the number of unmatched opening parentheses '(' that appear before the node's integer literal in s. Equivalently, the tree's nesting structure matches the parenthesis nesting in s.
    Preconditions: Same as spec_1. -/
  theorem spec_13 (s : Slice Std.U8) (hvalid : Valid s.val)
      (hlen : s.val.length ≤ 30000) (hbounds : NumsBounded s.val) :
      ∃ T : Tree, str2tree s = ok T ∧ IntTree.annotated (toIntTree T) = scanDepths s.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (s : Slice Std.U8) (hvalid : Valid s.val)
        (hlen : s.val.length ≤ 30000) (hbounds : NumsBounded s.val), ∃ T : Tree, str2tree s = ok T ∧ IntTree.annotated (toIntTree T) = scanDepths s.val) := by
    sorry

  end AegisSpec.Str2tree

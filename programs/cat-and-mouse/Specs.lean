import Aegis.CatMouseGame.Code.Funs

/-!
# Specifications of `Aegis.CatMouseGame.cat_mouse_game`

LeetCode problem `cat-and-mouse`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CatMouseGame

def rows (graph : Slice (alloc.vec.Vec Std.I64)) : List (List Int) :=
  graph.val.map (fun row => row.val.map (fun x => x.val))

def Adj (G : List (List Int)) (u v : Nat) : Prop :=
  (v : Int) ∈ G.getD u []

def NodePath (G : List (List Int)) (u v : Nat) : Prop :=
  Relation.ReflTransGen (Adj G) u v

inductive Player where
  | mouse
  | cat
  deriving DecidableEq, Repr

structure State where
  m : Nat
  c : Nat
  turn : Player
  deriving DecidableEq, Repr

def initialState : State := ⟨1, 2, Player.mouse⟩

def Terminal (s : State) : Prop := s.m = 0 ∨ s.m = s.c

def ValidState (G : List (List Int)) (s : State) : Prop :=
  s.m < G.length ∧ s.c < G.length ∧ 0 < s.c

def HasLegalMove (G : List (List Int)) (s : State) : Prop :=
  (s.turn = Player.mouse ∧ ∃ m', Adj G s.m m') ∨
  (s.turn = Player.cat ∧ ∃ c', Adj G s.c c' ∧ c' ≠ 0)

def Step (G : List (List Int)) (s t : State) : Prop :=
  ¬ Terminal s ∧
    ((s.turn = Player.mouse ∧ ∃ m', Adj G s.m m' ∧ t = ⟨m', s.c, Player.cat⟩) ∨
      (s.turn = Player.cat ∧ ∃ c', Adj G s.c c' ∧ c' ≠ 0 ∧ t = ⟨s.m, c', Player.mouse⟩))

def StateReachable (G : List (List Int)) (s : State) : Prop :=
  Relation.ReflTransGen (Step G) initialState s

def IsPlayPrefix (G : List (List Int)) (hist : List State) : Prop :=
  hist ≠ [] ∧ hist.head? = some initialState ∧
    ∀ (i : Nat) (s t : State), hist[i]? = some s → hist[i + 1]? = some t → Step G s t

def IsMouseStrategy (G : List (List Int)) (σ : List State → Nat) : Prop :=
  ∀ (hist : List State) (s : State), IsPlayPrefix G hist → hist.getLast? = some s →
    ¬ Terminal s → s.turn = Player.mouse → Adj G s.m (σ hist)

def IsCatStrategy (G : List (List Int)) (τ : List State → Nat) : Prop :=
  ∀ (hist : List State) (s : State), IsPlayPrefix G hist → hist.getLast? = some s →
    ¬ Terminal s → s.turn = Player.cat → Adj G s.c (τ hist) ∧ τ hist ≠ 0

def Play (G : List (List Int)) (σ τ : List State → Nat) (hist : List State) : Prop :=
  hist ≠ [] ∧
    hist.head? = some initialState ∧
    (∀ (i : Nat) (s t : State), hist[i]? = some s → hist[i + 1]? = some t →
      ((s.turn = Player.mouse ∧ σ (hist.take (i + 1)) = t.m) ∨
        (s.turn = Player.cat ∧ τ (hist.take (i + 1)) = t.c)) ∧
        Step G s t) ∧
    (∀ (i : Nat) (s : State), hist[i]? = some s → i + 1 < hist.length →
      ¬ Terminal s ∧ ¬ ∃ j, j < i ∧ hist[j]? = some s) ∧
    ∃ s, hist.getLast? = some s ∧
      (Terminal s ∨ ∃ j, j < hist.length - 1 ∧ hist[j]? = some s)

def EndsInMouseWin (hist : List State) : Prop :=
  ∃ s, hist.getLast? = some s ∧ s.m = 0

def EndsInCatWin (hist : List State) : Prop :=
  ∃ s, hist.getLast? = some s ∧ s.m = s.c

def EndsInDraw (hist : List State) : Prop :=
  ∃ s, hist.getLast? = some s ∧ ¬ Terminal s

def LastRepeats (hist : List State) : Prop :=
  ∃ (i : Nat) (s : State), i + 1 < hist.length ∧ hist[i]? = some s ∧
    hist.getLast? = some s

def MouseForcesWin (G : List (List Int)) : Prop :=
  ∃ σ, IsMouseStrategy G σ ∧
    ∀ τ, IsCatStrategy G τ → ∀ hist, Play G σ τ hist → EndsInMouseWin hist

def CatForcesWin (G : List (List Int)) : Prop :=
  ∃ τ, IsCatStrategy G τ ∧
    ∀ σ, IsMouseStrategy G σ → ∀ hist, Play G σ τ hist → EndsInCatWin hist

structure GraphPre (G : List (List Int)) : Prop where

  three_le : 3 ≤ G.length

  le_fifty : G.length ≤ 50

  row_nonempty : ∀ i, i < G.length → 1 ≤ (G.getD i []).length

  row_short : ∀ i, i < G.length → (G.getD i []).length < G.length

  row_bounds : ∀ (i : Nat) (v : Int), i < G.length → v ∈ G.getD i [] →
    0 ≤ v ∧ v < (G.length : Int) ∧ v ≠ (i : Int)

  row_nodup : ∀ i, i < G.length → (G.getD i []).Nodup

  undirected : ∀ u v, u < G.length → v < G.length → (Adj G u v ↔ Adj G v u)

  can_move : ∀ s, StateReachable G s → ¬ Terminal s → HasLegalMove G s

/-- Define a state as a triple (m,c,t) where 0 <= m < n, 1 <= c < n (the Cat never occupies the hole), and t is either Mouse or Cat. A state is terminal if m = 0 (Mouse has won) or m = c (Cat has won); terminal states are not played from. At a nonterminal state, if t = Mouse, the legal moves are all m' occurring in graph[m]; after moving to m', if m' = 0 the Mouse wins, if m' = c the Cat wins, otherwise the next state is (m',c,Cat). If t = Cat, the legal moves are all c' occurring in graph[c] with c' != 0; after moving to c', if c' = m the Cat wins, otherwise the next state is (m,c',Mouse). If a nonterminal state is reached that equals an earlier state of the play in both m, c, and t, the game stops in a draw. The initial state is (1,2,Mouse). A Mouse strategy assigns a legal move to every finite history ending in a nonterminal Mouse-turn state; a Cat strategy is defined analogously. For a pair of strategies, follow their moves until a terminal state or a repeated state; the outcome is respectively Mouse win, Cat win, or draw. The function returns a result r, and r = 1 if there exists a Mouse strategy such that every Cat strategy yields a Mouse win; r = 2 if there exists a Cat strategy such that every Mouse strategy yields a Cat win; otherwise r = 0.
  Preconditions: Let n = len(graph). The input satisfies: 3 <= n <= 50; for every i with 0 <= i < n, 1 <= len(graph[i]) < n; every element graph[i][j] satisfies 0 <= graph[i][j] < n and graph[i][j] != i; each graph[i] has no repeated values; the graph is undirected, i.e. for all u,v with 0 <= u,v < n, v occurs in graph[u] iff u occurs in graph[v]; and the promise 'the mouse and the cat can always move' holds: from every nonterminal state reachable from the initial state (1,2,Mouse) by legal moves under the rules in the statement, the player to move has at least one legal move. -/
theorem spec_1 (graph : Slice (alloc.vec.Vec Std.I64)) (h : GraphPre (rows graph)) :
    ∃ r, Aegis.CatMouseGame.cat_mouse_game graph = ok r ∧
      (r.val = 1 ↔ MouseForcesWin (rows graph)) ∧
      (r.val = 2 ↔ CatForcesWin (rows graph)) ∧
      (r.val = 0 ↔ ¬ MouseForcesWin (rows graph) ∧ ¬ CatForcesWin (rows graph)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (graph : Slice (alloc.vec.Vec Std.I64)) (h : GraphPre (rows graph)), ∃ r, Aegis.CatMouseGame.cat_mouse_game graph = ok r ∧
      (r.val = 1 ↔ MouseForcesWin (rows graph)) ∧
      (r.val = 2 ↔ CatForcesWin (rows graph)) ∧
      (r.val = 0 ↔ ¬ MouseForcesWin (rows graph) ∧ ¬ CatForcesWin (rows graph))) := by
  sorry

/-- For every graph satisfying the preconditions, the function cat_mouse_game(graph) returns a result r; it does not fail (no panic, overflow, or out-of-bounds).
  Preconditions: Same as spec_1. -/
theorem spec_2 (graph : Slice (alloc.vec.Vec Std.I64)) (h : GraphPre (rows graph)) :
    ∃ r, Aegis.CatMouseGame.cat_mouse_game graph = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (graph : Slice (alloc.vec.Vec Std.I64)) (h : GraphPre (rows graph)), ∃ r, Aegis.CatMouseGame.cat_mouse_game graph = ok r) := by
  sorry

/-- Whenever the function returns a result r, r is in {0,1,2}.
  Preconditions: Same as spec_1. -/
theorem spec_3 (graph : Slice (alloc.vec.Vec Std.I64)) (h : GraphPre (rows graph))
    (r : Std.I64) (hr : Aegis.CatMouseGame.cat_mouse_game graph = ok r) :
    r.val = 0 ∨ r.val = 1 ∨ r.val = 2 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (graph : Slice (alloc.vec.Vec Std.I64)) (h : GraphPre (rows graph))
    (r : Std.I64) (hr : Aegis.CatMouseGame.cat_mouse_game graph = ok r), r.val = 0 ∨ r.val = 1 ∨ r.val = 2) := by
  sorry

/-- If there exists a Mouse strategy such that, against every Cat strategy, the play from the initial state (1,2,Mouse) ends in a Mouse win under the game rules of spec_1, then the function returns 1.
  Preconditions: Same as spec_1. -/
theorem spec_4 (graph : Slice (alloc.vec.Vec Std.I64)) (h : GraphPre (rows graph))
    (hm : MouseForcesWin (rows graph)) :
    Aegis.CatMouseGame.cat_mouse_game graph = ok 1#i64 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (graph : Slice (alloc.vec.Vec Std.I64)) (h : GraphPre (rows graph))
    (hm : MouseForcesWin (rows graph)), Aegis.CatMouseGame.cat_mouse_game graph = ok 1#i64) := by
  sorry

/-- If there exists a Cat strategy such that, against every Mouse strategy, the play from the initial state (1,2,Mouse) ends in a Cat win under the game rules of spec_1, then the function returns 2.
  Preconditions: Same as spec_1. -/
theorem spec_5 (graph : Slice (alloc.vec.Vec Std.I64)) (h : GraphPre (rows graph))
    (hc : CatForcesWin (rows graph)) :
    Aegis.CatMouseGame.cat_mouse_game graph = ok 2#i64 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (graph : Slice (alloc.vec.Vec Std.I64)) (h : GraphPre (rows graph))
    (hc : CatForcesWin (rows graph)), Aegis.CatMouseGame.cat_mouse_game graph = ok 2#i64) := by
  sorry

/-- If neither a Mouse force-win strategy nor a Cat force-win strategy exists from the initial state (1,2,Mouse) under the game rules of spec_1, then the function returns 0.
  Preconditions: Same as spec_1. -/
theorem spec_6 (graph : Slice (alloc.vec.Vec Std.I64)) (h : GraphPre (rows graph))
    (hm : ¬ MouseForcesWin (rows graph)) (hc : ¬ CatForcesWin (rows graph)) :
    Aegis.CatMouseGame.cat_mouse_game graph = ok 0#i64 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (graph : Slice (alloc.vec.Vec Std.I64)) (h : GraphPre (rows graph))
    (hm : ¬ MouseForcesWin (rows graph)) (hc : ¬ CatForcesWin (rows graph)), Aegis.CatMouseGame.cat_mouse_game graph = ok 0#i64) := by
  sorry

/-- Whenever the function returns 1, there exists a Mouse strategy such that for every Cat strategy the play from (1,2,Mouse) reaches a terminal state with Mouse at node 0 before the Cat occupies the same node as the Mouse and before any nonterminal state repeats; equivalently, Mouse can force a win.
  Preconditions: Same as spec_1. -/
theorem spec_7 (graph : Slice (alloc.vec.Vec Std.I64)) (h : GraphPre (rows graph))
    (r : Std.I64) (hr : Aegis.CatMouseGame.cat_mouse_game graph = ok r) (h1 : r.val = 1) :
    ∃ σ, IsMouseStrategy (rows graph) σ ∧
      ∀ τ, IsCatStrategy (rows graph) τ → ∀ hist, Play (rows graph) σ τ hist →
        EndsInMouseWin hist := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (graph : Slice (alloc.vec.Vec Std.I64)) (h : GraphPre (rows graph))
    (r : Std.I64) (hr : Aegis.CatMouseGame.cat_mouse_game graph = ok r) (h1 : r.val = 1), ∃ σ, IsMouseStrategy (rows graph) σ ∧
      ∀ τ, IsCatStrategy (rows graph) τ → ∀ hist, Play (rows graph) σ τ hist →
        EndsInMouseWin hist) := by
  sorry

/-- Whenever the function returns 2, there exists a Cat strategy such that for every Mouse strategy the play from (1,2,Mouse) reaches a terminal state with Cat and Mouse on the same node before the Mouse reaches node 0 and before any nonterminal state repeats; equivalently, Cat can force a win.
  Preconditions: Same as spec_1. -/
theorem spec_8 (graph : Slice (alloc.vec.Vec Std.I64)) (h : GraphPre (rows graph))
    (r : Std.I64) (hr : Aegis.CatMouseGame.cat_mouse_game graph = ok r) (h2 : r.val = 2) :
    ∃ τ, IsCatStrategy (rows graph) τ ∧
      ∀ σ, IsMouseStrategy (rows graph) σ → ∀ hist, Play (rows graph) σ τ hist →
        EndsInCatWin hist := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (graph : Slice (alloc.vec.Vec Std.I64)) (h : GraphPre (rows graph))
    (r : Std.I64) (hr : Aegis.CatMouseGame.cat_mouse_game graph = ok r) (h2 : r.val = 2), ∃ τ, IsCatStrategy (rows graph) τ ∧
      ∀ σ, IsMouseStrategy (rows graph) σ → ∀ hist, Play (rows graph) σ τ hist →
        EndsInCatWin hist) := by
  sorry

/-- Whenever the function returns 0, for every Mouse strategy there exists a Cat strategy under which the play does not end in a Mouse win, and for every Cat strategy there exists a Mouse strategy under which the play does not end in a Cat win; equivalently, neither player can force a win and the game is a draw under optimal play.
  Preconditions: Same as spec_1. -/
theorem spec_9 (graph : Slice (alloc.vec.Vec Std.I64)) (h : GraphPre (rows graph))
    (r : Std.I64) (hr : Aegis.CatMouseGame.cat_mouse_game graph = ok r) (h0 : r.val = 0) :
    (∀ σ, IsMouseStrategy (rows graph) σ →
        ∃ τ, IsCatStrategy (rows graph) τ ∧
          ∀ hist, Play (rows graph) σ τ hist → ¬ EndsInMouseWin hist) ∧
      (∀ τ, IsCatStrategy (rows graph) τ →
        ∃ σ, IsMouseStrategy (rows graph) σ ∧
          ∀ hist, Play (rows graph) σ τ hist → ¬ EndsInCatWin hist) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (graph : Slice (alloc.vec.Vec Std.I64)) (h : GraphPre (rows graph))
    (r : Std.I64) (hr : Aegis.CatMouseGame.cat_mouse_game graph = ok r) (h0 : r.val = 0), (∀ σ, IsMouseStrategy (rows graph) σ →
        ∃ τ, IsCatStrategy (rows graph) τ ∧
          ∀ hist, Play (rows graph) σ τ hist → ¬ EndsInMouseWin hist) ∧
      (∀ τ, IsCatStrategy (rows graph) τ →
        ∃ σ, IsMouseStrategy (rows graph) σ ∧
          ∀ hist, Play (rows graph) σ τ hist → ¬ EndsInCatWin hist)) := by
  sorry

/-- The two calls cat_mouse_game(graph) and cat_mouse_game(graph') return the same result: if they return r and r' respectively, then r = r'.
  Preconditions: Let graph and graph' both satisfy the preconditions of spec_1 and have the same length n. For every i with 0 <= i < n, graph[i] and graph'[i] contain exactly the same set of values (their entries may be in different orders). -/
theorem spec_10 (graph graph' : Slice (alloc.vec.Vec Std.I64))
    (h : GraphPre (rows graph)) (h' : GraphPre (rows graph'))
    (hlen : (rows graph).length = (rows graph').length)
    (hsame : ∀ (i : Nat) (v : Int), i < (rows graph).length →
      (v ∈ (rows graph).getD i [] ↔ v ∈ (rows graph').getD i []))
    (r r' : Std.I64) (hr : Aegis.CatMouseGame.cat_mouse_game graph = ok r)
    (hr' : Aegis.CatMouseGame.cat_mouse_game graph' = ok r') :
    r = r' := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (graph graph' : Slice (alloc.vec.Vec Std.I64))
    (h : GraphPre (rows graph)) (h' : GraphPre (rows graph'))
    (hlen : (rows graph).length = (rows graph').length)
    (hsame : ∀ (i : Nat) (v : Int), i < (rows graph).length →
      (v ∈ (rows graph).getD i [] ↔ v ∈ (rows graph').getD i []))
    (r r' : Std.I64) (hr : Aegis.CatMouseGame.cat_mouse_game graph = ok r)
    (hr' : Aegis.CatMouseGame.cat_mouse_game graph' = ok r'), r = r') := by
  sorry

/-- If the function returns 1, then node 0 is reachable from node 1 in the undirected graph, i.e. there is a finite sequence of nodes v0,...,vk with v0=1, vk=0, and for each i, v_{i+1} occurs in graph[v_i].
  Preconditions: Same as spec_1. -/
theorem spec_11 (graph : Slice (alloc.vec.Vec Std.I64)) (h : GraphPre (rows graph))
    (r : Std.I64) (hr : Aegis.CatMouseGame.cat_mouse_game graph = ok r) (h1 : r.val = 1) :
    NodePath (rows graph) 1 0 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (graph : Slice (alloc.vec.Vec Std.I64)) (h : GraphPre (rows graph))
    (r : Std.I64) (hr : Aegis.CatMouseGame.cat_mouse_game graph = ok r) (h1 : r.val = 1), NodePath (rows graph) 1 0) := by
  sorry

/-- Whenever cat_mouse_game(graph) returns 0, there exist a Mouse strategy σ and a Cat strategy τ such that: (i) under σ and τ the play from (1,2,Mouse) ends in a draw, i.e. it reaches a nonterminal state equal to an earlier state of the play in both m, c, and t, and never reaches m=0 or m=c; (ii) for every Cat strategy τ', the play under σ and τ' does not end in a Cat win; and (iii) for every Mouse strategy σ', the play under σ' and τ does not end in a Mouse win.
  Preconditions: Same as spec_1. -/
theorem spec_12 (graph : Slice (alloc.vec.Vec Std.I64)) (h : GraphPre (rows graph))
    (r : Std.I64) (hr : Aegis.CatMouseGame.cat_mouse_game graph = ok r) (h0 : r.val = 0) :
    ∃ σ τ, IsMouseStrategy (rows graph) σ ∧ IsCatStrategy (rows graph) τ ∧
      (∃ hist, Play (rows graph) σ τ hist ∧ (∀ s, s ∈ hist → ¬ Terminal s) ∧
        LastRepeats hist) ∧
      (∀ τ', IsCatStrategy (rows graph) τ' → ∀ hist, Play (rows graph) σ τ' hist →
        ¬ EndsInCatWin hist) ∧
      (∀ σ', IsMouseStrategy (rows graph) σ' → ∀ hist, Play (rows graph) σ' τ hist →
        ¬ EndsInMouseWin hist) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (graph : Slice (alloc.vec.Vec Std.I64)) (h : GraphPre (rows graph))
    (r : Std.I64) (hr : Aegis.CatMouseGame.cat_mouse_game graph = ok r) (h0 : r.val = 0), ∃ σ τ, IsMouseStrategy (rows graph) σ ∧ IsCatStrategy (rows graph) τ ∧
      (∃ hist, Play (rows graph) σ τ hist ∧ (∀ s, s ∈ hist → ¬ Terminal s) ∧
        LastRepeats hist) ∧
      (∀ τ', IsCatStrategy (rows graph) τ' → ∀ hist, Play (rows graph) σ τ' hist →
        ¬ EndsInCatWin hist) ∧
      (∀ σ', IsMouseStrategy (rows graph) σ' → ∀ hist, Play (rows graph) σ' τ hist →
        ¬ EndsInMouseWin hist)) := by
  sorry

end AegisSpec.CatMouseGame

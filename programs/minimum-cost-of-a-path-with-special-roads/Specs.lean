import Aegis.MinimumCost.Code.Funs

/-!
# Specifications of `Aegis.MinimumCost.minimum_cost`

LeetCode problem `minimum-cost-of-a-path-with-special-roads`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

open Aegis.MinimumCost

namespace AegisSpec.MinimumCost

structure Point where

  x : Int

  y : Int
  deriving DecidableEq

namespace Point

def manhattan (p q : Point) : Int :=
  |q.x - p.x| + |q.y - p.y|

end Point

structure Road where

  startX : Int

  startY : Int

  endX : Int

  endY : Int

  cost : Int
  deriving DecidableEq

namespace Road

def start (r : Road) : Point := ⟨r.startX, r.startY⟩

def finish (r : Road) : Point := ⟨r.endX, r.endY⟩

def walkDist (r : Road) : Int := |r.endX - r.startX| + |r.endY - r.startY|

def mirror (r : Road) : Road :=
  ⟨r.startY, r.startX, r.endY, r.endX, r.cost⟩

def clampCost (r : Road) : Road :=
  ⟨r.startX, r.startY, r.endX, r.endY, max 1 (min r.cost r.walkDist)⟩

def toVector (r : Road) : List Int := [r.startX, r.startY, r.endX, r.endY, r.cost]

def within (r : Road) (sx sy tx ty : Int) : Prop :=
  sx ≤ r.startX ∧ r.startX ≤ tx ∧ sx ≤ r.endX ∧ r.endX ≤ tx ∧
    sy ≤ r.startY ∧ r.startY ≤ ty ∧ sy ≤ r.endY ∧ r.endY ≤ ty ∧
      1 ≤ r.cost ∧ r.cost ≤ 100000

end Road

def vecData (v : alloc.vec.Vec I64) : List Int := v.val.map (fun x => x.val)

def RoadsMatch (specialRoads : Slice (alloc.vec.Vec I64)) (roads : List Road) : Prop :=
  specialRoads.val.map vecData = roads.map Road.toVector

inductive Action (n : Nat) where

  | walk (q : Point) : Action n

  | road (i : Fin n) : Action n

namespace Action

def apply (roads : List Road) (p : Point) (a : Action roads.length) :
    Option (Point × Int) :=
  match a with
  | .walk q => some (q, Point.manhattan p q)
  | .road i =>
    if p = (roads.get i).start then
      some ((roads.get i).finish, (roads.get i).cost)
    else
      none

end Action

def journeyRun (roads : List Road) (p : Point) :
    List (Action roads.length) → Option (Point × Int)
  | [] => some (p, 0)
  | a :: rest =>
    match Action.apply roads p a with
    | none => none
    | some (p', c) =>
      match journeyRun roads p' rest with
      | none => none
      | some (q, d) => some (q, c + d)

def journeyCosts (roads : List Road) (s t : Point) : Set Int :=
  {v | ∃ J : List (Action roads.length), journeyRun roads s J = some (t, v)}

def vertexSet (s t : Point) (roads : List Road) : Set Point :=
  {p | p = s ∨ p = t ∨ ∃ r ∈ roads, p = r.start ∨ p = r.finish}

inductive pathCost (s t : Point) (roads : List Road) : Point → Point → Int → Prop where

  | refl (u : Point) : pathCost s t roads u u 0

  | walk {u v w : Point} {c : Int} (hu : u ∈ vertexSet s t roads)
      (hv : v ∈ vertexSet s t roads) :
      pathCost s t roads v w c → pathCost s t roads u w (Point.manhattan u v + c)

  | road {w : Point} {c : Int} (i : Fin roads.length) :
      pathCost s t roads (roads.get i).finish w c →
      pathCost s t roads (roads.get i).start w ((roads.get i).cost + c)

/-- Whenever the function returns a result r, r equals the minimum total cost of a journey from (sx,sy) to (tx,ty). A journey is a finite sequence of actions starting at (sx,sy) and ending at (tx,ty), where each action is either (a) an ordinary move to any point q, with cost |q.x - p.x| + |q.y - p.y| from the current point p, or (b) using special road i, allowed only when p=(ax_i,ay_i), with cost c_i and new point (bx_i,by_i). A special road may be used any number of times. The total cost is the sum of the action costs. The minimum is taken over all such journeys.
  Preconditions: Let sx=start[0], sy=start[1], tx=target[0], ty=target[1]. We assume len(start)=2, len(target)=2, 1<=len(specialRoads)<=200, and len(specialRoads[i])=5 for every 0<=i<len(specialRoads). We also assume 1<=sx<=tx<=100000 and 1<=sy<=ty<=100000. For each i, writing (ax_i,ay_i,bx_i,by_i,c_i) = (specialRoads[i][0], specialRoads[i][1], specialRoads[i][2], specialRoads[i][3], specialRoads[i][4]), we assume sx<=ax_i<=tx, sx<=bx_i<=tx, sy<=ay_i<=ty, sy<=by_i<=ty, and 1<=c_i<=100000. -/
theorem spec_1 (start target : Slice I64) (specialRoads : Slice (alloc.vec.Vec I64))
    (roads : List Road) (sx sy tx ty : Int)
    (hstart : start.val.map (fun x => x.val) = [sx, sy])
    (htarget : target.val.map (fun x => x.val) = [tx, ty])
    (hroads : RoadsMatch specialRoads roads)
    (hne : 1 ≤ specialRoads.val.length) (hle : specialRoads.val.length ≤ 200)
    (hfive : ∀ v ∈ specialRoads.val, v.val.length = 5)
    (hx : 1 ≤ sx ∧ sx ≤ tx ∧ tx ≤ 100000)
    (hy : 1 ≤ sy ∧ sy ≤ ty ∧ ty ≤ 100000)
    (hbox : ∀ r ∈ roads, r.within sx sy tx ty)
    (r : I64) (hr : minimum_cost start target specialRoads = ok r) :
    IsLeast (journeyCosts roads ⟨sx, sy⟩ ⟨tx, ty⟩) r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (start target : Slice I64) (specialRoads : Slice (alloc.vec.Vec I64))
    (roads : List Road) (sx sy tx ty : Int)
    (hstart : start.val.map (fun x => x.val) = [sx, sy])
    (htarget : target.val.map (fun x => x.val) = [tx, ty])
    (hroads : RoadsMatch specialRoads roads)
    (hne : 1 ≤ specialRoads.val.length) (hle : specialRoads.val.length ≤ 200)
    (hfive : ∀ v ∈ specialRoads.val, v.val.length = 5)
    (hx : 1 ≤ sx ∧ sx ≤ tx ∧ tx ≤ 100000)
    (hy : 1 ≤ sy ∧ sy ≤ ty ∧ ty ≤ 100000)
    (hbox : ∀ r ∈ roads, r.within sx sy tx ty)
    (r : I64) (hr : minimum_cost start target specialRoads = ok r), IsLeast (journeyCosts roads ⟨sx, sy⟩ ⟨tx, ty⟩) r.val) := by
  sorry

/-- Under the preconditions, the function returns a result r; it does not fail, overflow, panic, or access an out-of-bounds index.
  Preconditions: Let sx=start[0], sy=start[1], tx=target[0], ty=target[1]. We assume len(start)=2, len(target)=2, 1<=len(specialRoads)<=200, and len(specialRoads[i])=5 for every 0<=i<len(specialRoads). We also assume 1<=sx<=tx<=100000 and 1<=sy<=ty<=100000. For each i, writing (ax_i,ay_i,bx_i,by_i,c_i) = (specialRoads[i][0], specialRoads[i][1], specialRoads[i][2], specialRoads[i][3], specialRoads[i][4]), we assume sx<=ax_i<=tx, sx<=bx_i<=tx, sy<=ay_i<=ty, sy<=by_i<=ty, and 1<=c_i<=100000. -/
theorem spec_2 (start target : Slice I64) (specialRoads : Slice (alloc.vec.Vec I64))
    (roads : List Road) (sx sy tx ty : Int)
    (hstart : start.val.map (fun x => x.val) = [sx, sy])
    (htarget : target.val.map (fun x => x.val) = [tx, ty])
    (hroads : RoadsMatch specialRoads roads)
    (hne : 1 ≤ specialRoads.val.length) (hle : specialRoads.val.length ≤ 200)
    (hfive : ∀ v ∈ specialRoads.val, v.val.length = 5)
    (hx : 1 ≤ sx ∧ sx ≤ tx ∧ tx ≤ 100000)
    (hy : 1 ≤ sy ∧ sy ≤ ty ∧ ty ≤ 100000)
    (hbox : ∀ r ∈ roads, r.within sx sy tx ty) :
    ∃ r : I64, minimum_cost start target specialRoads = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (start target : Slice I64) (specialRoads : Slice (alloc.vec.Vec I64))
    (roads : List Road) (sx sy tx ty : Int)
    (hstart : start.val.map (fun x => x.val) = [sx, sy])
    (htarget : target.val.map (fun x => x.val) = [tx, ty])
    (hroads : RoadsMatch specialRoads roads)
    (hne : 1 ≤ specialRoads.val.length) (hle : specialRoads.val.length ≤ 200)
    (hfive : ∀ v ∈ specialRoads.val, v.val.length = 5)
    (hx : 1 ≤ sx ∧ sx ≤ tx ∧ tx ≤ 100000)
    (hy : 1 ≤ sy ∧ sy ≤ ty ∧ ty ≤ 100000)
    (hbox : ∀ r ∈ roads, r.within sx sy tx ty), ∃ r : I64, minimum_cost start target specialRoads = ok r) := by
  sorry

/-- Let D = |tx - sx| + |ty - sy|. Whenever the function returns a result r, r <= D.
  Preconditions: Let sx=start[0], sy=start[1], tx=target[0], ty=target[1]. We assume len(start)=2, len(target)=2, 1<=len(specialRoads)<=200, and len(specialRoads[i])=5 for every 0<=i<len(specialRoads). We also assume 1<=sx<=tx<=100000 and 1<=sy<=ty<=100000. For each i, writing (ax_i,ay_i,bx_i,by_i,c_i) = (specialRoads[i][0], specialRoads[i][1], specialRoads[i][2], specialRoads[i][3], specialRoads[i][4]), we assume sx<=ax_i<=tx, sx<=bx_i<=tx, sy<=ay_i<=ty, sy<=by_i<=ty, and 1<=c_i<=100000. -/
theorem spec_3 (start target : Slice I64) (specialRoads : Slice (alloc.vec.Vec I64))
    (roads : List Road) (sx sy tx ty : Int)
    (hstart : start.val.map (fun x => x.val) = [sx, sy])
    (htarget : target.val.map (fun x => x.val) = [tx, ty])
    (hroads : RoadsMatch specialRoads roads)
    (hne : 1 ≤ specialRoads.val.length) (hle : specialRoads.val.length ≤ 200)
    (hfive : ∀ v ∈ specialRoads.val, v.val.length = 5)
    (hx : 1 ≤ sx ∧ sx ≤ tx ∧ tx ≤ 100000)
    (hy : 1 ≤ sy ∧ sy ≤ ty ∧ ty ≤ 100000)
    (hbox : ∀ r ∈ roads, r.within sx sy tx ty)
    (r : I64) (hr : minimum_cost start target specialRoads = ok r) :
    r.val ≤ Point.manhattan ⟨sx, sy⟩ ⟨tx, ty⟩ := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (start target : Slice I64) (specialRoads : Slice (alloc.vec.Vec I64))
    (roads : List Road) (sx sy tx ty : Int)
    (hstart : start.val.map (fun x => x.val) = [sx, sy])
    (htarget : target.val.map (fun x => x.val) = [tx, ty])
    (hroads : RoadsMatch specialRoads roads)
    (hne : 1 ≤ specialRoads.val.length) (hle : specialRoads.val.length ≤ 200)
    (hfive : ∀ v ∈ specialRoads.val, v.val.length = 5)
    (hx : 1 ≤ sx ∧ sx ≤ tx ∧ tx ≤ 100000)
    (hy : 1 ≤ sy ∧ sy ≤ ty ∧ ty ≤ 100000)
    (hbox : ∀ r ∈ roads, r.within sx sy tx ty)
    (r : I64) (hr : minimum_cost start target specialRoads = ok r), r.val ≤ Point.manhattan ⟨sx, sy⟩ ⟨tx, ty⟩) := by
  sorry

/-- Let D = |tx - sx| + |ty - sy| and Cmin = min { c_i | 0 <= i < len(specialRoads) }. Whenever the function returns a result r, r >= min(D, Cmin).
  Preconditions: Let sx=start[0], sy=start[1], tx=target[0], ty=target[1]. We assume len(start)=2, len(target)=2, 1<=len(specialRoads)<=200, and len(specialRoads[i])=5 for every 0<=i<len(specialRoads). We also assume 1<=sx<=tx<=100000 and 1<=sy<=ty<=100000. For each i, writing (ax_i,ay_i,bx_i,by_i,c_i) = (specialRoads[i][0], specialRoads[i][1], specialRoads[i][2], specialRoads[i][3], specialRoads[i][4]), we assume sx<=ax_i<=tx, sx<=bx_i<=tx, sy<=ay_i<=ty, sy<=by_i<=ty, and 1<=c_i<=100000. -/
theorem spec_4 (start target : Slice I64) (specialRoads : Slice (alloc.vec.Vec I64))
    (roads : List Road) (sx sy tx ty : Int)
    (hstart : start.val.map (fun x => x.val) = [sx, sy])
    (htarget : target.val.map (fun x => x.val) = [tx, ty])
    (hroads : RoadsMatch specialRoads roads)
    (hne : 1 ≤ specialRoads.val.length) (hle : specialRoads.val.length ≤ 200)
    (hfive : ∀ v ∈ specialRoads.val, v.val.length = 5)
    (hx : 1 ≤ sx ∧ sx ≤ tx ∧ tx ≤ 100000)
    (hy : 1 ≤ sy ∧ sy ≤ ty ∧ ty ≤ 100000)
    (hbox : ∀ r ∈ roads, r.within sx sy tx ty)
    (Cmin : Int) (hCmin : IsLeast {c : Int | ∃ r ∈ roads, r.cost = c} Cmin)
    (r : I64) (hr : minimum_cost start target specialRoads = ok r) :
    min (Point.manhattan ⟨sx, sy⟩ ⟨tx, ty⟩) Cmin ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (start target : Slice I64) (specialRoads : Slice (alloc.vec.Vec I64))
    (roads : List Road) (sx sy tx ty : Int)
    (hstart : start.val.map (fun x => x.val) = [sx, sy])
    (htarget : target.val.map (fun x => x.val) = [tx, ty])
    (hroads : RoadsMatch specialRoads roads)
    (hne : 1 ≤ specialRoads.val.length) (hle : specialRoads.val.length ≤ 200)
    (hfive : ∀ v ∈ specialRoads.val, v.val.length = 5)
    (hx : 1 ≤ sx ∧ sx ≤ tx ∧ tx ≤ 100000)
    (hy : 1 ≤ sy ∧ sy ≤ ty ∧ ty ≤ 100000)
    (hbox : ∀ r ∈ roads, r.within sx sy tx ty)
    (Cmin : Int) (hCmin : IsLeast {c : Int | ∃ r ∈ roads, r.cost = c} Cmin)
    (r : I64) (hr : minimum_cost start target specialRoads = ok r), min (Point.manhattan ⟨sx, sy⟩ ⟨tx, ty⟩) Cmin ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, every finite journey J from (sx,sy) to (tx,ty) has total cost at least r. A journey is a finite sequence of ordinary moves (each from the current point p to any point q, costing |q.x-p.x|+|q.y-p.y|) and uses of the special directed roads (road i may be used only when the current point is (ax_i,ay_i), costs c_i, and moves the current point to (bx_i,by_i); each road may be used any number of times), beginning at (sx,sy) and ending at (tx,ty).
  Preconditions: Let sx=start[0], sy=start[1], tx=target[0], ty=target[1]. We assume len(start)=2, len(target)=2, 1<=len(specialRoads)<=200, and len(specialRoads[i])=5 for every 0<=i<len(specialRoads). We also assume 1<=sx<=tx<=100000 and 1<=sy<=ty<=100000. For each i, writing (ax_i,ay_i,bx_i,by_i,c_i) = (specialRoads[i][0], specialRoads[i][1], specialRoads[i][2], specialRoads[i][3], specialRoads[i][4]), we assume sx<=ax_i<=tx, sx<=bx_i<=tx, sy<=ay_i<=ty, sy<=by_i<=ty, and 1<=c_i<=100000. -/
theorem spec_5 (start target : Slice I64) (specialRoads : Slice (alloc.vec.Vec I64))
    (roads : List Road) (sx sy tx ty : Int)
    (hstart : start.val.map (fun x => x.val) = [sx, sy])
    (htarget : target.val.map (fun x => x.val) = [tx, ty])
    (hroads : RoadsMatch specialRoads roads)
    (hne : 1 ≤ specialRoads.val.length) (hle : specialRoads.val.length ≤ 200)
    (hfive : ∀ v ∈ specialRoads.val, v.val.length = 5)
    (hx : 1 ≤ sx ∧ sx ≤ tx ∧ tx ≤ 100000)
    (hy : 1 ≤ sy ∧ sy ≤ ty ∧ ty ≤ 100000)
    (hbox : ∀ r ∈ roads, r.within sx sy tx ty)
    (r : I64) (hr : minimum_cost start target specialRoads = ok r) :
    ∀ v ∈ journeyCosts roads ⟨sx, sy⟩ ⟨tx, ty⟩, r.val ≤ v := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (start target : Slice I64) (specialRoads : Slice (alloc.vec.Vec I64))
    (roads : List Road) (sx sy tx ty : Int)
    (hstart : start.val.map (fun x => x.val) = [sx, sy])
    (htarget : target.val.map (fun x => x.val) = [tx, ty])
    (hroads : RoadsMatch specialRoads roads)
    (hne : 1 ≤ specialRoads.val.length) (hle : specialRoads.val.length ≤ 200)
    (hfive : ∀ v ∈ specialRoads.val, v.val.length = 5)
    (hx : 1 ≤ sx ∧ sx ≤ tx ∧ tx ≤ 100000)
    (hy : 1 ≤ sy ∧ sy ≤ ty ∧ ty ≤ 100000)
    (hbox : ∀ r ∈ roads, r.within sx sy tx ty)
    (r : I64) (hr : minimum_cost start target specialRoads = ok r), ∀ v ∈ journeyCosts roads ⟨sx, sy⟩ ⟨tx, ty⟩, r.val ≤ v) := by
  sorry

/-- Whenever the function returns a result r, there exists a finite journey J from (sx,sy) to (tx,ty), using ordinary moves and the given directed special roads (each allowed only from its start point to its end point at its listed cost, and usable any number of times), whose total cost is exactly r.
  Preconditions: Let sx=start[0], sy=start[1], tx=target[0], ty=target[1]. We assume len(start)=2, len(target)=2, 1<=len(specialRoads)<=200, and len(specialRoads[i])=5 for every 0<=i<len(specialRoads). We also assume 1<=sx<=tx<=100000 and 1<=sy<=ty<=100000. For each i, writing (ax_i,ay_i,bx_i,by_i,c_i) = (specialRoads[i][0], specialRoads[i][1], specialRoads[i][2], specialRoads[i][3], specialRoads[i][4]), we assume sx<=ax_i<=tx, sx<=bx_i<=tx, sy<=ay_i<=ty, sy<=by_i<=ty, and 1<=c_i<=100000. -/
theorem spec_6 (start target : Slice I64) (specialRoads : Slice (alloc.vec.Vec I64))
    (roads : List Road) (sx sy tx ty : Int)
    (hstart : start.val.map (fun x => x.val) = [sx, sy])
    (htarget : target.val.map (fun x => x.val) = [tx, ty])
    (hroads : RoadsMatch specialRoads roads)
    (hne : 1 ≤ specialRoads.val.length) (hle : specialRoads.val.length ≤ 200)
    (hfive : ∀ v ∈ specialRoads.val, v.val.length = 5)
    (hx : 1 ≤ sx ∧ sx ≤ tx ∧ tx ≤ 100000)
    (hy : 1 ≤ sy ∧ sy ≤ ty ∧ ty ≤ 100000)
    (hbox : ∀ r ∈ roads, r.within sx sy tx ty)
    (r : I64) (hr : minimum_cost start target specialRoads = ok r) :
    r.val ∈ journeyCosts roads ⟨sx, sy⟩ ⟨tx, ty⟩ := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (start target : Slice I64) (specialRoads : Slice (alloc.vec.Vec I64))
    (roads : List Road) (sx sy tx ty : Int)
    (hstart : start.val.map (fun x => x.val) = [sx, sy])
    (htarget : target.val.map (fun x => x.val) = [tx, ty])
    (hroads : RoadsMatch specialRoads roads)
    (hne : 1 ≤ specialRoads.val.length) (hle : specialRoads.val.length ≤ 200)
    (hfive : ∀ v ∈ specialRoads.val, v.val.length = 5)
    (hx : 1 ≤ sx ∧ sx ≤ tx ∧ tx ≤ 100000)
    (hy : 1 ≤ sy ∧ sy ≤ ty ∧ ty ≤ 100000)
    (hbox : ∀ r ∈ roads, r.within sx sy tx ty)
    (r : I64) (hr : minimum_cost start target specialRoads = ok r), r.val ∈ journeyCosts roads ⟨sx, sy⟩ ⟨tx, ty⟩) := by
  sorry

/-- Let D = |tx - sx| + |ty - sy|. Whenever the function returns a result r, r = D.
  Preconditions: Let sx=start[0], sy=start[1], tx=target[0], ty=target[1]. We assume len(start)=2, len(target)=2, 1<=len(specialRoads)<=200, and len(specialRoads[i])=5 for every 0<=i<len(specialRoads). We also assume 1<=sx<=tx<=100000 and 1<=sy<=ty<=100000. For each i, writing (ax_i,ay_i,bx_i,by_i,c_i) = (specialRoads[i][0], specialRoads[i][1], specialRoads[i][2], specialRoads[i][3], specialRoads[i][4]), we assume sx<=ax_i<=tx, sx<=bx_i<=tx, sy<=ay_i<=ty, sy<=by_i<=ty, and 1<=c_i<=100000. Additionally, for every i with 0 <= i < len(specialRoads), c_i >= |bx_i - ax_i| + |by_i - ay_i|. -/
theorem spec_7 (start target : Slice I64) (specialRoads : Slice (alloc.vec.Vec I64))
    (roads : List Road) (sx sy tx ty : Int)
    (hstart : start.val.map (fun x => x.val) = [sx, sy])
    (htarget : target.val.map (fun x => x.val) = [tx, ty])
    (hroads : RoadsMatch specialRoads roads)
    (hne : 1 ≤ specialRoads.val.length) (hle : specialRoads.val.length ≤ 200)
    (hfive : ∀ v ∈ specialRoads.val, v.val.length = 5)
    (hx : 1 ≤ sx ∧ sx ≤ tx ∧ tx ≤ 100000)
    (hy : 1 ≤ sy ∧ sy ≤ ty ∧ ty ≤ 100000)
    (hbox : ∀ r ∈ roads, r.within sx sy tx ty)
    (hcheap : ∀ r ∈ roads, r.walkDist ≤ r.cost)
    (r : I64) (hr : minimum_cost start target specialRoads = ok r) :
    r.val = Point.manhattan ⟨sx, sy⟩ ⟨tx, ty⟩ := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (start target : Slice I64) (specialRoads : Slice (alloc.vec.Vec I64))
    (roads : List Road) (sx sy tx ty : Int)
    (hstart : start.val.map (fun x => x.val) = [sx, sy])
    (htarget : target.val.map (fun x => x.val) = [tx, ty])
    (hroads : RoadsMatch specialRoads roads)
    (hne : 1 ≤ specialRoads.val.length) (hle : specialRoads.val.length ≤ 200)
    (hfive : ∀ v ∈ specialRoads.val, v.val.length = 5)
    (hx : 1 ≤ sx ∧ sx ≤ tx ∧ tx ≤ 100000)
    (hy : 1 ≤ sy ∧ sy ≤ ty ∧ ty ≤ 100000)
    (hbox : ∀ r ∈ roads, r.within sx sy tx ty)
    (hcheap : ∀ r ∈ roads, r.walkDist ≤ r.cost)
    (r : I64) (hr : minimum_cost start target specialRoads = ok r), r.val = Point.manhattan ⟨sx, sy⟩ ⟨tx, ty⟩) := by
  sorry

/-- For every permutation pi of {0,...,len(specialRoads)-1}, let specialRoads' be the array of length len(specialRoads) with specialRoads'[j] = specialRoads[pi(j)] for every j. Whenever the function returns a result r for (start,target,specialRoads) and a result r' for (start,target,specialRoads'), it holds that r = r'.
  Preconditions: Let sx=start[0], sy=start[1], tx=target[0], ty=target[1]. We assume len(start)=2, len(target)=2, 1<=len(specialRoads)<=200, and len(specialRoads[i])=5 for every 0<=i<len(specialRoads). We also assume 1<=sx<=tx<=100000 and 1<=sy<=ty<=100000. For each i, writing (ax_i,ay_i,bx_i,by_i,c_i) = (specialRoads[i][0], specialRoads[i][1], specialRoads[i][2], specialRoads[i][3], specialRoads[i][4]), we assume sx<=ax_i<=tx, sx<=bx_i<=tx, sy<=ay_i<=ty, sy<=by_i<=ty, and 1<=c_i<=100000. -/
theorem spec_8 (start target : Slice I64) (specialRoads : Slice (alloc.vec.Vec I64))
    (roads : List Road) (sx sy tx ty : Int)
    (hstart : start.val.map (fun x => x.val) = [sx, sy])
    (htarget : target.val.map (fun x => x.val) = [tx, ty])
    (hroads : RoadsMatch specialRoads roads)
    (hne : 1 ≤ specialRoads.val.length) (hle : specialRoads.val.length ≤ 200)
    (hfive : ∀ v ∈ specialRoads.val, v.val.length = 5)
    (hx : 1 ≤ sx ∧ sx ≤ tx ∧ tx ≤ 100000)
    (hy : 1 ≤ sy ∧ sy ≤ ty ∧ ty ≤ 100000)
    (hbox : ∀ r ∈ roads, r.within sx sy tx ty)
    (specialRoads' : Slice (alloc.vec.Vec I64)) (roads' : List Road)
    (hroads' : RoadsMatch specialRoads' roads') (hperm : roads.Perm roads')
    (r r' : I64) (hr : minimum_cost start target specialRoads = ok r)
    (hr' : minimum_cost start target specialRoads' = ok r') :
    r = r' := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (start target : Slice I64) (specialRoads : Slice (alloc.vec.Vec I64))
    (roads : List Road) (sx sy tx ty : Int)
    (hstart : start.val.map (fun x => x.val) = [sx, sy])
    (htarget : target.val.map (fun x => x.val) = [tx, ty])
    (hroads : RoadsMatch specialRoads roads)
    (hne : 1 ≤ specialRoads.val.length) (hle : specialRoads.val.length ≤ 200)
    (hfive : ∀ v ∈ specialRoads.val, v.val.length = 5)
    (hx : 1 ≤ sx ∧ sx ≤ tx ∧ tx ≤ 100000)
    (hy : 1 ≤ sy ∧ sy ≤ ty ∧ ty ≤ 100000)
    (hbox : ∀ r ∈ roads, r.within sx sy tx ty)
    (specialRoads' : Slice (alloc.vec.Vec I64)) (roads' : List Road)
    (hroads' : RoadsMatch specialRoads' roads') (hperm : roads.Perm roads')
    (r r' : I64) (hr : minimum_cost start target specialRoads = ok r)
    (hr' : minimum_cost start target specialRoads' = ok r'), r = r') := by
  sorry

/-- For every index k with 0 <= k < len(specialRoads) and c_k >= |bx_k - ax_k| + |by_k - ay_k|, let specialRoads' be the array obtained from specialRoads by deleting index k, keeping the remaining entries in their original relative order. Whenever the function returns a result r for (start,target,specialRoads) and a result r' for (start,target,specialRoads'), it holds that r = r'.
  Preconditions: Let sx=start[0], sy=start[1], tx=target[0], ty=target[1]. We assume len(start)=2, len(target)=2, 1<=len(specialRoads)<=200, and len(specialRoads[i])=5 for every 0<=i<len(specialRoads). We also assume 1<=sx<=tx<=100000 and 1<=sy<=ty<=100000. For each i, writing (ax_i,ay_i,bx_i,by_i,c_i) = (specialRoads[i][0], specialRoads[i][1], specialRoads[i][2], specialRoads[i][3], specialRoads[i][4]), we assume sx<=ax_i<=tx, sx<=bx_i<=tx, sy<=ay_i<=ty, sy<=by_i<=ty, and 1<=c_i<=100000. Additionally len(specialRoads) >= 2. -/
theorem spec_9 (start target : Slice I64) (specialRoads : Slice (alloc.vec.Vec I64))
    (roads : List Road) (sx sy tx ty : Int)
    (hstart : start.val.map (fun x => x.val) = [sx, sy])
    (htarget : target.val.map (fun x => x.val) = [tx, ty])
    (hroads : RoadsMatch specialRoads roads)
    (hne : 1 ≤ specialRoads.val.length) (hle : specialRoads.val.length ≤ 200)
    (hfive : ∀ v ∈ specialRoads.val, v.val.length = 5)
    (hx : 1 ≤ sx ∧ sx ≤ tx ∧ tx ≤ 100000)
    (hy : 1 ≤ sy ∧ sy ≤ ty ∧ ty ≤ 100000)
    (hbox : ∀ r ∈ roads, r.within sx sy tx ty)
    (hne2 : 2 ≤ specialRoads.val.length)
    (k : Nat) (hk : k < roads.length) (rk : Road) (hrk : roads[k]? = some rk)
    (hcheap : rk.walkDist ≤ rk.cost)
    (specialRoads' : Slice (alloc.vec.Vec I64)) (roads' : List Road)
    (hroads' : RoadsMatch specialRoads' roads') (hdel : roads' = roads.eraseIdx k)
    (r r' : I64) (hr : minimum_cost start target specialRoads = ok r)
    (hr' : minimum_cost start target specialRoads' = ok r') :
    r = r' := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (start target : Slice I64) (specialRoads : Slice (alloc.vec.Vec I64))
    (roads : List Road) (sx sy tx ty : Int)
    (hstart : start.val.map (fun x => x.val) = [sx, sy])
    (htarget : target.val.map (fun x => x.val) = [tx, ty])
    (hroads : RoadsMatch specialRoads roads)
    (hne : 1 ≤ specialRoads.val.length) (hle : specialRoads.val.length ≤ 200)
    (hfive : ∀ v ∈ specialRoads.val, v.val.length = 5)
    (hx : 1 ≤ sx ∧ sx ≤ tx ∧ tx ≤ 100000)
    (hy : 1 ≤ sy ∧ sy ≤ ty ∧ ty ≤ 100000)
    (hbox : ∀ r ∈ roads, r.within sx sy tx ty)
    (hne2 : 2 ≤ specialRoads.val.length)
    (k : Nat) (hk : k < roads.length) (rk : Road) (hrk : roads[k]? = some rk)
    (hcheap : rk.walkDist ≤ rk.cost)
    (specialRoads' : Slice (alloc.vec.Vec I64)) (roads' : List Road)
    (hroads' : RoadsMatch specialRoads' roads') (hdel : roads' = roads.eraseIdx k)
    (r r' : I64) (hr : minimum_cost start target specialRoads = ok r)
    (hr' : minimum_cost start target specialRoads' = ok r'), r = r') := by
  sorry

/-- For each i, let d_i = |bx_i - ax_i| + |by_i - ay_i| and c'_i = max(1, min(c_i, d_i)). Let specialRoads' be the array with the same coordinates as specialRoads and costs c'_i. Whenever the function returns a result r for (start,target,specialRoads) and a result r' for (start,target,specialRoads'), it holds that r = r'.
  Preconditions: Let sx=start[0], sy=start[1], tx=target[0], ty=target[1]. We assume len(start)=2, len(target)=2, 1<=len(specialRoads)<=200, and len(specialRoads[i])=5 for every 0<=i<len(specialRoads). We also assume 1<=sx<=tx<=100000 and 1<=sy<=ty<=100000. For each i, writing (ax_i,ay_i,bx_i,by_i,c_i) = (specialRoads[i][0], specialRoads[i][1], specialRoads[i][2], specialRoads[i][3], specialRoads[i][4]), we assume sx<=ax_i<=tx, sx<=bx_i<=tx, sy<=ay_i<=ty, sy<=by_i<=ty, and 1<=c_i<=100000. -/
theorem spec_10 (start target : Slice I64) (specialRoads : Slice (alloc.vec.Vec I64))
    (roads : List Road) (sx sy tx ty : Int)
    (hstart : start.val.map (fun x => x.val) = [sx, sy])
    (htarget : target.val.map (fun x => x.val) = [tx, ty])
    (hroads : RoadsMatch specialRoads roads)
    (hne : 1 ≤ specialRoads.val.length) (hle : specialRoads.val.length ≤ 200)
    (hfive : ∀ v ∈ specialRoads.val, v.val.length = 5)
    (hx : 1 ≤ sx ∧ sx ≤ tx ∧ tx ≤ 100000)
    (hy : 1 ≤ sy ∧ sy ≤ ty ∧ ty ≤ 100000)
    (hbox : ∀ r ∈ roads, r.within sx sy tx ty)
    (specialRoads' : Slice (alloc.vec.Vec I64)) (roads' : List Road)
    (hroads' : RoadsMatch specialRoads' roads')
    (hclamp : roads' = roads.map Road.clampCost)
    (r r' : I64) (hr : minimum_cost start target specialRoads = ok r)
    (hr' : minimum_cost start target specialRoads' = ok r') :
    r = r' := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (start target : Slice I64) (specialRoads : Slice (alloc.vec.Vec I64))
    (roads : List Road) (sx sy tx ty : Int)
    (hstart : start.val.map (fun x => x.val) = [sx, sy])
    (htarget : target.val.map (fun x => x.val) = [tx, ty])
    (hroads : RoadsMatch specialRoads roads)
    (hne : 1 ≤ specialRoads.val.length) (hle : specialRoads.val.length ≤ 200)
    (hfive : ∀ v ∈ specialRoads.val, v.val.length = 5)
    (hx : 1 ≤ sx ∧ sx ≤ tx ∧ tx ≤ 100000)
    (hy : 1 ≤ sy ∧ sy ≤ ty ∧ ty ≤ 100000)
    (hbox : ∀ r ∈ roads, r.within sx sy tx ty)
    (specialRoads' : Slice (alloc.vec.Vec I64)) (roads' : List Road)
    (hroads' : RoadsMatch specialRoads' roads')
    (hclamp : roads' = roads.map Road.clampCost)
    (r r' : I64) (hr : minimum_cost start target specialRoads = ok r)
    (hr' : minimum_cost start target specialRoads' = ok r'), r = r') := by
  sorry

/-- Whenever the function returns a result r for (start,target,specialRoads) and a result r' for (start,target,specialRoads'), it holds that r' <= r.
  Preconditions: Let sx=start[0], sy=start[1], tx=target[0], ty=target[1]. We assume len(start)=2, len(target)=2, 1<=len(specialRoads)<=200, and len(specialRoads[i])=5 for every 0<=i<len(specialRoads). We also assume 1<=sx<=tx<=100000 and 1<=sy<=ty<=100000. For each i, writing (ax_i,ay_i,bx_i,by_i,c_i) = (specialRoads[i][0], specialRoads[i][1], specialRoads[i][2], specialRoads[i][3], specialRoads[i][4]), we assume sx<=ax_i<=tx, sx<=bx_i<=tx, sy<=ay_i<=ty, sy<=by_i<=ty, and 1<=c_i<=100000. Let specialRoads' be any array with the same coordinates as specialRoads and with costs c'_i satisfying 1 <= c'_i <= c_i for every i. -/
theorem spec_11 (start target : Slice I64) (specialRoads : Slice (alloc.vec.Vec I64))
    (roads : List Road) (sx sy tx ty : Int)
    (hstart : start.val.map (fun x => x.val) = [sx, sy])
    (htarget : target.val.map (fun x => x.val) = [tx, ty])
    (hroads : RoadsMatch specialRoads roads)
    (hne : 1 ≤ specialRoads.val.length) (hle : specialRoads.val.length ≤ 200)
    (hfive : ∀ v ∈ specialRoads.val, v.val.length = 5)
    (hx : 1 ≤ sx ∧ sx ≤ tx ∧ tx ≤ 100000)
    (hy : 1 ≤ sy ∧ sy ≤ ty ∧ ty ≤ 100000)
    (hbox : ∀ r ∈ roads, r.within sx sy tx ty)
    (specialRoads' : Slice (alloc.vec.Vec I64)) (roads' : List Road)
    (hroads' : RoadsMatch specialRoads' roads')
    (hrel : List.Forall₂ (fun r r' =>
        r'.startX = r.startX ∧ r'.startY = r.startY ∧
          r'.endX = r.endX ∧ r'.endY = r.endY ∧
            1 ≤ r'.cost ∧ r'.cost ≤ r.cost) roads roads')
    (r r' : I64) (hr : minimum_cost start target specialRoads = ok r)
    (hr' : minimum_cost start target specialRoads' = ok r') :
    r' ≤ r := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (start target : Slice I64) (specialRoads : Slice (alloc.vec.Vec I64))
    (roads : List Road) (sx sy tx ty : Int)
    (hstart : start.val.map (fun x => x.val) = [sx, sy])
    (htarget : target.val.map (fun x => x.val) = [tx, ty])
    (hroads : RoadsMatch specialRoads roads)
    (hne : 1 ≤ specialRoads.val.length) (hle : specialRoads.val.length ≤ 200)
    (hfive : ∀ v ∈ specialRoads.val, v.val.length = 5)
    (hx : 1 ≤ sx ∧ sx ≤ tx ∧ tx ≤ 100000)
    (hy : 1 ≤ sy ∧ sy ≤ ty ∧ ty ≤ 100000)
    (hbox : ∀ r ∈ roads, r.within sx sy tx ty)
    (specialRoads' : Slice (alloc.vec.Vec I64)) (roads' : List Road)
    (hroads' : RoadsMatch specialRoads' roads')
    (hrel : List.Forall₂ (fun r r' =>
        r'.startX = r.startX ∧ r'.startY = r.startY ∧
          r'.endX = r.endX ∧ r'.endY = r.endY ∧
            1 ≤ r'.cost ∧ r'.cost ≤ r.cost) roads roads')
    (r r' : I64) (hr : minimum_cost start target specialRoads = ok r)
    (hr' : minimum_cost start target specialRoads' = ok r'), r' ≤ r) := by
  sorry

/-- Let start' = [sy, sx], target' = [ty, tx], and for each i let specialRoads'[i] = [ay_i, ax_i, by_i, bx_i, c_i]. Whenever the function returns a result r for (start,target,specialRoads) and a result r' for (start',target',specialRoads'), it holds that r = r'.
  Preconditions: Let sx=start[0], sy=start[1], tx=target[0], ty=target[1]. We assume len(start)=2, len(target)=2, 1<=len(specialRoads)<=200, and len(specialRoads[i])=5 for every 0<=i<len(specialRoads). We also assume 1<=sx<=tx<=100000 and 1<=sy<=ty<=100000. For each i, writing (ax_i,ay_i,bx_i,by_i,c_i) = (specialRoads[i][0], specialRoads[i][1], specialRoads[i][2], specialRoads[i][3], specialRoads[i][4]), we assume sx<=ax_i<=tx, sx<=bx_i<=tx, sy<=ay_i<=ty, sy<=by_i<=ty, and 1<=c_i<=100000. -/
theorem spec_12 (start target : Slice I64) (specialRoads : Slice (alloc.vec.Vec I64))
    (roads : List Road) (sx sy tx ty : Int)
    (hstart : start.val.map (fun x => x.val) = [sx, sy])
    (htarget : target.val.map (fun x => x.val) = [tx, ty])
    (hroads : RoadsMatch specialRoads roads)
    (hne : 1 ≤ specialRoads.val.length) (hle : specialRoads.val.length ≤ 200)
    (hfive : ∀ v ∈ specialRoads.val, v.val.length = 5)
    (hx : 1 ≤ sx ∧ sx ≤ tx ∧ tx ≤ 100000)
    (hy : 1 ≤ sy ∧ sy ≤ ty ∧ ty ≤ 100000)
    (hbox : ∀ r ∈ roads, r.within sx sy tx ty)
    (start' target' : Slice I64) (specialRoads' : Slice (alloc.vec.Vec I64))
    (roads' : List Road)
    (hstart' : start'.val.map (fun x => x.val) = [sy, sx])
    (htarget' : target'.val.map (fun x => x.val) = [ty, tx])
    (hroads' : RoadsMatch specialRoads' roads')
    (hmirror : roads' = roads.map Road.mirror)
    (r r' : I64) (hr : minimum_cost start target specialRoads = ok r)
    (hr' : minimum_cost start' target' specialRoads' = ok r') :
    r = r' := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (start target : Slice I64) (specialRoads : Slice (alloc.vec.Vec I64))
    (roads : List Road) (sx sy tx ty : Int)
    (hstart : start.val.map (fun x => x.val) = [sx, sy])
    (htarget : target.val.map (fun x => x.val) = [tx, ty])
    (hroads : RoadsMatch specialRoads roads)
    (hne : 1 ≤ specialRoads.val.length) (hle : specialRoads.val.length ≤ 200)
    (hfive : ∀ v ∈ specialRoads.val, v.val.length = 5)
    (hx : 1 ≤ sx ∧ sx ≤ tx ∧ tx ≤ 100000)
    (hy : 1 ≤ sy ∧ sy ≤ ty ∧ ty ≤ 100000)
    (hbox : ∀ r ∈ roads, r.within sx sy tx ty)
    (start' target' : Slice I64) (specialRoads' : Slice (alloc.vec.Vec I64))
    (roads' : List Road)
    (hstart' : start'.val.map (fun x => x.val) = [sy, sx])
    (htarget' : target'.val.map (fun x => x.val) = [ty, tx])
    (hroads' : RoadsMatch specialRoads' roads')
    (hmirror : roads' = roads.map Road.mirror)
    (r r' : I64) (hr : minimum_cost start target specialRoads = ok r)
    (hr' : minimum_cost start' target' specialRoads' = ok r'), r = r') := by
  sorry

/-- Let V be the finite set containing (sx,sy), (tx,ty), and for each i the points (ax_i,ay_i) and (bx_i,by_i). Consider the directed graph on V with an ordinary edge u->v of cost |u.x-v.x|+|u.y-v.y| for every ordered pair u,v in V, and with an additional edge (ax_i,ay_i)->(bx_i,by_i) of cost c_i for each i. Whenever the function returns a result r, r equals the minimum cost of a directed path in this graph from (sx,sy) to (tx,ty).
  Preconditions: Let sx=start[0], sy=start[1], tx=target[0], ty=target[1]. Assume len(start)=2, len(target)=2, 1<=len(specialRoads)<=200, len(specialRoads[i])=5 for every i, 1<=sx<=tx<=100000, 1<=sy<=ty<=100000, and for each i with (ax_i,ay_i,bx_i,by_i,c_i)=specialRoads[i], sx<=ax_i<=tx, sx<=bx_i<=tx, sy<=ay_i<=ty, sy<=by_i<=ty, 1<=c_i<=100000. -/
theorem spec_13 (start target : Slice I64) (specialRoads : Slice (alloc.vec.Vec I64))
    (roads : List Road) (sx sy tx ty : Int)
    (hstart : start.val.map (fun x => x.val) = [sx, sy])
    (htarget : target.val.map (fun x => x.val) = [tx, ty])
    (hroads : RoadsMatch specialRoads roads)
    (hne : 1 ≤ specialRoads.val.length) (hle : specialRoads.val.length ≤ 200)
    (hfive : ∀ v ∈ specialRoads.val, v.val.length = 5)
    (hx : 1 ≤ sx ∧ sx ≤ tx ∧ tx ≤ 100000)
    (hy : 1 ≤ sy ∧ sy ≤ ty ∧ ty ≤ 100000)
    (hbox : ∀ r ∈ roads, r.within sx sy tx ty)
    (r : I64) (hr : minimum_cost start target specialRoads = ok r) :
    IsLeast {c : Int | pathCost ⟨sx, sy⟩ ⟨tx, ty⟩ roads ⟨sx, sy⟩ ⟨tx, ty⟩ c} r.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (start target : Slice I64) (specialRoads : Slice (alloc.vec.Vec I64))
    (roads : List Road) (sx sy tx ty : Int)
    (hstart : start.val.map (fun x => x.val) = [sx, sy])
    (htarget : target.val.map (fun x => x.val) = [tx, ty])
    (hroads : RoadsMatch specialRoads roads)
    (hne : 1 ≤ specialRoads.val.length) (hle : specialRoads.val.length ≤ 200)
    (hfive : ∀ v ∈ specialRoads.val, v.val.length = 5)
    (hx : 1 ≤ sx ∧ sx ≤ tx ∧ tx ≤ 100000)
    (hy : 1 ≤ sy ∧ sy ≤ ty ∧ ty ≤ 100000)
    (hbox : ∀ r ∈ roads, r.within sx sy tx ty)
    (r : I64) (hr : minimum_cost start target specialRoads = ok r), IsLeast {c : Int | pathCost ⟨sx, sy⟩ ⟨tx, ty⟩ roads ⟨sx, sy⟩ ⟨tx, ty⟩ c} r.val) := by
  sorry

/-- Let specialRoads' be the array obtained from specialRoads by deleting index q, keeping the remaining entries in their original relative order. Whenever the function returns a result r for (start,target,specialRoads) and a result r' for (start,target,specialRoads'), it holds that r = r'.
  Preconditions: Let sx=start[0], sy=start[1], tx=target[0], ty=target[1]. Assume len(start)=2, len(target)=2, 1<=len(specialRoads)<=200, len(specialRoads[i])=5 for every i, 1<=sx<=tx<=100000, 1<=sy<=ty<=100000, and for each i with (ax_i,ay_i,bx_i,by_i,c_i)=specialRoads[i], sx<=ax_i<=tx, sx<=bx_i<=tx, sy<=ay_i<=ty, sy<=by_i<=ty, 1<=c_i<=100000. Additionally len(specialRoads)>=2 and there exist indices p<q with (ax_p,ay_p,bx_p,by_p)=(ax_q,ay_q,bx_q,by_q) and c_p<=c_q. -/
theorem spec_14 (start target : Slice I64) (specialRoads : Slice (alloc.vec.Vec I64))
    (roads : List Road) (sx sy tx ty : Int)
    (hstart : start.val.map (fun x => x.val) = [sx, sy])
    (htarget : target.val.map (fun x => x.val) = [tx, ty])
    (hroads : RoadsMatch specialRoads roads)
    (hne : 1 ≤ specialRoads.val.length) (hle : specialRoads.val.length ≤ 200)
    (hfive : ∀ v ∈ specialRoads.val, v.val.length = 5)
    (hx : 1 ≤ sx ∧ sx ≤ tx ∧ tx ≤ 100000)
    (hy : 1 ≤ sy ∧ sy ≤ ty ∧ ty ≤ 100000)
    (hbox : ∀ r ∈ roads, r.within sx sy tx ty)
    (hne2 : 2 ≤ specialRoads.val.length)
    (p q : Nat) (hpq : p < q) (hq : q < roads.length)
    (rp rq : Road) (hrp : roads[p]? = some rp) (hrq : roads[q]? = some rq)
    (hsame : rp.startX = rq.startX ∧ rp.startY = rq.startY ∧
      rp.endX = rq.endX ∧ rp.endY = rq.endY)
    (hcost : rp.cost ≤ rq.cost)
    (specialRoads' : Slice (alloc.vec.Vec I64)) (roads' : List Road)
    (hroads' : RoadsMatch specialRoads' roads') (hdel : roads' = roads.eraseIdx q)
    (r r' : I64) (hr : minimum_cost start target specialRoads = ok r)
    (hr' : minimum_cost start target specialRoads' = ok r') :
    r = r' := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (start target : Slice I64) (specialRoads : Slice (alloc.vec.Vec I64))
    (roads : List Road) (sx sy tx ty : Int)
    (hstart : start.val.map (fun x => x.val) = [sx, sy])
    (htarget : target.val.map (fun x => x.val) = [tx, ty])
    (hroads : RoadsMatch specialRoads roads)
    (hne : 1 ≤ specialRoads.val.length) (hle : specialRoads.val.length ≤ 200)
    (hfive : ∀ v ∈ specialRoads.val, v.val.length = 5)
    (hx : 1 ≤ sx ∧ sx ≤ tx ∧ tx ≤ 100000)
    (hy : 1 ≤ sy ∧ sy ≤ ty ∧ ty ≤ 100000)
    (hbox : ∀ r ∈ roads, r.within sx sy tx ty)
    (hne2 : 2 ≤ specialRoads.val.length)
    (p q : Nat) (hpq : p < q) (hq : q < roads.length)
    (rp rq : Road) (hrp : roads[p]? = some rp) (hrq : roads[q]? = some rq)
    (hsame : rp.startX = rq.startX ∧ rp.startY = rq.startY ∧
      rp.endX = rq.endX ∧ rp.endY = rq.endY)
    (hcost : rp.cost ≤ rq.cost)
    (specialRoads' : Slice (alloc.vec.Vec I64)) (roads' : List Road)
    (hroads' : RoadsMatch specialRoads' roads') (hdel : roads' = roads.eraseIdx q)
    (r r' : I64) (hr : minimum_cost start target specialRoads = ok r)
    (hr' : minimum_cost start target specialRoads' = ok r'), r = r') := by
  sorry

end AegisSpec.MinimumCost

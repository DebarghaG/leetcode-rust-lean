import Aegis.MaxProfit.Code.Funs

/-!
# Specifications of `Aegis.MaxProfit.max_profit`

LeetCode problem `sell-diminishing-valued-colored-balls`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaxProfit

  def M : ℤ := 1000000007

  def entries (inventory : Slice I64) : List ℤ := inventory.val.map (fun x => x.val)

  def entry (inventory : Slice I64) (i : ℕ) : ℤ := (entries inventory).getD i 0

  def size (inventory : Slice I64) : ℕ := (entries inventory).length

  def total (inventory : Slice I64) : ℤ := (entries inventory).sum

  def maxEntry (inventory : Slice I64) : ℤ := (entries inventory).foldr max 0

  def allocSum (a : ℕ → ℤ) (n : ℕ) : ℤ := ((List.range n).map a).sum

  def allocValue (inventory : Slice I64) (a : ℕ → ℤ) : ℤ :=
    ((List.range (size inventory)).map
      (fun i => a i * entry inventory i - a i * (a i - 1) / 2)).sum

  def Feasible (inventory : Slice I64) (orders : ℤ) (a : ℕ → ℤ) : Prop :=
    (∀ i, i < size inventory → 0 ≤ a i ∧ a i ≤ entry inventory i) ∧
      allocSum a (size inventory) = orders

  def IsMaxValue (inventory : Slice I64) (orders K : ℤ) : Prop :=
    (∃ a, Feasible inventory orders a ∧ allocValue inventory a = K) ∧
      ∀ a, Feasible inventory orders a → allocValue inventory a ≤ K

  def Optimal (inventory : Slice I64) (orders : ℤ) (a : ℕ → ℤ) : Prop :=
    Feasible inventory orders a ∧
      ∀ b, Feasible inventory orders b → allocValue inventory b ≤ allocValue inventory a

  def triTotal (inventory : Slice I64) : ℤ :=
    ((entries inventory).map (fun v => v * (v + 1) / 2)).sum

  def layerCount (inventory : Slice I64) (t : ℤ) : ℤ :=
    ((entries inventory).map (fun v => max 0 (v - t + 1))).sum

  def layerSum (inventory : Slice I64) (orders : ℤ) : ℤ :=
    ((List.range (maxEntry inventory).toNat).map
      (fun k => min orders (layerCount inventory ((k : ℤ) + 1)))).sum

  def soldAbove (inventory : Slice I64) (a : ℕ → ℤ) (t : ℤ) : ℤ :=
    ((List.range (size inventory)).map
      (fun i => min (a i) (max 0 (entry inventory i - t + 1)))).sum

  theorem size_eq (inventory : Slice I64) : size inventory = inventory.val.length := by
    simp [size, entries]

  /-- Let M = 1000000007. Call an integer allocation a[0],...,a[len(inventory)-1] feasible when 0 <= a[i] <= inventory[i] for every i and sum_{i=0}^{len(inventory)-1} a[i] = orders. For a feasible allocation a define V(a) = sum_{i=0}^{len(inventory)-1} sum_{t=0}^{a[i]-1} (inventory[i] - t), which equals sum_i (a[i]*inventory[i] - a[i]*(a[i]-1)/2). The function returns a result r with r = (max over all feasible a of V(a)) mod M, where mod M means the least nonnegative remainder. This is the maximum total value obtainable by selling exactly orders balls.
    Preconditions: len(inventory) >= 1 and len(inventory) <= 100000; for every i with 0 <= i < len(inventory), 1 <= inventory[i] and inventory[i] <= 1000000000; 1 <= orders and orders <= min(sum_{i=0}^{len(inventory)-1} inventory[i], 1000000000). -/
  theorem spec_1 (inventory : Slice I64) (orders : I64)
      (hlen1 : 1 ≤ size inventory) (hlen2 : size inventory ≤ 100000)
      (hentries : ∀ i, i < size inventory → 1 ≤ entry inventory i ∧ entry inventory i ≤ 1000000000)
      (horders1 : 1 ≤ orders.val)
      (horders2 : orders.val ≤ min (total inventory) 1000000000) :
      ∃ K r, IsMaxValue inventory orders.val K ∧
        Aegis.MaxProfit.max_profit inventory orders = Result.ok r ∧ r.val = K % M := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (inventory : Slice I64) (orders : I64)
        (hlen1 : 1 ≤ size inventory) (hlen2 : size inventory ≤ 100000)
        (hentries : ∀ i, i < size inventory → 1 ≤ entry inventory i ∧ entry inventory i ≤ 1000000000)
        (horders1 : 1 ≤ orders.val)
        (horders2 : orders.val ≤ min (total inventory) 1000000000), ∃ K r, IsMaxValue inventory orders.val K ∧
          Aegis.MaxProfit.max_profit inventory orders = Result.ok r ∧ r.val = K % M) := by
    sorry

  /-- For every input satisfying the preconditions, the function does not fail: it returns a result r (no arithmetic overflow, out-of-bounds access, or panic).
    Preconditions: len(inventory) >= 1 and len(inventory) <= 100000; for every i with 0 <= i < len(inventory), 1 <= inventory[i] and inventory[i] <= 1000000000; 1 <= orders and orders <= min(sum_{i=0}^{len(inventory)-1} inventory[i], 1000000000). -/
  theorem spec_2 (inventory : Slice I64) (orders : I64)
      (hlen1 : 1 ≤ size inventory) (hlen2 : size inventory ≤ 100000)
      (hentries : ∀ i, i < size inventory → 1 ≤ entry inventory i ∧ entry inventory i ≤ 1000000000)
      (horders1 : 1 ≤ orders.val)
      (horders2 : orders.val ≤ min (total inventory) 1000000000) :
      ∃ r, Aegis.MaxProfit.max_profit inventory orders = Result.ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (inventory : Slice I64) (orders : I64)
        (hlen1 : 1 ≤ size inventory) (hlen2 : size inventory ≤ 100000)
        (hentries : ∀ i, i < size inventory → 1 ≤ entry inventory i ∧ entry inventory i ≤ 1000000000)
        (horders1 : 1 ≤ orders.val)
        (horders2 : orders.val ≤ min (total inventory) 1000000000), ∃ r, Aegis.MaxProfit.max_profit inventory orders = Result.ok r) := by
    sorry

  /-- The function returns a result r with 0 <= r < 1000000007.
    Preconditions: len(inventory) >= 1 and len(inventory) <= 100000; for every i with 0 <= i < len(inventory), 1 <= inventory[i] and inventory[i] <= 1000000000; 1 <= orders and orders <= min(sum_{i=0}^{len(inventory)-1} inventory[i], 1000000000). -/
  theorem spec_3 (inventory : Slice I64) (orders : I64)
      (hlen1 : 1 ≤ size inventory) (hlen2 : size inventory ≤ 100000)
      (hentries : ∀ i, i < size inventory → 1 ≤ entry inventory i ∧ entry inventory i ≤ 1000000000)
      (horders1 : 1 ≤ orders.val)
      (horders2 : orders.val ≤ min (total inventory) 1000000000) :
      ∃ r, Aegis.MaxProfit.max_profit inventory orders = Result.ok r ∧ 0 ≤ r.val ∧ r.val < M := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (inventory : Slice I64) (orders : I64)
        (hlen1 : 1 ≤ size inventory) (hlen2 : size inventory ≤ 100000)
        (hentries : ∀ i, i < size inventory → 1 ≤ entry inventory i ∧ entry inventory i ≤ 1000000000)
        (horders1 : 1 ≤ orders.val)
        (horders2 : orders.val ≤ min (total inventory) 1000000000), ∃ r, Aegis.MaxProfit.max_profit inventory orders = Result.ok r ∧ 0 ≤ r.val ∧ r.val < M) := by
    sorry

  /-- The function returns r = max_{0 <= i < len(inventory)} inventory[i]. No reduction modulo M is needed because this maximum is at most 1000000000 < 1000000007.
    Preconditions: len(inventory) >= 1 and len(inventory) <= 100000; for every i with 0 <= i < len(inventory), 1 <= inventory[i] and inventory[i] <= 1000000000; 1 <= orders and orders <= min(sum_{i=0}^{len(inventory)-1} inventory[i], 1000000000); orders = 1. -/
  theorem spec_4 (inventory : Slice I64) (orders : I64)
      (hlen1 : 1 ≤ size inventory) (hlen2 : size inventory ≤ 100000)
      (hentries : ∀ i, i < size inventory → 1 ≤ entry inventory i ∧ entry inventory i ≤ 1000000000)
      (horders1 : 1 ≤ orders.val)
      (horders2 : orders.val ≤ min (total inventory) 1000000000)
      (horders : orders.val = 1) :
      ∃ r, Aegis.MaxProfit.max_profit inventory orders = Result.ok r ∧ r.val = maxEntry inventory := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (inventory : Slice I64) (orders : I64)
        (hlen1 : 1 ≤ size inventory) (hlen2 : size inventory ≤ 100000)
        (hentries : ∀ i, i < size inventory → 1 ≤ entry inventory i ∧ entry inventory i ≤ 1000000000)
        (horders1 : 1 ≤ orders.val)
        (horders2 : orders.val ≤ min (total inventory) 1000000000)
        (horders : orders.val = 1), ∃ r, Aegis.MaxProfit.max_profit inventory orders = Result.ok r ∧ r.val = maxEntry inventory) := by
    sorry

  /-- The function returns r = (orders * inventory[0] - orders*(orders-1)/2) mod 1000000007.
    Preconditions: len(inventory) >= 1 and len(inventory) <= 100000; for every i with 0 <= i < len(inventory), 1 <= inventory[i] and inventory[i] <= 1000000000; 1 <= orders and orders <= min(sum_{i=0}^{len(inventory)-1} inventory[i], 1000000000); len(inventory) = 1. -/
  theorem spec_5 (inventory : Slice I64) (orders : I64)
      (hlen1 : 1 ≤ size inventory) (hlen2 : size inventory ≤ 100000)
      (hentries : ∀ i, i < size inventory → 1 ≤ entry inventory i ∧ entry inventory i ≤ 1000000000)
      (horders1 : 1 ≤ orders.val)
      (horders2 : orders.val ≤ min (total inventory) 1000000000)
      (hlen : size inventory = 1) :
      ∃ r, Aegis.MaxProfit.max_profit inventory orders = Result.ok r ∧
        r.val = (orders.val * entry inventory 0 - orders.val * (orders.val - 1) / 2) % M := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (inventory : Slice I64) (orders : I64)
        (hlen1 : 1 ≤ size inventory) (hlen2 : size inventory ≤ 100000)
        (hentries : ∀ i, i < size inventory → 1 ≤ entry inventory i ∧ entry inventory i ≤ 1000000000)
        (horders1 : 1 ≤ orders.val)
        (horders2 : orders.val ≤ min (total inventory) 1000000000)
        (hlen : size inventory = 1), ∃ r, Aegis.MaxProfit.max_profit inventory orders = Result.ok r ∧
          r.val = (orders.val * entry inventory 0 - orders.val * (orders.val - 1) / 2) % M) := by
    sorry

  /-- The function returns r = (sum_{i=0}^{len(inventory)-1} inventory[i]*(inventory[i]+1)/2) mod 1000000007.
    Preconditions: len(inventory) >= 1 and len(inventory) <= 100000; for every i with 0 <= i < len(inventory), 1 <= inventory[i] and inventory[i] <= 1000000000; 1 <= orders and orders <= min(sum_{i=0}^{len(inventory)-1} inventory[i], 1000000000); orders = sum_{i=0}^{len(inventory)-1} inventory[i]. -/
  theorem spec_6 (inventory : Slice I64) (orders : I64)
      (hlen1 : 1 ≤ size inventory) (hlen2 : size inventory ≤ 100000)
      (hentries : ∀ i, i < size inventory → 1 ≤ entry inventory i ∧ entry inventory i ≤ 1000000000)
      (horders1 : 1 ≤ orders.val)
      (horders2 : orders.val ≤ min (total inventory) 1000000000)
      (horders : orders.val = total inventory) :
      ∃ r, Aegis.MaxProfit.max_profit inventory orders = Result.ok r ∧
        r.val = triTotal inventory % M := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (inventory : Slice I64) (orders : I64)
        (hlen1 : 1 ≤ size inventory) (hlen2 : size inventory ≤ 100000)
        (hentries : ∀ i, i < size inventory → 1 ≤ entry inventory i ∧ entry inventory i ≤ 1000000000)
        (horders1 : 1 ≤ orders.val)
        (horders2 : orders.val ≤ min (total inventory) 1000000000)
        (horders : orders.val = total inventory), ∃ r, Aegis.MaxProfit.max_profit inventory orders = Result.ok r ∧
          r.val = triTotal inventory % M) := by
    sorry

  /-- The function returns r = ( (sum_{i=0}^{len(inventory)-1} inventory[i]*(inventory[i]+1)/2) - 1 ) mod 1000000007.
    Preconditions: len(inventory) >= 1 and len(inventory) <= 100000; for every i with 0 <= i < len(inventory), 1 <= inventory[i] and inventory[i] <= 1000000000; 1 <= orders and orders <= min(sum_{i=0}^{len(inventory)-1} inventory[i], 1000000000); sum_{i=0}^{len(inventory)-1} inventory[i] >= 2 and orders = sum_{i=0}^{len(inventory)-1} inventory[i] - 1. -/
  theorem spec_7 (inventory : Slice I64) (orders : I64)
      (hlen1 : 1 ≤ size inventory) (hlen2 : size inventory ≤ 100000)
      (hentries : ∀ i, i < size inventory → 1 ≤ entry inventory i ∧ entry inventory i ≤ 1000000000)
      (horders1 : 1 ≤ orders.val)
      (horders2 : orders.val ≤ min (total inventory) 1000000000)
      (htotal : 2 ≤ total inventory)
      (horders : orders.val = total inventory - 1) :
      ∃ r, Aegis.MaxProfit.max_profit inventory orders = Result.ok r ∧
        r.val = (triTotal inventory - 1) % M := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (inventory : Slice I64) (orders : I64)
        (hlen1 : 1 ≤ size inventory) (hlen2 : size inventory ≤ 100000)
        (hentries : ∀ i, i < size inventory → 1 ≤ entry inventory i ∧ entry inventory i ≤ 1000000000)
        (horders1 : 1 ≤ orders.val)
        (horders2 : orders.val ≤ min (total inventory) 1000000000)
        (htotal : 2 ≤ total inventory)
        (horders : orders.val = total inventory - 1), ∃ r, Aegis.MaxProfit.max_profit inventory orders = Result.ok r ∧
          r.val = (triTotal inventory - 1) % M) := by
    sorry

  /-- Let m = len(inventory), q = orders div m, and s = orders mod m, so orders = q*m + s and 0 <= s < m. The function returns r = ( m*(q*v - q*(q-1)/2) + s*(v-q) ) mod 1000000007.
    Preconditions: len(inventory) >= 1 and len(inventory) <= 100000; for every i with 0 <= i < len(inventory), 1 <= inventory[i] and inventory[i] <= 1000000000; 1 <= orders and orders <= min(sum_{i=0}^{len(inventory)-1} inventory[i], 1000000000); there exists v with 1 <= v <= 1000000000 such that inventory[i] = v for every i with 0 <= i < len(inventory). -/
  theorem spec_8 (inventory : Slice I64) (orders : I64) (v : ℤ)
      (hlen1 : 1 ≤ size inventory) (hlen2 : size inventory ≤ 100000)
      (hentries : ∀ i, i < size inventory → 1 ≤ entry inventory i ∧ entry inventory i ≤ 1000000000)
      (horders1 : 1 ≤ orders.val)
      (horders2 : orders.val ≤ min (total inventory) 1000000000)
      (hv1 : 1 ≤ v) (hv2 : v ≤ 1000000000)
      (hconst : ∀ i, i < size inventory → entry inventory i = v) :
      ∃ r, Aegis.MaxProfit.max_profit inventory orders = Result.ok r ∧
        (let m : ℤ := (size inventory : ℤ)
         let q : ℤ := orders.val / m
         let s : ℤ := orders.val % m
         r.val = (m * (q * v - q * (q - 1) / 2) + s * (v - q)) % M) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (inventory : Slice I64) (orders : I64) (v : ℤ)
        (hlen1 : 1 ≤ size inventory) (hlen2 : size inventory ≤ 100000)
        (hentries : ∀ i, i < size inventory → 1 ≤ entry inventory i ∧ entry inventory i ≤ 1000000000)
        (horders1 : 1 ≤ orders.val)
        (horders2 : orders.val ≤ min (total inventory) 1000000000)
        (hv1 : 1 ≤ v) (hv2 : v ≤ 1000000000)
        (hconst : ∀ i, i < size inventory → entry inventory i = v), ∃ r, Aegis.MaxProfit.max_profit inventory orders = Result.ok r ∧
          (let m : ℤ := (size inventory : ℤ)
           let q : ℤ := orders.val / m
           let s : ℤ := orders.val % m
           r.val = (m * (q * v - q * (q - 1) / 2) + s * (v - q)) % M)) := by
    sorry

  /-- For any slice inventory' of the same length whose entries are a permutation of the entries of inventory, the function returns the same value for (inventory', orders) as for (inventory, orders): max_profit(inventory, orders) = max_profit(inventory', orders).
    Preconditions: len(inventory) >= 1 and len(inventory) <= 100000; for every i with 0 <= i < len(inventory), 1 <= inventory[i] and inventory[i] <= 1000000000; 1 <= orders and orders <= min(sum_{i=0}^{len(inventory)-1} inventory[i], 1000000000). -/
  theorem spec_9 (inventory inventory' : Slice I64) (orders : I64)
      (hlen1 : 1 ≤ size inventory) (hlen2 : size inventory ≤ 100000)
      (hentries : ∀ i, i < size inventory → 1 ≤ entry inventory i ∧ entry inventory i ≤ 1000000000)
      (horders1 : 1 ≤ orders.val)
      (horders2 : orders.val ≤ min (total inventory) 1000000000)
      (hlen1' : 1 ≤ size inventory') (hlen2' : size inventory' ≤ 100000)
      (hentries' : ∀ i, i < size inventory' →
        1 ≤ entry inventory' i ∧ entry inventory' i ≤ 1000000000)
      (hperm : (entries inventory').Perm (entries inventory)) :
      ∃ r, Aegis.MaxProfit.max_profit inventory orders = Result.ok r ∧
        Aegis.MaxProfit.max_profit inventory' orders = Result.ok r := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (inventory inventory' : Slice I64) (orders : I64)
        (hlen1 : 1 ≤ size inventory) (hlen2 : size inventory ≤ 100000)
        (hentries : ∀ i, i < size inventory → 1 ≤ entry inventory i ∧ entry inventory i ≤ 1000000000)
        (horders1 : 1 ≤ orders.val)
        (horders2 : orders.val ≤ min (total inventory) 1000000000)
        (hlen1' : 1 ≤ size inventory') (hlen2' : size inventory' ≤ 100000)
        (hentries' : ∀ i, i < size inventory' →
          1 ≤ entry inventory' i ∧ entry inventory' i ≤ 1000000000)
        (hperm : (entries inventory').Perm (entries inventory)), ∃ r, Aegis.MaxProfit.max_profit inventory orders = Result.ok r ∧
          Aegis.MaxProfit.max_profit inventory' orders = Result.ok r) := by
    sorry

  /-- Let max_inv = max_{0 <= i < len(inventory)} inventory[i]. For each integer t >= 1 define C_t = sum_{i=0}^{len(inventory)-1} max(0, inventory[i] - t + 1), the number of balls whose value is at least t before any sale. The function returns r = ( sum_{t=1}^{max_inv} min(orders, C_t) ) mod 1000000007.
    Preconditions: len(inventory) >= 1 and len(inventory) <= 100000; for every i with 0 <= i < len(inventory), 1 <= inventory[i] and inventory[i] <= 1000000000; 1 <= orders and orders <= min(sum_{i=0}^{len(inventory)-1} inventory[i], 1000000000). -/
  theorem spec_10 (inventory : Slice I64) (orders : I64)
      (hlen1 : 1 ≤ size inventory) (hlen2 : size inventory ≤ 100000)
      (hentries : ∀ i, i < size inventory → 1 ≤ entry inventory i ∧ entry inventory i ≤ 1000000000)
      (horders1 : 1 ≤ orders.val)
      (horders2 : orders.val ≤ min (total inventory) 1000000000) :
      ∃ r, Aegis.MaxProfit.max_profit inventory orders = Result.ok r ∧
        r.val = layerSum inventory orders.val % M := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (inventory : Slice I64) (orders : I64)
        (hlen1 : 1 ≤ size inventory) (hlen2 : size inventory ≤ 100000)
        (hentries : ∀ i, i < size inventory → 1 ≤ entry inventory i ∧ entry inventory i ≤ 1000000000)
        (horders1 : 1 ≤ orders.val)
        (horders2 : orders.val ≤ min (total inventory) 1000000000), ∃ r, Aegis.MaxProfit.max_profit inventory orders = Result.ok r ∧
          r.val = layerSum inventory orders.val % M) := by
    sorry

  /-- Define V(a) = sum_{i=0}^{len(inventory)-1} (a[i]*inventory[i] - a[i]*(a[i]-1)/2) for an allocation a. There exist integers a[0],...,a[len(inventory)-1] such that: (i) 0 <= a[i] <= inventory[i] for all i; (ii) sum_i a[i] = orders; (iii) V(a) is maximum among all feasible allocations; (iv) the returned r satisfies r = V(a) mod 1000000007; and (v) for every pair i,j with a[i] < inventory[i] and a[j] > 0, inventory[i] - a[i] <= inventory[j] - a[j] + 1.
    Preconditions: len(inventory) >= 1 and len(inventory) <= 100000; for every i with 0 <= i < len(inventory), 1 <= inventory[i] and inventory[i] <= 1000000000; 1 <= orders and orders <= min(sum_{i=0}^{len(inventory)-1} inventory[i], 1000000000). -/
  theorem spec_11 (inventory : Slice I64) (orders : I64)
      (hlen1 : 1 ≤ size inventory) (hlen2 : size inventory ≤ 100000)
      (hentries : ∀ i, i < size inventory → 1 ≤ entry inventory i ∧ entry inventory i ≤ 1000000000)
      (horders1 : 1 ≤ orders.val)
      (horders2 : orders.val ≤ min (total inventory) 1000000000) :
      ∃ a r, Optimal inventory orders.val a ∧
        Aegis.MaxProfit.max_profit inventory orders = Result.ok r ∧
        r.val = allocValue inventory a % M ∧
        (∀ i j, i < size inventory → j < size inventory →
          a i < entry inventory i → 0 < a j →
            entry inventory i - a i ≤ entry inventory j - a j + 1) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (inventory : Slice I64) (orders : I64)
        (hlen1 : 1 ≤ size inventory) (hlen2 : size inventory ≤ 100000)
        (hentries : ∀ i, i < size inventory → 1 ≤ entry inventory i ∧ entry inventory i ≤ 1000000000)
        (horders1 : 1 ≤ orders.val)
        (horders2 : orders.val ≤ min (total inventory) 1000000000), ∃ a r, Optimal inventory orders.val a ∧
          Aegis.MaxProfit.max_profit inventory orders = Result.ok r ∧
          r.val = allocValue inventory a % M ∧
          (∀ i j, i < size inventory → j < size inventory →
            a i < entry inventory i → 0 < a j →
              entry inventory i - a i ≤ entry inventory j - a j + 1)) := by
    sorry

  end AegisSpec.MaxProfit

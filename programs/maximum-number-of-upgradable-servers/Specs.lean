import Aegis.MaxUpgrades.Code.Funs

/-!
# Specifications of `Aegis.MaxUpgrades.max_upgrades`

LeetCode problem `maximum-number-of-upgradable-servers`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  set_option autoImplicit false

  namespace AegisSpec.MaxUpgrades

  def getInt (l : List I64) (i : Nat) : Int :=
    ((l[i]?).map (fun x => x.val)).getD 0

  def fdiv (a b : Int) : Int := Int.ediv a b

  /-- Whenever max_upgrades(count, upgrade, sell, money) returns a result r, r is a vector of length n, and for every i with 0 <= i < n, r[i] = min(count[i], floor((money[i] + sell[i]*count[i]) / (upgrade[i] + sell[i]))). Here floor denotes integer division rounding down, and the denominator upgrade[i] + sell[i] is positive.
    Preconditions: Let n = len(count). We have 1 <= n <= 100000, len(upgrade) = len(sell) = len(money) = n, and for every i with 0 <= i < n, 1 <= count[i] <= 100000, 1 <= upgrade[i] <= 100000, 1 <= sell[i] <= 100000, and 1 <= money[i] <= 1000000000. -/
  theorem spec_1
      (count upgrade sell money : Slice I64) (n : Nat)
      (h_n_lower : 1 ≤ n) (h_n_upper : n ≤ 100000)
      (h_count_len : count.val.length = n)
      (h_upgrade_len : upgrade.val.length = n)
      (h_sell_len : sell.val.length = n)
      (h_money_len : money.val.length = n)
      (h_count_bounds : ∀ i, i < n → 1 ≤ getInt count.val i ∧ getInt count.val i ≤ 100000)
      (h_upgrade_bounds : ∀ i, i < n → 1 ≤ getInt upgrade.val i ∧ getInt upgrade.val i ≤ 100000)
      (h_sell_bounds : ∀ i, i < n → 1 ≤ getInt sell.val i ∧ getInt sell.val i ≤ 100000)
      (h_money_bounds : ∀ i, i < n → 1 ≤ getInt money.val i ∧ getInt money.val i ≤ 1000000000) :
      ∀ r, Aegis.MaxUpgrades.max_upgrades count upgrade sell money = ok r →
        r.val.length = n ∧
          ∀ i, i < n →
            getInt r.val i =
              min (getInt count.val i)
                (fdiv (getInt money.val i + getInt sell.val i * getInt count.val i)
                  (getInt upgrade.val i + getInt sell.val i)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (count upgrade sell money : Slice I64) (n : Nat)
        (h_n_lower : 1 ≤ n) (h_n_upper : n ≤ 100000)
        (h_count_len : count.val.length = n)
        (h_upgrade_len : upgrade.val.length = n)
        (h_sell_len : sell.val.length = n)
        (h_money_len : money.val.length = n)
        (h_count_bounds : ∀ i, i < n → 1 ≤ getInt count.val i ∧ getInt count.val i ≤ 100000)
        (h_upgrade_bounds : ∀ i, i < n → 1 ≤ getInt upgrade.val i ∧ getInt upgrade.val i ≤ 100000)
        (h_sell_bounds : ∀ i, i < n → 1 ≤ getInt sell.val i ∧ getInt sell.val i ≤ 100000)
        (h_money_bounds : ∀ i, i < n → 1 ≤ getInt money.val i ∧ getInt money.val i ≤ 1000000000), ∀ r, Aegis.MaxUpgrades.max_upgrades count upgrade sell money = ok r →
          r.val.length = n ∧
            ∀ i, i < n →
              getInt r.val i =
                min (getInt count.val i)
                  (fdiv (getInt money.val i + getInt sell.val i * getInt count.val i)
                    (getInt upgrade.val i + getInt sell.val i))) := by
    sorry

  /-- Whenever max_upgrades(count, upgrade, sell, money) returns a result r, len(r) = n.
    Preconditions: Let n = len(count). We have 1 <= n <= 100000, len(upgrade) = len(sell) = len(money) = n, and for every i with 0 <= i < n, 1 <= count[i] <= 100000, 1 <= upgrade[i] <= 100000, 1 <= sell[i] <= 100000, and 1 <= money[i] <= 1000000000. -/
  theorem spec_2
      (count upgrade sell money : Slice I64) (n : Nat)
      (h_n_lower : 1 ≤ n) (h_n_upper : n ≤ 100000)
      (h_count_len : count.val.length = n)
      (h_upgrade_len : upgrade.val.length = n)
      (h_sell_len : sell.val.length = n)
      (h_money_len : money.val.length = n)
      (h_count_bounds : ∀ i, i < n → 1 ≤ getInt count.val i ∧ getInt count.val i ≤ 100000)
      (h_upgrade_bounds : ∀ i, i < n → 1 ≤ getInt upgrade.val i ∧ getInt upgrade.val i ≤ 100000)
      (h_sell_bounds : ∀ i, i < n → 1 ≤ getInt sell.val i ∧ getInt sell.val i ≤ 100000)
      (h_money_bounds : ∀ i, i < n → 1 ≤ getInt money.val i ∧ getInt money.val i ≤ 1000000000) :
      ∀ r, Aegis.MaxUpgrades.max_upgrades count upgrade sell money = ok r →
        r.val.length = n := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (count upgrade sell money : Slice I64) (n : Nat)
        (h_n_lower : 1 ≤ n) (h_n_upper : n ≤ 100000)
        (h_count_len : count.val.length = n)
        (h_upgrade_len : upgrade.val.length = n)
        (h_sell_len : sell.val.length = n)
        (h_money_len : money.val.length = n)
        (h_count_bounds : ∀ i, i < n → 1 ≤ getInt count.val i ∧ getInt count.val i ≤ 100000)
        (h_upgrade_bounds : ∀ i, i < n → 1 ≤ getInt upgrade.val i ∧ getInt upgrade.val i ≤ 100000)
        (h_sell_bounds : ∀ i, i < n → 1 ≤ getInt sell.val i ∧ getInt sell.val i ≤ 100000)
        (h_money_bounds : ∀ i, i < n → 1 ≤ getInt money.val i ∧ getInt money.val i ≤ 1000000000), ∀ r, Aegis.MaxUpgrades.max_upgrades count upgrade sell money = ok r →
          r.val.length = n) := by
    sorry

  /-- Whenever max_upgrades(count, upgrade, sell, money) returns a result r, for every i with 0 <= i < n, 0 <= r[i] <= count[i].
    Preconditions: Let n = len(count). We have 1 <= n <= 100000, len(upgrade) = len(sell) = len(money) = n, and for every i with 0 <= i < n, 1 <= count[i] <= 100000, 1 <= upgrade[i] <= 100000, 1 <= sell[i] <= 100000, and 1 <= money[i] <= 1000000000. -/
  theorem spec_3
      (count upgrade sell money : Slice I64) (n : Nat)
      (h_n_lower : 1 ≤ n) (h_n_upper : n ≤ 100000)
      (h_count_len : count.val.length = n)
      (h_upgrade_len : upgrade.val.length = n)
      (h_sell_len : sell.val.length = n)
      (h_money_len : money.val.length = n)
      (h_count_bounds : ∀ i, i < n → 1 ≤ getInt count.val i ∧ getInt count.val i ≤ 100000)
      (h_upgrade_bounds : ∀ i, i < n → 1 ≤ getInt upgrade.val i ∧ getInt upgrade.val i ≤ 100000)
      (h_sell_bounds : ∀ i, i < n → 1 ≤ getInt sell.val i ∧ getInt sell.val i ≤ 100000)
      (h_money_bounds : ∀ i, i < n → 1 ≤ getInt money.val i ∧ getInt money.val i ≤ 1000000000) :
      ∀ r, Aegis.MaxUpgrades.max_upgrades count upgrade sell money = ok r →
        ∀ i, i < n → 0 ≤ getInt r.val i ∧ getInt r.val i ≤ getInt count.val i := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (count upgrade sell money : Slice I64) (n : Nat)
        (h_n_lower : 1 ≤ n) (h_n_upper : n ≤ 100000)
        (h_count_len : count.val.length = n)
        (h_upgrade_len : upgrade.val.length = n)
        (h_sell_len : sell.val.length = n)
        (h_money_len : money.val.length = n)
        (h_count_bounds : ∀ i, i < n → 1 ≤ getInt count.val i ∧ getInt count.val i ≤ 100000)
        (h_upgrade_bounds : ∀ i, i < n → 1 ≤ getInt upgrade.val i ∧ getInt upgrade.val i ≤ 100000)
        (h_sell_bounds : ∀ i, i < n → 1 ≤ getInt sell.val i ∧ getInt sell.val i ≤ 100000)
        (h_money_bounds : ∀ i, i < n → 1 ≤ getInt money.val i ∧ getInt money.val i ≤ 1000000000), ∀ r, Aegis.MaxUpgrades.max_upgrades count upgrade sell money = ok r →
          ∀ i, i < n → 0 ≤ getInt r.val i ∧ getInt r.val i ≤ getInt count.val i) := by
    sorry

  /-- Whenever max_upgrades(count, upgrade, sell, money) returns a result r, for every i with 0 <= i < n, the value r[i] is achievable by selling exactly count[i]-r[i] servers at center i and then upgrading the remaining r[i] servers: upgrade[i]*r[i] <= money[i] + sell[i]*(count[i]-r[i]).
    Preconditions: Let n = len(count). We have 1 <= n <= 100000, len(upgrade) = len(sell) = len(money) = n, and for every i with 0 <= i < n, 1 <= count[i] <= 100000, 1 <= upgrade[i] <= 100000, 1 <= sell[i] <= 100000, and 1 <= money[i] <= 1000000000. -/
  theorem spec_4
      (count upgrade sell money : Slice I64) (n : Nat)
      (h_n_lower : 1 ≤ n) (h_n_upper : n ≤ 100000)
      (h_count_len : count.val.length = n)
      (h_upgrade_len : upgrade.val.length = n)
      (h_sell_len : sell.val.length = n)
      (h_money_len : money.val.length = n)
      (h_count_bounds : ∀ i, i < n → 1 ≤ getInt count.val i ∧ getInt count.val i ≤ 100000)
      (h_upgrade_bounds : ∀ i, i < n → 1 ≤ getInt upgrade.val i ∧ getInt upgrade.val i ≤ 100000)
      (h_sell_bounds : ∀ i, i < n → 1 ≤ getInt sell.val i ∧ getInt sell.val i ≤ 100000)
      (h_money_bounds : ∀ i, i < n → 1 ≤ getInt money.val i ∧ getInt money.val i ≤ 1000000000) :
      ∀ r, Aegis.MaxUpgrades.max_upgrades count upgrade sell money = ok r →
        ∀ i, i < n →
          getInt upgrade.val i * getInt r.val i ≤
            getInt money.val i + getInt sell.val i * (getInt count.val i - getInt r.val i) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (count upgrade sell money : Slice I64) (n : Nat)
        (h_n_lower : 1 ≤ n) (h_n_upper : n ≤ 100000)
        (h_count_len : count.val.length = n)
        (h_upgrade_len : upgrade.val.length = n)
        (h_sell_len : sell.val.length = n)
        (h_money_len : money.val.length = n)
        (h_count_bounds : ∀ i, i < n → 1 ≤ getInt count.val i ∧ getInt count.val i ≤ 100000)
        (h_upgrade_bounds : ∀ i, i < n → 1 ≤ getInt upgrade.val i ∧ getInt upgrade.val i ≤ 100000)
        (h_sell_bounds : ∀ i, i < n → 1 ≤ getInt sell.val i ∧ getInt sell.val i ≤ 100000)
        (h_money_bounds : ∀ i, i < n → 1 ≤ getInt money.val i ∧ getInt money.val i ≤ 1000000000), ∀ r, Aegis.MaxUpgrades.max_upgrades count upgrade sell money = ok r →
          ∀ i, i < n →
            getInt upgrade.val i * getInt r.val i ≤
              getInt money.val i + getInt sell.val i * (getInt count.val i - getInt r.val i)) := by
    sorry

  /-- Whenever max_upgrades(count, upgrade, sell, money) returns a result r, for every i with 0 <= i < n and every integer y with r[i] < y <= count[i], even selling every server not upgraded in a plan to upgrade y servers leaves too little money: upgrade[i]*y > money[i] + sell[i]*(count[i]-y).
    Preconditions: Let n = len(count). We have 1 <= n <= 100000, len(upgrade) = len(sell) = len(money) = n, and for every i with 0 <= i < n, 1 <= count[i] <= 100000, 1 <= upgrade[i] <= 100000, 1 <= sell[i] <= 100000, and 1 <= money[i] <= 1000000000. -/
  theorem spec_5
      (count upgrade sell money : Slice I64) (n : Nat)
      (h_n_lower : 1 ≤ n) (h_n_upper : n ≤ 100000)
      (h_count_len : count.val.length = n)
      (h_upgrade_len : upgrade.val.length = n)
      (h_sell_len : sell.val.length = n)
      (h_money_len : money.val.length = n)
      (h_count_bounds : ∀ i, i < n → 1 ≤ getInt count.val i ∧ getInt count.val i ≤ 100000)
      (h_upgrade_bounds : ∀ i, i < n → 1 ≤ getInt upgrade.val i ∧ getInt upgrade.val i ≤ 100000)
      (h_sell_bounds : ∀ i, i < n → 1 ≤ getInt sell.val i ∧ getInt sell.val i ≤ 100000)
      (h_money_bounds : ∀ i, i < n → 1 ≤ getInt money.val i ∧ getInt money.val i ≤ 1000000000) :
      ∀ r, Aegis.MaxUpgrades.max_upgrades count upgrade sell money = ok r →
        ∀ i, i < n → ∀ y : Int, getInt r.val i < y → y ≤ getInt count.val i →
          getInt upgrade.val i * y >
            getInt money.val i + getInt sell.val i * (getInt count.val i - y) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (count upgrade sell money : Slice I64) (n : Nat)
        (h_n_lower : 1 ≤ n) (h_n_upper : n ≤ 100000)
        (h_count_len : count.val.length = n)
        (h_upgrade_len : upgrade.val.length = n)
        (h_sell_len : sell.val.length = n)
        (h_money_len : money.val.length = n)
        (h_count_bounds : ∀ i, i < n → 1 ≤ getInt count.val i ∧ getInt count.val i ≤ 100000)
        (h_upgrade_bounds : ∀ i, i < n → 1 ≤ getInt upgrade.val i ∧ getInt upgrade.val i ≤ 100000)
        (h_sell_bounds : ∀ i, i < n → 1 ≤ getInt sell.val i ∧ getInt sell.val i ≤ 100000)
        (h_money_bounds : ∀ i, i < n → 1 ≤ getInt money.val i ∧ getInt money.val i ≤ 1000000000), ∀ r, Aegis.MaxUpgrades.max_upgrades count upgrade sell money = ok r →
          ∀ i, i < n → ∀ y : Int, getInt r.val i < y → y ≤ getInt count.val i →
            getInt upgrade.val i * y >
              getInt money.val i + getInt sell.val i * (getInt count.val i - y)) := by
    sorry

  /-- Whenever max_upgrades(count, upgrade, sell, money) returns a result r, for every i with 0 <= i < n, r[i] = count[i] if and only if money[i] >= upgrade[i]*count[i].
    Preconditions: Let n = len(count). We have 1 <= n <= 100000, len(upgrade) = len(sell) = len(money) = n, and for every i with 0 <= i < n, 1 <= count[i] <= 100000, 1 <= upgrade[i] <= 100000, 1 <= sell[i] <= 100000, and 1 <= money[i] <= 1000000000. -/
  theorem spec_6
      (count upgrade sell money : Slice I64) (n : Nat)
      (h_n_lower : 1 ≤ n) (h_n_upper : n ≤ 100000)
      (h_count_len : count.val.length = n)
      (h_upgrade_len : upgrade.val.length = n)
      (h_sell_len : sell.val.length = n)
      (h_money_len : money.val.length = n)
      (h_count_bounds : ∀ i, i < n → 1 ≤ getInt count.val i ∧ getInt count.val i ≤ 100000)
      (h_upgrade_bounds : ∀ i, i < n → 1 ≤ getInt upgrade.val i ∧ getInt upgrade.val i ≤ 100000)
      (h_sell_bounds : ∀ i, i < n → 1 ≤ getInt sell.val i ∧ getInt sell.val i ≤ 100000)
      (h_money_bounds : ∀ i, i < n → 1 ≤ getInt money.val i ∧ getInt money.val i ≤ 1000000000) :
      ∀ r, Aegis.MaxUpgrades.max_upgrades count upgrade sell money = ok r →
        ∀ i, i < n →
          (getInt r.val i = getInt count.val i ↔
            getInt money.val i ≥ getInt upgrade.val i * getInt count.val i) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (count upgrade sell money : Slice I64) (n : Nat)
        (h_n_lower : 1 ≤ n) (h_n_upper : n ≤ 100000)
        (h_count_len : count.val.length = n)
        (h_upgrade_len : upgrade.val.length = n)
        (h_sell_len : sell.val.length = n)
        (h_money_len : money.val.length = n)
        (h_count_bounds : ∀ i, i < n → 1 ≤ getInt count.val i ∧ getInt count.val i ≤ 100000)
        (h_upgrade_bounds : ∀ i, i < n → 1 ≤ getInt upgrade.val i ∧ getInt upgrade.val i ≤ 100000)
        (h_sell_bounds : ∀ i, i < n → 1 ≤ getInt sell.val i ∧ getInt sell.val i ≤ 100000)
        (h_money_bounds : ∀ i, i < n → 1 ≤ getInt money.val i ∧ getInt money.val i ≤ 1000000000), ∀ r, Aegis.MaxUpgrades.max_upgrades count upgrade sell money = ok r →
          ∀ i, i < n →
            (getInt r.val i = getInt count.val i ↔
              getInt money.val i ≥ getInt upgrade.val i * getInt count.val i)) := by
    sorry

  /-- Whenever max_upgrades(count, upgrade, sell, money) returns a result r, for every i with 0 <= i < n, r[i] = 0 if and only if upgrade[i] > money[i] + sell[i]*(count[i]-1).
    Preconditions: Let n = len(count). We have 1 <= n <= 100000, len(upgrade) = len(sell) = len(money) = n, and for every i with 0 <= i < n, 1 <= count[i] <= 100000, 1 <= upgrade[i] <= 100000, 1 <= sell[i] <= 100000, and 1 <= money[i] <= 1000000000. -/
  theorem spec_7
      (count upgrade sell money : Slice I64) (n : Nat)
      (h_n_lower : 1 ≤ n) (h_n_upper : n ≤ 100000)
      (h_count_len : count.val.length = n)
      (h_upgrade_len : upgrade.val.length = n)
      (h_sell_len : sell.val.length = n)
      (h_money_len : money.val.length = n)
      (h_count_bounds : ∀ i, i < n → 1 ≤ getInt count.val i ∧ getInt count.val i ≤ 100000)
      (h_upgrade_bounds : ∀ i, i < n → 1 ≤ getInt upgrade.val i ∧ getInt upgrade.val i ≤ 100000)
      (h_sell_bounds : ∀ i, i < n → 1 ≤ getInt sell.val i ∧ getInt sell.val i ≤ 100000)
      (h_money_bounds : ∀ i, i < n → 1 ≤ getInt money.val i ∧ getInt money.val i ≤ 1000000000) :
      ∀ r, Aegis.MaxUpgrades.max_upgrades count upgrade sell money = ok r →
        ∀ i, i < n →
          (getInt r.val i = 0 ↔
            getInt upgrade.val i >
              getInt money.val i + getInt sell.val i * (getInt count.val i - 1)) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (count upgrade sell money : Slice I64) (n : Nat)
        (h_n_lower : 1 ≤ n) (h_n_upper : n ≤ 100000)
        (h_count_len : count.val.length = n)
        (h_upgrade_len : upgrade.val.length = n)
        (h_sell_len : sell.val.length = n)
        (h_money_len : money.val.length = n)
        (h_count_bounds : ∀ i, i < n → 1 ≤ getInt count.val i ∧ getInt count.val i ≤ 100000)
        (h_upgrade_bounds : ∀ i, i < n → 1 ≤ getInt upgrade.val i ∧ getInt upgrade.val i ≤ 100000)
        (h_sell_bounds : ∀ i, i < n → 1 ≤ getInt sell.val i ∧ getInt sell.val i ≤ 100000)
        (h_money_bounds : ∀ i, i < n → 1 ≤ getInt money.val i ∧ getInt money.val i ≤ 1000000000), ∀ r, Aegis.MaxUpgrades.max_upgrades count upgrade sell money = ok r →
          ∀ i, i < n →
            (getInt r.val i = 0 ↔
              getInt upgrade.val i >
                getInt money.val i + getInt sell.val i * (getInt count.val i - 1))) := by
    sorry

  /-- Whenever max_upgrades(count, upgrade, sell, money) returns a result r, for every i with 0 <= i < n, if money[i] >= upgrade[i], then r[i] >= 1.
    Preconditions: Let n = len(count). We have 1 <= n <= 100000, len(upgrade) = len(sell) = len(money) = n, and for every i with 0 <= i < n, 1 <= count[i] <= 100000, 1 <= upgrade[i] <= 100000, 1 <= sell[i] <= 100000, and 1 <= money[i] <= 1000000000. -/
  theorem spec_8
      (count upgrade sell money : Slice I64) (n : Nat)
      (h_n_lower : 1 ≤ n) (h_n_upper : n ≤ 100000)
      (h_count_len : count.val.length = n)
      (h_upgrade_len : upgrade.val.length = n)
      (h_sell_len : sell.val.length = n)
      (h_money_len : money.val.length = n)
      (h_count_bounds : ∀ i, i < n → 1 ≤ getInt count.val i ∧ getInt count.val i ≤ 100000)
      (h_upgrade_bounds : ∀ i, i < n → 1 ≤ getInt upgrade.val i ∧ getInt upgrade.val i ≤ 100000)
      (h_sell_bounds : ∀ i, i < n → 1 ≤ getInt sell.val i ∧ getInt sell.val i ≤ 100000)
      (h_money_bounds : ∀ i, i < n → 1 ≤ getInt money.val i ∧ getInt money.val i ≤ 1000000000) :
      ∀ r, Aegis.MaxUpgrades.max_upgrades count upgrade sell money = ok r →
        ∀ i, i < n → getInt money.val i ≥ getInt upgrade.val i → getInt r.val i ≥ 1 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (count upgrade sell money : Slice I64) (n : Nat)
        (h_n_lower : 1 ≤ n) (h_n_upper : n ≤ 100000)
        (h_count_len : count.val.length = n)
        (h_upgrade_len : upgrade.val.length = n)
        (h_sell_len : sell.val.length = n)
        (h_money_len : money.val.length = n)
        (h_count_bounds : ∀ i, i < n → 1 ≤ getInt count.val i ∧ getInt count.val i ≤ 100000)
        (h_upgrade_bounds : ∀ i, i < n → 1 ≤ getInt upgrade.val i ∧ getInt upgrade.val i ≤ 100000)
        (h_sell_bounds : ∀ i, i < n → 1 ≤ getInt sell.val i ∧ getInt sell.val i ≤ 100000)
        (h_money_bounds : ∀ i, i < n → 1 ≤ getInt money.val i ∧ getInt money.val i ≤ 1000000000), ∀ r, Aegis.MaxUpgrades.max_upgrades count upgrade sell money = ok r →
          ∀ i, i < n → getInt money.val i ≥ getInt upgrade.val i → getInt r.val i ≥ 1) := by
    sorry

  /-- If max_upgrades(count, upgrade, sell, money1) returns r1 and max_upgrades(count, upgrade, sell, money2) returns r2, then for every i with 0 <= i < n, r1[i] <= r2[i].
    Preconditions: Let n be a common length with 1 <= n <= 100000. The arrays count, upgrade, sell, money1, and money2 all have length n. For every i with 0 <= i < n, 1 <= count[i] <= 100000, 1 <= upgrade[i] <= 100000, 1 <= sell[i] <= 100000, 1 <= money1[i] <= 1000000000, 1 <= money2[i] <= 1000000000, and money1[i] <= money2[i]. -/
  theorem spec_9
      (count upgrade sell money1 money2 : Slice I64) (n : Nat)
      (h_n_lower : 1 ≤ n) (h_n_upper : n ≤ 100000)
      (h_count_len : count.val.length = n)
      (h_upgrade_len : upgrade.val.length = n)
      (h_sell_len : sell.val.length = n)
      (h_money1_len : money1.val.length = n)
      (h_money2_len : money2.val.length = n)
      (h_count_bounds : ∀ i, i < n → 1 ≤ getInt count.val i ∧ getInt count.val i ≤ 100000)
      (h_upgrade_bounds : ∀ i, i < n → 1 ≤ getInt upgrade.val i ∧ getInt upgrade.val i ≤ 100000)
      (h_sell_bounds : ∀ i, i < n → 1 ≤ getInt sell.val i ∧ getInt sell.val i ≤ 100000)
      (h_money1_bounds : ∀ i, i < n → 1 ≤ getInt money1.val i ∧ getInt money1.val i ≤ 1000000000)
      (h_money2_bounds : ∀ i, i < n → 1 ≤ getInt money2.val i ∧ getInt money2.val i ≤ 1000000000)
      (h_money_le : ∀ i, i < n → getInt money1.val i ≤ getInt money2.val i) :
      ∀ r1 r2,
        Aegis.MaxUpgrades.max_upgrades count upgrade sell money1 = ok r1 →
        Aegis.MaxUpgrades.max_upgrades count upgrade sell money2 = ok r2 →
        ∀ i, i < n → getInt r1.val i ≤ getInt r2.val i := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (count upgrade sell money1 money2 : Slice I64) (n : Nat)
        (h_n_lower : 1 ≤ n) (h_n_upper : n ≤ 100000)
        (h_count_len : count.val.length = n)
        (h_upgrade_len : upgrade.val.length = n)
        (h_sell_len : sell.val.length = n)
        (h_money1_len : money1.val.length = n)
        (h_money2_len : money2.val.length = n)
        (h_count_bounds : ∀ i, i < n → 1 ≤ getInt count.val i ∧ getInt count.val i ≤ 100000)
        (h_upgrade_bounds : ∀ i, i < n → 1 ≤ getInt upgrade.val i ∧ getInt upgrade.val i ≤ 100000)
        (h_sell_bounds : ∀ i, i < n → 1 ≤ getInt sell.val i ∧ getInt sell.val i ≤ 100000)
        (h_money1_bounds : ∀ i, i < n → 1 ≤ getInt money1.val i ∧ getInt money1.val i ≤ 1000000000)
        (h_money2_bounds : ∀ i, i < n → 1 ≤ getInt money2.val i ∧ getInt money2.val i ≤ 1000000000)
        (h_money_le : ∀ i, i < n → getInt money1.val i ≤ getInt money2.val i), ∀ r1 r2,
          Aegis.MaxUpgrades.max_upgrades count upgrade sell money1 = ok r1 →
          Aegis.MaxUpgrades.max_upgrades count upgrade sell money2 = ok r2 →
          ∀ i, i < n → getInt r1.val i ≤ getInt r2.val i) := by
    sorry

  /-- If max_upgrades(count, upgrade1, sell, money) returns r1 and max_upgrades(count, upgrade2, sell, money) returns r2, then for every i with 0 <= i < n, r1[i] >= r2[i].
    Preconditions: Let n be a common length with 1 <= n <= 100000. The arrays count, upgrade1, upgrade2, sell, and money all have length n. For every i with 0 <= i < n, 1 <= count[i] <= 100000, 1 <= upgrade1[i] <= 100000, 1 <= upgrade2[i] <= 100000, 1 <= sell[i] <= 100000, 1 <= money[i] <= 1000000000, and upgrade1[i] <= upgrade2[i]. -/
  theorem spec_10
      (count upgrade1 upgrade2 sell money : Slice I64) (n : Nat)
      (h_n_lower : 1 ≤ n) (h_n_upper : n ≤ 100000)
      (h_count_len : count.val.length = n)
      (h_upgrade1_len : upgrade1.val.length = n)
      (h_upgrade2_len : upgrade2.val.length = n)
      (h_sell_len : sell.val.length = n)
      (h_money_len : money.val.length = n)
      (h_count_bounds : ∀ i, i < n → 1 ≤ getInt count.val i ∧ getInt count.val i ≤ 100000)
      (h_upgrade1_bounds : ∀ i, i < n → 1 ≤ getInt upgrade1.val i ∧ getInt upgrade1.val i ≤ 100000)
      (h_upgrade2_bounds : ∀ i, i < n → 1 ≤ getInt upgrade2.val i ∧ getInt upgrade2.val i ≤ 100000)
      (h_sell_bounds : ∀ i, i < n → 1 ≤ getInt sell.val i ∧ getInt sell.val i ≤ 100000)
      (h_money_bounds : ∀ i, i < n → 1 ≤ getInt money.val i ∧ getInt money.val i ≤ 1000000000)
      (h_upgrade_le : ∀ i, i < n → getInt upgrade1.val i ≤ getInt upgrade2.val i) :
      ∀ r1 r2,
        Aegis.MaxUpgrades.max_upgrades count upgrade1 sell money = ok r1 →
        Aegis.MaxUpgrades.max_upgrades count upgrade2 sell money = ok r2 →
        ∀ i, i < n → getInt r1.val i ≥ getInt r2.val i := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (count upgrade1 upgrade2 sell money : Slice I64) (n : Nat)
        (h_n_lower : 1 ≤ n) (h_n_upper : n ≤ 100000)
        (h_count_len : count.val.length = n)
        (h_upgrade1_len : upgrade1.val.length = n)
        (h_upgrade2_len : upgrade2.val.length = n)
        (h_sell_len : sell.val.length = n)
        (h_money_len : money.val.length = n)
        (h_count_bounds : ∀ i, i < n → 1 ≤ getInt count.val i ∧ getInt count.val i ≤ 100000)
        (h_upgrade1_bounds : ∀ i, i < n → 1 ≤ getInt upgrade1.val i ∧ getInt upgrade1.val i ≤ 100000)
        (h_upgrade2_bounds : ∀ i, i < n → 1 ≤ getInt upgrade2.val i ∧ getInt upgrade2.val i ≤ 100000)
        (h_sell_bounds : ∀ i, i < n → 1 ≤ getInt sell.val i ∧ getInt sell.val i ≤ 100000)
        (h_money_bounds : ∀ i, i < n → 1 ≤ getInt money.val i ∧ getInt money.val i ≤ 1000000000)
        (h_upgrade_le : ∀ i, i < n → getInt upgrade1.val i ≤ getInt upgrade2.val i), ∀ r1 r2,
          Aegis.MaxUpgrades.max_upgrades count upgrade1 sell money = ok r1 →
          Aegis.MaxUpgrades.max_upgrades count upgrade2 sell money = ok r2 →
          ∀ i, i < n → getInt r1.val i ≥ getInt r2.val i) := by
    sorry

  /-- If max_upgrades(count, upgrade, sell1, money) returns r1 and max_upgrades(count, upgrade, sell2, money) returns r2, then for every i with 0 <= i < n, r1[i] <= r2[i].
    Preconditions: Let n be a common length with 1 <= n <= 100000. The arrays count, upgrade, sell1, sell2, and money all have length n. For every i with 0 <= i < n, 1 <= count[i] <= 100000, 1 <= upgrade[i] <= 100000, 1 <= sell1[i] <= 100000, 1 <= sell2[i] <= 100000, 1 <= money[i] <= 1000000000, and sell1[i] <= sell2[i]. -/
  theorem spec_11
      (count upgrade sell1 sell2 money : Slice I64) (n : Nat)
      (h_n_lower : 1 ≤ n) (h_n_upper : n ≤ 100000)
      (h_count_len : count.val.length = n)
      (h_upgrade_len : upgrade.val.length = n)
      (h_sell1_len : sell1.val.length = n)
      (h_sell2_len : sell2.val.length = n)
      (h_money_len : money.val.length = n)
      (h_count_bounds : ∀ i, i < n → 1 ≤ getInt count.val i ∧ getInt count.val i ≤ 100000)
      (h_upgrade_bounds : ∀ i, i < n → 1 ≤ getInt upgrade.val i ∧ getInt upgrade.val i ≤ 100000)
      (h_sell1_bounds : ∀ i, i < n → 1 ≤ getInt sell1.val i ∧ getInt sell1.val i ≤ 100000)
      (h_sell2_bounds : ∀ i, i < n → 1 ≤ getInt sell2.val i ∧ getInt sell2.val i ≤ 100000)
      (h_money_bounds : ∀ i, i < n → 1 ≤ getInt money.val i ∧ getInt money.val i ≤ 1000000000)
      (h_sell_le : ∀ i, i < n → getInt sell1.val i ≤ getInt sell2.val i) :
      ∀ r1 r2,
        Aegis.MaxUpgrades.max_upgrades count upgrade sell1 money = ok r1 →
        Aegis.MaxUpgrades.max_upgrades count upgrade sell2 money = ok r2 →
        ∀ i, i < n → getInt r1.val i ≤ getInt r2.val i := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (count upgrade sell1 sell2 money : Slice I64) (n : Nat)
        (h_n_lower : 1 ≤ n) (h_n_upper : n ≤ 100000)
        (h_count_len : count.val.length = n)
        (h_upgrade_len : upgrade.val.length = n)
        (h_sell1_len : sell1.val.length = n)
        (h_sell2_len : sell2.val.length = n)
        (h_money_len : money.val.length = n)
        (h_count_bounds : ∀ i, i < n → 1 ≤ getInt count.val i ∧ getInt count.val i ≤ 100000)
        (h_upgrade_bounds : ∀ i, i < n → 1 ≤ getInt upgrade.val i ∧ getInt upgrade.val i ≤ 100000)
        (h_sell1_bounds : ∀ i, i < n → 1 ≤ getInt sell1.val i ∧ getInt sell1.val i ≤ 100000)
        (h_sell2_bounds : ∀ i, i < n → 1 ≤ getInt sell2.val i ∧ getInt sell2.val i ≤ 100000)
        (h_money_bounds : ∀ i, i < n → 1 ≤ getInt money.val i ∧ getInt money.val i ≤ 1000000000)
        (h_sell_le : ∀ i, i < n → getInt sell1.val i ≤ getInt sell2.val i), ∀ r1 r2,
          Aegis.MaxUpgrades.max_upgrades count upgrade sell1 money = ok r1 →
          Aegis.MaxUpgrades.max_upgrades count upgrade sell2 money = ok r2 →
          ∀ i, i < n → getInt r1.val i ≤ getInt r2.val i) := by
    sorry

  /-- If max_upgrades(count1, upgrade, sell, money) returns r1 and max_upgrades(count2, upgrade, sell, money) returns r2, then for every i with 0 <= i < n, r1[i] <= r2[i].
    Preconditions: Let n be a common length with 1 <= n <= 100000. The arrays count1, count2, upgrade, sell, and money all have length n. For every i with 0 <= i < n, 1 <= count1[i] <= 100000, 1 <= count2[i] <= 100000, 1 <= upgrade[i] <= 100000, 1 <= sell[i] <= 100000, 1 <= money[i] <= 1000000000, and count1[i] <= count2[i]. -/
  theorem spec_12
      (count1 count2 upgrade sell money : Slice I64) (n : Nat)
      (h_n_lower : 1 ≤ n) (h_n_upper : n ≤ 100000)
      (h_count1_len : count1.val.length = n)
      (h_count2_len : count2.val.length = n)
      (h_upgrade_len : upgrade.val.length = n)
      (h_sell_len : sell.val.length = n)
      (h_money_len : money.val.length = n)
      (h_count1_bounds : ∀ i, i < n → 1 ≤ getInt count1.val i ∧ getInt count1.val i ≤ 100000)
      (h_count2_bounds : ∀ i, i < n → 1 ≤ getInt count2.val i ∧ getInt count2.val i ≤ 100000)
      (h_upgrade_bounds : ∀ i, i < n → 1 ≤ getInt upgrade.val i ∧ getInt upgrade.val i ≤ 100000)
      (h_sell_bounds : ∀ i, i < n → 1 ≤ getInt sell.val i ∧ getInt sell.val i ≤ 100000)
      (h_money_bounds : ∀ i, i < n → 1 ≤ getInt money.val i ∧ getInt money.val i ≤ 1000000000)
      (h_count_le : ∀ i, i < n → getInt count1.val i ≤ getInt count2.val i) :
      ∀ r1 r2,
        Aegis.MaxUpgrades.max_upgrades count1 upgrade sell money = ok r1 →
        Aegis.MaxUpgrades.max_upgrades count2 upgrade sell money = ok r2 →
        ∀ i, i < n → getInt r1.val i ≤ getInt r2.val i := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (count1 count2 upgrade sell money : Slice I64) (n : Nat)
        (h_n_lower : 1 ≤ n) (h_n_upper : n ≤ 100000)
        (h_count1_len : count1.val.length = n)
        (h_count2_len : count2.val.length = n)
        (h_upgrade_len : upgrade.val.length = n)
        (h_sell_len : sell.val.length = n)
        (h_money_len : money.val.length = n)
        (h_count1_bounds : ∀ i, i < n → 1 ≤ getInt count1.val i ∧ getInt count1.val i ≤ 100000)
        (h_count2_bounds : ∀ i, i < n → 1 ≤ getInt count2.val i ∧ getInt count2.val i ≤ 100000)
        (h_upgrade_bounds : ∀ i, i < n → 1 ≤ getInt upgrade.val i ∧ getInt upgrade.val i ≤ 100000)
        (h_sell_bounds : ∀ i, i < n → 1 ≤ getInt sell.val i ∧ getInt sell.val i ≤ 100000)
        (h_money_bounds : ∀ i, i < n → 1 ≤ getInt money.val i ∧ getInt money.val i ≤ 1000000000)
        (h_count_le : ∀ i, i < n → getInt count1.val i ≤ getInt count2.val i), ∀ r1 r2,
          Aegis.MaxUpgrades.max_upgrades count1 upgrade sell money = ok r1 →
          Aegis.MaxUpgrades.max_upgrades count2 upgrade sell money = ok r2 →
          ∀ i, i < n → getInt r1.val i ≤ getInt r2.val i) := by
    sorry

  /-- If max_upgrades(count1, upgrade1, sell1, money1) returns r1 and max_upgrades(count2, upgrade2, sell2, money2) returns r2, then r1[i] = r2[i].
    Preconditions: Let n be a common length with 1 <= n <= 100000. Two input tuples (count1, upgrade1, sell1, money1) and (count2, upgrade2, sell2, money2) both satisfy: for every j with 0 <= j < n, 1 <= count1[j] <= 100000, 1 <= upgrade1[j] <= 100000, 1 <= sell1[j] <= 100000, 1 <= money1[j] <= 1000000000, and the same four bounds hold for count2[j], upgrade2[j], sell2[j], money2[j]; all four arrays in each tuple have length n. Fix an index i with 0 <= i < n such that count1[i]=count2[i], upgrade1[i]=upgrade2[i], sell1[i]=sell2[i], and money1[i]=money2[i]. -/
  theorem spec_13
      (count1 upgrade1 sell1 money1 count2 upgrade2 sell2 money2 : Slice I64)
      (n i : Nat)
      (h_n_lower : 1 ≤ n) (h_n_upper : n ≤ 100000)
      (h_i_lt : i < n)
      (h_count1_len : count1.val.length = n)
      (h_upgrade1_len : upgrade1.val.length = n)
      (h_sell1_len : sell1.val.length = n)
      (h_money1_len : money1.val.length = n)
      (h_count2_len : count2.val.length = n)
      (h_upgrade2_len : upgrade2.val.length = n)
      (h_sell2_len : sell2.val.length = n)
      (h_money2_len : money2.val.length = n)
      (h_count1_bounds : ∀ j, j < n → 1 ≤ getInt count1.val j ∧ getInt count1.val j ≤ 100000)
      (h_upgrade1_bounds : ∀ j, j < n → 1 ≤ getInt upgrade1.val j ∧ getInt upgrade1.val j ≤ 100000)
      (h_sell1_bounds : ∀ j, j < n → 1 ≤ getInt sell1.val j ∧ getInt sell1.val j ≤ 100000)
      (h_money1_bounds : ∀ j, j < n → 1 ≤ getInt money1.val j ∧ getInt money1.val j ≤ 1000000000)
      (h_count2_bounds : ∀ j, j < n → 1 ≤ getInt count2.val j ∧ getInt count2.val j ≤ 100000)
      (h_upgrade2_bounds : ∀ j, j < n → 1 ≤ getInt upgrade2.val j ∧ getInt upgrade2.val j ≤ 100000)
      (h_sell2_bounds : ∀ j, j < n → 1 ≤ getInt sell2.val j ∧ getInt sell2.val j ≤ 100000)
      (h_money2_bounds : ∀ j, j < n → 1 ≤ getInt money2.val j ∧ getInt money2.val j ≤ 1000000000)
      (h_count_eq : getInt count1.val i = getInt count2.val i)
      (h_upgrade_eq : getInt upgrade1.val i = getInt upgrade2.val i)
      (h_sell_eq : getInt sell1.val i = getInt sell2.val i)
      (h_money_eq : getInt money1.val i = getInt money2.val i) :
      ∀ r1 r2,
        Aegis.MaxUpgrades.max_upgrades count1 upgrade1 sell1 money1 = ok r1 →
        Aegis.MaxUpgrades.max_upgrades count2 upgrade2 sell2 money2 = ok r2 →
        getInt r1.val i = getInt r2.val i := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (count1 upgrade1 sell1 money1 count2 upgrade2 sell2 money2 : Slice I64)
        (n i : Nat)
        (h_n_lower : 1 ≤ n) (h_n_upper : n ≤ 100000)
        (h_i_lt : i < n)
        (h_count1_len : count1.val.length = n)
        (h_upgrade1_len : upgrade1.val.length = n)
        (h_sell1_len : sell1.val.length = n)
        (h_money1_len : money1.val.length = n)
        (h_count2_len : count2.val.length = n)
        (h_upgrade2_len : upgrade2.val.length = n)
        (h_sell2_len : sell2.val.length = n)
        (h_money2_len : money2.val.length = n)
        (h_count1_bounds : ∀ j, j < n → 1 ≤ getInt count1.val j ∧ getInt count1.val j ≤ 100000)
        (h_upgrade1_bounds : ∀ j, j < n → 1 ≤ getInt upgrade1.val j ∧ getInt upgrade1.val j ≤ 100000)
        (h_sell1_bounds : ∀ j, j < n → 1 ≤ getInt sell1.val j ∧ getInt sell1.val j ≤ 100000)
        (h_money1_bounds : ∀ j, j < n → 1 ≤ getInt money1.val j ∧ getInt money1.val j ≤ 1000000000)
        (h_count2_bounds : ∀ j, j < n → 1 ≤ getInt count2.val j ∧ getInt count2.val j ≤ 100000)
        (h_upgrade2_bounds : ∀ j, j < n → 1 ≤ getInt upgrade2.val j ∧ getInt upgrade2.val j ≤ 100000)
        (h_sell2_bounds : ∀ j, j < n → 1 ≤ getInt sell2.val j ∧ getInt sell2.val j ≤ 100000)
        (h_money2_bounds : ∀ j, j < n → 1 ≤ getInt money2.val j ∧ getInt money2.val j ≤ 1000000000)
        (h_count_eq : getInt count1.val i = getInt count2.val i)
        (h_upgrade_eq : getInt upgrade1.val i = getInt upgrade2.val i)
        (h_sell_eq : getInt sell1.val i = getInt sell2.val i)
        (h_money_eq : getInt money1.val i = getInt money2.val i), ∀ r1 r2,
          Aegis.MaxUpgrades.max_upgrades count1 upgrade1 sell1 money1 = ok r1 →
          Aegis.MaxUpgrades.max_upgrades count2 upgrade2 sell2 money2 = ok r2 →
          getInt r1.val i = getInt r2.val i) := by
    sorry

  /-- For every input satisfying the preconditions, max_upgrades(count, upgrade, sell, money) returns a result r; it does not fail or panic.
    Preconditions: Let n = len(count). We have 1 <= n <= 100000, len(upgrade) = len(sell) = len(money) = n, and for every i with 0 <= i < n, 1 <= count[i] <= 100000, 1 <= upgrade[i] <= 100000, 1 <= sell[i] <= 100000, and 1 <= money[i] <= 1000000000. -/
  theorem spec_14
      (count upgrade sell money : Slice I64) (n : Nat)
      (h_n_lower : 1 ≤ n) (h_n_upper : n ≤ 100000)
      (h_count_len : count.val.length = n)
      (h_upgrade_len : upgrade.val.length = n)
      (h_sell_len : sell.val.length = n)
      (h_money_len : money.val.length = n)
      (h_count_bounds : ∀ i, i < n → 1 ≤ getInt count.val i ∧ getInt count.val i ≤ 100000)
      (h_upgrade_bounds : ∀ i, i < n → 1 ≤ getInt upgrade.val i ∧ getInt upgrade.val i ≤ 100000)
      (h_sell_bounds : ∀ i, i < n → 1 ≤ getInt sell.val i ∧ getInt sell.val i ≤ 100000)
      (h_money_bounds : ∀ i, i < n → 1 ≤ getInt money.val i ∧ getInt money.val i ≤ 1000000000) :
      ∃ r, Aegis.MaxUpgrades.max_upgrades count upgrade sell money = ok r := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (count upgrade sell money : Slice I64) (n : Nat)
        (h_n_lower : 1 ≤ n) (h_n_upper : n ≤ 100000)
        (h_count_len : count.val.length = n)
        (h_upgrade_len : upgrade.val.length = n)
        (h_sell_len : sell.val.length = n)
        (h_money_len : money.val.length = n)
        (h_count_bounds : ∀ i, i < n → 1 ≤ getInt count.val i ∧ getInt count.val i ≤ 100000)
        (h_upgrade_bounds : ∀ i, i < n → 1 ≤ getInt upgrade.val i ∧ getInt upgrade.val i ≤ 100000)
        (h_sell_bounds : ∀ i, i < n → 1 ≤ getInt sell.val i ∧ getInt sell.val i ≤ 100000)
        (h_money_bounds : ∀ i, i < n → 1 ≤ getInt money.val i ∧ getInt money.val i ≤ 1000000000), ∃ r, Aegis.MaxUpgrades.max_upgrades count upgrade sell money = ok r) := by
    sorry

  end AegisSpec.MaxUpgrades

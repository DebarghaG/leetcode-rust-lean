pub fn dist_money(money: i64, children: i64) -> i64 {
    if money < children {
        return -1;
    }

    let extra: i64 = money - children;
    let mut ans: i64 = extra / 7;

    if ans > children {
        ans = children;
    }

    let leftover: i64 = extra - ans * 7;
    let remaining: i64 = children - ans;

    if remaining == 0 {
        if leftover > 0 {
            ans = ans - 1;
        }
    } else {
        if remaining == 1 {
            if leftover == 3 {
                ans = ans - 1;
            }
        }
    }

    ans
}

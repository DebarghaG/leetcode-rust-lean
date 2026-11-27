pub fn min_cost(costs: &[Vec<i64>]) -> i64 {
    let n = costs.len();
    if n == 0 {
        return 0;
    }

    let mut red: i64 = costs[0][0];
    let mut blue: i64 = costs[0][1];
    let mut green: i64 = costs[0][2];

    let mut i: usize = 1;
    while i < n {
        let cost_red = costs[i][0];
        let cost_blue = costs[i][1];
        let cost_green = costs[i][2];

        let next_red = cost_red + if blue < green { blue } else { green };
        let next_blue = cost_blue + if red < green { red } else { green };
        let next_green = cost_green + if red < blue { red } else { blue };

        red = next_red;
        blue = next_blue;
        green = next_green;

        i += 1;
    }

    let mut ans = red;
    if blue < ans {
        ans = blue;
    }
    if green < ans {
        ans = green;
    }
    ans
}

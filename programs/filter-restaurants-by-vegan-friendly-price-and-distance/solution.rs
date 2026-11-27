pub fn filter_restaurants(
    restaurants: &[Vec<i64>],
    veganFriendly: i64,
    maxPrice: i64,
    maxDistance: i64,
) -> Vec<i64> {
    let mut keys: Vec<i64> = Vec::new();
    let n = restaurants.len();
    let mut i = 0;

    while i < n {
        let r = &restaurants[i];
        let id = r[0];
        let rating = r[1];
        let vegan = r[2];
        let price = r[3];
        let distance = r[4];

        let mut include = true;

        if veganFriendly == 1 && vegan != 1 {
            include = false;
        }
        if price > maxPrice {
            include = false;
        }
        if distance > maxDistance {
            include = false;
        }

        if include {
            keys.push(rating * 1_000_000_000 + id);
        }

        i += 1;
    }

    keys.sort();

    let mut out: Vec<i64> = Vec::new();
    let mut j = keys.len();

    while j > 0 {
        j -= 1;
        let key = keys[j];
        out.push(key % 1_000_000_000);
    }

    out
}

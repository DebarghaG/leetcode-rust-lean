pub fn find_winners(matches: &[Vec<i64>]) -> Vec<Vec<i64>> {
    let mut answer: Vec<Vec<i64>> = Vec::new();

    if matches.len() == 0 {
        let empty0: Vec<i64> = Vec::new();
        let empty1: Vec<i64> = Vec::new();
        answer.push(empty0);
        answer.push(empty1);
        return answer;
    }

    let mut max_player: i64 = 0;
    let mut i: usize = 0;
    while i < matches.len() {
        let winner = matches[i][0];
        let loser = matches[i][1];
        if winner > max_player {
            max_player = winner;
        }
        if loser > max_player {
            max_player = loser;
        }
        i += 1;
    }

    let size: usize = (max_player + 1) as usize;
    let mut losses: Vec<i64> = Vec::new();
    let mut played: Vec<i64> = Vec::new();

    let mut j: usize = 0;
    while j < size {
        losses.push(0);
        played.push(0);
        j += 1;
    }

    i = 0;
    while i < matches.len() {
        let winner = matches[i][0];
        let loser = matches[i][1];

        let wi: usize = winner as usize;
        let li: usize = loser as usize;

        played[wi] = 1;
        played[li] = 1;
        losses[li] = losses[li] + 1;

        i += 1;
    }

    let mut no_loss: Vec<i64> = Vec::new();
    let mut one_loss: Vec<i64> = Vec::new();

    let mut player: i64 = 1;
    while player <= max_player {
        let idx: usize = player as usize;
        if played[idx] == 1 {
            if losses[idx] == 0 {
                no_loss.push(player);
            } else if losses[idx] == 1 {
                one_loss.push(player);
            }
        }
        player += 1;
    }

    answer.push(no_loss);
    answer.push(one_loss);
    answer
}

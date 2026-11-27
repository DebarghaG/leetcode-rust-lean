pub fn min_number_of_hours(initialEnergy: i64, initialExperience: i64, energy: &[i64], experience: &[i64]) -> i64 {
    let n = energy.len();
    let mut hours: i64 = 0;

    let mut current_experience = initialExperience;
    let mut i = 0;
    while i < n {
        if current_experience <= experience[i] {
            let needed = experience[i] - current_experience + 1;
            hours += needed;
            current_experience += needed;
        }
        current_experience += experience[i];
        i += 1;
    }

    let mut required_energy: i64 = 1;
    let mut j = 0;
    while j < n {
        required_energy += energy[j];
        j += 1;
    }

    if initialEnergy < required_energy {
        hours += required_energy - initialEnergy;
    }

    hours
}

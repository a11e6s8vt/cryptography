/// 
/// Returns a non-negative integer a < m that satisfies a ≡ c^x(mod m)
/// c: base
/// x: exponent
/// m: modulus
/// 
pub fn modular_pow(c: u64, mut x: u64, m: u64) -> u64 {
    // initialization
    let mut a: u64 = 1;
    let mut s = c % m;

    // Converts exponent to its binary representation
    // Go through the digits from LSB to MSB in each iteration
    // if the digit == 1, a = a * s % modulus, s = s * s
    // if digit == 0, s = s * s
    while x > 0 {
        // Extract the LSB from the exp.
        if x & 1 == 1 {
            a = (a * s) % m;
        }

        s = (s * s) % m;

        // Division by 2 to get the next digit
        x = x >> 1;
    }

    a
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_modular_pow() {
        let result = modular_pow(2, 825, 173);
        assert_eq!(result, 107);
    }
}

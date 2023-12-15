use rand::Rng;
use std::{ops::Range, collections::HashMap};

/// 
/// GCD Calculator - The Euclidean Algorithm
/// Input: A pair of integers a and b, not both equal to zero
/// Output: gcd(a, b) 
/// 
pub fn gcd_euclid(mut a: u64, mut b: u64, print_steps: bool) -> u64 {
    let mut gcd: u64 = 0;
    if b > a {
        gcd = gcd_euclid(b, a, print_steps);
    } else {
        let mut r: u64 = a % b;
        let mut steps = 1;
        while r > 0 {
            let q = a / b;
            r = a % b;
            if print_steps {
                println!("Step {}: {} = {}x{} + {}", steps, a, q, b, r);
            }
            if r != 0 {
                a = b;
                b = r;
            }
            steps += 1;
        }

        gcd = b;
    }

    gcd
}

/// 
/// Generates a list of integers less than n and co-prime to n.
/// 
fn get_integers_coprime_n(n: u64) -> Vec<u64> {
    let mut coprimes: Vec<u64> = Vec::new();
    let r = Range {
        start: 1,
        end: n,
    };

    for num in r {
        if gcd_euclid(num, n, false) == 1 {
            coprimes.push(num)
        }
    }
    coprimes.sort();
    coprimes
}

/// 
/// Returns a non-negative integer a < m that satisfies a ≡ cˣ(mod m)
/// c: base
/// e: exponent
/// m: modulus
/// 
pub fn modular_pow(c: u64, mut e: u64, m: u64) -> u64 {
    // initialization
    let mut a: u64 = 1;
    let mut s = c % m;

    // Converts exponent to its binary representation
    // Go through the digits from LSB to MSB in each iteration
    // if the digit == 1, a = a * s % modulus, s = s * s
    // if digit == 0, s = s * s
    while e > 0 {
        // Extract the LSB from the exp.
        if e & 1 == 1 {
            a = (a * s) % m;
        }

        s = (s * s) % m;

        // Division by 2 to get the next digit
        e = e >> 1;
    }

    a
}

///
/// is_prime calculates if a number is prime by verifying numbers upto √n.
/// 
pub fn is_prime(n: u64) -> bool {
    if n <= 3 {
        return n > 1;
    }

    if n % 2 == 0 || n % 3 == 0 {
        return false;
    }

    let limit: u64 = (n as f64).sqrt().ceil() as u64;
    for i in (5..=limit).step_by(6) {
        if n % i == 0 || n % (i + 2) == 0 {
            return false;
        }
    }

    true
}

/// Miller-Rabin Test Step-1
/// It accepts an integer and returns a boolean value
/// 1. Express n - 1 as 2ᶠm
pub fn miller_rabin_primality(n: u64) -> bool {
    if n <= 1 || n == 4 {
        return false;
    }
    if n <= 3 {
        return true;
    }

    let mut d = n - 1;
    // Express n - 1 as 2ᶠ.m
    while d % 2 == 0 {
        d = d >> 1;
    }
    // d = (n - 1) / 2ᶠ

    for _ in 0..5 {
        if miller_test(d, n) == false {
            // If miller-rabin test returns false once, the given integer
            // is not a prime
            return false;
        }
    }

    true
}

/// Miller-Rabin Test - Step 2
/// 
fn miller_test(mut d: u64, n: u64) -> bool {
    let mut rng = rand::thread_rng();
    // Randomly generate a base: a such that 1 < a < n - 1
    let a: u64 = rng.gen_range(2..n - 1);

    // Calculate x ≡ a^d(mod n)
    let mut x = modular_pow(a, d, n);

    // if x ≡ ±1 (mod n), return true
    if x == 1 || x == n - 1 {
        return true;
    }
    
    // if x ≢ ±1 (mod n), while d != n-1 . 
    // d was obtained by repeated division of (m - 1) by 2.
    // multiplying it with 2 repeatedly until it equals (m - 1)
    while d != n - 1 {
        // sqaure x - This is a^((2^j)m)(mod n)
        x = modular_pow(x, 2, n);

        // if x ≡ -1 (mod n) the input number is probably prime
        if x == n - 1 {
            return true;
        }

        // if x ≡ -1 (mod n), then x is a factor of n
        if x == 1 {
            return false;
        }

        // left shifting for multiplication by 2
        d = d << 1;
    }

    false
}

pub fn prime_factors(mut n: u64) -> Vec<(u64, usize)> {
    // Check if n is prime
    if miller_rabin_primality(n) {
        return vec![(n, 1)];
    }

    let start_no: u64 = 2;
    let mut end_no: u64 = (n as f64).sqrt().ceil() as u64;
    end_no += 1;

    let r = Range {
        start: start_no,
        end: end_no,
    };

    let mut primes: Vec<u64> = Vec::new();

    for m in r {
        if miller_rabin_primality(m) {
            primes.push(m);
        }
    }

    let mut res: HashMap<u64, usize> = HashMap::new();

    'outer: while n > 1 {
        for p in primes.iter() {
            if n % p == 0 {
                res.entry(*p).and_modify(|c| *c += 1).or_insert(1);
                n = n / p;
                if miller_rabin_primality(n) {
                    res.entry(n).and_modify(|c| *c += 1).or_insert(1);
                    break 'outer;
                }
                break;
            } else {
                continue;
            }
        }
    }

    let mut res = res.into_iter().filter_map(|(key, value)| Some((key, value))).collect::<Vec<(u64, usize)>>();
    res.sort_by_key(|k| k.0);
    res
}

///
/// Get list of divisors of a number n > 2
/// 
pub fn divisors_of_n(n: u64) -> Vec<u64> {
    let mut divisors: Vec<u64> = Vec::new();
    let p_factors_n = prime_factors(n);
    let p_factors_n = p_factors_n
        .iter().map(|(p, _)| *p).collect::<Vec<u64>>();
    
    for p in p_factors_n {
        let mut i = 0;
        loop {
            let pow = p.pow(i);
            if n % pow == 0 {
                divisors.push(n / pow);
                divisors.push(pow);
                i += 1;
            } else {
                break;
            }
        }
    }
    divisors.sort();
    divisors.dedup();
    divisors
}

///
/// `euler_totient_phi_v1` calculates the phi value by counting the coprimes to n
/// 
pub fn euler_totient_phi_v1(n: u64) -> u64 {
    let coprimes = get_integers_coprime_n(n);
    return coprimes.len() as u64;
}

///
/// `euler_totient_phi` calculates the phi value using prime factorisation
/// 
pub fn euler_totient_phi(n: u64) -> u64 {
    let p_factors = prime_factors(n);
    let phi: u64 = p_factors.iter().map(|(p, a)| {
        (p - 1) * p.pow(*a as u32 - 1)
    }).product();
    phi
}

///
/// To find all primitive roots modulo n, we follow these steps: 
///
pub fn primitive_roots_trial_n_error(n: u64) -> Vec<u64> {
    let mut primitive_roots: Vec<u64> = Vec::new();
    let mut has_primitive_roots: bool = false;
    let phi_n = euler_totient_phi(n);
    // 
    let divisors_phi_n = divisors_of_n(phi_n);
    let nums_coprime_n: Vec<u64> = get_integers_coprime_n(n);

    for a in nums_coprime_n {
        let mut has_order_phi: bool = true;
        for order in divisors_phi_n.iter() {
            if modular_pow(a, *order, n) == 1 {
                if *order != phi_n {
                    has_order_phi = false;
                }
            } 
        }

        if has_order_phi {
            primitive_roots.push(a);
            has_primitive_roots = true;
            break;
        }
    }

    if has_primitive_roots {
        let orders_coprime_phi_n: Vec<u64> = get_integers_coprime_n(phi_n);
        // first coprime number is 1 and we are skipping that when calculating power
        for order in orders_coprime_phi_n.iter().skip(1) {
            primitive_roots.push(modular_pow(primitive_roots[0], *order, n));
        }
    }

    primitive_roots.sort();


    for (i, num) in primitive_roots.clone().iter().enumerate() {
        if *num == 1 {
            primitive_roots.remove(i);
            continue;
        }

        if modular_pow(*num, phi_n, n) != 1 {
            primitive_roots.remove(i);
        }
    }

    primitive_roots
}

/// It checks the existence of primitive roots modulo n 
/// an returns the number of primitive roots
pub fn primitive_roots_count_modulo_n(n: u64) -> u64 {
    let mut p_factors = prime_factors(n);
    if p_factors.len() < 1 || p_factors.len() > 2 {
        return 0;
    }

    match p_factors.len() {
        1 => {
            if let Some(first) = p_factors.pop() {
                match first.0 {
                    2 => if first.1 < 1 || first.1 > 2 {
                        return 0;
                    },
                    _ => {}
                } 
            }
        }
        2 => {
            let first = p_factors.remove(0);
            match first.0 {
                2 => {
                    if first.1 > 1 {
                        return 0;
                    }
                }
                _ => return 0,
            } 
        },
        _ => return 0,
    }
    let phi_n: u64 = euler_totient_phi(n);
    let phi_phi_n = euler_totient_phi(phi_n);
    phi_phi_n
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_gcd_euclid_1() {
        let result = gcd_euclid(100, 76, false);
        assert_eq!(result, 4);
    }

    #[test]
    fn test_get_integers_coprime_n_1() {
        let result = get_integers_coprime_n(10);
        assert_eq!(result, vec![1, 3, 7, 9]);
    }

    #[test]
    fn test_get_integers_coprime_n_2() {
        let result = get_integers_coprime_n(17);
        let s = (1..17).collect::<Vec<u64>>();
        assert_eq!(result, s);
    }

    #[test]
    fn test_modular_pow() {
        let result = modular_pow(2, 825, 173);
        assert_eq!(result, 107);
    }

    #[test]
    fn test_is_prime_1() {
        let result = is_prime(409);
        assert_eq!(result, true);
    }

    #[test]
    fn test_is_prime_2() {
        let result = is_prime(1363);
        assert_eq!(result, false);
        let result = is_prime(37909);
        assert_eq!(result, false);
        let result = is_prime(37949);
        assert_eq!(result, false);
        let result = is_prime(37979);
        assert_eq!(result, false);
    }

    #[test]
    fn test_miller_rabin_primality_1() {
        let result = miller_rabin_primality(409);
        assert_eq!(result, true);
    }

    #[test]
    fn test_miller_rabin_primality_2() {
        let result = miller_rabin_primality(511);
        assert_eq!(result, false);
        let result = miller_rabin_primality(721);
        assert_eq!(result, false);
    }

    #[test]
    fn test_prime_factors() {
        let result = prime_factors(100);
        assert_eq!(result, vec![(2, 2), (5, 2)]);
    }

    #[test]
    fn test_divisors_of_n() {
        let result = divisors_of_n(160);
        let d: Vec<u64> = vec![1, 2, 4, 5, 8, 10, 16, 20, 32, 40, 80, 160];
        assert_eq!(result, d);
    }

    #[test]
    fn test_euler_totient_phi_v1() {
        let result = euler_totient_phi_v1(378);
        assert_eq!(result, 108);

        let result = euler_totient_phi_v1(601);
        assert_eq!(result, 600);
    }

    #[test]
    fn test_euler_totient() {
        let result = euler_totient_phi(378);
        assert_eq!(result, 108);
    }

    #[test]
    fn test_primitive_roots_trial_n_error() {
        let result = primitive_roots_trial_n_error(25);
        assert_eq!(result, vec![2, 3, 8, 12, 13, 17, 22, 23])
    }

    #[test]
    fn test_primitive_roots_count_modulo_n() {
        let result = primitive_roots_count_modulo_n(1250);
        assert_eq!(result, 200);
        let result = primitive_roots_count_modulo_n(59);
        assert_eq!(result, 28);
        let result = primitive_roots_count_modulo_n(20);
        assert_eq!(result, 0);
        let result = primitive_roots_count_modulo_n(30);
        assert_eq!(result, 0);
        let result = primitive_roots_count_modulo_n(10);
        assert_eq!(result, 2);
        let result = primitive_roots_count_modulo_n(40);
        assert_eq!(result, 0);
    }
}

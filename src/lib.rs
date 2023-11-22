use rand::Rng;
use std::{ops::Range, collections::HashMap};

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

pub fn miller_rabin_primality(n: u64) -> bool {
    if n <= 1 || n == 4 {
        return false;
    }
    if n <= 3 {
        return true;
    }

    let mut d = n - 1;
    // Express n - 1 as 2^f.m
    while d % 2 == 0 {
        d = d >> 1;
    }

    for _ in 0..5 {
        if miller_test(d, n) == false {
            return false;
        }
    }

    true
}

fn miller_test(mut d: u64, n: u64) -> bool {
    let mut rng = rand::thread_rng();
    // Randomly generate a base: a such that 1 < a < n - 1
    let a: u64 = rng.gen_range(2..n - 1);
    let mut x = modular_pow(a, d, n);

    // if x ≡ ±1 (mod n), return true
    if x == 1 || x == n - 1 {
        return true;
    }
    
    // if x ≢ ±1 (mod n), while d != n-1 . 
    // d was obtained by repeated division of (m - 1) by 2.
    // multiplying it with 2 repeatedly until it equals (m - 1)
    while d != n - 1 {
        // sqaure x
        x = (x * x) % n;

        // if x ≡ -1 (mod n)
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
    let mut end_no: u64 = (n as f64).sqrt() as u64;
    if start_no == end_no {
        end_no += 1;
    }

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

pub fn euler_totient_phi(n: u64) -> u64 {
    let p_factors = prime_factors(n);
    let phi: u64 = p_factors.iter().map(|(p, a)| {
        (p - 1) * p.pow(*a as u32 - 1)
    }).product();
    phi
}

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
    fn test_modular_pow() {
        let result = modular_pow(2, 825, 173);
        assert_eq!(result, 107);
    }

    #[test]
    fn test_miller_rabin_primality_1() {
        let result = miller_rabin_primality(409);
        assert_eq!(result, true);
    }

    #[test]
    fn test_miller_rabin_primality_2() {
        let result = miller_rabin_primality(721);
        assert_eq!(result, false)
    }

    #[test]
    fn test_prime_factors() {
        let result = prime_factors(100);
        assert_eq!(result, vec![(2, 2), (5, 2)]);
    }

    #[test]
    fn test_euler_totient() {
        let result = euler_totient_phi(378);
        assert_eq!(result, 108);
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
    }
}

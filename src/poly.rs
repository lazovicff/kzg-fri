use bls12_381::Scalar;
use ff::{Field, PrimeField};
use rand::Rng;

use crate::utils::log2;

/// Represents a polynomial with coefficients in the scalar field
#[derive(Debug, Clone)]
pub struct Polynomial {
    /// Coefficients of the polynomial, where coeffs[i] is the coefficient of x^i
    pub coeffs: Vec<Scalar>,
}

impl Polynomial {
    /// Creates a new polynomial from coefficients
    ///
    /// # Arguments
    /// * `coeffs` - Vector of coefficients where coeffs[i] is the coefficient of x^i
    ///
    /// # Example
    /// ```
    /// use kzg::Polynomial;
    /// use bls12_381::Scalar;
    /// let poly = Polynomial::new(vec![
    ///     Scalar::from(3u64), // constant term
    ///     Scalar::from(2u64), // coefficient of x
    ///     Scalar::from(1u64), // coefficient of x^2
    /// ]);
    /// // This represents: f(x) = 3 + 2x + x^2
    /// ```
    pub fn new(coeffs: Vec<Scalar>) -> Self {
        Self { coeffs }
    }

    /// Creates a zero polynomial
    pub fn zero() -> Self {
        Self {
            coeffs: vec![Scalar::ZERO],
        }
    }

    /// Creates a random polynomial of given degree
    ///
    /// # Arguments
    /// * `degree` - Maximum degree of the polynomial
    /// * `rng` - Random number generator
    pub fn random<R: Rng>(degree: usize, rng: &mut R) -> Self {
        let mut coeffs = Vec::with_capacity(degree + 1);
        for _ in 0..=degree {
            coeffs.push(Scalar::random(&mut *rng));
        }
        Self { coeffs }
    }

    /// Returns the degree of the polynomial
    /// Returns 0 for the zero polynomial
    pub fn degree(&self) -> usize {
        if self.coeffs.is_empty() {
            return 0;
        }

        // Find the highest non-zero coefficient
        for i in (0..self.coeffs.len()).rev() {
            if self.coeffs[i] != Scalar::ZERO {
                return i;
            }
        }
        0
    }

    /// Evaluates the polynomial at a given point using Horner's method
    ///
    /// # Arguments
    /// * `x` - Point at which to evaluate the polynomial
    ///
    /// # Returns
    /// The value p(x)
    ///
    /// # Example
    /// ```
    /// use kzg::Polynomial;
    /// use bls12_381::Scalar;
    /// use ff::Field;
    /// // For polynomial 3 + 2x + x^2, evaluate at x = 5
    /// let poly = Polynomial::new(vec![
    ///     Scalar::from(3u64), // constant term
    ///     Scalar::from(2u64), // coefficient of x
    ///     Scalar::from(1u64), // coefficient of x^2
    /// ]);
    /// let result = poly.evaluate(&Scalar::from(5u64));
    /// assert_eq!(result, Scalar::from(38u64)); // 3 + 10 + 25 = 38
    /// ```
    pub fn evaluate(&self, x: &Scalar) -> Scalar {
        if self.coeffs.is_empty() {
            return Scalar::ZERO;
        }

        // Horner's method: p(x) = a_0 + x(a_1 + x(a_2 + x(...)))
        let mut result = self.coeffs[self.coeffs.len() - 1];
        for i in (0..self.coeffs.len() - 1).rev() {
            result = result * x + self.coeffs[i];
        }
        result
    }

    /// Adds two polynomials
    ///
    /// # Arguments
    /// * `other` - The polynomial to add
    ///
    /// # Returns
    /// A new polynomial representing the sum
    pub fn add(&self, other: &Polynomial) -> Polynomial {
        let max_len = self.coeffs.len().max(other.coeffs.len());
        let mut result_coeffs = Vec::with_capacity(max_len);

        for i in 0..max_len {
            let a = self.coeffs.get(i).copied().unwrap_or(Scalar::ZERO);
            let b = other.coeffs.get(i).copied().unwrap_or(Scalar::ZERO);
            result_coeffs.push(a + b);
        }

        Polynomial::new(result_coeffs)
    }

    /// Subtracts another polynomial from this one
    ///
    /// # Arguments
    /// * `other` - The polynomial to subtract
    ///
    /// # Returns
    /// A new polynomial representing the difference
    pub fn subtract(&self, other: &Polynomial) -> Polynomial {
        let max_len = self.coeffs.len().max(other.coeffs.len());
        let mut result_coeffs = Vec::with_capacity(max_len);

        for i in 0..max_len {
            let a = self.coeffs.get(i).copied().unwrap_or(Scalar::ZERO);
            let b = other.coeffs.get(i).copied().unwrap_or(Scalar::ZERO);
            result_coeffs.push(a - b);
        }

        Polynomial::new(result_coeffs)
    }

    /// Multiplies the polynomial by a scalar
    ///
    /// # Arguments
    /// * `scalar` - The scalar to multiply by
    ///
    /// # Returns
    /// A new polynomial representing the product
    pub fn multiply_scalar(&self, scalar: &Scalar) -> Polynomial {
        let result_coeffs: Vec<Scalar> = self.coeffs.iter().map(|coeff| *coeff * scalar).collect();

        Polynomial::new(result_coeffs)
    }

    /// Polynomial division by (x - point)
    /// Returns (quotient, remainder) where p(x) = quotient(x) * (x - point) + remainder
    ///
    /// This is used in KZG proofs to compute the witness polynomial
    ///
    /// # Arguments
    /// * `point` - The point to divide by (x - point)
    ///
    /// # Returns
    /// A tuple (quotient_polynomial, remainder_scalar)
    pub fn divide_by_linear(&self, point: &Scalar) -> (Polynomial, Scalar) {
        if self.coeffs.is_empty() {
            return (Polynomial::zero(), Scalar::ZERO);
        }

        let n = self.coeffs.len();
        if n == 1 {
            return (Polynomial::zero(), self.coeffs[0]);
        }

        // Synthetic division by (x - point)
        let mut quotient_coeffs = Vec::with_capacity(n - 1);
        let mut remainder = self.coeffs[n - 1];

        // Start from the highest degree coefficient
        quotient_coeffs.push(remainder);

        for i in (1..n).rev() {
            remainder = remainder * point + self.coeffs[i - 1];
            if i > 1 {
                quotient_coeffs.push(remainder);
            }
        }

        // Reverse the quotient coefficients since we built them backwards
        quotient_coeffs.reverse();

        let quotient = if quotient_coeffs.is_empty() {
            Polynomial::zero()
        } else {
            Polynomial::new(quotient_coeffs)
        };

        (quotient, remainder)
    }

    /// Creates a polynomial from its roots
    /// Constructs the polynomial (x - root1)(x - root2)...(x - rootn)
    ///
    /// # Arguments
    /// * `roots` - Vector of roots
    ///
    /// # Returns
    /// The polynomial having the given roots
    pub fn from_roots(roots: &[Scalar]) -> Polynomial {
        if roots.is_empty() {
            return Polynomial::new(vec![Scalar::ONE]);
        }

        // Start with (x - roots[0])
        let mut result = Polynomial::new(vec![-roots[0], Scalar::ONE]);

        // Multiply by (x - roots[i]) for each remaining root
        for &root in &roots[1..] {
            let linear_factor = Polynomial::new(vec![-root, Scalar::ONE]);
            result = result.multiply(&linear_factor);
        }

        result
    }

    /// Multiplies two polynomials
    ///
    /// # Arguments
    /// * `other` - The polynomial to multiply with
    ///
    /// # Returns
    /// A new polynomial representing the product
    pub fn multiply(&self, other: &Polynomial) -> Polynomial {
        if self.coeffs.is_empty() || other.coeffs.is_empty() {
            return Polynomial::zero();
        }

        let result_degree = self.coeffs.len() + other.coeffs.len() - 1;
        let mut result_coeffs = vec![Scalar::ZERO; result_degree];

        for (i, &a) in self.coeffs.iter().enumerate() {
            for (j, &b) in other.coeffs.iter().enumerate() {
                result_coeffs[i + j] += a * b;
            }
        }

        Polynomial::new(result_coeffs)
    }

    /// Lagrange interpolation to construct a polynomial from points
    /// Given points (x_i, y_i), constructs the unique polynomial of degree at most n-1
    /// that passes through all points
    ///
    /// # Arguments
    /// * `points` - Vector of (x, y) pairs
    ///
    /// # Returns
    /// The interpolating polynomial
    pub fn lagrange_interpolation(points: &[(Scalar, Scalar)]) -> Polynomial {
        if points.is_empty() {
            return Polynomial::zero();
        }

        if points.len() == 1 {
            return Polynomial::new(vec![points[0].1]);
        }

        let mut result = Polynomial::zero();

        for (i, &(x_i, y_i)) in points.iter().enumerate() {
            // Compute the i-th Lagrange basis polynomial L_i(x)
            let mut basis = Polynomial::new(vec![Scalar::ONE]);
            let mut denominator = Scalar::ONE;

            for (j, &(x_j, _)) in points.iter().enumerate() {
                if i != j {
                    // Multiply by (x - x_j)
                    let linear_factor = Polynomial::new(vec![-x_j, Scalar::ONE]);
                    basis = basis.multiply(&linear_factor);

                    // Update denominator with (x_i - x_j)
                    denominator *= x_i - x_j;
                }
            }

            // Scale by y_i / denominator
            let scale = y_i * denominator.invert().unwrap();
            basis = basis.multiply_scalar(&scale);

            // Add to result
            result = result.add(&basis);
        }

        result
    }

    /// Divides this polynomial by another polynomial
    /// Returns (quotient, remainder) where p(x) = quotient(x) * divisor(x) + remainder(x)
    ///
    /// # Arguments
    /// * `divisor` - The polynomial to divide by
    ///
    /// # Returns
    /// A tuple (quotient_polynomial, remainder_polynomial)
    pub fn divide(&self, divisor: &Polynomial) -> (Polynomial, Polynomial) {
        if divisor.coeffs.is_empty() || divisor.coeffs.iter().all(|&c| c == Scalar::ZERO) {
            panic!("Division by zero polynomial");
        }

        let dividend_degree = self.degree();
        let divisor_degree = divisor.degree();

        if dividend_degree < divisor_degree {
            return (Polynomial::zero(), self.clone());
        }

        let mut remainder = self.clone();
        let mut quotient_coeffs = vec![Scalar::ZERO; dividend_degree - divisor_degree + 1];

        // Get leading coefficient of divisor
        let divisor_leading = divisor.coeffs[divisor_degree];

        while remainder.degree() >= divisor_degree
            && !remainder.coeffs.iter().all(|&c| c == Scalar::ZERO)
        {
            let remainder_degree = remainder.degree();
            let remainder_leading = remainder.coeffs[remainder_degree];

            // Compute the next term of the quotient
            let coeff = remainder_leading * divisor_leading.invert().unwrap();
            let degree_diff = remainder_degree - divisor_degree;
            quotient_coeffs[degree_diff] = coeff;

            // Subtract coeff * x^degree_diff * divisor from remainder
            for (i, &divisor_coeff) in divisor.coeffs.iter().enumerate() {
                if i + degree_diff < remainder.coeffs.len() {
                    remainder.coeffs[i + degree_diff] -= coeff * divisor_coeff;
                }
            }

            // Remove leading zeros from remainder
            while remainder.coeffs.len() > 1
                && remainder.coeffs[remainder.coeffs.len() - 1] == Scalar::ZERO
            {
                remainder.coeffs.pop();
            }
        }

        let quotient = if quotient_coeffs.iter().all(|&c| c == Scalar::ZERO) {
            Polynomial::zero()
        } else {
            Polynomial::new(quotient_coeffs)
        };

        (quotient, remainder)
    }

    /// helper function to get the roots of unity of a polynomial
    pub fn get_omega(&self) -> Scalar {
        let mut coeffs = self.coeffs.to_vec();
        let n = coeffs.len() - 1;
        if !n.is_power_of_two() {
            let num_coeffs = coeffs.len().checked_next_power_of_two().unwrap();
            // pad the coefficients with zeros to the nearest power of two
            for i in coeffs.len()..num_coeffs {
                coeffs[i] = Scalar::ZERO;
            }
        }

        let m = coeffs.len();
        let exp = log2(m);
        let mut omega = Scalar::ROOT_OF_UNITY;
        for _ in exp..Scalar::S {
            omega = omega.square();
        }
        omega
    }

    /// given a set of coefficients of a polynomial, evaluate at roots of unity domain
    pub fn get_evaluation_points(&self, omega: Scalar, blowup_factor: u64) -> Vec<Scalar> {
        let evaluation_size = self.coeffs.len() as u64 * blowup_factor;
        let mut evaluation_vec = vec![];
        for i in 0..evaluation_size {
            evaluation_vec.push(self.evaluate(&omega.pow(&[i, 0, 0, 0])));
        }

        evaluation_vec
    }

    /// helper function to fold a polynomial into its odd and even component and
    /// add them back up by multiplying the odd component with a random value
    pub fn fold(&self, random_value: Scalar) -> Polynomial {
        // collect the odd coefficients
        let odd_poly: Vec<Scalar> = self.coeffs.iter().skip(1).step_by(2).copied().collect();

        // collect the even coefficients
        let even_poly: Vec<Scalar> = self.coeffs.iter().step_by(2).copied().collect();

        // we assume that poly will always be of degree 2^n, so number of coefficients will be even
        // odd_poly and even_poly has the same number of coefficients
        let folded_poly = even_poly
            .into_iter()
            .zip(odd_poly)
            .map(|(even_coeff, odd_coeff)| even_coeff + random_value * odd_coeff)
            .collect();

        Self::new(folded_poly)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // BLS12_381 curve uses a prime field
    #[test]
    fn test_fold_polynomial() {
        // create a simple polynomial with coefficients in Fp64
        let poly: Polynomial = Polynomial::new(vec![
            Scalar::from(1), // x^0
            Scalar::from(2), // x^1
            Scalar::from(3), // x^2
            Scalar::from(4), // x^3
        ]);

        let random_value = Scalar::from(5);

        let folded = poly.fold(random_value);

        // for polynomial 1 + 2x + 3x^2 + 4x^3
        // even coefficients are [1, 3]
        // odd coefficients are [2, 4]
        // after folding with random value r:
        // result should be [(1 + 5*2), (3 + 5*4)]
        assert_eq!(folded.coeffs.len(), 2);
        assert_eq!(folded.coeffs[0], Scalar::from(11));
        assert_eq!(folded.coeffs[1], Scalar::from(23));
    }
}

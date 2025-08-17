//! # Sumcheck Protocol Implementation
//!
//! This module implements the sumcheck protocol, an interactive proof system
//! that allows a prover to convince a verifier that the sum of a multivariate
//! polynomial over all vertices of the boolean hypercube {0,1}^n equals a
//! claimed value.
//!
//! ## Protocol Overview
//!
//! Given a multivariate polynomial f(x₁, x₂, ..., xₙ) and a claimed sum S,
//! the protocol works as follows:
//!
//! 1. **Prover claims**: ∑_{x∈{0,1}ⁿ} f(x) = S
//! 2. **Round i (for i = 1 to n)**:
//!    - Prover sends gᵢ(X) = ∑_{xᵢ₊₁,...,xₙ∈{0,1}ⁿ⁻ⁱ} f(r₁, ..., rᵢ₋₁, X, xᵢ₊₁, ..., xₙ)
//!    - Verifier checks gᵢ(0) + gᵢ(1) = expected sum from previous round
//!    - Verifier sends random challenge rᵢ ← F
//! 3. **Final check**: Evaluate f(r₁, ..., rₙ) and verify against gₙ(rₙ)
//!
//! ## Security
//!
//! The protocol is sound: if the claimed sum is incorrect, a cheating prover
//! will be caught with high probability. The soundness error is at most
//! d·n/|F| where d is the degree and |F| is the field size.
//!
//! ## Example Usage
//!
//! ```rust
//! use bls12_381::Scalar;
//! use ff::Field;
//!
//! // Create a 2-variable polynomial with evaluations [1, 2, 3, 4]
//! let evaluations = vec![
//!     Scalar::from(1u64), // f(0,0) = 1
//!     Scalar::from(2u64), // f(0,1) = 2
//!     Scalar::from(3u64), // f(1,0) = 3
//!     Scalar::from(4u64), // f(1,1) = 4
//! ];
//! let poly = MultivariatePolynomial::new(2, evaluations);
//! let claimed_sum = poly.sum(); // 1 + 2 + 3 + 4 = 10
//!
//! // Run the protocol
//! let prover = SumcheckProver::new(poly.clone());
//! let mut verifier = SumcheckVerifier::new(2, claimed_sum);
//!
//! let mut rng = rand::thread_rng();
//! let (proof, challenges) = prover.prove_interactive(&mut verifier, &mut rng);
//! let is_valid = verifier.verify_final(&poly, &challenges);
//! assert!(is_valid);
//! ```

use crate::poly::{MultivariatePolynomial, Polynomial};
use bls12_381::Scalar;
use ff::Field;
use rand::Rng;

/// Sumcheck protocol proof
#[derive(Debug, Clone)]
pub struct SumcheckProof {
    /// Univariate polynomials sent in each round
    pub round_polynomials: Vec<Polynomial>,
    /// Final evaluation at the challenge point
    pub final_evaluation: Scalar,
}

/// Sumcheck prover state for interactive protocol
pub struct SumcheckProver {
    /// The original multivariate polynomial
    original_polynomial: MultivariatePolynomial,
    /// Current polynomial state (gets reduced each round)
    current_polynomial: MultivariatePolynomial,
    /// Round number (0-indexed)
    current_round: usize,
    /// Challenges received so far
    challenges: Vec<Scalar>,
}

impl SumcheckProver {
    /// Creates a new sumcheck prover
    pub fn new(polynomial: MultivariatePolynomial) -> Self {
        Self {
            current_polynomial: polynomial.clone(),
            original_polynomial: polynomial,
            current_round: 0,
            challenges: Vec::new(),
        }
    }

    /// Generates the next round polynomial
    pub fn next_round(&mut self) -> Option<Polynomial> {
        if self.current_round >= self.original_polynomial.num_vars {
            return None;
        }

        let round_poly = self.compute_round_polynomial();
        self.current_round += 1;
        Some(round_poly)
    }

    /// Receives a challenge and updates the polynomial state
    pub fn receive_challenge(&mut self, challenge: Scalar) {
        if self.challenges.len() >= self.original_polynomial.num_vars {
            return;
        }

        self.challenges.push(challenge);

        // Partially evaluate the current polynomial
        if self.current_polynomial.num_vars > 0 {
            self.current_polynomial = self.partial_evaluation(challenge);
        }
    }

    /// Gets the final evaluation at all challenge points
    pub fn final_evaluation(&self) -> Scalar {
        if self.challenges.len() == self.original_polynomial.num_vars {
            self.original_polynomial.evaluate(&self.challenges)
        } else {
            Scalar::ZERO
        }
    }

    /// Non-interactive version: generates full proof with predetermined challenges
    pub fn prove(&self, _claimed_sum: Scalar, challenges: &[Scalar]) -> SumcheckProof {
        assert_eq!(challenges.len(), self.original_polynomial.num_vars);

        let mut round_polynomials = Vec::new();
        let mut current_poly = self.original_polynomial.clone();

        for &challenge in challenges {
            let round_poly = Self::compute_round_polynomial_static(&current_poly);
            round_polynomials.push(round_poly);

            if current_poly.num_vars > 0 {
                current_poly = Self::partial_evaluation_static(&current_poly, challenge);
            }
        }

        let final_evaluation = self.original_polynomial.evaluate(challenges);

        SumcheckProof {
            round_polynomials,
            final_evaluation,
        }
    }

    /// Interactive version: runs full protocol with verifier
    pub fn prove_interactive<R: Rng>(
        &self,
        verifier: &mut SumcheckVerifier,
        rng: &mut R,
    ) -> (SumcheckProof, Vec<Scalar>) {
        let mut prover_state = Self::new(self.original_polynomial.clone());
        let mut round_polynomials = Vec::new();
        let mut challenges = Vec::new();

        for _ in 0..self.original_polynomial.num_vars {
            // Prover sends round polynomial
            let round_poly = prover_state.next_round().unwrap();

            // Verifier checks and generates challenge
            let challenge = verifier.verify_round(&round_poly, rng);
            if challenge.is_none() {
                // Verification failed
                break;
            }
            let challenge = challenge.unwrap();

            round_polynomials.push(round_poly);
            challenges.push(challenge);

            // Prover receives challenge
            prover_state.receive_challenge(challenge);
        }

        let final_evaluation = prover_state.final_evaluation();

        let proof = SumcheckProof {
            round_polynomials,
            final_evaluation,
        };

        (proof, challenges)
    }

    /// Computes the univariate polynomial for the current round
    fn compute_round_polynomial(&self) -> Polynomial {
        Self::compute_round_polynomial_static(&self.current_polynomial)
    }

    /// Static version of round polynomial computation
    fn compute_round_polynomial_static(poly: &MultivariatePolynomial) -> Polynomial {
        if poly.num_vars == 0 {
            return Polynomial::new(vec![poly.evaluations[0]]);
        }

        // Sum evaluations where the first variable is 0 and where it's 1
        let mut sum_at_0 = Scalar::ZERO;
        let mut sum_at_1 = Scalar::ZERO;

        let half_size = poly.evaluations.len() / 2;

        // First half: evaluations where first variable = 0
        // Second half: evaluations where first variable = 1
        for i in 0..half_size {
            sum_at_0 += poly.evaluations[i];
            sum_at_1 += poly.evaluations[i + half_size];
        }

        // Return linear polynomial: sum_at_0 * (1-X) + sum_at_1 * X
        // = sum_at_0 + (sum_at_1 - sum_at_0) * X
        Polynomial::new(vec![sum_at_0, sum_at_1 - sum_at_0])
    }

    /// Partially evaluates the polynomial at the given value for the first variable
    fn partial_evaluation(&self, value: Scalar) -> MultivariatePolynomial {
        Self::partial_evaluation_static(&self.current_polynomial, value)
    }

    /// Static version of partial evaluation
    fn partial_evaluation_static(
        poly: &MultivariatePolynomial,
        value: Scalar,
    ) -> MultivariatePolynomial {
        if poly.num_vars == 0 {
            return poly.clone();
        }

        if poly.num_vars == 1 {
            let eval0 = poly.evaluations[0];
            let eval1 = poly.evaluations[1];
            let result = eval0 * (Scalar::ONE - value) + eval1 * value;
            return MultivariatePolynomial::new(0, vec![result]);
        }

        let mut new_evaluations = Vec::new();
        let half_size = poly.evaluations.len() / 2;

        for i in 0..half_size {
            // Linear interpolation between f(...,0,...) and f(...,1,...)
            let val = poly.evaluations[i] * (Scalar::ONE - value)
                + poly.evaluations[i + half_size] * value;
            new_evaluations.push(val);
        }

        MultivariatePolynomial::new(poly.num_vars - 1, new_evaluations)
    }
}

/// Sumcheck verifier
pub struct SumcheckVerifier {
    /// Number of variables in the polynomial
    num_vars: usize,
    /// Claimed sum
    claimed_sum: Scalar,
    /// Current round (0-indexed)
    current_round: usize,
    /// Expected sum for current round
    expected_sum: Scalar,
    /// Challenges sent so far
    challenges: Vec<Scalar>,
}

impl SumcheckVerifier {
    /// Creates a new sumcheck verifier
    pub fn new(num_vars: usize, claimed_sum: Scalar) -> Self {
        Self {
            num_vars,
            claimed_sum,
            current_round: 0,
            expected_sum: claimed_sum,
            challenges: Vec::new(),
        }
    }

    /// Verifies a round polynomial and returns a challenge
    pub fn verify_round<R: Rng>(&mut self, round_poly: &Polynomial, rng: &mut R) -> Option<Scalar> {
        if self.current_round >= self.num_vars {
            return None;
        }

        // Check that g_i(0) + g_i(1) equals the expected sum
        let sum_at_endpoints =
            round_poly.evaluate(&Scalar::ZERO) + round_poly.evaluate(&Scalar::ONE);

        if sum_at_endpoints != self.expected_sum {
            return None; // Verification failed
        }

        // Generate random challenge
        let challenge = Scalar::random(&mut *rng);
        self.challenges.push(challenge);

        // Update expected sum for next round
        self.expected_sum = round_poly.evaluate(&challenge);
        self.current_round += 1;

        Some(challenge)
    }

    /// Final verification: check that the polynomial evaluation matches
    pub fn verify_final(&self, polynomial: &MultivariatePolynomial, challenges: &[Scalar]) -> bool {
        if challenges.len() != self.num_vars {
            return false;
        }

        let actual_evaluation = polynomial.evaluate(challenges);
        actual_evaluation == self.expected_sum
    }

    /// Non-interactive verification with predetermined challenges
    pub fn verify_with_challenges(&self, proof: SumcheckProof, challenges: &[Scalar]) -> bool {
        if proof.round_polynomials.len() != self.num_vars {
            return false;
        }

        if challenges.len() != self.num_vars {
            return false;
        }

        let mut expected_sum = self.claimed_sum;

        for (round, round_poly) in proof.round_polynomials.iter().enumerate() {
            // Check that g_i(0) + g_i(1) equals the expected sum from previous round
            let sum_at_endpoints =
                round_poly.evaluate(&Scalar::ZERO) + round_poly.evaluate(&Scalar::ONE);

            if sum_at_endpoints != expected_sum {
                return false;
            }

            // Update expected sum for next round using the challenge
            expected_sum = round_poly.evaluate(&challenges[round]);
        }

        // Final check: verify that the final evaluation matches
        proof.final_evaluation == expected_sum
    }

    /// Full non-interactive verification
    pub fn verify<R: Rng>(
        &self,
        proof: SumcheckProof,
        polynomial: &MultivariatePolynomial,
        rng: &mut R,
    ) -> bool {
        if proof.round_polynomials.len() != self.num_vars {
            return false;
        }

        let mut expected_sum = self.claimed_sum;
        let mut challenges = Vec::new();

        for round_poly in proof.round_polynomials.iter() {
            // Check that g_i(0) + g_i(1) equals the expected sum from previous round
            let sum_at_endpoints =
                round_poly.evaluate(&Scalar::ZERO) + round_poly.evaluate(&Scalar::ONE);

            if sum_at_endpoints != expected_sum {
                return false;
            }

            // Generate random challenge
            let challenge = Scalar::random(&mut *rng);
            challenges.push(challenge);

            // Update expected sum for next round
            expected_sum = round_poly.evaluate(&challenge);
        }

        // Final check: verify polynomial evaluation
        let actual_evaluation = polynomial.evaluate(&challenges);
        actual_evaluation == expected_sum && actual_evaluation == proof.final_evaluation
    }

    /// Reset verifier state
    pub fn reset(&mut self, claimed_sum: Scalar) {
        self.claimed_sum = claimed_sum;
        self.current_round = 0;
        self.expected_sum = claimed_sum;
        self.challenges.clear();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::thread_rng;

    #[test]
    fn test_multivariate_polynomial_evaluation() {
        // Test with a simple 2-variable polynomial
        // f(x1, x2) = x1 + x2 (multilinear extension)
        let evaluations = vec![
            Scalar::ZERO,       // f(0,0) = 0
            Scalar::ONE,        // f(0,1) = 1
            Scalar::ONE,        // f(1,0) = 1
            Scalar::from(2u64), // f(1,1) = 2
        ];
        let poly = MultivariatePolynomial::new(2, evaluations);

        // Test boolean evaluations
        assert_eq!(poly.evaluate_boolean(&[false, false]), Scalar::ZERO);
        assert_eq!(poly.evaluate_boolean(&[false, true]), Scalar::ONE);
        assert_eq!(poly.evaluate_boolean(&[true, false]), Scalar::ONE);
        assert_eq!(poly.evaluate_boolean(&[true, true]), Scalar::from(2u64));

        // Test arbitrary evaluations
        let point = vec![Scalar::from(2u64), Scalar::from(3u64)];
        let result = poly.evaluate(&point);
        // f(2,3) should be 2 + 3 = 5 for the multilinear extension
        assert_eq!(result, Scalar::from(5u64));
    }

    #[test]
    fn test_sumcheck_protocol_simple() {
        // Create a simple 2-variable polynomial
        let evaluations = vec![
            Scalar::from(1u64), // f(0,0) = 1
            Scalar::from(2u64), // f(0,1) = 2
            Scalar::from(3u64), // f(1,0) = 3
            Scalar::from(4u64), // f(1,1) = 4
        ];
        let poly = MultivariatePolynomial::new(2, evaluations);
        let claimed_sum = poly.sum(); // 1 + 2 + 3 + 4 = 10

        // Generate challenges
        let challenges = vec![Scalar::from(5u64), Scalar::from(7u64)];

        // Run sumcheck protocol
        let prover = SumcheckProver::new(poly.clone());
        let proof = prover.prove(claimed_sum, &challenges);

        let verifier = SumcheckVerifier::new(2, claimed_sum);
        let is_valid = verifier.verify_with_challenges(proof, &challenges);

        assert!(is_valid);
    }

    #[test]
    fn test_sumcheck_protocol_interactive() {
        let mut rng = thread_rng();

        // Create a simple polynomial
        let evaluations = vec![
            Scalar::from(1u64),
            Scalar::from(2u64),
            Scalar::from(3u64),
            Scalar::from(4u64),
        ];
        let poly = MultivariatePolynomial::new(2, evaluations);
        let claimed_sum = poly.sum();

        // Run interactive protocol
        let prover = SumcheckProver::new(poly.clone());
        let mut verifier = SumcheckVerifier::new(2, claimed_sum);

        let (_proof, challenges) = prover.prove_interactive(&mut verifier, &mut rng);
        let is_valid = verifier.verify_final(&poly, &challenges);

        assert!(is_valid);
    }

    #[test]
    fn test_sumcheck_protocol_random() {
        let mut rng = thread_rng();
        let num_vars = 3;

        // Create a random polynomial
        let poly = MultivariatePolynomial::random(num_vars, &mut rng);
        let claimed_sum = poly.sum();

        // Generate random challenges
        let challenges: Vec<Scalar> = (0..num_vars).map(|_| Scalar::random(&mut rng)).collect();

        // Run sumcheck protocol
        let prover = SumcheckProver::new(poly.clone());
        let proof = prover.prove(claimed_sum, &challenges);

        let verifier = SumcheckVerifier::new(num_vars, claimed_sum);
        let is_valid = verifier.verify_with_challenges(proof, &challenges);

        assert!(is_valid);
    }

    #[test]
    fn test_sumcheck_protocol_wrong_sum() {
        // Create a simple polynomial
        let evaluations = vec![
            Scalar::from(1u64),
            Scalar::from(2u64),
            Scalar::from(3u64),
            Scalar::from(4u64),
        ];
        let poly = MultivariatePolynomial::new(2, evaluations);
        let wrong_sum = Scalar::from(100u64); // Wrong claimed sum

        let challenges = vec![Scalar::from(5u64), Scalar::from(7u64)];

        // Run sumcheck protocol with wrong sum
        let prover = SumcheckProver::new(poly.clone());
        let proof = prover.prove(poly.sum(), &challenges); // Prover uses correct sum

        let verifier = SumcheckVerifier::new(2, wrong_sum); // Verifier has wrong sum
        let is_valid = verifier.verify_with_challenges(proof, &challenges);

        // Should fail because the claimed sum is wrong
        assert!(!is_valid);
    }

    #[test]
    fn test_partial_evaluation() {
        // Test partial evaluation on a 2-variable polynomial
        let evaluations = vec![
            Scalar::from(1u64), // f(0,0) = 1
            Scalar::from(2u64), // f(0,1) = 2
            Scalar::from(3u64), // f(1,0) = 3
            Scalar::from(4u64), // f(1,1) = 4
        ];
        let poly = MultivariatePolynomial::new(2, evaluations);

        // Partially evaluate at x1 = 0.5
        let partial = SumcheckProver::partial_evaluation_static(
            &poly,
            Scalar::from(5u64).invert().unwrap() * Scalar::from(2u64).invert().unwrap(),
        ); // 0.5

        // Should result in a 1-variable polynomial
        assert_eq!(partial.num_vars, 1);
        assert_eq!(partial.evaluations.len(), 2);
    }

    #[test]
    fn test_round_polynomial_computation() {
        // Test round polynomial computation
        let evaluations = vec![
            Scalar::from(1u64), // f(0,0) = 1
            Scalar::from(2u64), // f(0,1) = 2
            Scalar::from(3u64), // f(1,0) = 3
            Scalar::from(4u64), // f(1,1) = 4
        ];
        let poly = MultivariatePolynomial::new(2, evaluations);

        let round_poly = SumcheckProver::compute_round_polynomial_static(&poly);

        // g(0) should be f(0,0) + f(0,1) = 1 + 2 = 3
        // g(1) should be f(1,0) + f(1,1) = 3 + 4 = 7
        assert_eq!(round_poly.evaluate(&Scalar::ZERO), Scalar::from(3u64));
        assert_eq!(round_poly.evaluate(&Scalar::ONE), Scalar::from(7u64));

        // Sum should be 3 + 7 = 10, which equals the total sum
        assert_eq!(
            round_poly.evaluate(&Scalar::ZERO) + round_poly.evaluate(&Scalar::ONE),
            poly.sum()
        );
    }

    #[test]
    fn test_single_variable_polynomial() {
        let evaluations = vec![Scalar::from(5u64), Scalar::from(7u64)];
        let poly = MultivariatePolynomial::new(1, evaluations);

        // Test evaluation
        assert_eq!(poly.evaluate(&[Scalar::ZERO]), Scalar::from(5u64));
        assert_eq!(poly.evaluate(&[Scalar::ONE]), Scalar::from(7u64));

        // Test sum
        assert_eq!(poly.sum(), Scalar::from(12u64));

        // Test round polynomial
        let round_poly = SumcheckProver::compute_round_polynomial_static(&poly);
        assert_eq!(round_poly.evaluate(&Scalar::ZERO), Scalar::from(5u64));
        assert_eq!(round_poly.evaluate(&Scalar::ONE), Scalar::from(7u64));
    }

    #[test]
    fn test_zero_variable_polynomial() {
        let evaluations = vec![Scalar::from(42u64)];
        let poly = MultivariatePolynomial::new(0, evaluations);

        assert_eq!(poly.evaluate(&[]), Scalar::from(42u64));
        assert_eq!(poly.sum(), Scalar::from(42u64));
    }
}

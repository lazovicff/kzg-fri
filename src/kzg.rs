use crate::poly;
use bls12_381::{G1Affine, G1Projective, G2Affine, G2Projective, Scalar};
use ff::Field;
use group::Curve;
use poly::Polynomial;
use rand::Rng;

#[derive(Debug, Clone)]
pub struct Proof(pub G1Affine);

#[derive(Debug, Clone)]
pub struct KZGTrustedSetup {
    pub srs_g1: Vec<G1Affine>,
    pub srs_g2: Vec<G2Affine>,
    pub max_degree: usize,
}

impl KZGTrustedSetup {
    pub fn new<R: Rng>(max_degree: usize, rng: R) -> Self {
        let tau = Scalar::random(rng);
        let g1 = G1Projective::generator();
        let mut srs_g1 = Vec::with_capacity(max_degree + 1);
        let mut tau_power = Scalar::ONE;

        for _ in 0..=max_degree {
            srs_g1.push((g1 * tau_power).to_affine());
            tau_power *= tau;
        }

        let g2 = G2Projective::generator();
        let mut srs_g2 = Vec::with_capacity(max_degree + 1);
        tau_power = Scalar::ONE;

        for _ in 0..=max_degree {
            srs_g2.push((g2 * tau_power).to_affine());
            tau_power *= tau;
        }

        Self {
            srs_g1,
            srs_g2,
            max_degree,
        }
    }
}

pub struct KZGProver {
    setup: KZGTrustedSetup,
}

impl KZGProver {
    pub fn new(setup: KZGTrustedSetup) -> Self {
        Self { setup }
    }

    pub fn commit(&self, polynomial: &Polynomial) -> G1Affine {
        if polynomial.degree() > self.setup.max_degree {
            panic!(
                "Polynomial degree {} exceeds maximum degree {}",
                polynomial.degree(),
                self.setup.max_degree
            );
        }

        let mut commitment = G1Projective::identity();

        for (i, &coeff) in polynomial.coeffs.iter().enumerate() {
            if coeff != Scalar::ZERO {
                commitment += self.setup.srs_g1[i] * coeff;
            }
        }

        commitment.to_affine()
    }

    pub fn prove(&self, polynomial: &Polynomial, challenge: &Scalar) -> Proof {
        let value = polynomial.evaluate(challenge);

        // Create polynomial p(x) - y
        let mut adjusted_coeffs = polynomial.coeffs.clone();
        if adjusted_coeffs.is_empty() {
            adjusted_coeffs.push(-value);
        } else {
            adjusted_coeffs[0] -= value;
        }
        let adjusted_poly = Polynomial::new(adjusted_coeffs);

        // Compute quotient polynomial q(x) = (p(x) - y) / (x - z)
        // where x is the polynomial variable and z is the evaluation point
        let (quotient, remainder) = adjusted_poly.divide_by_linear(challenge);

        // The remainder should be zero if our evaluation is correct
        assert_eq!(remainder, Scalar::ZERO, "Division remainder should be zero");

        // Create proof: π = q(τ) * g1
        Proof(self.commit(&quotient))
    }
}

pub struct KZGVerifier {
    setup: KZGTrustedSetup,
}

impl KZGVerifier {
    pub fn new(setup: KZGTrustedSetup) -> Self {
        Self { setup }
    }

    pub fn verify(
        &self,
        commitment: &G1Affine,
        challenge: &Scalar,
        value: &Scalar,
        proof: &Proof,
    ) -> bool {
        use bls12_381::pairing;

        // Compute p(τ)*g1 - y*g1 = (p(τ) - y)*g1
        let adjusted_commitment = G1Projective::from(commitment) - (value * self.setup.srs_g1[0]);

        // Compute τ*g2 - z*g2 = (τ - z)*g2
        let tau_minus_z =
            self.setup.srs_g2[1] - (G2Projective::from(self.setup.srs_g2[0]) * challenge);

        // Verify: e(C - y*g1, g2) = e(q(τ) * g1, (τ - z)*g2)
        let lhs = pairing(&adjusted_commitment.to_affine(), &self.setup.srs_g2[0]);
        let rhs = pairing(&proof.0, &tau_minus_z.to_affine());

        lhs == rhs
    }
}

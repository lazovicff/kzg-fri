use bls12_381::Scalar;

use crate::{merkle::MerkleTree, poly::Polynomial};

pub struct FRI {
    blowup_factor: u64,
    prover: Prover,
    verifier: Verifier,
}

/// Items that need to be stored by the prover
pub struct Prover {
    // Initial polynomial and all the intermediate folded polynomials (in coefficient form)
    polys: Vec<Polynomial>,
    // Merkle trees constructed from initial polynomial and intermediate folder polynomials (in evaluation form)
    merkle_trees: Vec<MerkleTree>,
}

impl Default for Prover {
    fn default() -> Self {
        Self {
            polys: Vec::new(),
            merkle_trees: Vec::new(),
        }
    }
}

/// Items that need to be stored by the verifier
pub struct Verifier {
    // Random values that are sent to the prover during the commit phase (in reality this would be fiat shamir)
    random_values: Vec<Scalar>,
    // Commitments that are provided by the prover
    commitments: Vec<Scalar>,
}

impl Default for Verifier {
    fn default() -> Self {
        Self {
            random_values: Vec::new(),
            commitments: Vec::new(),
        }
    }
}

/// Each proof contains evaluation point at f(g), f(-g) and the merkle proof
#[derive(Debug)]

pub struct RoundProof {
    omega: Scalar,
    f_g: Scalar,
    f_negative_g: Scalar,
    merkle_path: Vec<Scalar>,
    index: u64,
}

impl FRI {
    pub fn new(blowup_factor: u64) -> Self {
        Self {
            blowup_factor,
            prover: Prover::default(),
            verifier: Verifier::default(),
        }
    }

    pub fn commit(&mut self, mut poly: Polynomial, random_values: Vec<Scalar>) -> Vec<Scalar> {
        // for a polynomial with length 2^n, it requires folding n times to get to a plaintext
        assert_eq!(
            2u32.pow(random_values.len() as u32),
            poly.coeffs.len() as u32
        );

        // vector that stores the commitment at each round
        let mut commitments: Vec<Scalar> = vec![];

        // vector that stores the initial polynomial and intermediate folded polynomials
        let mut polys: Vec<Polynomial> = vec![];

        // vector that stores the merkle tree for the initial polynomial and folded polynomials
        let mut merkle_trees: Vec<MerkleTree> = vec![];

        // roots of unity point
        let mut omega = poly.get_omega();

        // fold the polynomial until it's a constant polynomial
        let mut random_value_idx = 0;
        while poly.coeffs.len() > 1 {
            // at each round, commit to the merkle tree
            let eval_points = poly.get_evaluation_points(omega, self.blowup_factor);
            let merkle_tree = MerkleTree::new(eval_points);
            let merkle_root = merkle_tree.root;
            commitments.push(merkle_root);
            polys.push(poly.clone());
            merkle_trees.push(merkle_tree);

            poly = poly.fold(random_values[random_value_idx]);
            random_value_idx += 1;
            // evaluation points for the next round are used using the square of current roots of unity point
            omega = omega.pow(&[2, 0, 0, 0]);
        }

        // the final commitment is a plaintext
        assert_eq!(poly.coeffs.len(), 1);
        commitments.push(poly.coeffs[0]);

        // prover store the information needed
        self.prover = Prover {
            polys,
            merkle_trees,
        };

        // verifier stores the information needed
        self.verifier = Verifier {
            random_values,
            commitments: commitments.clone(),
        };

        commitments
    }

    pub fn query(&self, mut index: u64) -> Vec<RoundProof> {
        // when verifier passes the prover with an evaluation point (a point within the roots of unity)
        // the prover sends the proof for each round to the verifier
        let mut proofs = vec![];
        let mut omega = self.prover.polys[0].get_omega().pow(&[index, 0, 0, 0]);
        for (poly, merkle_tree) in self
            .prover
            .polys
            .iter()
            .zip(self.prover.merkle_trees.iter())
        {
            // handle cases where index is larger than the length of polynomial (needs to wrap around)
            if index >= poly.coeffs.len() as u64 {
                index = index % poly.coeffs.len() as u64;
            }

            // generate proof
            let proof = RoundProof {
                omega,
                f_g: poly.evaluate(&omega),
                f_negative_g: poly.evaluate(&omega.neg()),
                merkle_path: merkle_tree.get_merkle_path(index),
                index,
            };

            proofs.push(proof);

            // square the omega
            omega = omega.pow(&[2, 0, 0, 0]);
        }

        proofs
    }

    pub fn verify(&self, proofs: Vec<RoundProof>) -> bool {
        let mut i = 0;
        let mut previous_proof: Option<&RoundProof> = None;
        for (proof, commitment) in proofs.iter().zip(self.verifier.commitments.iter()) {
            // verify that the evaluation point matches the merkle commitment
            let merkle_root =
                MerkleTree::reconstruct_merkle_root(proof.f_g, &proof.merkle_path, proof.index);
            if &merkle_root != commitment {
                return false;
            }

            // check that the evaluation matches the evaluations of previous round
            match previous_proof {
                Some(prev_round) => {
                    // f1(x^2) = (x+r1)(f0(x))/2x + (r1-x)(f0(-x))/2(-x)
                    if proof.f_g
                        != (prev_round.omega + self.verifier.random_values[i - 1])
                            * (prev_round.f_g)
                            * (Scalar::from(2) * prev_round.omega).invert().unwrap()
                            + (self.verifier.random_values[i - 1] - prev_round.omega)
                                * (prev_round.f_negative_g)
                                * (Scalar::from(2) * -prev_round.omega).invert().unwrap()
                    {
                        return false;
                    }
                }
                None => {}
            }

            previous_proof = Some(proof);
            i += 1;
        }

        // check final plaintext commitment value
        let final_round = previous_proof.expect("final round proof must exist");
        let final_commitment = self
            .verifier
            .commitments
            .last()
            .expect("final commitment must exist")
            .to_owned();
        if final_commitment
            != (final_round.omega + self.verifier.random_values[i - 1])
                * (final_round.f_g)
                * (Scalar::from(2) * final_round.omega).invert().unwrap()
                + (self.verifier.random_values[i - 1] - final_round.omega)
                    * (final_round.f_negative_g)
                    * (Scalar::from(2) * -final_round.omega).invert().unwrap()
        {
            return false;
        }

        true
    }
}

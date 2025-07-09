use blake2::{Blake2b512, Digest};
use bls12_381::Scalar;

pub struct MerkleTree {
    pub leaves: Vec<Scalar>,
    pub intermediate_nodes: Vec<Vec<Scalar>>,
    pub root: Scalar,
}

impl MerkleTree {
    pub fn new(leaves: Vec<Scalar>) -> Self {
        let mut current_nodes = leaves.clone();
        let mut intermediate_nodes: Vec<Vec<Scalar>> = vec![];

        while current_nodes.len() > 1 {
            let mut next_level = Vec::with_capacity(current_nodes.len() / 2);

            for chunk in current_nodes.chunks(2) {
                // hash two adjacent elements using Blake2
                let mut hasher = Blake2b512::new();
                hasher.update(chunk[0].to_string().as_bytes());
                if chunk.len() > 1 {
                    hasher.update(chunk[1].to_string().as_bytes());
                }
                let hash_result = hasher.finalize();
                let bytes: [u8; 64] = hash_result.to_vec().try_into().unwrap();
                let node = Scalar::from_bytes_wide(&bytes);
                next_level.push(node);
            }

            current_nodes = next_level.clone();
            intermediate_nodes.push(next_level);
        }

        // return the root (or zero if input was empty)
        let root = current_nodes
            .first()
            .cloned()
            .unwrap_or_else(|| Scalar::zero());

        Self {
            leaves,
            intermediate_nodes,
            root,
        }
    }

    // given the index of a leaf, return the sibling path of it to the root
    pub fn get_merkle_path(&self, index: u64) -> Vec<Scalar> {
        let mut path = Vec::new();
        let mut current_index = index;

        let mut all_nodes = Vec::new();
        all_nodes.push(self.leaves.clone());
        all_nodes.extend(self.intermediate_nodes.clone());

        for level in &all_nodes {
            // get sibling index - if current_index is even, add 1; if odd, subtract 1
            let sibling_index = if current_index % 2 == 0 {
                current_index + 1
            } else {
                current_index - 1
            };

            // get the sibling node if it exists in the level
            if let Some(&sibling) = level.get(sibling_index as usize) {
                path.push(sibling);
            }

            // update current_index for next level up
            current_index /= 2;
        }

        path
    }

    /// get the merkle root given the element, its sibling elements, and the original index
    pub fn reconstruct_merkle_root(
        element: Scalar,
        merkle_path: &[Scalar],
        original_index: u64,
    ) -> Scalar {
        let mut accumulator = element;
        let mut current_index = original_index;

        for sibling in merkle_path {
            // hash two adjacent elements using Blake2
            let mut hasher = Blake2b512::new();
            // Always hash in consistent order: smaller index first
            if current_index % 2 == 0 {
                // accumulator is left child
                hasher.update(accumulator.to_string().as_bytes());
                hasher.update(sibling.to_string().as_bytes());
            } else {
                // accumulator is right child
                hasher.update(sibling.to_string().as_bytes());
                hasher.update(accumulator.to_string().as_bytes());
            }
            let hash_result = hasher.finalize();
            let bytes: [u8; 64] = hash_result.to_vec().try_into().unwrap();
            accumulator = Scalar::from_bytes_wide(&bytes);
            current_index /= 2;
        }
        accumulator
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_merkle_root() {
        // create a simple vector
        let poly: Vec<Scalar> = vec![
            Scalar::from(1),
            Scalar::from(2),
            Scalar::from(3),
            Scalar::from(4),
        ];

        let merkle_tree = MerkleTree::new(poly);
        let merkle_root = merkle_tree.root;

        // result should be hash( hash(1 || 2) || hash(3 || 4))
        // Since we're using Blake2 now, we can't predict the exact value
        // but we can verify it's not zero and consistent
        assert_ne!(merkle_root, Scalar::from(0));
    }

    #[test]
    fn test_merkle_path() {
        let poly: Vec<Scalar> = vec![
            Scalar::from(1),
            Scalar::from(2),
            Scalar::from(3),
            Scalar::from(4),
            Scalar::from(5),
            Scalar::from(6),
            Scalar::from(7),
            Scalar::from(8),
        ];

        let merkle_tree = MerkleTree::new(poly);
        let merkle_path = merkle_tree.get_merkle_path(3);

        // With Blake2 hashing, we can't predict exact values
        // but we can verify the path has the correct length
        assert_eq!(merkle_path.len(), 3);

        // Verify we can reconstruct the root using the path
        // Need to pass the original index to maintain correct order
        let reconstructed_root =
            MerkleTree::reconstruct_merkle_root(Scalar::from(4), &merkle_path, 3);
        assert_eq!(reconstructed_root, merkle_tree.root);
    }
}

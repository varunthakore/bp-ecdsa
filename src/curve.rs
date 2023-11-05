// Equations defined for secp256k1: y^2 = x^3 + 7

use bellpepper::gadgets::num::AllocatedNum;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use ff::PrimeField;

pub struct AllocatedAffinePoint<F: PrimeField> {
    x: AllocatedNum<F>,
    y: AllocatedNum<F>,
}

impl<F: PrimeField> AllocatedAffinePoint<F> {
    pub fn alloc_affine_point<CS>(cs: &mut CS, x: F, y: F) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        // Check (x, y) on secp256k1
        let lhs = y.square();
        let rhs = x.square() * x + F::from(7u64);
        assert_eq!(lhs, rhs, "(x,y) not on secp256k1");

        let x_alloc = AllocatedNum::alloc(&mut cs.namespace(|| "alloc x"), || Ok(x))?;
        let y_alloc = AllocatedNum::alloc(&mut cs.namespace(|| "alloc y"), || Ok(y))?;

        Ok(AllocatedAffinePoint {
            x: x_alloc,
            y: y_alloc,
        })
    }

    pub fn add_incomplete<CS>(cs: &mut CS, p: Self, q: Self) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let dx = p.x.sub(&mut cs.namespace(|| "px-qx"), &q.x)?;
        let dy = p.y.sub(&mut cs.namespace(|| "py-qy"), &q.y)?;
        let lambda = dy.div(&mut cs.namespace(|| "dy by dx"), &dx)?;

        let outx = AllocatedNum::alloc(&mut cs.namespace(|| "output x"), || {
            let mut tmp = lambda
                .get_value()
                .ok_or(SynthesisError::AssignmentMissing)?;
            tmp.mul_assign(tmp);
            tmp.sub_assign(p.x.get_value().ok_or(SynthesisError::AssignmentMissing)?);
            tmp.sub_assign(q.x.get_value().ok_or(SynthesisError::AssignmentMissing)?);
            Ok(tmp)
        })?;
        cs.enforce(
            || "outx === lambda * lambda - px - qx",
            |lc| lc + lambda.get_variable(),
            |lc| lc + lambda.get_variable(),
            |lc| lc + outx.get_variable() + p.x.get_variable() + q.x.get_variable(),
        );

        let outy = AllocatedNum::alloc(&mut cs.namespace(|| "output y"), || {
            let mut other_tmp = p.x.get_value().ok_or(SynthesisError::AssignmentMissing)?;
            other_tmp.sub_assign(outx.get_value().ok_or(SynthesisError::AssignmentMissing)?);
            let mut tmp = lambda
                .get_value()
                .ok_or(SynthesisError::AssignmentMissing)?;
            tmp.mul_assign(other_tmp);
            tmp.sub_assign(p.y.get_value().ok_or(SynthesisError::AssignmentMissing)?);
            Ok(tmp)
        })?;
        cs.enforce(
            || "outY === lambda * (xP - outX) - yP",
            |lc| lc + lambda.get_variable(),
            |lc| lc + p.x.get_variable() - outx.get_variable(),
            |lc| lc + outy.get_variable() + p.y.get_variable(),
        );

        Ok(AllocatedAffinePoint { x: outx, y: outy })
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use bellpepper_core::test_cs::TestConstraintSystem;
    use halo2curves::secp256k1::{Fp, Secp256k1Affine};
    use rand_core::SeedableRng;
    use rand_xorshift::XorShiftRng;

    #[test]
    fn test_add_incomplete() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x3d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for _ in 0..100 {
            let mut cs = TestConstraintSystem::<Fp>::new();

            let p1 = Secp256k1Affine::random(&mut rng);
            let p2 = Secp256k1Affine::random(&mut rng);
            let add_exp: Secp256k1Affine = (p1 + p2).try_into().unwrap();

            let p1_alloc = AllocatedAffinePoint::alloc_affine_point(
                &mut cs.namespace(|| "alloc p1"),
                p1.x,
                p1.y,
            )
            .unwrap();
            let p2_alloc = AllocatedAffinePoint::alloc_affine_point(
                &mut cs.namespace(|| "alloc p2"),
                p2.x,
                p2.y,
            )
            .unwrap();
            let add_alloc = AllocatedAffinePoint::add_incomplete(
                &mut cs.namespace(|| "point1 + point2"),
                p1_alloc,
                p2_alloc,
            )
            .unwrap();

            assert!(cs.is_satisfied());
            assert_eq!(cs.num_constraints(), 5);
            assert_eq!(add_exp.x, add_alloc.x.get_value().unwrap());
            assert_eq!(add_exp.y, add_alloc.y.get_value().unwrap());
        }
    }
}

use bellpepper_core::{boolean::Boolean, ConstraintSystem, SynthesisError};
use crypto_bigint::U256;
use ff::{PrimeField, PrimeFieldBits};

use crate::curve::AllocatedAffinePoint;

pub fn verify_eff<F, CS>(
    cs: &mut CS,
    scalar: U256,
    t: AllocatedAffinePoint<F>,
    u: AllocatedAffinePoint<F>,
    pub_key: AllocatedAffinePoint<F>,
) -> Result<Boolean, SynthesisError>
where
    F: PrimeField<Repr = [u8; 32]> + PrimeFieldBits,
    CS: ConstraintSystem<F>,
{
    let s_t = t.scalar_mult(&mut cs.namespace(|| "calc s * T"), scalar)?;
    let pub_key_calc =
        AllocatedAffinePoint::add_complete(&mut cs.namespace(|| "s * T + U"), s_t, u)?;

    pub_key_calc.is_equal(&mut cs.namespace(|| "pub_key == s * T + U"), pub_key)
}

#[cfg(test)]
mod test {
    use super::*;
    use bellpepper_core::test_cs::TestConstraintSystem;
    use crypto_bigint::{Encoding, U256};
    use ff::Field;
    use halo2curves::secp256k1::{Fp, Fq, Secp256k1Affine};
    use rand::thread_rng;
    use std::ops::{Mul, Neg};

    fn sign(msg: Fq, priv_key: Fq) -> (Secp256k1Affine, Fq) {
        let mut rng = thread_rng();
        let n =
            U256::from_be_hex("fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141");
        let g = Secp256k1Affine::generator();

        let k = Fq::random(&mut rng);
        let k_inv = k.invert();
        assert!(bool::from(k_inv.is_some()));
        let k_inv = k_inv.unwrap();

        let r: Secp256k1Affine = g.mul(k).into();
        let r_x = Fq::from_repr(
            U256::from_le_bytes(r.x.to_bytes())
                .add_mod(&U256::ZERO, &n)
                .to_le_bytes(),
        );
        assert!(bool::from(r_x.is_some()));
        let r_x = r_x.unwrap();

        let s = k_inv * (msg + priv_key * r_x);

        (r, s)
    }

    fn get_points(r: Secp256k1Affine, msg: Fq) -> (Secp256k1Affine, Secp256k1Affine) {
        let n =
            U256::from_be_hex("fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141");

        let g = Secp256k1Affine::generator();

        let r_q = Fq::from_repr(
            U256::from_le_bytes(r.x.to_bytes())
                .add_mod(&U256::ZERO, &n)
                .to_le_bytes(),
        );
        assert!(bool::from(r_q.is_some()));
        let r_q = r_q.unwrap();

        let r_q_inv = r_q.invert();
        assert!(bool::from(r_q_inv.is_some()));
        let r_q_inv = r_q_inv.unwrap();

        let t: Secp256k1Affine = r.mul(r_q_inv).into();
        let u: Secp256k1Affine = g.mul(r_q_inv * msg).neg().into();

        (t, u)
    }

    fn verify(
        scalar: U256,
        t: Secp256k1Affine,
        u: Secp256k1Affine,
        pub_key: Secp256k1Affine,
    ) -> bool {
        let scalar = Fq::from_repr(scalar.to_le_bytes());
        assert!(bool::from(scalar.is_some()));
        let scalar = scalar.unwrap();

        let st: Secp256k1Affine = t.mul(scalar).into();
        let pub_key_calc: Secp256k1Affine = (st + u).into();

        let x_is_same = pub_key.x == pub_key_calc.x;
        let y_is_same = pub_key.y == pub_key_calc.y;

        x_is_same & y_is_same
    }

    #[test]
    fn test_verify_eff() {
        for _ in 0..100 {
            let mut rng = thread_rng();
            let g = Secp256k1Affine::generator();

            let msg = Fq::random(&mut rng);
            let priv_key = Fq::random(&mut rng);
            let (r, s) = sign(msg, priv_key);

            let pub_key: Secp256k1Affine = g.mul(priv_key).into();

            let (t, u) = get_points(r, msg);

            let mut cs = TestConstraintSystem::<Fp>::new();

            let pub_key_alloc = AllocatedAffinePoint::alloc_affine_point(
                &mut cs.namespace(|| "alloc pub key"),
                pub_key.x,
                pub_key.y,
            )
            .unwrap();

            let t_alloc =
                AllocatedAffinePoint::alloc_affine_point(&mut cs.namespace(|| "alloc t"), t.x, t.y)
                    .unwrap();
            let u_alloc =
                AllocatedAffinePoint::alloc_affine_point(&mut cs.namespace(|| "alloc u"), u.x, u.y)
                    .unwrap();

            let scalar = U256::from_le_bytes(s.to_bytes());

            let out = verify_eff(
                &mut cs.namespace(|| "verify"),
                scalar,
                t_alloc,
                u_alloc,
                pub_key_alloc,
            )
            .unwrap();
            let _ = Boolean::enforce_equal(
                &mut cs.namespace(|| "verify == true"),
                &out,
                &Boolean::constant(true),
            );

            let out_exp = verify(scalar, t, u, pub_key);
            assert!(out_exp == out.get_value().unwrap());

            assert!(cs.is_satisfied());
            assert_eq!(cs.num_constraints(), 3389);
        }
    }

    #[test]
    fn test_scalar_false() {
        for _ in 0..100 {
            let mut rng = thread_rng();
            let g = Secp256k1Affine::generator();

            let msg = Fq::random(&mut rng);
            let priv_key = Fq::random(&mut rng);
            let (r, _s) = sign(msg, priv_key);

            let pub_key: Secp256k1Affine = g.mul(priv_key).into();

            let (t, u) = get_points(r, msg);

            let mut cs = TestConstraintSystem::<Fp>::new();

            let pub_key_alloc = AllocatedAffinePoint::alloc_affine_point(
                &mut cs.namespace(|| "alloc pub key"),
                pub_key.x,
                pub_key.y,
            )
            .unwrap();

            let t_alloc =
                AllocatedAffinePoint::alloc_affine_point(&mut cs.namespace(|| "alloc t"), t.x, t.y)
                    .unwrap();
            let u_alloc =
                AllocatedAffinePoint::alloc_affine_point(&mut cs.namespace(|| "alloc u"), u.x, u.y)
                    .unwrap();

            let scalar = U256::from_le_bytes(Fq::random(&mut rng).to_bytes());

            let out = verify_eff(
                &mut cs.namespace(|| "verify"),
                scalar,
                t_alloc,
                u_alloc,
                pub_key_alloc,
            )
            .unwrap();
            let _ = Boolean::enforce_equal(
                &mut cs.namespace(|| "verify == true"),
                &out,
                &Boolean::constant(false),
            );

            let out_exp = verify(scalar, t, u, pub_key);
            assert!(out_exp == out.get_value().unwrap());

            assert!(cs.is_satisfied());
            assert_eq!(cs.num_constraints(), 3389);
        }
    }
}

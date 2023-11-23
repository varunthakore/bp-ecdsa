use bellpepper_core::{
    boolean::Boolean,
    ConstraintSystem, SynthesisError,
};
use crypto_bigint::U256;
use ff::{PrimeField, PrimeFieldBits};

use crate::curve::AllocatedAffinePoint;

pub fn verify_eff<F, CS>(
    cs: &mut CS, 
    scalar: U256,
    t: AllocatedAffinePoint<F>,
    u: AllocatedAffinePoint<F>,
    pub_key: AllocatedAffinePoint<F>
) -> Result<Boolean, SynthesisError>
where
    F: PrimeField<Repr = [u8; 32]> + PrimeFieldBits,
    CS: ConstraintSystem<F>,
{
    let s_t = t.scalar_mult( &mut cs.namespace(|| "calc s * T"), scalar)?;
    let pub_key_calc = AllocatedAffinePoint::add_complete(&mut cs.namespace(|| "s * T + U"), s_t, u)?;

    pub_key_calc.is_equal(&mut cs.namespace(|| "pub_key == s * T + U"), pub_key)
}


#[cfg(test)]
mod test {
    use super::*;
    use bellpepper_core::test_cs::TestConstraintSystem;
    use crypto_bigint::{Encoding, U256};
    use ff::Field;
    use halo2curves::{secp256k1::{Fp, Fq, Secp256k1Affine}, CurveAffine};
    use rand::thread_rng;
    use std::ops::{Mul, Neg};

    fn sign(msg: Fq, priv_key: Fq) -> (Fq, Fq) {
        let mut rng = thread_rng();
        let g = Secp256k1Affine::generator();
        
        let k = Fq::random(&mut rng);
        let k_inv = k.invert();
        assert!(bool::from(k_inv.is_some()));
        let k_inv = k_inv.unwrap();
        
        let r: Secp256k1Affine = g.mul(k).into();
        let r_x = Fq::from_repr(r.x.to_bytes());
        assert!(bool::from(r_x.is_some()));
        let r_x = r_x.unwrap();
        
        let s = k_inv * (msg + priv_key * r_x);

        (r_x, s)

    }

    fn get_points(rx: Fq, msg: Fq) -> (Secp256k1Affine, Secp256k1Affine) {
        let g = Secp256k1Affine::generator();

        let r_x = Fp::from_repr(rx.to_bytes());
        assert!(bool::from(r_x.is_some()));
        let r_x = r_x.unwrap();

        let r_y = (r_x.square() * r_x + Fp::from(7)).sqrt();
        assert!(bool::from(r_y.is_some()));
        let r_y = r_y.unwrap();
        let r = Secp256k1Affine::from_xy(r_x, r_y);
        assert!(bool::from(r.is_some()));
        let r = r.unwrap();

        let r_x_inv = Fq::from_repr(r_x.to_bytes()).unwrap().invert();
        assert!(bool::from(r_x_inv.is_some()));
        let r_x_inv = r_x_inv.unwrap();

        let t: Secp256k1Affine = r.mul(r_x_inv).into();
        let u: Secp256k1Affine = g.mul(r_x_inv * msg).neg().into();

        (t, u)        
    }

    #[test]
    fn test_verify_eff() {

        for _ in 0..100 {
            let mut rng = thread_rng();
            let g = Secp256k1Affine::generator();
    
            let msg = Fq::random(&mut rng);
            let priv_key = Fq::random(&mut rng);
            let (r_x, s) = sign(msg, priv_key);
    
            let pub_key: Secp256k1Affine = g.mul(priv_key).into();
    
            let (t, u) = get_points(r_x, msg);
    
            let mut cs = TestConstraintSystem::<Fp>::new();
            
            let pub_key_alloc = AllocatedAffinePoint::alloc_affine_point(
                &mut cs.namespace(|| "alloc pub key"), 
                pub_key.x, 
                pub_key.y
            ).unwrap();
    
            let t_alloc = AllocatedAffinePoint::alloc_affine_point(&mut cs.namespace(|| "alloc t"), t.x, t.y).unwrap();
            let u_alloc = AllocatedAffinePoint::alloc_affine_point(&mut cs.namespace(|| "alloc u"), u.x, u.y).unwrap();
    
            let scalar = U256::from_le_bytes(s.to_bytes());
    
            let verify = verify_eff(&mut cs.namespace(|| "verify"), scalar, t_alloc, u_alloc, pub_key_alloc).unwrap();
            let _ = Boolean::enforce_equal(&mut cs.namespace(|| "verify == true"), &verify, &Boolean::constant(true));
            assert!(cs.is_satisfied());
            assert_eq!(cs.num_constraints(), 3389);
        }

    }
}
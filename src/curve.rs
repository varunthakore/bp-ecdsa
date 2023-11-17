// Equations defined for secp256k1: y^2 = x^3 + 7

use bellpepper::gadgets::num::AllocatedNum;
use bellpepper_core::{
    boolean::{AllocatedBit, Boolean},
    ConstraintSystem, SynthesisError,
};
use ff::PrimeField;

#[derive(Clone)]
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
        if (lhs != F::ZERO) & (rhs != F::from(7u64)) {
            // assert only for points other than (0, 0)
            assert_eq!(lhs, rhs, "(x,y) not on secp256k1");
        }

        let x_alloc = AllocatedNum::alloc(&mut cs.namespace(|| "alloc x"), || Ok(x))?;
        let y_alloc = AllocatedNum::alloc(&mut cs.namespace(|| "alloc y"), || Ok(y))?;

        Ok(AllocatedAffinePoint {
            x: x_alloc,
            y: y_alloc,
        })
    }

    pub fn conditionally_select<CS>(
        cs: &mut CS,
        a: &Self,
        b: &Self,
        condition: &Boolean,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let x = AllocatedNum::conditionally_select(
            &mut cs.namespace(|| "allocate value of output x coordinate"),
            &a.x,
            &b.x,
            condition,
        )?;

        let y = AllocatedNum::conditionally_select(
            &mut cs.namespace(|| "allocate value of output y coordinate"),
            &a.y,
            &b.y,
            condition,
        )?;

        Ok(Self { x, y })
    }

    pub fn mux_tree<'a, CS>(
        cs: &mut CS,
        mut select_bits: impl Iterator<Item = &'a Boolean> + Clone,
        inputs: &[Self],
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        if let Some(bit) = select_bits.next() {
            if inputs.len() & 1 != 0 {
                return Err(SynthesisError::Unsatisfiable);
            }
            let left_half = &inputs[..(inputs.len() / 2)];
            let right_half = &inputs[(inputs.len() / 2)..];
            let left =
                Self::mux_tree(&mut cs.namespace(|| "left"), select_bits.clone(), left_half)?;
            let right = Self::mux_tree(&mut cs.namespace(|| "right"), select_bits, right_half)?;
            Self::conditionally_select(&mut cs.namespace(|| "join"), &left, &right, bit)
        } else {
            if inputs.len() != 1 {
                return Err(SynthesisError::Unsatisfiable);
            }
            Ok(inputs[0].clone())
        }
    }

    //This function only works for points where p.x != q.x and are not at infinity
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

    pub fn add_complete<CS>(cs: &mut CS, p: Self, q: Self) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let zero = AllocatedNum::alloc(&mut cs.namespace(|| "alloc zero"), || Ok(F::ZERO))?;

        let px_sq = p.x.square(&mut cs.namespace(|| "p.x * p.x"))?;

        let is_x_eq = p.x.is_equal(&mut cs.namespace(|| "p.x == q.x"), &q.x)?;

        let is_px_zero = p.x.is_zero(&mut cs.namespace(|| "p.x == 0"))?;
        let is_qx_zero = q.x.is_zero(&mut cs.namespace(|| "q.x == 0"))?;

        let is_either_x_zero = Boolean::or(
            &mut cs.namespace(|| "p.x==0 OR q.x==0"),
            &is_px_zero,
            &is_qx_zero,
        )?;

        let dx = q.x.sub(&mut cs.namespace(|| "qx-px"), &p.x)?;

        let dy = AllocatedNum::alloc(&mut cs.namespace(|| "alloc dy"), || {
            if is_x_eq
                .get_value()
                .ok_or(SynthesisError::AssignmentMissing)?
            {
                Ok(F::ZERO)
            } else {
                Ok(q.y.get_value().ok_or(SynthesisError::AssignmentMissing)?
                    - p.y.get_value().ok_or(SynthesisError::AssignmentMissing)?)
            }
        })?;
        cs.enforce(
            || "(q.y - p.y) * (1 - is_x_eq) === dy",
            |lc| lc + q.y.get_variable() - p.y.get_variable(),
            |lc| lc + CS::one() - &is_x_eq.lc(CS::one(), F::ONE),
            |lc| lc + dy.get_variable(),
        );

        let lambda_a = AllocatedNum::alloc(&mut cs.namespace(|| "alloc lambda_a"), || {
            if is_x_eq
                .get_value()
                .ok_or(SynthesisError::AssignmentMissing)?
            {
                Ok(F::ZERO)
            } else {
                let dx_val = dx.get_value().ok_or(SynthesisError::AssignmentMissing)?;
                let dx_inv = dx_val.invert();
                assert!(bool::from(dx_inv.is_some()));
                let dx_inv = dx_inv.unwrap();
                let dy_val = dy.get_value().ok_or(SynthesisError::AssignmentMissing)?;
                Ok(dy_val * dx_inv)
            }
        })?;
        cs.enforce(
            || "dx * lambda_a === dy",
            |lc| lc + dx.get_variable(),
            |lc| lc + lambda_a.get_variable(),
            |lc| lc + dy.get_variable(),
        );

        let lambda_b = AllocatedNum::alloc(&mut cs.namespace(|| "alloc lambda_b"), || {
            if p.y.get_value().ok_or(SynthesisError::AssignmentMissing)? == F::ZERO {
                Ok(F::ZERO)
            } else {
                let py_double_inv = (F::from(2u64)
                    * p.y.get_value().ok_or(SynthesisError::AssignmentMissing)?)
                .invert();
                assert!(bool::from(py_double_inv.is_some()));
                let py_double_inv = py_double_inv.unwrap();
                Ok(F::from(3u64)
                    * px_sq.get_value().ok_or(SynthesisError::AssignmentMissing)?
                    * py_double_inv)
            }
        })?;
        cs.enforce(
            || "lambda_b * 2 * p.y === 3 * px_sq",
            |lc| lc + lambda_b.get_variable(),
            |lc| lc + p.y.get_variable() + p.y.get_variable(),
            |lc| lc + px_sq.get_variable() + px_sq.get_variable() + px_sq.get_variable(),
        );

        let lambda = AllocatedNum::conditionally_select(
            &mut cs.namespace(|| "select lambda"),
            &lambda_a,
            &lambda_b,
            &is_x_eq,
        )?;

        let out_ax = AllocatedNum::alloc(&mut cs.namespace(|| "output ax"), || {
            let mut tmp = lambda
                .get_value()
                .ok_or(SynthesisError::AssignmentMissing)?;
            tmp.mul_assign(tmp);
            tmp.sub_assign(q.x.get_value().ok_or(SynthesisError::AssignmentMissing)?);
            tmp.sub_assign(p.x.get_value().ok_or(SynthesisError::AssignmentMissing)?);
            Ok(tmp)
        })?;
        cs.enforce(
            || "out_ax === lambda * lambda - px - qx",
            |lc| lc + lambda.get_variable(),
            |lc| lc + lambda.get_variable(),
            |lc| lc + out_ax.get_variable() + p.x.get_variable() + q.x.get_variable(),
        );

        let out_ay = AllocatedNum::alloc(&mut cs.namespace(|| "output ay"), || {
            let mut other_tmp = p.x.get_value().ok_or(SynthesisError::AssignmentMissing)?;
            other_tmp.sub_assign(
                out_ax
                    .get_value()
                    .ok_or(SynthesisError::AssignmentMissing)?,
            );
            let mut tmp = lambda
                .get_value()
                .ok_or(SynthesisError::AssignmentMissing)?;
            tmp.mul_assign(other_tmp);
            tmp.sub_assign(p.y.get_value().ok_or(SynthesisError::AssignmentMissing)?);
            Ok(tmp)
        })?;
        cs.enforce(
            || "out_ay === lambda * (px - out_ax) - py",
            |lc| lc + lambda.get_variable(),
            |lc| lc + p.x.get_variable() - out_ax.get_variable(),
            |lc| lc + out_ay.get_variable() + p.y.get_variable(),
        );

        let out_bx = AllocatedNum::conditionally_select(
            &mut cs.namespace(|| "select out_bx"),
            &out_ax,
            &zero,
            &is_either_x_zero,
        )?;
        let out_by = AllocatedNum::conditionally_select(
            &mut cs.namespace(|| "select out_by"),
            &out_ay,
            &zero,
            &is_either_x_zero,
        )?;

        let out_cx = AllocatedNum::conditionally_select(
            &mut cs.namespace(|| "select out_cx"),
            &zero,
            &q.x,
            &is_px_zero,
        )?;
        let out_cy = AllocatedNum::conditionally_select(
            &mut cs.namespace(|| "select out_cy"),
            &zero,
            &q.y,
            &is_px_zero,
        )?;

        let out_dx = AllocatedNum::conditionally_select(
            &mut cs.namespace(|| "select out_dx"),
            &zero,
            &p.x,
            &is_qx_zero,
        )?;
        let out_dy = AllocatedNum::conditionally_select(
            &mut cs.namespace(|| "select out_dy"),
            &zero,
            &p.y,
            &is_qx_zero,
        )?;

        let add_y_is_zero = Boolean::from(AllocatedBit::alloc(
            &mut cs.namespace(|| "alloc add_y_is_zero"),
            {
                Some(
                    p.y.get_value().ok_or(SynthesisError::AssignmentMissing)?
                        + q.y.get_value().ok_or(SynthesisError::AssignmentMissing)?
                        == F::ZERO,
                )
            },
        )?);
        cs.enforce(
            || "add_y_is_zero * (p.y + q.y) === 0",
            |lc| lc + &add_y_is_zero.lc(CS::one(), F::ONE),
            |lc| lc + p.y.get_variable() + q.y.get_variable(),
            |lc| lc,
        );

        let zeroize_a = Boolean::and(
            &mut cs.namespace(|| "calc zeroize_a"),
            &is_x_eq,
            &add_y_is_zero,
        )?;

        let zeroize_b = Boolean::and(
            &mut cs.namespace(|| "calc zeroize_b"),
            &is_px_zero,
            &is_qx_zero,
        )?;

        let zeroize = Boolean::or(
            &mut cs.namespace(|| "zeroize_a OR zeroize_b"),
            &zeroize_a,
            &zeroize_b,
        )?;

        let mut sum_x = out_bx.add(&mut cs.namespace(|| "add out_cx"), &out_cx)?;
        sum_x = sum_x.add(&mut cs.namespace(|| "add out_dx"), &out_dx)?;
        let mut sum_y = out_by.add(&mut cs.namespace(|| "add out_cy"), &out_cy)?;
        sum_y = sum_y.add(&mut cs.namespace(|| "add out_dy"), &out_dy)?;

        let out_x = AllocatedNum::conditionally_select(
            &mut cs.namespace(|| "calc out_x"),
            &sum_x,
            &zero,
            &zeroize,
        )?;
        let out_y = AllocatedNum::conditionally_select(
            &mut cs.namespace(|| "calc out_y"),
            &sum_y,
            &zero,
            &zeroize,
        )?;

        Ok(AllocatedAffinePoint { x: out_x, y: out_y })
    }

    pub fn double<CS>(cs: &mut CS, p: Self) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let px_sq = p.x.square(&mut cs.namespace(|| "p.x * p.x"))?;

        let lambda = AllocatedNum::alloc(&mut cs.namespace(|| "alloc lambda"), || {
            if p.y.get_value().ok_or(SynthesisError::AssignmentMissing)? == F::ZERO {
                Ok(F::ZERO)
            } else {
                let py_double_inv = (F::from(2u64)
                    * p.y.get_value().ok_or(SynthesisError::AssignmentMissing)?)
                .invert();
                assert!(bool::from(py_double_inv.is_some()));
                let py_double_inv = py_double_inv.unwrap();
                Ok(F::from(3u64)
                    * px_sq.get_value().ok_or(SynthesisError::AssignmentMissing)?
                    * py_double_inv)
            }
        })?;
        cs.enforce(
            || "lambda * 2 * p.y === 3 * px_sq",
            |lc| lc + lambda.get_variable(),
            |lc| lc + p.y.get_variable() + p.y.get_variable(),
            |lc| lc + px_sq.get_variable() + px_sq.get_variable() + px_sq.get_variable(),
        );

        let out_x = AllocatedNum::alloc(&mut cs.namespace(|| "output x"), || {
            let mut tmp = lambda
                .get_value()
                .ok_or(SynthesisError::AssignmentMissing)?;
            tmp.mul_assign(tmp);
            tmp.sub_assign(p.x.get_value().ok_or(SynthesisError::AssignmentMissing)?);
            tmp.sub_assign(p.x.get_value().ok_or(SynthesisError::AssignmentMissing)?);
            Ok(tmp)
        })?;
        cs.enforce(
            || "out_ax === lambda * lambda - px - px",
            |lc| lc + lambda.get_variable(),
            |lc| lc + lambda.get_variable(),
            |lc| lc + out_x.get_variable() + p.x.get_variable() + p.x.get_variable(),
        );

        let out_y = AllocatedNum::alloc(&mut cs.namespace(|| "output y"), || {
            let mut other_tmp = p.x.get_value().ok_or(SynthesisError::AssignmentMissing)?;
            other_tmp.sub_assign(out_x.get_value().ok_or(SynthesisError::AssignmentMissing)?);
            let mut tmp = lambda
                .get_value()
                .ok_or(SynthesisError::AssignmentMissing)?;
            tmp.mul_assign(other_tmp);
            tmp.sub_assign(p.y.get_value().ok_or(SynthesisError::AssignmentMissing)?);
            Ok(tmp)
        })?;
        cs.enforce(
            || "out_ay === lambda * (px - out_ax) - py",
            |lc| lc + lambda.get_variable(),
            |lc| lc + p.x.get_variable() - out_x.get_variable(),
            |lc| lc + out_y.get_variable() + p.y.get_variable(),
        );

        Ok(AllocatedAffinePoint { x: out_x, y: out_y })
    }

    pub fn scalar_multiplication_1_bit<CS>(
        self,
        cs: &mut CS,
        scalar: Vec<Boolean>,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        assert!(scalar.len() <= 256usize);
        let mut output = AllocatedAffinePoint::alloc_affine_point(
            &mut cs.namespace(|| "alloc point at infinity"),
            F::ZERO,
            F::ZERO,
        )?;

        let mut step_point = self;

        for (i, bit) in scalar.iter().enumerate() {
            let output0 = output.clone();
            let output1 = Self::add_complete(
                &mut cs.namespace(|| format!("sum in step {i} if bit is one")),
                output,
                step_point.clone(),
            )?;

            let output_x = AllocatedNum::conditionally_select(
                &mut cs.namespace(|| format!("conditionally select x coordinate in step {i}")),
                &output0.x,
                &output1.x,
                bit,
            )?;
            let output_y = AllocatedNum::conditionally_select(
                &mut cs.namespace(|| format!("conditionally select y coordinate in step {i}")),
                &output0.y,
                &output1.y,
                bit,
            )?;

            output = Self {
                x: output_x,
                y: output_y,
            };

            step_point = Self::double(
                &mut cs.namespace(|| format!("point doubling in step {i}")),
                step_point,
            )?;
        }

        Ok(output)
    }

    pub fn scalar_multiplication_m_bit<CS>(
        self,
        cs: &mut CS,
        scalar: Vec<Boolean>,
        m: usize, // Number of bits
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let scalar_len = scalar.len();
        assert!(scalar_len <= 256usize);
        let identity = AllocatedAffinePoint::alloc_affine_point(
            &mut cs.namespace(|| "alloc point at infinity"),
            F::ZERO,
            F::ZERO,
        )?;

        let mut lookup_vec: Vec<AllocatedAffinePoint<F>> = vec![];
        lookup_vec.push(identity.clone());
        lookup_vec.push(self.clone());

        for i in 2..(1 << m) {
            let point = Self::add_complete(
                &mut cs.namespace(|| format!("allocate {} times the base", i)),
                lookup_vec[i - 1].clone(),
                self.clone(),
            )?;
            lookup_vec.push(point);
        }
        assert_eq!(lookup_vec.len(), (1 << m));

        let n = scalar_len - 1;

        let mut lookup_bits: Vec<Boolean> = vec![];
        for i in ((n + 1 - m)..(n + 1)).rev() {
            lookup_bits.push(scalar[i].clone());
        }
        assert_eq!(lookup_bits.len(), m);

        let mut output = Self::mux_tree(
            &mut cs.namespace(|| "allocate initial value of output"),
            lookup_bits.iter(),
            &lookup_vec,
        )?;

        let mut i: i32 = n as i32 - m as i32;
        while i > 0 {
            if i < (m as i32) - 1 {
                for j in 0..(i + 1) {
                    output = Self::double(
                        &mut cs.namespace(|| format!("{j} doubling in iteration {i}")),
                        output,
                    )?;
                }

                let mut lookup_bits: Vec<Boolean> = vec![];
                for j in (0..(i + 1)).rev() {
                    lookup_bits.push(scalar[j as usize].clone());
                }

                let tmp = Self::mux_tree(
                    &mut cs.namespace(|| format!("allocate tmp value in iteration {i}")),
                    lookup_bits.iter(),
                    &lookup_vec[0..(1 << (i as usize + 1))],
                )?;

                output = Self::add_complete(
                    &mut cs
                        .namespace(|| format!("allocate sum of output and tmp in iteration {i}")),
                    output,
                    tmp,
                )?;

                break;
            }

            for j in 0..m {
                output = Self::double(
                    &mut cs.namespace(|| format!("{j} doubling in iteration {i}")),
                    output,
                )?;
            }
            let mut lookup_bits: Vec<Boolean> = vec![];
            for j in ((i as usize + 1 - m)..(i as usize + 1)).rev() {
                lookup_bits.push(scalar[j].clone());
            }
            assert_eq!(lookup_bits.len(), m);

            let tmp = Self::mux_tree(
                &mut cs.namespace(|| format!("allocate tmp value in iteration {i}")),
                lookup_bits.iter(),
                &lookup_vec,
            )?;

            output = Self::add_complete(
                &mut cs.namespace(|| format!("allocate sum of output and tmp in iteration {i}")),
                output,
                tmp,
            )?;

            i -= m as i32;
        }

        if n % m == 0 {
            output = Self::double(&mut cs.namespace(|| "final doubling of output"), output)?;
            let tmp = Self::add_complete(
                &mut cs.namespace(|| "final sum of output and base"),
                output.clone(),
                self,
            )?;
            output = Self::conditionally_select(cs, &output, &tmp, &scalar[0])?;
        }

        Ok(output)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use bellpepper_core::test_cs::TestConstraintSystem;
    use crypto_bigint::{Encoding, Integer, U256};
    use ff::Field;
    use halo2curves::secp256k1::{Fp, Fq, Secp256k1Affine};
    use rand_core::SeedableRng;
    use rand_xorshift::XorShiftRng;
    use std::ops::{Mul, Neg};

    #[test]
    fn test_conditional_select() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x3d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);
        {
            let mut cs = TestConstraintSystem::<Fp>::new();

            let p1 = Secp256k1Affine::random(&mut rng);
            let p2 = Secp256k1Affine::random(&mut rng);
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
            let condition = Boolean::constant(false);
            let c = AllocatedAffinePoint::conditionally_select(
                &mut cs, &p1_alloc, &p2_alloc, &condition,
            )
            .unwrap();

            assert!(cs.is_satisfied());
            assert_eq!(cs.num_constraints(), 2);
            assert_eq!(p1_alloc.x.get_value().unwrap(), c.x.get_value().unwrap());
            assert_eq!(p1_alloc.y.get_value().unwrap(), c.y.get_value().unwrap());
        }

        {
            let mut cs = TestConstraintSystem::<Fp>::new();

            let p1 = Secp256k1Affine::random(&mut rng);
            let p2 = Secp256k1Affine::random(&mut rng);
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
            let condition = Boolean::constant(true);
            let c = AllocatedAffinePoint::conditionally_select(
                &mut cs, &p1_alloc, &p2_alloc, &condition,
            )
            .unwrap();

            assert!(cs.is_satisfied());
            assert_eq!(cs.num_constraints(), 2);
            assert_eq!(p2_alloc.x.get_value().unwrap(), c.x.get_value().unwrap());
            assert_eq!(p2_alloc.y.get_value().unwrap(), c.y.get_value().unwrap());
        }
    }

    #[test]
    fn test_mux_tree() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x3d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        let conditions = vec![(false, false), (false, true), (true, false), (true, true)];

        for (c1, c0) in conditions {
            let mut cs = TestConstraintSystem::<Fp>::new();

            let condition0 = Boolean::constant(c0);
            let condition1 = Boolean::constant(c1);
            let select = &[condition1, condition0];

            let a0_point = Secp256k1Affine::random(&mut rng);
            let a0 = AllocatedAffinePoint::alloc_affine_point(
                &mut cs.namespace(|| "alloc a0"),
                a0_point.x,
                a0_point.y,
            )
            .unwrap();
            let a1_point = Secp256k1Affine::random(&mut rng);
            let a1 = AllocatedAffinePoint::alloc_affine_point(
                &mut cs.namespace(|| "alloc a1"),
                a1_point.x,
                a1_point.y,
            )
            .unwrap();
            let a2_point = Secp256k1Affine::random(&mut rng);
            let a2 = AllocatedAffinePoint::alloc_affine_point(
                &mut cs.namespace(|| "alloc a2"),
                a2_point.x,
                a2_point.y,
            )
            .unwrap();
            let a3_point = Secp256k1Affine::random(&mut rng);
            let a3 = AllocatedAffinePoint::alloc_affine_point(
                &mut cs.namespace(|| "alloc a3"),
                a3_point.x,
                a3_point.y,
            )
            .unwrap();

            let res = AllocatedAffinePoint::<Fp>::mux_tree(
                &mut cs.namespace(|| format!("mux tree result for conditions = {c1}, {c0}")),
                select.iter(),
                &[a0.clone(), a1.clone(), a2.clone(), a3.clone()],
            );
            assert!(res.is_ok());
            let res = res.unwrap();

            let res_expected = match (c1, c0) {
                (false, false) => a0.clone(),
                (false, true) => a1.clone(),
                (true, false) => a2.clone(),
                (true, true) => a3.clone(),
            };
            cs.enforce(
                || format!("res x equality for conditions = {c1}, {c0}"),
                |lc| lc,
                |lc| lc,
                |lc| lc + res_expected.x.get_variable() - res.x.get_variable(),
            );
            cs.enforce(
                || format!("res y equality for conditions = {c1}, {c0}"),
                |lc| lc,
                |lc| lc,
                |lc| lc + res_expected.y.get_variable() - res.y.get_variable(),
            );

            assert!(cs.is_satisfied());
            assert_eq!(cs.num_constraints(), 8);
        }
    }

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

    #[test]
    fn test_add_complete() {
        {
            // test O + O == O
            let mut cs = TestConstraintSystem::<Fp>::new();
            let infi_alloc = AllocatedAffinePoint::alloc_affine_point(
                &mut cs.namespace(|| "alloc point at infinity"),
                Fp::ZERO,
                Fp::ZERO,
            )
            .unwrap();
            let add_alloc = AllocatedAffinePoint::add_complete(
                &mut cs.namespace(|| "point1 + point2"),
                infi_alloc.clone(),
                infi_alloc,
            )
            .unwrap();
            assert!(cs.is_satisfied());
            assert_eq!(cs.num_constraints(), 36);
            assert_eq!(Fp::ZERO, add_alloc.x.get_value().unwrap());
            assert_eq!(Fp::ZERO, add_alloc.y.get_value().unwrap());
        }

        {
            // test O + Q == Q
            let mut rng = XorShiftRng::from_seed([
                0x59, 0x62, 0xbe, 0x3d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
                0xbc, 0xe5,
            ]);
            let mut cs = TestConstraintSystem::<Fp>::new();
            let infi_alloc = AllocatedAffinePoint::alloc_affine_point(
                &mut cs.namespace(|| "alloc point at infinity"),
                Fp::ZERO,
                Fp::ZERO,
            )
            .unwrap();

            let q = Secp256k1Affine::random(&mut rng);
            let q_alloc =
                AllocatedAffinePoint::alloc_affine_point(&mut cs.namespace(|| "alloc Q"), q.x, q.y)
                    .unwrap();

            let add_alloc = AllocatedAffinePoint::add_complete(
                &mut cs.namespace(|| "O + Q"),
                infi_alloc,
                q_alloc,
            )
            .unwrap();
            assert!(cs.is_satisfied());
            assert_eq!(cs.num_constraints(), 36);
            assert_eq!(q.x, add_alloc.x.get_value().unwrap());
            assert_eq!(q.y, add_alloc.y.get_value().unwrap());
        }

        {
            // test P + O == P
            let mut rng = XorShiftRng::from_seed([
                0x59, 0x62, 0xbe, 0x3d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
                0xbc, 0xe5,
            ]);
            let mut cs = TestConstraintSystem::<Fp>::new();
            let infi_alloc = AllocatedAffinePoint::alloc_affine_point(
                &mut cs.namespace(|| "alloc point at infinity"),
                Fp::ZERO,
                Fp::ZERO,
            )
            .unwrap();

            let p = Secp256k1Affine::random(&mut rng);
            let p_alloc =
                AllocatedAffinePoint::alloc_affine_point(&mut cs.namespace(|| "alloc P"), p.x, p.y)
                    .unwrap();

            let add_alloc = AllocatedAffinePoint::add_complete(
                &mut cs.namespace(|| "P + O"),
                p_alloc,
                infi_alloc,
            )
            .unwrap();
            assert!(cs.is_satisfied());
            assert_eq!(cs.num_constraints(), 36);
            assert_eq!(p.x, add_alloc.x.get_value().unwrap());
            assert_eq!(p.y, add_alloc.y.get_value().unwrap());
        }

        {
            // test P + P == 2P
            let mut rng = XorShiftRng::from_seed([
                0x59, 0x62, 0xbe, 0x3d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
                0xbc, 0xe5,
            ]);
            let mut cs = TestConstraintSystem::<Fp>::new();

            let p = Secp256k1Affine::random(&mut rng);
            let p_double: Secp256k1Affine = (p + p).try_into().unwrap();
            let p_alloc =
                AllocatedAffinePoint::alloc_affine_point(&mut cs.namespace(|| "alloc P"), p.x, p.y)
                    .unwrap();

            let add_alloc = AllocatedAffinePoint::add_complete(
                &mut cs.namespace(|| "P + P"),
                p_alloc.clone(),
                p_alloc,
            )
            .unwrap();
            assert!(cs.is_satisfied());
            assert_eq!(cs.num_constraints(), 36);
            assert_eq!(p_double.x, add_alloc.x.get_value().unwrap());
            assert_eq!(p_double.y, add_alloc.y.get_value().unwrap());
        }

        {
            // test P + (-P) == O
            let mut rng = XorShiftRng::from_seed([
                0x59, 0x62, 0xbe, 0x3d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
                0xbc, 0xe5,
            ]);
            let mut cs = TestConstraintSystem::<Fp>::new();

            let p = Secp256k1Affine::random(&mut rng);
            let p_neg = p.neg();
            let p_alloc =
                AllocatedAffinePoint::alloc_affine_point(&mut cs.namespace(|| "alloc P"), p.x, p.y)
                    .unwrap();
            let p_neg_alloc = AllocatedAffinePoint::alloc_affine_point(
                &mut cs.namespace(|| "alloc P neg"),
                p_neg.x,
                p_neg.y,
            )
            .unwrap();

            let add_alloc = AllocatedAffinePoint::add_complete(
                &mut cs.namespace(|| "P + (-P)"),
                p_alloc,
                p_neg_alloc,
            )
            .unwrap();
            assert!(cs.is_satisfied());
            assert_eq!(cs.num_constraints(), 36);
            assert_eq!(Fp::ZERO, add_alloc.x.get_value().unwrap());
            assert_eq!(Fp::ZERO, add_alloc.y.get_value().unwrap());
        }

        {
            // test P + Q when p.x != q.x
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
                let add_alloc = AllocatedAffinePoint::add_complete(
                    &mut cs.namespace(|| "point1 + point2"),
                    p1_alloc,
                    p2_alloc,
                )
                .unwrap();

                assert!(cs.is_satisfied());
                assert_eq!(cs.num_constraints(), 36);
                assert_eq!(add_exp.x, add_alloc.x.get_value().unwrap());
                assert_eq!(add_exp.y, add_alloc.y.get_value().unwrap());
            }
        }
    }

    #[test]
    fn test_double() {
        {
            // test O + O == O
            let mut cs = TestConstraintSystem::<Fp>::new();
            let infi_alloc = AllocatedAffinePoint::alloc_affine_point(
                &mut cs.namespace(|| "alloc point at infinity"),
                Fp::ZERO,
                Fp::ZERO,
            )
            .unwrap();
            let double = AllocatedAffinePoint::double(
                &mut cs.namespace(|| "2 * point1"),
                infi_alloc.clone(),
            )
            .unwrap();
            assert!(cs.is_satisfied());
            assert_eq!(cs.num_constraints(), 4);
            assert_eq!(Fp::ZERO, double.x.get_value().unwrap());
            assert_eq!(Fp::ZERO, double.y.get_value().unwrap());
        }

        {
            // test P + P == 2P
            let mut rng = XorShiftRng::from_seed([
                0x59, 0x62, 0xbe, 0x3d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
                0xbc, 0xe5,
            ]);
            let mut cs = TestConstraintSystem::<Fp>::new();

            let p = Secp256k1Affine::random(&mut rng);
            let p_double: Secp256k1Affine = (p + p).try_into().unwrap();
            let p_alloc =
                AllocatedAffinePoint::alloc_affine_point(&mut cs.namespace(|| "alloc P"), p.x, p.y)
                    .unwrap();

            let double =
                AllocatedAffinePoint::double(&mut cs.namespace(|| "P + P"), p_alloc).unwrap();
            assert!(cs.is_satisfied());
            assert_eq!(cs.num_constraints(), 4);
            assert_eq!(p_double.x, double.x.get_value().unwrap());
            assert_eq!(p_double.y, double.y.get_value().unwrap());
        }
    }

    #[test]
    fn scalar_multiplication_window_1() {
        let mut rng = rand::thread_rng();
        let b = Secp256k1Affine::generator();

        for _ in 0..100 {
            let scalar = Fq::random(&mut rng);
            let p: Secp256k1Affine = b.mul(scalar).into();

            let mut scalar_bigint = U256::from_le_bytes(scalar.to_repr());
            let mut scalar_vec: Vec<Boolean> = vec![];
            for _i in 0..256 {
                if bool::from(scalar_bigint.is_odd()) {
                    scalar_vec.push(Boolean::constant(true))
                } else {
                    scalar_vec.push(Boolean::constant(false))
                };
                scalar_bigint = scalar_bigint >> 1;
            }

            let mut cs = TestConstraintSystem::<Fp>::new();

            let b_alloc = AllocatedAffinePoint::alloc_affine_point(
                &mut cs.namespace(|| "allocate base point"),
                b.x,
                b.y,
            );
            assert!(b_alloc.is_ok());
            let b_al = b_alloc.unwrap();

            let p_alloc = b_al.scalar_multiplication_1_bit(
                &mut cs.namespace(|| "scalar multiplication"),
                scalar_vec,
            );
            assert!(p_alloc.is_ok());
            let p_al = p_alloc.unwrap();

            assert_eq!(p.x, p_al.x.get_value().unwrap());
            assert_eq!(p.y, p_al.y.get_value().unwrap());

            assert!(cs.is_satisfied());
            assert_eq!(cs.num_constraints(), 10752);
        }
    }

    #[test]
    fn scalar_multiplication_window_m() {
        let mut rng = rand::thread_rng();
        let b = Secp256k1Affine::generator();

        for _ in 0..100 {
            let scalar = Fq::random(&mut rng);
            let p: Secp256k1Affine = b.mul(scalar).into();

            let mut scalar_bigint = U256::from_le_bytes(scalar.to_repr());
            let mut scalar_vec: Vec<Boolean> = vec![];
            for _i in 0..256 {
                if bool::from(scalar_bigint.is_odd()) {
                    scalar_vec.push(Boolean::constant(true))
                } else {
                    scalar_vec.push(Boolean::constant(false))
                };
                scalar_bigint = scalar_bigint >> 1;
            }

            let mut cs = TestConstraintSystem::<Fp>::new();

            let b_alloc = AllocatedAffinePoint::alloc_affine_point(
                &mut cs.namespace(|| "allocate base point"),
                b.x,
                b.y,
            );
            assert!(b_alloc.is_ok());
            let b_al = b_alloc.unwrap();

            let p_alloc = b_al.scalar_multiplication_m_bit(
                &mut cs.namespace(|| "scalar multiplication"),
                scalar_vec,
                3,
            );
            assert!(p_alloc.is_ok());
            let p_al = p_alloc.unwrap();

            assert_eq!(p.x, p_al.x.get_value().unwrap());
            assert_eq!(p.y, p_al.y.get_value().unwrap());

            assert!(cs.is_satisfied());
            assert_eq!(cs.num_constraints(), 5480);
        }
    }
}

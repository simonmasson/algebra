use crate::{
    models::{ModelParameters, SWModelParameters},
    PairingEngine,
};
use ark_ff::fields::{
    fp3::Fp3Parameters,
    fp6_2over3::{Fp6, Fp6Parameters},
    BitIteratorBE, Field, PrimeField, SquareRootField,
};
use num_traits::One;

use core::{convert::TryInto, marker::PhantomData};

pub enum TwistType {
    M,
    D,
}

pub trait BW6Parameters: 'static + Eq + PartialEq {
    const X: <Self::Fp as PrimeField>::BigInt;
    const X_MINUS_ONE: <Self::Fp as PrimeField>::BigInt;
    const X_MINUS_ONE_DIV_THREE: <Self::Fp as PrimeField>::BigInt;
    const X_IS_NEGATIVE: bool;
    const ATE_LOOP_COUNT_1: &'static [u64];
    const ATE_LOOP_COUNT_1_IS_NEGATIVE: bool;
    const ATE_LOOP_COUNT_2: &'static [i8];
    const ATE_LOOP_COUNT_2_IS_NEGATIVE: bool;
    const TWIST_TYPE: TwistType;
    const H_T: i32;
    const H_Y: i32;
    type Fp: PrimeField + SquareRootField + Into<<Self::Fp as PrimeField>::BigInt>;
    type Fp3Params: Fp3Parameters<Fp = Self::Fp>;
    type Fp6Params: Fp6Parameters<Fp3Params = Self::Fp3Params>;
    type G1Parameters: SWModelParameters<BaseField = Self::Fp>;
    type G2Parameters: SWModelParameters<
        BaseField = Self::Fp,
        ScalarField = <Self::G1Parameters as ModelParameters>::ScalarField,
    >;
}

pub mod g1;
pub mod g2;

pub use self::{
    g1::{G1Affine, G1Prepared, G1Projective},
    g2::{G2Affine, G2Prepared, G2Projective},
};

#[derive(Derivative)]
#[derivative(Copy, Clone, PartialEq, Eq, Debug, Hash)]
pub struct BW6<P: BW6Parameters>(PhantomData<fn() -> P>);

impl<P: BW6Parameters> BW6<P> {
    // Evaluate the line function at point p.
    fn ell(f: &mut Fp6<P::Fp6Params>, coeffs: &(P::Fp, P::Fp, P::Fp), p: &G1Affine<P>) {
        let mut c0 = coeffs.0;
        let mut c1 = coeffs.1;
        let mut c2 = coeffs.2;

        match P::TWIST_TYPE {
            TwistType::M => {
                c2 *= &p.y;
                c1 *= &p.x;
                f.mul_by_014(&c0, &c1, &c2);
            },
            TwistType::D => {
                c0 *= &p.y;
                c1 *= &p.x;
                f.mul_by_034(&c0, &c1, &c2);
            },
        }
    }

    fn exp_by_x(mut f: Fp6<P::Fp6Params>) -> Fp6<P::Fp6Params> {
        f = f.cyclotomic_exp(&P::X);
        if P::X_IS_NEGATIVE {
            f.conjugate();
        }
        f
    }

    fn exp_by_x_minus_one(mut f: Fp6<P::Fp6Params>) -> Fp6<P::Fp6Params> {
        f = f.cyclotomic_exp(&P::X_MINUS_ONE);
        if P::X_IS_NEGATIVE {
            f.conjugate();
        }
        f
    }

    fn exp_by_x_minus_one_div_3(mut f: Fp6<P::Fp6Params>) -> Fp6<P::Fp6Params> {
        f = f.cyclotomic_exp(&P::X_MINUS_ONE_DIV_THREE);
        if P::X_IS_NEGATIVE {
            f.conjugate();
        }
        f
    }

    pub fn final_exponentiation(value: &Fp6<P::Fp6Params>) -> Fp6<P::Fp6Params> {
        let value_inv = value.inverse().unwrap();
        let value_to_first_chunk = Self::final_exponentiation_first_chunk(value, &value_inv);
        Self::final_exponentiation_last_chunk(&value_to_first_chunk, P::H_T, P::H_Y)
    }

    pub fn final_exponentiation_first_chunk(
        elt: &Fp6<P::Fp6Params>,
        elt_inv: &Fp6<P::Fp6Params>,
    ) -> Fp6<P::Fp6Params> {
        // (q^3-1)*(q+1)

        // elt_q3 = elt^(q^3)
        let mut elt_q3 = *elt;
        elt_q3.conjugate();
        // elt_q3_over_elt = elt^(q^3-1)
        let elt_q3_over_elt = elt_q3 * elt_inv;
        // alpha = elt^((q^3-1) * q)
        let mut alpha = elt_q3_over_elt;
        alpha.frobenius_map(1);
        // beta = elt^((q^3-1)*(q+1)
        alpha * &elt_q3_over_elt
    }

    #[allow(clippy::let_and_return)]
    pub fn final_exponentiation_last_chunk(
        m: &Fp6<P::Fp6Params>,
        h_t: i32,
        h_y: i32,
    ) -> Fp6<P::Fp6Params> {
        // We follow https://hal.inria.fr/hal-03667798/file/AranhaElHousniGuillevic.pdf
        // Warning: this implementation works for BW6 curves with p of the form
        // p_{bw,3}, and not p_{bw, 0} (following the paper notation).

        // A = m**(u-1)
        let mut a = Self::exp_by_x_minus_one(*m);
        // A = A**(u-1)
        a = Self::exp_by_x_minus_one(a);
        // A = A * m.frobenius()        # A = m^((u-1)^2 + q)
        let mut mq = m.clone();
        mq.frobenius_map(1);
        a = a * mq;
        // B = A**(u+1) * m.conjugate() # B = m**((u^3-u^2-u) + (u+1)*q)
        let mut m_conj = m.clone();
        m_conj.conjugate();
        let b = Self::exp_by_x(a) * a * m_conj;
        // A = A**2 * A                 # A = m**(3*((u^2-2*u+1) + q))
        a = a.square() * a;

        // C = B**((u-1)//3)
        let c = Self::exp_by_x_minus_one_div_3(b);
        // D = C**(u-1)
        let d = Self::exp_by_x_minus_one(c);
        // E = (D**(u-1))**(u-1) * D             # B^((d-1)/3)
        let e = Self::exp_by_x_minus_one(Self::exp_by_x_minus_one(d)) * d;
        // D = D.conjugate()
        let mut d_conj = d.clone();
        d_conj.conjugate();
        // Fc = D * B
        let fc = d_conj * b;
        // G = E**(u+1) * Fc
        let g = Self::exp_by_x(e) * e * fc;
        // H = G * C                             # B^(t3/3)
        let h = g * c;
        // I = (G * D)**(u+1) * Fc.conjugate()   # B^r
        let mut fc_conj = fc.clone();
        fc_conj.conjugate();
        let i = Self::exp_by_x(g * d_conj) * g * d_conj * fc_conj;

        // d2 = (ht**2+3*hy**2)//4
        let d2: u64 = ((h_t * h_t + 3 * h_y * h_y) / 4).try_into().unwrap();
        // d2 is always positive

        // d1 = (ht+hy)//2
        let d1 = (h_t + h_y) / 2;
        // d1 can be negative
        let d1_is_neg = d1 < 0;
        let abs_d1: u64 = d1.abs().try_into().unwrap();

        // J = H**d1 * E
        let mut h_d1 = h.pow(&[abs_d1]);
        if d1_is_neg {
            h_d1 = h_d1.inverse().unwrap();
        }
        let j = h_d1 * e;
        // K = J**2 * J * B * I**d2
        let i_d2 = i.pow(&[d2]);
        let k = j * j * j * b * i_d2;
        a * k
    }
}

impl<P: BW6Parameters> PairingEngine for BW6<P> {
    type Fr = <P::G1Parameters as ModelParameters>::ScalarField;
    type G1Projective = G1Projective<P>;
    type G1Affine = G1Affine<P>;
    type G1Prepared = G1Prepared<P>;
    type G2Projective = G2Projective<P>;
    type G2Affine = G2Affine<P>;
    type G2Prepared = G2Prepared<P>;
    type Fq = P::Fp;
    type Fqe = P::Fp;
    type Fqk = Fp6<P::Fp6Params>;

    fn miller_loop<'a, I>(i: I) -> Self::Fqk
    where
        I: IntoIterator<Item = &'a (Self::G1Prepared, Self::G2Prepared)>,
    {
        // Alg.5 in https://eprint.iacr.org/2020/351.pdf

        let mut pairs_1 = vec![];
        let mut pairs_2 = vec![];
        for (p, q) in i {
            if !p.is_zero() && !q.is_zero() {
                pairs_1.push((p, q.ell_coeffs_1.iter()));
                pairs_2.push((p, q.ell_coeffs_2.iter()));
            }
        }

        // f_{u+1,Q}(P)
        let mut f_1 = Self::Fqk::one();

        for i in BitIteratorBE::new(P::ATE_LOOP_COUNT_1).skip(1) {
            f_1.square_in_place();

            for (p, ref mut coeffs) in &mut pairs_1 {
                Self::ell(&mut f_1, coeffs.next().unwrap(), &p.0);
            }
            if i {
                for &mut (p, ref mut coeffs) in &mut pairs_1 {
                    Self::ell(&mut f_1, coeffs.next().unwrap(), &p.0);
                }
            }
        }

        if P::ATE_LOOP_COUNT_1_IS_NEGATIVE {
            f_1.conjugate();
        }

        // f_{u^2-u^2-u,Q}(P)
        let mut f_2 = Self::Fqk::one();

        for i in (1..P::ATE_LOOP_COUNT_2.len()).rev() {
            if i != P::ATE_LOOP_COUNT_2.len() - 1 {
                f_2.square_in_place();
            }

            for (p, ref mut coeffs) in &mut pairs_2 {
                Self::ell(&mut f_2, coeffs.next().unwrap(), &p.0);
            }

            let bit = P::ATE_LOOP_COUNT_2[i - 1];
            match bit {
                1 => {
                    for &mut (p, ref mut coeffs) in &mut pairs_2 {
                        Self::ell(&mut f_2, coeffs.next().unwrap(), &p.0);
                    }
                },
                -1 => {
                    for &mut (p, ref mut coeffs) in &mut pairs_2 {
                        Self::ell(&mut f_2, coeffs.next().unwrap(), &p.0);
                    }
                },
                _ => continue,
            }
        }

        if P::ATE_LOOP_COUNT_2_IS_NEGATIVE {
            f_2.conjugate();
        }

        f_2.frobenius_map(1);

        f_1 * &f_2
    }

    fn final_exponentiation(f: &Self::Fqk) -> Option<Self::Fqk> {
        Some(Self::final_exponentiation(f))
    }
}

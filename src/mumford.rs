use crate::field::FieldElement;
use crate::polynomial::Poly;
use creusot_contracts::*;

use core::clone::Clone;
use core::marker::Copy;
use core::cmp::{Eq, PartialEq};


#[derive(Clone, Copy, PartialEq, Eq)]
pub struct MumfordDivisor<const MODULUS: u64>
{
    pub(crate) u1: FieldElement<MODULUS>,
    pub(crate) u0: FieldElement<MODULUS>,
    pub(crate) v1: FieldElement<MODULUS>,
    pub(crate) v0: FieldElement<MODULUS>
}

impl<const MODULUS: u64> DeepModel for MumfordDivisor<MODULUS> {
    type DeepModelTy = (Int, Int, Int, Int);

    #[logic]
    fn deep_model(self) -> Self::DeepModelTy {
        (self.u1.deep_model(), self.u0.deep_model(), self.v1.deep_model(), self.v0.deep_model())
    }
}

impl<const MODULUS: u64> MumfordDivisor<MODULUS> {
    pub const fn to_poly_u(&self) -> Poly<MODULUS> {
        // U(x)는 정의상 모닉(monic)입니다.
        Poly { c: [self.u0, self.u1, FieldElement::one(), FieldElement::zero(), FieldElement::zero(), FieldElement::zero()] }
    }
    pub const fn to_poly_v(&self) -> Poly<MODULUS> {
        // U(x)는 정의상 모닉(monic)입니다.
        Poly { c: [self.v0, self.v1, FieldElement::zero(), FieldElement::zero(), FieldElement::zero(), FieldElement::zero()] }
    }

    pub const fn from_polys(u_poly: Poly<MODULUS>, v_poly: Poly<MODULUS>) -> Self {
        // u_poly.c[2]가 1이 아닐 경우, make_monic()을 호출해야 하지만,
        // Cantor 알고리즘이 올바르게 구현되었다면 u_poly는 이미 모닉입니다.
        // proof_assert!(u_poly.c[2].is_one());

        Self {
            u1: u_poly.c[1],
            u0: u_poly.c[0],
            v1: v_poly.c[1],
            v0: v_poly.c[0],
        }
    }
}
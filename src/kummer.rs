use creusot_contracts::logic::Int;
use creusot_contracts::model::DeepModel;
use creusot_contracts::macros::{logic, requires};
use crate::field::FieldElement;


use core::clone::Clone;
use core::marker::Copy;
use core::cmp::{Eq, PartialEq};
use core::fmt::Debug;


#[derive(Debug, Clone, Copy)]
pub struct KummerPoint<const MODULUS: u64>
{
    pub x: FieldElement<MODULUS>,
    pub y: FieldElement<MODULUS>,
    pub z: FieldElement<MODULUS>,
    pub t: FieldElement<MODULUS>
}

impl<const MODULUS: u64> const PartialEq for KummerPoint<MODULUS> {
    fn eq(&self, other: &Self) -> bool {
        match (self.is_identity(), other.is_identity()) {
            (true, true) => true,
            (false, false) => {
                self.x * other.y == self.y * other.x &&
                self.x * other.z == self.z * other.x &&
                self.x * other.t == self.t * other.x &&
                self.y * other.z == self.z * other.y &&
                self.y * other.t == self.t * other.y &&
                self.z * other.t == self.t * other.z
            },
            _ => false
        }
    }
}

impl<const MODULUS: u64> const Eq for KummerPoint<MODULUS> {

}

impl<const MODULUS: u64> DeepModel for KummerPoint<MODULUS> {
    type DeepModelTy = (Int, Int, Int, Int);

    #[logic]
    fn deep_model(self) -> Self::DeepModelTy {
        (self.x.deep_model(), self.y.deep_model(), self.z.deep_model(), self.t.deep_model())
    }
}



impl<const MODULUS: u64> KummerPoint<MODULUS> {
    pub const fn is_identity(&self) -> bool {
        // !self.y.is_nonzero() && self.x == self.z && !self.t.is_nonzero()
        self.x.is_one() && !self.y.is_nonzero() && self.z.is_one() && !self.t.is_nonzero()
    }



    /// 상수 시간 조건부 이동 (Conditional Move).
    ///
    /// condition이 'true' (1)이면 'b'를, 'false' (0)이면 'a'를 반환합니다.
    #[requires(condition@ == 0 || condition@ == 1)]
    // (Creusot가 is_on_surface를 알지 못하므로 여기서는 계약 생략)
    // (만약 is_on_surface가 트레이트 외부로 이동했다면 계약 추가 가능)
    pub const fn cmov(a: Self, b: Self, condition: u64) -> Self {
        Self {
            x: FieldElement::cmov(a.x, b.x, condition),
            y: FieldElement::cmov(a.y, b.y, condition),
            z: FieldElement::cmov(a.z, b.z, condition),
            t: FieldElement::cmov(a.t, b.t, condition),
        }
    }

    pub const fn identity() -> Self {
        Self {
            x: FieldElement::one(), // X = 1
            y: FieldElement::zero(), // Y = 0
            z: FieldElement::one(),  // Z = 1
            t: FieldElement::zero(), // T = 0
        }
    }

    pub fn new(x: FieldElement<MODULUS>, y: FieldElement<MODULUS>, z: FieldElement<MODULUS>, t: FieldElement<MODULUS>) -> Self {
        Self {
            x, y, z, t
        }
    }
}
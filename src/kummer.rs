use crate::field::FieldElement;
use creusot_contracts::*;

use core::clone::Clone;
use core::marker::Copy;
use core::cmp::{Eq, PartialEq};


#[derive(Clone, Copy, PartialEq, Eq)]
pub struct KummerPoint<const MODULUS: u64>
{
    pub(crate) x: FieldElement<MODULUS>,
    pub(crate) y: FieldElement<MODULUS>,
    pub(crate) z: FieldElement<MODULUS>,
    pub(crate) t: FieldElement<MODULUS>
}

impl<const MODULUS: u64> DeepModel for KummerPoint<MODULUS> {
    type DeepModelTy = (Int, Int, Int, Int);

    #[logic]
    fn deep_model(self) -> Self::DeepModelTy {
        (self.x.deep_model(), self.y.deep_model(), self.z.deep_model(), self.t.deep_model())
    }
}

impl<const MODULUS: u64> KummerPoint<MODULUS> {
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
}
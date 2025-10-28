use creusot_contracts::logic::Int;
use creusot_contracts::model::DeepModel;
use creusot_contracts::macros::{logic, requires};
use crate::field::FieldElement;


use core::clone::Clone;
use core::marker::Copy;
use core::cmp::{Eq, PartialEq};
use core::fmt::Debug;


#[derive(Debug, Clone, Copy, Eq)]
pub struct KummerPoint<const MODULUS: u64>
{
    pub x: FieldElement<MODULUS>,
    pub y: FieldElement<MODULUS>,
    pub z: FieldElement<MODULUS>,
    pub t: FieldElement<MODULUS>
}

impl<const MODULUS: u64> PartialEq for KummerPoint<MODULUS> {
    fn eq(&self, other: &Self) -> bool {
        let self_is_identity = !self.z.is_nonzero();
        let other_is_identity = !other.z.is_nonzero();

        if self_is_identity && other_is_identity {
            // 둘 다 항등원이면 같음 (더 정확한 항등원 표현 비교 필요 시 수정)
            // 예: self.x, self.y, self.t 도 0인지 확인
            return !(self.x.is_nonzero() || self.y.is_nonzero() || self.t.is_nonzero() ||
                   other.x.is_nonzero() || other.y.is_nonzero() || other.t.is_nonzero());
        } else if self_is_identity || other_is_identity {
            // 하나만 항등원이면 다름
            return false;
        } else {
            // Z != 0 인 경우: 교차 곱 비교
            // X₁Z₂ == X₂Z₁ AND Y₁Z₂ == Y₂Z₁ AND T₁Z₂ == T₂Z₁
            (self.x * other.z == other.x * self.z) &&
            (self.y * other.z == other.y * self.z) &&
            (self.t * other.z == other.t * self.z)
        }
    }
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

    pub const fn identity() -> Self {
        Self {
            x: FieldElement::zero(), // u₁ = 0
            y: FieldElement::zero(), // u₀ = 0
            z: FieldElement::zero(),  // Z = 1
            t: FieldElement::one(), // k₄ = 0
        }
    }

    pub fn new(x: FieldElement<MODULUS>, y: FieldElement<MODULUS>, z: FieldElement<MODULUS>, t: FieldElement<MODULUS>) -> Self {
        Self {
            x, y, z, t
        }
    }
}
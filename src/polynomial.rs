use creusot_contracts::*;
use crate::field::FieldElement;
use core::clone::Clone;
use core::cmp::{min, Eq, PartialEq};
use core::ops::{Add, AddAssign, Div, Mul, MulAssign, Neg, Rem, Sub, SubAssign};
/// 다항식을 나타내는 구조체. f(x) = c[0] + c[1]x + ... + c[5]x^5
/// (Genus 2의 f(x)는 5차이므로, 6개의 계수가 필요)
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Poly<const MODULUS: u64> {
    pub c: [FieldElement<MODULUS>; 6], // c[i] = x^i의 계수
}

impl<const MODULUS: u64> Poly<MODULUS> {
    /// 0 다항식
    pub const fn zero() -> Self {
        Self { c: [FieldElement::zero(); 6] }
    }

    /// 상수 1 다항식
    pub const fn one() -> Self {
        Self { c: [FieldElement::one(), FieldElement::zero(), FieldElement::zero(), FieldElement::zero(), FieldElement::zero(), FieldElement::zero()] }
    }

    /// x^i 항 생성
    pub const fn monomial(coeff: FieldElement<MODULUS>, degree: usize) -> Self {
        let mut c = [FieldElement::zero(); 6];
        if degree < 6 {
            c[degree] = coeff;
        }
        Self { c }
    }

    pub const fn degree(&self) -> usize {
        let mut i = 6usize;
        while i > 0 {
            if self.c[i-1].is_nonzero() {
                return i-1;
            }
            i -= 1;
        }
        0 // 0 다항식의 차수는 0으로 처리
    }
    
    /// 최고차항의 계수 (Leading Coefficient)
    pub const fn lead_coeff(&self) -> FieldElement<MODULUS> {
        self.c[self.degree()]
    }

    pub const fn is_zero(&self) -> bool {
        let mut is_nonzero = false;
        let mut i = 0usize;
        while i < 6 {
            is_nonzero = is_nonzero || self.c[i].is_nonzero();
            i += 1;
        }
        !is_nonzero
    }

    /// 모닉(Monic) 다항식으로 만들기 (최고차항 계수로 나눔)
    /// [!!] 필드 역원(inv) 사용
    #[allow(creusot::contractless_external_function)]
    pub const fn make_monic(self) -> Self {
        let lead = self.lead_coeff();
        if lead.is_one() { return self; }
        
        // 상수 시간 inv() 호출
        let lead_inv = lead.inv().expect("Leading coefficient is zero in make_monic");
        
        let mut result = self;
        let mut i = 0usize;
        while i < 6 {
            result.c[i] *= lead_inv;
            i += 1;
        }
        result
    }

    /// 다항식 나눗셈 (몫과 나머지)
    /// [!!] 필드 역원(inv) 사용
    #[allow(creusot::contractless_external_function)] // inv()가 복잡하므로 계약 추론이 어려움
    pub const fn poly_div_rem(self, g: Self) -> (Self, Self) {
        let mut q = Self::zero();
        let mut r = self;
        let deg_g = g.degree();
        
        if deg_g == 0 && !g.c[0].is_nonzero() { panic!("Division by zero poly"); }

        // g의 최고차항 계수의 역원 (상수 시간 inv 호출)
        let lead_g_inv = g.c[deg_g].inv().unwrap_or(FieldElement::<MODULUS>::zero());

        while r.c[0].is_nonzero() && r.degree() >= deg_g {
            let deg_r = r.degree();
            let lead_r = r.c[deg_r];
            
            // 몫의 항 계산
            let q_coeff = lead_r * lead_g_inv;
            let q_deg = deg_r - deg_g;
            
            q.c[q_deg] = q.c[q_deg] + q_coeff;
            
            // q_term * g를 r에서 빼기
            let mut i = 0usize;
            while i <= deg_g {
                if i + q_deg < 6 {
                    r.c[i + q_deg] = r.c[i + q_deg] - (g.c[i] * q_coeff);
                }
                i += 1;
            }
        }
        (q, r)
    }

    pub const fn scalar_mul(self, rhs: FieldElement<MODULUS>) -> Self {
        Self {
            c: [
                self.c[0] * rhs,
                self.c[1] * rhs,
                self.c[2] * rhs,
                self.c[3] * rhs,
                self.c[4] * rhs,
                self.c[5] * rhs
            ]
        }
    }

    /// 다항식 확장 GCD (XGCD)
    /// (d, s, t) 반환: d = s*a + t*b
    /// [!!] poly_div_rem을 통해 필드 역원(inv) 사용
    #[allow(creusot::contractless_external_function)]
    pub const fn poly_xgcd(a: Self, b: Self) -> (Self, Self, Self) {
        let (mut r_prev, mut r) = (a, b);
        let (mut s_prev, mut s) = (Self::one(), Self::zero());
        let (mut t_prev, mut t) = (Self::zero(), Self::one());

        while !r.is_zero() {
            // q = r_prev / r
            let (q, r_new) = r_prev.poly_div_rem(r);
            
            (r_prev, r) = (r, r_new);
            (s_prev, s) = (s, s_prev - (q * s));
            (t_prev, t) = (t, t_prev - (q * t));
        }
        
        // d = r_prev
        // make d monic
        let d_lead_inv = r_prev.lead_coeff().inv().expect("XGCD result is zero poly");
        
        (
            r_prev.scalar_mul(d_lead_inv), // d
            s_prev.scalar_mul(d_lead_inv), // s
            t_prev.scalar_mul(d_lead_inv)  // t
        )
    }
}

// --- 다항식 사칙연산 ---

impl<const MODULUS: u64> const Add for Poly<MODULUS> {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        let mut result = Self::zero();
        let mut i = 0usize;
        while i < 6 {
            result.c[i] = self.c[i] + rhs.c[i];
            i += 1;
        }
        result
    }
}

impl<const MODULUS: u64> const Sub for Poly<MODULUS> {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self {
        let mut result = Self::zero();
        let mut i = 0usize;
        while i < 6 {
            result.c[i] = self.c[i] - rhs.c[i];
            i += 1;
        }
        result
    }
}

impl<const MODULUS: u64> const Neg for Poly<MODULUS> {
    type Output = Self;
    fn neg(self) -> Self {
        let mut result = Self::zero();
        let mut i = 0usize;
        while i < 6 {
            result.c[i] = -self.c[i];
            i += 1;
        }
        result
    }
}
// (Sub, Neg 구현)

impl<const MODULUS: u64> const Mul<Self> for Poly<MODULUS> {
    type Output = Self;
    /// 다항식 곱셈 (Convolution)
    /// (결과가 5차를 넘으면 잘림)
    fn mul(self, rhs: Self) -> Self {
        let mut result = Self::zero();

        let mut i = 0usize;
        while i < 6 {
            let mut j = 0usize;
            while i + j < 6 {
                result.c[i + j] = result.c[i + j] + (self.c[i] * rhs.c[j]);
                j += 1;
            }
            i += 1;
        }
        result
    }
}

impl<const MODULUS: u64> MulAssign<Self> for Poly<MODULUS> { fn mul_assign(&mut self, rhs: Self) { *self = *self * rhs; } }

impl<const MODULUS: u64> const Div for Poly<MODULUS> { type Output = Self; fn div(self, rhs: Self) -> Self { self.poly_div_rem(rhs).0 } }
impl<const MODULUS: u64> const Rem for Poly<MODULUS> { type Output = Self; fn rem(self, rhs: Self) -> Self { self.poly_div_rem(rhs).1 } }
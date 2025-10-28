use creusot_contracts::logic::Int;
use creusot_contracts::logic::ops::{AddLogic, MulLogic, NegLogic, SubLogic};
use creusot_contracts::model::DeepModel;
use creusot_contracts::macros::{ensures, logic, pearlite, proof_assert, requires, trusted, variant};
use core::cmp::{PartialEq, Eq};
use core::clone::Clone;
use core::ops::{Add, AddAssign, Mul, MulAssign, Neg, Rem, Sub, SubAssign};

pub const MODULUS_GOLDILOCKS: u64 = 18446744069414584321u64;







#[derive(Debug, Clone, Copy)]
pub struct FieldElement<const MODULUS: u64>(u64);

impl<const MODULUS: u64> DeepModel for FieldElement<MODULUS> {
    type DeepModelTy = <u64 as DeepModel>::DeepModelTy;

    #[logic]
    #[requires(self.is_valid())]
    fn deep_model(self) -> Self::DeepModelTy {
        self.0.deep_model()
    }
}

impl<const MODULUS: u64> const PartialEq for FieldElement<MODULUS> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<const MODULUS: u64> const Eq for FieldElement<MODULUS> {

}

impl<const MODULUS: u64> FieldElement<MODULUS> {
    #[requires(MODULUS@ > 1)]
    #[ensures(result == Self::new_logical(val))]
    pub const fn new(val: u64) -> Self {
        if MODULUS > 1 {
            Self(val % MODULUS)
        } else {
            panic!("MODULUS must be larger than 1")
        }
    }

    pub const fn one() -> Self {
        if MODULUS > 1 {
            Self(1u64)
        } else {
            panic!("MODULUS must be larger than 1")
        }
    }

    pub const fn zero() -> Self {
        if MODULUS > 1 {
            Self(0u64)
        } else {
            panic!("MODULUS must be larger than 1")
        }
    }

    /// 0이 아닌지 확인 (Creusot 로직)
    pub const fn is_nonzero(self) -> bool {
        self.0 != 0
    }

    pub const fn is_one(self) -> bool {
        self.0 == 1
    }

    pub const fn get_value(self) -> u64 {
        self.0
    }

    #[logic]
    pub const fn get_logical_value(self) -> Int {
        pearlite! { self.0@ }
    }

    #[logic]
    #[variant(self.0)] // 재귀 종료를 위한 명시 (여기선 불필요하나 좋은 습관)
    #[ensures(result == (self.get_logical_value() < MODULUS@))]
    pub const fn is_valid(self) -> bool {
        self.0 < MODULUS
    }


    // 상수 시간 조건부 이동 (Conditional Move).
    ///
    /// condition이 'true' (1)이면 'b'를, 'false' (0)이면 'a'를 반환합니다.
    ///
    /// [Creusot 계약]
    /// - `condition`은 0 또는 1이어야 합니다.
    /// - `condition`이 1이면 결과는 `b`와 같습니다.
    /// - `condition`이 0이면 결과는 `a`와 같습니다.
    #[requires(a.is_valid() && b.is_valid())]
    #[requires(condition@ == 0 || condition@ == 1)]
    #[ensures(result.is_valid())]
    #[ensures(condition@ == 1 ==> result.get_logical_value() == b.get_logical_value())]
    #[ensures(condition@ == 0 ==> result.get_logical_value() == a.get_logical_value())]
    pub const fn cmov(a: Self, b: Self, condition: u64) -> Self {
        // Rust 1.58+ 에서는 `u64::from(bool)`가 1 또는 0을 반환합니다.
        // 하지만 'condition'을 u64로 받았으므로,
        // 'condition'이 1일 때 all-ones (0xFF...FF) 마스크를 생성합니다.
        // 'condition'이 0일 때 all-zeros (0x00...00) 마스크를 생성합니다.
        
        // 1. (condition == 1) -> 0xFF...FF (all ones)
        //    (condition == 0) -> 0x00...00 (all zeros)
        // 'condition'은 0 또는 1이므로 (0 - 1)은 오버플로우를 이용합니다.
        let mask = 0u64.wrapping_sub(condition); 

        // 2. 비트 연산을 통한 선택
        // mask == 0xFF...FF (cond=1): (a & 0) | (b & 0xFF..FF) = b
        // mask == 0x00...00 (cond=0): (a & 0xFF..FF) | (b & 0) = a
        let val = (a.0 & !mask) | (b.0 & mask);

        // 3. Creusot 증명 보조
        // 'mask'가 0 또는 0xFF...FF 임을 단언합니다.
        proof_assert!(
            (condition@ == 0 && mask@ == 0) || (condition@ == 1 && mask == u64::MAX)
        );
        // 'val'이 'a' 또는 'b'의 값과 같음을 단언합니다.
        proof_assert!(
            (condition@ == 0 && val == a.0) || (condition@ == 1 && val == b.0)
        );

        FieldElement(val)
    }

    #[logic(opaque)]
    pub const fn new_logical(_val: u64) -> Self {
        dead
    }

    #[logic]
    pub const fn get_logical_raw_value(self) -> u64 {
        self.0
    }

}

#[logic]
#[requires(a >= 0 && b >= 0)]
#[variant(b)] // 논리 함수의 종료 조건
#[trusted]
#[ensures(result >= 0)]
pub fn spec_gcd(a: Int, b: Int) -> Int {
    pearlite! {
        if b == 0 {
            a
        } else {
            spec_gcd(b, a % b)
        }
    }
}

#[logic]
#[trusted]
#[ensures(result >= 0)]
pub const fn abs(n: Int) -> Int {
    if n < 0 {
        -n
    } else {
        n
    }
}


#[ensures(a_in@ % result.0@ == 0)]
#[ensures(b_in@ % result.0@ == 0)]
pub const fn extended_gcd(a_in: u64, b_in: u64) -> (u64, i128, i128) {
    // 내부 계산을 위해 i128로 캐스팅
    let a = a_in as i128;
    let b = b_in as i128;

    // r 변수들: (old_r, r)은 사용자의 (x, y)와 같습니다.
    let (mut old_r, mut r) = (a, b);
    
    // s 계수들: old_r = old_s * a + old_t * b
    let (mut old_s, mut s) = (1, 0);
    
    // t 계수들: r = s * a + t * b
    let (mut old_t, mut t) = (0, 1);

    // 루프 종료 조건 (gcd의 'y'와 동일)
    #[variant(r)]
    
    // 루프 불변 조건 (Creusot 증명을 위해 매우 중요)
    // 1. 베주 항등식이 루프의 매 단계마다 성립함
    #[invariant(old_r == old_s * a + old_t * b)]
    #[invariant(r == s * a + t * b)]
    // 2. 현재 (old_r, r)의 gcd가 초기 (a, b)의 gcd와 동일함
    #[invariant(spec_gcd(abs(old_r@), abs(r@)) == spec_gcd(a_in@, b_in@))]
    while r != 0 {
        // 유클리드 호제법의 핵심: 몫(quotient) 계산
        let quotient = old_r / r;

        // 1. (old_r, r) 갱신 (사용자의 gcd(x,y)와 동일한 로직)
        // (old_r, r) = (r, old_r % r)
        // (old_r, r) = (r, old_r - quotient * r)
        let temp_r = r;
        r = old_r - quotient * r;
        old_r = temp_r;

        // 2. (old_s, s) 갱신 (r과 동일한 연산 적용)
        // (old_s, s) = (s, old_s - quotient * s)
        let temp_s = s;
        s = old_s - quotient * s;
        old_s = temp_s;

        // 3. (old_t, t) 갱신 (r과 동일한 연산 적용)
        // (old_t, t) = (t, old_t - quotient * t)
        let temp_t = t;
        t = old_t - quotient * t;
        old_t = temp_t;
    }

    // 루프 종료 시: r == 0
    // 따라서 gcd = old_r
    // 계수는 (old_s, old_t)
    
    // old_r은 gcd이므로 항상 0 이상이어야 함
    proof_assert!(old_r@ >= 0);
    
    (old_r as u64, old_s, old_t)
}


#[logic]
#[ensures(spec_gcd(a@, b@) % spec_gcd(a@, b@) == 0)] // (당연함)
#[ensures(a@ % spec_gcd(a@, b@) == 0)] // <- 증명 필요
#[ensures(b@ % spec_gcd(a@, b@) == 0)] // <- 증명 필요
#[ensures(forall<d: u64> d@ > 0 && a@ % d@ == 0 && b@ % d@ == 0 ==> spec_gcd(a@, b@) % d@ == 0)] // <- "최대" 속성 증명
pub fn lemma_gcd_is_greatest_common_divisor(a: u64, b: u64) {
}

impl <const MODULUS: u64> MulLogic for FieldElement<MODULUS> {
    type Output = Self;

    #[logic(opaque)]
    fn mul(self, _other: Self) -> Self::Output {
        dead
    }
}

impl <const MODULUS: u64> AddLogic for FieldElement<MODULUS> {
    type Output = Self;

    #[logic(opaque)]
    fn add(self, _other: Self) -> Self::Output {
        dead
    }
}

impl <const MODULUS: u64> SubLogic for FieldElement<MODULUS> {
    type Output = Self;

    #[logic(opaque)]
    fn sub(self, _other: Self) -> Self::Output {
        dead
    }
}

impl <const MODULUS: u64> NegLogic for FieldElement<MODULUS> {
    type Output = Self;

    #[logic(opaque)]
    fn neg(self) -> Self::Output {
        dead
    }
}

impl<const MODULUS: u64> FieldElement<MODULUS> where Self: const Add<Self, Output = Self> + const AddAssign + const Sub<Self, Output = Self> + const SubAssign + const Mul<Self, Output = Self> + const MulAssign + const Neg<Output = Self> {
    #[requires(self.is_valid())]
    #[ensures(result.is_valid())]
    #[ensures(result.get_logical_value() == (self.get_logical_value() * self.get_logical_value()) % MODULUS@)]
    #[ensures(result == self * self)] // 'Mul' 트레이트의 로직을 따름
    #[ensures(result == self.square_logical())]
    pub const fn square(self) -> Self {
        // 'mul' 구현과 동일한 로직 사용
        let prod = (self.0 as u128) * (self.0 as u128);
        let result = (prod % MODULUS as u128) as u64;
        
        proof_assert!(result < MODULUS);
        FieldElement::<MODULUS>(result)
    }

    #[logic(opaque)]
    pub const fn square_logical(self) -> Self {
        dead
    }
    
    /// 모듈러 거듭제곱 (Square-and-Multiply)
    /// base^exp % MODULUS
    #[requires(self.is_valid())]
    #[ensures(result.is_valid())]
    // Creusot가 이 함수의 수학적 정확성을 증명하는 것은 매우 어렵습니다.
    // (logic 함수로 재귀적인 pow 정의가 필요함)
    // 여기서는 구현과 타입/유효성 불변 조건에 집중합니다.
    pub const fn pow(self, exp: u64) -> Self {
        let mut result = Self::one();
        let mut b = self;
        let mut e = exp;

        const NUM_BITS: usize = 64;

        let mut i = 0usize;

        #[variant(NUM_BITS - i)]
        while i < NUM_BITS {
            // 1. 현재 비트(e의 최하위 비트) 확인
            let cond: u64 = e & 1; // 0 또는 1

            // 2. 'if (cond == 1) { result = result * b }'
            
            let new_result = result * b;
            result = Self::cmov(result, new_result, cond);
            
            // 3. 다음 루프 준비
            b = b.square();
            e >>= 1;

            i += 1;
        }
        
        result
    }

    /// 모듈러 역원 (Inverse)
    #[requires(self.is_valid())]
    #[ensures(
        match result {
            Some(inv) => {
                // 역원이 존재하면, inv는 유효하고 self * inv = 1 이어야 함
                inv.is_valid() && 
                (self * inv).get_logical_value() == 1 &&
                spec_gcd(self.get_logical_value(), MODULUS@) == 1 &&
                spec_gcd(inv.get_logical_value(), MODULUS@) == 1
            },
            None => {
                spec_gcd(self.get_logical_value(), MODULUS@) != 1
            }
        }
    )]
    #[ensures(spec_gcd(self.get_logical_value(), MODULUS@) == 1 ==> result != None)]
    #[ensures(spec_gcd(self.get_logical_value(), MODULUS@) != 1 ==> result == None)]
    pub const fn inv(self) -> Option<Self> {
        let a = self.0;
        let m = MODULUS; // const u64

        // (gcd, s, t)를 계산. s*a + t*m = gcd
        let (gcd, s, _t) = extended_gcd(a, m);

        if gcd != 1 {
            // 역원이 존재하지 않음 (gcd(a, m) != 1)
            None
        } else {
            // 역원이 존재함 (s*a + t*m = 1)
            // (s*a) % m = 1
            // 's'가 우리가 찾는 역원. 단, 음수일 수 있음.

            // s를 i128로 변환하여 모듈러 연산 수행
            let m_i128 = m as i128;
            let mut inv_val_i128 = s % m_i128;

            // s가 음수인 경우 m을 더해 [0, m-1] 범위로 이동
            if inv_val_i128 < 0 {
                inv_val_i128 += m_i128;
            }

            let inv_val = inv_val_i128 as u64;

            // Creusot에게 이 값이 유효함을 단언
            proof_assert!(inv_val < MODULUS);
            
            Some(FieldElement(inv_val))
        }
    }
    
    
    pub const fn sqrt(self) -> (bool, Self) { // (is_square, sqrt)
        let root = self.pow((MODULUS_GOLDILOCKS + 1u64) >> 2u64);
        let check = root.square();
        
        // 제곱근이 맞는지 확인
        let is_square = check == self;
        // cmov를 사용한 상수 시간 반환
        let cond = is_square as u64;
        
        (is_square, Self::cmov(Self::zero(), root, cond))
    }
}

impl<const MODULUS: u64> const Add for FieldElement<MODULUS> where Self: AddLogic<Output = Self> {
    type Output = Self;

    #[requires(self.is_valid() && rhs.is_valid())] // 사전조건: 입력이 유효함
    #[ensures(result.is_valid())] // 사후조건: 출력이 유효함
    #[ensures(result.get_logical_value() == (self.get_logical_value() + rhs.get_logical_value()) % MODULUS@)]
    #[ensures(result == self + rhs)]
    fn add(self, rhs: Self) -> Self::Output {
        let result = ((self.0 as u128) + (rhs.0 as u128)).rem(MODULUS as u128) as u64;
        // Creusot가 post-condition을 증명할 수 있도록 보장
        proof_assert!(result < MODULUS); 
        FieldElement::<MODULUS>(result)
    }
}

impl<const MODULUS: u64> const Sub for FieldElement<MODULUS> where Self: SubLogic<Output = Self> {
    type Output = Self;

    #[requires(self.is_valid() && rhs.is_valid())] // 사전조건: 입력이 유효함
    #[ensures(result.is_valid())] // 사후조건: 출력이 유효함
    #[ensures(result.get_logical_value() == (self.get_logical_value() - rhs.get_logical_value()) % MODULUS@)]
    #[ensures(result == self - rhs)]
    fn sub(self, rhs: Self) -> Self::Output {
        let result = if self.0 < rhs.0 {
            (((self.0 as u128) + (MODULUS - rhs.0) as u128) % (MODULUS as u128)) as u64
        } else {
            self.0 - rhs.0
        };
        proof_assert!(result < MODULUS); 
        FieldElement::<MODULUS>(result)
    }
}

impl<const MODULUS: u64> const Mul for FieldElement<MODULUS> where Self: MulLogic<Output = Self> {
    type Output = Self;
    
    // 곱셈 구현 (Montgomery 곱셈 등을 사용해야 효율적)
    #[requires(self.is_valid() && rhs.is_valid())]
    #[ensures(result.is_valid())]
    #[ensures(result == self * rhs)]
    fn mul(self, rhs: Self) -> Self::Output {
        let prod = (self.0 as u128) * (rhs.0 as u128);
        let result = (prod % (MODULUS as u128)) as u64;
        proof_assert!(result < MODULUS);
        FieldElement::<MODULUS>(result)
    }
}

impl<const MODULUS: u64> const Neg for FieldElement<MODULUS> where Self: NegLogic<Output = Self> {
    type Output = Self;

    #[requires(self.is_valid())]
    #[ensures(result.is_valid())]
    #[ensures((result.get_logical_value() + self.get_logical_value() % MODULUS@) == 0)]
    #[ensures(result == -self)]
    fn neg(self) -> Self::Output {
        FieldElement::<MODULUS>(MODULUS - self.0)
    }
}

impl<const MODULUS: u64> const AddAssign for FieldElement<MODULUS> {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl<const MODULUS: u64> const SubAssign for FieldElement<MODULUS> {
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl<const MODULUS: u64> const MulAssign for FieldElement<MODULUS> {
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}
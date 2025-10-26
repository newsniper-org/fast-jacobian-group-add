use creusot_contracts::*;

use crate::{field::FieldElement, kummer::KummerPoint, surface::KummerOperations};

pub const GOLDILOCKS_MODULUS: u64 = 0xFFFFFFFF00000001;

/// "Goldilocks Prime" (2^64 - 2^32 + 1) 기반 Kummer Surface.
/// A = 4, B = 2 (K=1) 파라미터를 사용합니다.
pub struct GoldilocksSurface;

impl const KummerOperations<GOLDILOCKS_MODULUS> for GoldilocksSurface {
    const A: FieldElement<GOLDILOCKS_MODULUS> = FieldElement::new(4);
    const B: FieldElement<GOLDILOCKS_MODULUS> = FieldElement::new(2);
    const K_PARAM: FieldElement<GOLDILOCKS_MODULUS> = FieldElement::new(1);

    #[logic]
    fn k_param_is_correct() -> bool {
        // ... (A=4, B=2, K=1이 맞는지 검증하는 로직)
        let k = Self::K_PARAM.get_logical_value(); // 1
        let a = Self::A.get_logical_value();
        let b = Self::B.get_logical_value();     // 2
        let a2 = a * a;               // 16
        let four_b = b * 4;       // 8
        let rhs = a2 - four_b;    // 8
        let lhs = 8 * k;      // 8
        lhs == rhs
    }

    #[logic]
    #[requires(Self::k_param_is_correct())]
    fn is_on_surface(p: KummerPoint<GOLDILOCKS_MODULUS>) -> bool {
        // ... (이전에 구현한 복잡한 대수 방정식) ...
        true // 임시
    }

    #[requires(Self::is_on_surface(p))]
    #[ensures(Self::is_on_surface(result))]
    fn dbl(p: KummerPoint<GOLDILOCKS_MODULUS>) -> KummerPoint<GOLDILOCKS_MODULUS> {
        // --- 0. 상수 정의 ---
        // FieldElement에 'one()'이 구현되어 있다고 가정합니다.
        let one = FieldElement::<GOLDILOCKS_MODULUS>::one();
        let two = one + one;
        let four = two + two;
        let eight = four + four;

        // --- 1. 논문 공식 포팅 ---
        // t1 = X^2
        let t1 = p.x.square();
        // t2 = Z^2
        let t2 = p.z.square();
        // t3 = Y^2
        let t3 = p.y.square();

        // t4 = 2XZ
        // t4 = (X+Z)^2 - X^2 - Z^2
        let t4 = (p.x + p.z).square() - t1 - t2;

        // t5 = 2XY
        // t5 = (X+Y)^2 - X^2 - Y^2
        let t5 = (p.x + p.y).square() - t1 - t3;

        // t6 = (Z-T)^2
        let t6 = (p.z - p.t).square();
        // t7 = (Z+T)^2
        let t7 = (p.z + p.t).square();

        // t8 = 4ZT
        // t8 = (Z+T)^2 - (Z-T)^2
        let t8 = t7 - t6;

        // t9 = 8 * Y^2
        let t9 = t3 * eight;

        // t10 = k * (t7 + t6)
        // [최적화] k=1 이므로, t10 = t7 + t6
        let t10 = t7 + t6;

        // t11 = 2YZ
        // t11 = (Y+Z)^2 - Y^2 - Z^2
        let t11 = (p.y + p.z).square() - t3 - t2;

        // t12 = t10 + Y^2
        let t12 = t10 + t3;

        // --- 2. 새 좌표 계산 ---

        // Z2 = (X^2 - t12)^2 - t9 * t4
        let nz = (t1 - t12).square() - (t9 * t4);

        // T2 = (X^2 - t12)(t12 - Z^2) - X^2*t10 + Z^2*Y^2 - t9*(t5 - t11)
        let nt_1 = (t1 - t12) * (t12 - t2);
        let nt_2 = t1 * t10;
        let nt_3 = t2 * t3;
        let nt_4 = t9 * (t5 - t11);
        let nt = (nt_1 - nt_2) + nt_3 - nt_4;
        
        // X2 = (Z^2 - t12)^2 - k * t8^2
        // [최적화] k=1 이므로, X2 = (Z^2 - t12)^2 - t8^2
        let nx = (t2 - t12).square() - t8.square();

        // Y2 = (X^2*t10 - Z^2*Y^2)(X^2 - Z^2) + Z2 * (t5 + t11)
        let ny_1 = (t1 * t10) - (t2 * t3);
        let ny_2 = t1 - t2;
        let ny_3 = nz * (t5 + t11);
        let ny = (ny_1 * ny_2) + ny_3;

        // --- 3. Creusot 증명 보조 ---
        //
        // 'FieldElement'의 연산(+, *, square)이 'ensures(result.is_valid())'를
        // 보장하므로, nx, ny, nz, nt는 'is_valid()'가 보장됩니다.
        //
        // 'cargo creusot' 실행 시, SMT 솔버는 위의 20~30개 연산으로
        // 구성된 'nx, ny, nz, nt'가 'is_on_surface'의 대수 방정식을
        // 만족하는지 증명해야 합니다.
        //
        // 증명 실패 시, 이 지점에 'proof_assert!(...)'로 
        // 중간 단계의 보조 정리(lemma)들을 추가해야 합니다.
        //

        KummerPoint {
            x: nx,
            y: ny,
            z: nz,
            t: nt,
        }
    }

    #[requires(Self::is_on_surface(p))]
    #[requires(Self::is_on_surface(q))]
    #[requires(Self::is_on_surface(p_minus_q))]
    #[ensures(Self::is_on_surface(result))]
    fn diff_add(
        p: KummerPoint<GOLDILOCKS_MODULUS>,
        q: KummerPoint<GOLDILOCKS_MODULUS>,
        p_minus_q: KummerPoint<GOLDILOCKS_MODULUS>,
    ) -> KummerPoint<GOLDILOCKS_MODULUS> {
        // --- 0. 상수 정의 ---
        let two = FieldElement::<GOLDILOCKS_MODULUS>::one() + FieldElement::<GOLDILOCKS_MODULUS>::one();
        let four = two + two;

        // --- 1. 논문 공식 포팅 ---
        // (X_1, Y_1, Z_1, T_1) = p
        // (X_2, Y_2, Z_2, T_2) = q
        // (X_3, Y_3, Z_3, T_3) = p_minus_q (P-Q)
        
        let t1 = p.x * q.x;
        let t2 = p.y * q.y;
        let t3 = p.z * q.z;
        let t4 = p.t * q.t;
        
        // t5 = (X_1+Y_1)(X_2+Y_2) - t1 - t2 = X_1*Y_2 + Y_1*X_2
        let t5 = (p.x + p.y) * (q.x + q.y) - t1 - t2;
        
        // t6 = (X_1+Z_1)(X_2+Z_2) - t1 - t3 = X_1*Z_2 + Z_1*X_2
        let t6 = (p.x + p.z) * (q.x + q.z) - t1 - t3;
        
        // t7 = (Z_1+T_1)(Z_2+T_2) - t3 - t4 = Z_1*T_2 + T_1*Z_2
        let t7 = (p.z + p.t) * (q.z + q.t) - t3 - t4;

        // t8 = k * t7^2
        // [최적화] k=1 이므로, t8 = t7.square()
        let t8 = t7.square();

        // t9 = 2 * ( (A^2 - 4B)*t3*t4 + A*(t1*t7 - t2*t6) + B*(t5*t7 - t2*t4) + t1*t3 )
        // [최적화] A=4, B=2, (A^2-4B)=8
        // t9 = 2 * ( 8*t3*t4 + 4*(t1*t7 - t2*t6) + 2*(t5*t7 - t2*t4) + t1*t3 )
        let a_term = (t1 * t7) - (t2 * t6);
        let b_term = (t5 * t7) - (t2 * t4);
        let k_term = (two + two + four) * t3 * t4; // 8*t3*t4
        let t9_inner = k_term + (four * a_term) + (two * b_term) + (t1 * t3);
        let t9 = two * t9_inner;

        // t10 = t1 + t2
        let t10 = t1 + t2;
        // t11 = t1 - t2
        let t11 = t1 - t2;

        // --- 2. 새 좌표 계산 (P+Q) ---
        // X_4 = (t10^2 - t9 - t8) * Z_3
        let nx = (t10.square() - t9 - t8) * p_minus_q.z;

        // Y_4 = (t11^2 - t9 + t8) * Y_3
        let ny = (t11.square() - t9 + t8) * p_minus_q.y;

        // Z_4 = (t10^2 - t11^2 + 4*t8) * X_3
        let nz = (t10.square() - t11.square() + (four * t8)) * p_minus_q.x;

        // T_4 = (t11^2 - t10^2 + 4*t9) * T_3
        let nt = (t11.square() - t10.square() + (four * t9)) * p_minus_q.t;

        // --- 3. Creusot 증명 보조 ---
        // 'dbl'과 마찬가지로, SMT 솔버가 'is_on_surface' 증명에
        // 실패하면, 이 지점에 'proof_assert!(...)'로 
        // 중간 보조 정리(lemma)들을 추가해야 합니다.
        //

        KummerPoint {
            x: nx,
            y: ny,
            z: nz,
            t: nt,
        }
    }
}

use creusot_contracts::macros::{ensures, logic, proof_assert, requires};
use creusot_contracts::logic::Int;

use crate::{field::FieldElement, kummer::KummerPoint, mumford::MumfordDivisor, polynomial::Poly, surface::{KummerOperations, KummerUtility}};

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
        let a2 = Self::A.square_logical();               // 16
        let four_b = Self::B * FieldElement::new_logical(4u64);       // 8
        let rhs = a2 - four_b;    // 8
        let lhs = FieldElement::new_logical(8u64) * Self::K_PARAM;      // 8
        lhs == rhs
    }

    #[logic]
    #[requires(Self::k_param_is_correct())]
    fn is_on_surface(p: KummerPoint<GOLDILOCKS_MODULUS>) -> bool {
        // 불변 방정식 (Stange, 2011):
        // k(Z^2 - T^2)^2 + (Y^2 - X^2)(Y^2 + X^2 - 2AZT) + 4BZT(X^2 - ZT) == 0 (mod M)

        // --- 항 1: k * (Z^2 - T^2)^2 ---
        let z2 = p.z.square_logical();
        let t2 = p.t.square_logical();
        let z2_sub_t2 = z2 - t2;
        let term1 = Self::K_PARAM * (z2_sub_t2.square_logical());

        // --- 항 2: (Y^2 - X^2) * (Y^2 + X^2 - 2*A*Z*T) ---
        let x2 = p.x.square_logical();
        let y2 = p.y.square_logical();
        let y2_sub_x2 = y2 - x2;
        let zt = p.z * p.t;
        let azt = Self::A * zt;
        let two_azt = FieldElement::new_logical(2u64) * azt;
        let y2_add_x2 = y2 + x2;
        let inner_term2 = y2_add_x2 - two_azt;
        let term2 = y2_sub_x2 * inner_term2;

        // --- 항 3: 4 * B * Z * T * (X^2 - Z*T) ---
        let bzt = Self::B * zt;
        let four_bzt = FieldElement::new_logical(4u64) * bzt;
        let x2_sub_zt = x2 - zt;
        let term3 = four_bzt * x2_sub_zt;

        // --- 최종 합계 ---
        let sum123 = term1 + term2 + term3;
        sum123.get_logical_value() == 0
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
    
    #[requires(Self::is_on_surface(p))]
    #[requires(Self::is_on_surface(q))]
    #[ensures(Self::is_on_surface(result))]
    fn general_add(p:KummerPoint<GOLDILOCKS_MODULUS> ,q:KummerPoint<GOLDILOCKS_MODULUS>) -> KummerPoint<GOLDILOCKS_MODULUS>  {
        // 1. 점 복원 (Kummer -> Mumford)
        let mumford_p = Self::kummer_to_mumford(p);
        let mumford_q = Self::kummer_to_mumford(q);

        // 2. Cantor 덧셈 (Mumford + Mumford)
        // (내부적으로 polynomial::poly_xgcd, poly_div_rem 등 호출)
        let mumford_result = Self::mumford_add(mumford_p, mumford_q);

        // 3. 다시 변환 (Mumford -> Kummer)
        let kummer_result = Self::mumford_to_kummer(mumford_result);

        // 4. Creusot 증명 보조
        // 이 3단계가 'is_on_surface'를 보존함을 증명해야 함
        proof_assert!(Self::is_on_surface(kummer_result));

        kummer_result
    }
}

impl KummerUtility<GOLDILOCKS_MODULUS> for GoldilocksSurface {
    #[requires(forall<i: Int> i >= 0 && i < ps@.len() ==> Self::is_on_surface(ps[i]))]
    #[ensures(Self::is_on_surface(result))]
    fn general_sum(ps: &[KummerPoint<GOLDILOCKS_MODULUS>]) -> KummerPoint<GOLDILOCKS_MODULUS>  {
        // 1. 점 복원 (Kummer -> Mumford) 및 2. Cantor 덧셈 (Mumford + Mumford)
        // (내부적으로 polynomial::poly_xgcd, poly_div_rem 등 호출)
        
        let mumford_result = ps.iter().map(|p| Self::kummer_to_mumford(*p)).reduce(|mumford_sum, p| Self::mumford_add(mumford_sum, p)).unwrap_or(MumfordDivisor::zero());

        // 3. 다시 변환 (Mumford -> Kummer)
        let kummer_result = Self::mumford_to_kummer(mumford_result);

        // 4. Creusot 증명 보조
        // 이 3단계가 'is_on_surface'를 보존함을 증명해야 함
        proof_assert!(Self::is_on_surface(kummer_result));

        kummer_result
    }
}

/// GoldilocksSurface에만 해당하는 헬퍼 함수들
impl GoldilocksSurface {

    /// 1. Kummer 좌표 -> Mumford 표현 (Point Recovery)
    /// (X,Y,Z,T) -> (u1, u0, v1, v0)
    /// !!! 주의: 이 공식은 매우 복잡하며, A=4, B=2 및 (X:Y:Z:T) 좌표계에
    /// !!! 특화되어 유도되어야 합니다.
     // inv() 등 복잡한 연산
    pub(crate) const fn kummer_to_mumford(p: KummerPoint<GOLDILOCKS_MODULUS>) -> MumfordDivisor<GOLDILOCKS_MODULUS> {
        // --- Constants ---
        let two = FieldElement::one() + FieldElement::one();
        let four = two + two;
        let zero_divisor = MumfordDivisor::zero(); // Assuming MumfordDivisor::zero() exists

        // --- 1단계: (k₁, k₂, k₃)로부터 (u1, u0) 복원 ---
        
        if let Some(z_inv) = p.z.inv() { // inv() call #1
            let (u1, u0) = (-(p.x * z_inv), p.y * z_inv);
                // --- 2. Calculate Intermediate A, B, C ---
            // A = -u₁⁴ + u₁²(u₀+4) + (u₀² - 4u₀ + 2)
            let u1_sq = u1.square(); // Use the corrected 'square' name
            let u1_pow4 = u1_sq.square();
            let u0_sq = u0.square();
            let term_a1 = -u1_pow4;
            let term_a2 = u1_sq * (u0 + four);
            let term_a3 = u0_sq - (four * u0) + two;
            let val_a = term_a1 + term_a2 + term_a3;

            // B = 2Au₁ - 4u₁u₀(u₁² - 2u₀ + 4)
            let r0_term = u1 * u0 * (u1_sq - (two * u0) + four); // r₀ part
            let term_b1 = two * val_a * u1;
            let term_b2 = four * r0_term;
            let val_b = term_b1 - term_b2;

            // C = 2(u₁² - 4u₀)
            let denominator_v1_sq = u1_sq - (four * u0);
            let val_c = two * denominator_v1_sq;

            // --- 3. Calculate v₁² ---
            // v₁² = [-B ± sqrt(B² - C²A²)] / C

            // Check for C = 0 before inversion
            if let Some(c_inv) = val_c.inv() { // inv() call #2
                let b_sq = val_b.square();
                let c_sq = val_c.square();
                let discriminant_sq = b_sq - (c_sq * val_a.square()); // D = B² - C²A²

                // Calculate sqrt(D)
                let (is_disc_square, discriminant_sqrt) = discriminant_sq.sqrt(); // sqrt() call #1
                if !is_disc_square {
                    // Should not happen for points on the curve, but handle defensively
                    // Maybe return zero divisor or a specific error?
                    panic!("Should not happen for points on the curve") // Or handle error appropriately
                }

                // Choose the '+' sign deterministically for v₁² calculation
                // v₁² = (-B + sqrt(D)) * C⁻¹
                let v1_sq = (-val_b + discriminant_sqrt) * c_inv;
                // --- 4. Calculate v₁ ---
                let (is_v1_square, v1) = v1_sq.sqrt(); // sqrt() call #2
                if !is_v1_square {
                    // Should not happen for points on the curve
                    return zero_divisor; // Or handle error appropriately
                }

                // --- 5. Calculate v₀ ---
                // v₀ = (u₁v₁² + A) / (2v₁)

                let two_v1 = two * v1;
                let numerator_v0 = (u1 * v1_sq) + val_a;
                let (v1, v0) = if let Some(two_v1_inv) = two_v1.inv() { // inv() call #3
                    (v1 * FieldElement::one(), numerator_v0 * two_v1_inv)
                } else {
                    // 2v₁ = 0 => v₁ = 0.
                    // Check consistency: If v₁=0, then v₁²=0.
                    // The v₁² formula implies -B ± sqrt(B²) = 0.
                    // If B=0, then A=0 (since C!=0). Check if v₀=0 is consistent.
                    // v₀² - u₀v₁² = r₀ => v₀² = r₀.
                    // If v₁=0, then r₀ should be a square.
                    // For simplicity, assume v₁=0 implies v₀=0 (covers identity).
                    (v1 * FieldElement::zero(), numerator_v0 * FieldElement::zero())
                };


                MumfordDivisor { u1, u0, v1, v0 }
            } else {
                // C = 0 implies u₁² = 4u₀. This is a special case (potentially 2-torsion).
                // For simplicity, returning zero divisor. Precise handling might differ.
                if !p.x.is_nonzero() && !p.y.is_nonzero() && !p.z.is_nonzero() && p.t.is_nonzero() {
                    return zero_divisor;
                } else {
                    panic!("k1 (Z coordinate) is zero unexpectedly");
                }
            }
        } else {
            // Z=0 implies identity point
            return zero_divisor;
        }        
    }

    /// 2. Cantor 알고리즘 (Mumford 덧셈)
    
    pub(crate) const fn mumford_add(d1: MumfordDivisor<GOLDILOCKS_MODULUS>, d2: MumfordDivisor<GOLDILOCKS_MODULUS>) -> MumfordDivisor<GOLDILOCKS_MODULUS> {
        // A=4, B=2 이므로 f(x) = x^5 + 4x^3 + 2x
        let f_poly = Poly { c: [FieldElement::<GOLDILOCKS_MODULUS>::zero(), FieldElement::new(2), FieldElement::zero(), FieldElement::new(4), FieldElement::zero(), FieldElement::one()] };

        let u1 = d1.to_poly_u(); // MumfordDivisor -> Poly 변환 헬퍼 필요
        let u2 = d2.to_poly_u();
        let v1 = d1.to_poly_v();
        let v2 = d2.to_poly_v();

        // --- (1) 합성 (Composition) ---
        // (d1_gcd, s1, s2) = XGCD(u1, u2)
        let (d1_gcd, s1, s2) = Poly::poly_xgcd(u1, u2); 
        // (d, c1, c2) = XGCD(d1_gcd, v1 + v2)
        let (d, c1, c2) = Poly::poly_xgcd(d1_gcd, v1 + v2);

        let s1_prime = s1 * c1;
        let s2_prime = s2 * c1;
        let s3_prime = c2;
        
        // U_temp = (U1 * U2) / d^2
        let (u_temp, _urem) = (u1 * u2).poly_div_rem(d * d);

        // V_temp = (s1' U1 V2 + s2' U2 V1 + s3' (V1 V2 + f)) / d (mod U_temp)
        let v_term1 = s1_prime * u1 * v2;
        let v_term2 = s2_prime * u2 * v1;
        let v_term3 = s3_prime * ((v1 * v2) + f_poly);
        let (v_temp_unmod, _vrem) = (v_term1 + v_term2 + v_term3).poly_div_rem(d);
        let (_vquot, v_temp) = (v_temp_unmod).poly_div_rem(u_temp); // (mod U_temp)

        // --- (2) 축소 (Reduction) ---
        // U_new = (f - V_temp^2) / U_temp
        let (u_new, _urem) = (f_poly - (v_temp * v_temp)).poly_div_rem(u_temp);

        // V_new = -V_temp (mod U_new)
        let (_, v_new) = (-v_temp).poly_div_rem(u_new);

        // U_new, V_new 계수로부터 MumfordDivisor 생성
        MumfordDivisor::from_polys(u_new, v_new) // 헬퍼 필요
    }

    /// 3. Mumford 표현 -> Kummer 좌표
    /// (u1, u0, v1, v0) -> (X,Y,Z,T)
    /// [!!] !!! 대수 공식 구현 필요 !!! [!!]
    
    pub(crate) const fn mumford_to_kummer(d: MumfordDivisor<GOLDILOCKS_MODULUS>) -> KummerPoint<GOLDILOCKS_MODULUS> {
        let u1 = d.u1;
        let u0 = d.u0;
        let v1 = d.v1;
        let v0 = d.v0;

        // --- 상수 정의 ---
        let two = FieldElement::one() + FieldElement::one();
        let four = two + two;

        // --- k₄ 계산 ---
        // k₄ = [-u₁(2 + 4u₀ + u₀²) - (2v₁²u₀ - 2v₁v₀u₁ + 2v₀²)] / (u₁² - 4u₀)

        let u1_sq = u1.square();
        let u0_sq = u0.square();
        let v1_sq = v1.square();
        let v0_sq = v0.square();
        let v1v0 = v1 * v0;

        // 분자 계산
        let num_term1 = -u1 * (two + (four * u0) + u0_sq);
        let num_term2 = (two * v1_sq * u0) - (two * v1v0 * u1) + (two * v0_sq);
        let numerator_k4 = num_term1 - num_term2;

        // 분모 계산
        let denominator_k4 = u1_sq - (four * u0);

        // k₄ = Numerator / Denominator
        match denominator_k4.inv() {
            Some(denom_inv) => {
                let k4 = numerator_k4 * denom_inv;
                // --- 최종 좌표 (X:Y:Z:T) = (u₁ : u₀ : 1 : k₄) ---
                KummerPoint {
                    x: -u1,
                    y: u0,
                    z: FieldElement::one(), // Z=1로 정규화
                    t: k4,
                }
            },
            None => {
                KummerPoint::identity()
            }
        }

        
    }
}
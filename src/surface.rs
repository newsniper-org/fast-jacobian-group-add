use creusot_contracts::macros::{ensures, logic, proof_assert, requires, variant};
use crate::field::FieldElement;
use crate::kummer::KummerPoint;


/// 특정 Kummer 곡선 모델에 대한 모든 파라미터와 '논리'를 정의하는 트레이트.
/// 이 트레이트를 구현하는 것 자체가 "하나의 완성된 Kummer 곡선"을 정의합니다.
pub const trait KummerOperations<const MODULUS: u64> {

    /// 커브 파라미터 (예: A, B, K_PARAM)
    const A: FieldElement<MODULUS>;
    const B: FieldElement<MODULUS>;
    const K_PARAM: FieldElement<MODULUS>;
    const THETA_K_PARAMS: (FieldElement<MODULUS>, FieldElement<MODULUS>, FieldElement<MODULUS>, FieldElement<MODULUS>);
    const THETA_CONSTS_1: (FieldElement<MODULUS>, FieldElement<MODULUS>, FieldElement<MODULUS>);
    const THETA_CONSTS_2: (FieldElement<MODULUS>, FieldElement<MODULUS>, FieldElement<MODULUS>);
    const THETA_EQUATION_PARAMS: (FieldElement<MODULUS>, FieldElement<MODULUS>, FieldElement<MODULUS>, FieldElement<MODULUS>);

    /// [핵심 1] 이 커브 모델의 'is_on_surface' 논리
    #[logic]
    fn is_on_surface(p: KummerPoint<MODULUS>) -> bool;

    /// [핵심 2] 이 커브 모델의 'dbl' 구현 및 계약
    #[requires(Self::is_on_surface(p))]
    #[ensures(Self::is_on_surface(result))]
    fn dbl(p: KummerPoint<MODULUS>) -> KummerPoint<MODULUS>;

    /// [핵심 3] 이 커브 모델의 'diff_add' 구현 및 계약
    #[requires(Self::is_on_surface(p))]
    #[requires(Self::is_on_surface(q))]
    #[requires(Self::is_on_surface(p_minus_q))]
    #[ensures(Self::is_on_surface(result))]
    fn diff_add(
        p: KummerPoint<MODULUS>,
        q: KummerPoint<MODULUS>,
        p_minus_q: KummerPoint<MODULUS>,
    ) -> KummerPoint<MODULUS>;

    // (k_param_is_correct 헬퍼도 여기에 포함)
    #[logic]
    fn k_param_is_correct() -> bool;

    // --- [추가] ---
    /// Kummer 곡면의 일반 덧셈 (General Addition)
    /// (P, Q) -> P+Q
    ///
    /// 이 함수는 'diff_add'와 달리 P-Q를 요구하지 않지만,
    /// 내부적으로 필드 역원(inv)을 사용할 수 있습니다.
    #[requires(Self::is_on_surface(p))]
    #[requires(Self::is_on_surface(q))]
    #[ensures(Self::is_on_surface(result))]
    fn general_add(
        p: KummerPoint<MODULUS>,
        q: KummerPoint<MODULUS>,
    ) -> KummerPoint<MODULUS>;
}

/// 스칼라 곱은 이제 이 트레이트에 대해 제네릭하게 구현될 수 있습니다.
#[requires(P::is_on_surface(p))]
#[ensures(P::is_on_surface(result))]
pub const fn scalar_mul<const MODULUS: u64, P: const KummerOperations<MODULUS>>(
    p: KummerPoint<MODULUS>,
    k: u64, // 64비트 스칼라
) -> KummerPoint<MODULUS> {
    
    let num_bits: usize = 64; 

    // R0 = 0*P (항등원), R1 = 1*P
    // [!! 수정 !!] 몽고메리 래더는 (P, 2P)로 초기화해야 합니다.
    let mut r0 = p;
    let mut r1 = P::dbl(p);

    proof_assert!(P::is_on_surface(r1));

    // 비트를 상위 비트(MSB)부터 순회합니다 (최상위 비트(63)는 이미 처리됨).
    let mut i1: usize = num_bits - 1; // 63 -> (i = 62)

    #[variant(i1)]
    #[invariant(P::is_on_surface(r0))]
    #[invariant(P::is_on_surface(r1))]
    while i1 > 0 {
        let i = i1 - 1; // i = 62, 61, ... 0
        
        let k_i: u64 = (k >> i) & 1u64;

        // --- 상수 시간 몽고메리 래더 로직 ---
        // if k_i == 0:
        //   R1 = diff_add(R0, R1, P)
        //   R0 = dbl(R0)
        // if k_i == 1:
        //   R0 = diff_add(R0, R1, P)
        //   R1 = dbl(R1)

        let (r0_if_0, r1_if_0) = (P::dbl(r0), P::diff_add(r0, r1, p));
        let (r0_if_1, r1_if_1) = (P::diff_add(r0, r1, p), P::dbl(r1));
        
        proof_assert!(P::is_on_surface(r0_if_0));
        proof_assert!(P::is_on_surface(r1_if_0));
        proof_assert!(P::is_on_surface(r0_if_1));
        proof_assert!(P::is_on_surface(r1_if_1));

        r0 = KummerPoint::cmov(r0_if_0, r0_if_1, k_i);
        r1 = KummerPoint::cmov(r1_if_0, r1_if_1, k_i);
        // --- 로직 종료 ---

        i1 -= 1usize;
    }

    // 최종 결과
    r0
}
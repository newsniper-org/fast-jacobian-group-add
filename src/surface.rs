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
    k: u64,
) -> KummerPoint<MODULUS> {
    // 타이밍 공격을 방지하기 위해 스칼라 길이를 고정합니다.
    // 예시: 256비트.
    let num_bits: usize = 64; 

    // R0 = 0*P (항등원), R1 = 1*P
    let mut r0 = KummerPoint::identity();
    let mut r1 = p;

    // Creusot 증명을 위한 사전 단언
    // 'dbl'의 ensures 계약 덕분에 'r1'이 유효함을 증명할 수 있습니다.
    proof_assert!(P::is_on_surface(r1));

    // 비트를 하위 비트(LSB)부터 순회합니다.
    let mut i1: usize = num_bits;

    #[variant(i1)]
    #[invariant(P::is_on_surface(r0))]
    #[invariant(P::is_on_surface(r1))]
    while i1 > 0 {
        let i = i1-1;
        // k의 i번째 비트 추출 (k_i)
        let k_i: u64 = (k >> i) & 1u64;
        // --- 비-분기(Branchless) 로직 시작 ---
        (r0, r1) = (
            KummerPoint::cmov(r0, r1, k_i),
            KummerPoint::cmov(r1, r0, k_i)
        );
        
        (r0, r1) = (P::dbl(r0), P::general_add(r0, r1));

        (r0, r1) = (
            KummerPoint::cmov(r0, r1, k_i),
            KummerPoint::cmov(r1, r0, k_i)
        );
        // --- 비-분기 로직 종료 ---

        i1 -= 1usize;
    }

    // 최종 결과
    r0
}
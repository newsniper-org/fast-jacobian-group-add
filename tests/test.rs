#[cfg(test)]
mod tests {
    use fast_jacobian_group_add::{field::FieldElement, goldilocks::GOLDILOCKS_MODULUS, kummer::KummerPoint};
    use core::cmp::PartialEq;
    use core::fmt::{Debug, Display};
    use fast_jacobian_group_add::{goldilocks::*, mumford::*, polynomial::*, surface::*}; // GoldilocksSurface, KummerPoint 등을 가져옴

    // --- 테스트 벡터 정의 (SageMath 등에서 미리 계산) ---
    const BASE_POINT_P_X: u64 = 6820916806754936679;
    const BASE_POINT_P_Y: u64 = 16934191869074070341;
    const BASE_POINT_P_Z: u64 = 1;
    const BASE_POINT_P_T: u64 = 12944129927166111199;

    // POINT_2P = (x^2 + 9424878815846631976*x + 3688387053381944177, y + 9599089192781263723*x + 15883860524806195842)
    const POINT_2P_X: u64 = 9424878815846631976;
    const POINT_2P_Y: u64 = 3688387053381944177;
    const POINT_2P_Z: u64 = 1;
    const POINT_2P_T: u64 = 12816157016097971611;

    // POINT_3P = (x^2 + 3538015276753590834*x + 13651079901637174068, y + 16075639490092231120*x + 16813315020493913151)
    const POINT_3P_X: u64 = 3538015276753590834;
    const POINT_3P_Y: u64 = 13651079901637174068;
    const POINT_3P_Z: u64 = 1;
    const POINT_3P_T: u64 = 12093890501746799666;

    // ANOTHER_POINT_Q = (x^2 + 12836183021611606677*x + 10030985822928510596, y + 14717884592847128053*x + 10250024639220343379)
    const ANOTHER_POINT_Q_X: u64 = 12836183021611606677;
    const ANOTHER_POINT_Q_Y: u64 = 10030985822928510596;
    const ANOTHER_POINT_Q_Z: u64 = 1;
    const ANOTHER_POINT_Q_T: u64 = 13108932139397820747;

    // POINT_P_PLUS_Q = (x^2 + 8660418874568370510*x + 17156245274621427765, y + 10377324346690235887*x + 2775359005398004261)
    const POINT_P_PLUS_Q_X: u64 = 8660418874568370510;
    const POINT_P_PLUS_Q_Y: u64 = 17156245274621427765;
    const POINT_P_PLUS_Q_Z: u64 = 1;
    const POINT_P_PLUS_Q_T: u64 = 11625536497942078847;

    fn assert_partial_eq(a: KummerPoint<GOLDILOCKS_MODULUS>, b: KummerPoint<GOLDILOCKS_MODULUS>, msg: &'static str) {
        let (ax, ay, az, at) = (a.x.get_value(), a.y.get_value(), a.z.get_value(), a.t.get_value());
        let (bx, by, bz, bt) = (b.x.get_value(), b.y.get_value(), b.z.get_value(), b.t.get_value());
        println!("{0}, {1}, {2}, {3}", ax, ay, az, at);
        println!("{0}, {1}, {2}, {3}", bx, by, bz, bt);
        assert!(a.eq(&b), "{}", msg)
    }

    #[test]
    fn test_doubling() {
        let p = KummerPoint::<GOLDILOCKS_MODULUS>::new(
            FieldElement::new(BASE_POINT_P_X),
            FieldElement::new(BASE_POINT_P_Y),
            FieldElement::new(BASE_POINT_P_Z),
            FieldElement::new(BASE_POINT_P_T)
        );
        let expected_2p = KummerPoint::<GOLDILOCKS_MODULUS>::new(
            FieldElement::new(POINT_2P_X),
            FieldElement::new(POINT_2P_Y),
            FieldElement::new(POINT_2P_Z),
            FieldElement::new(POINT_2P_T)
        );

        let result_2p = GoldilocksSurface::dbl(p);
        assert_partial_eq(result_2p, expected_2p, "Doubling failed");
    }

    #[test]
    fn test_scalar_mul_3() {
        let p = KummerPoint::<GOLDILOCKS_MODULUS>::new(
            FieldElement::new(BASE_POINT_P_X),
            FieldElement::new(BASE_POINT_P_Y),
            FieldElement::new(BASE_POINT_P_Z),
            FieldElement::new(BASE_POINT_P_T)
        );
        let scalar_3 = [3u64, 0, 0, 0]; // 스칼라 3
        let expected_3p = KummerPoint::<GOLDILOCKS_MODULUS>::new(
            FieldElement::new(POINT_3P_X),
            FieldElement::new(POINT_3P_Y),
            FieldElement::new(POINT_3P_Z),
            FieldElement::new(POINT_3P_T)
        );

        let result_3p = scalar_mul::<GOLDILOCKS_MODULUS, GoldilocksSurface>(p, scalar_3);
        assert_partial_eq(result_3p, expected_3p, "Scalar mult by 3 failed");
    }

    #[test]
    fn test_general_add() {
        let p = KummerPoint::<GOLDILOCKS_MODULUS>::new(
            FieldElement::new(BASE_POINT_P_X),
            FieldElement::new(BASE_POINT_P_Y),
            FieldElement::new(BASE_POINT_P_Z),
            FieldElement::new(BASE_POINT_P_T)
        );
        let q = KummerPoint::<GOLDILOCKS_MODULUS>::new(  
            FieldElement::new(ANOTHER_POINT_Q_X),
            FieldElement::new(ANOTHER_POINT_Q_Y),
            FieldElement::new(ANOTHER_POINT_Q_Z),
            FieldElement::new(ANOTHER_POINT_Q_T)
        );
        let expected_p_plus_q = KummerPoint::<GOLDILOCKS_MODULUS>::new(
            FieldElement::new(POINT_P_PLUS_Q_X),
            FieldElement::new(POINT_P_PLUS_Q_Y),
            FieldElement::new(POINT_P_PLUS_Q_Z),
            FieldElement::new(POINT_P_PLUS_Q_T)
        );

        let result_p_plus_q = GoldilocksSurface::general_add(p, q);
        assert_partial_eq(result_p_plus_q, expected_p_plus_q, "General add failed");
    }

    #[test]
    fn test_add_identity() {
        let p = KummerPoint::<GOLDILOCKS_MODULUS>::new(
            FieldElement::new(BASE_POINT_P_X),
            FieldElement::new(BASE_POINT_P_Y),
            FieldElement::new(BASE_POINT_P_Z),
            FieldElement::new(BASE_POINT_P_T)
        );
        let identity = KummerPoint::identity(); // 항등원 필요

        let result = GoldilocksSurface::general_add(p, identity);
        assert_partial_eq(result, p, "Adding identity failed");

        let result2 = GoldilocksSurface::general_add(identity, p);
        assert_partial_eq(result2, p, "Adding identity (reversed) failed");
    }

    #[test]
    fn test_general_sum() {
        let p = KummerPoint::<GOLDILOCKS_MODULUS>::new(
            FieldElement::new(BASE_POINT_P_X),
            FieldElement::new(BASE_POINT_P_Y),
            FieldElement::new(BASE_POINT_P_Z),
            FieldElement::new(BASE_POINT_P_T)
        );
        let q = KummerPoint::<GOLDILOCKS_MODULUS>::new(  
            FieldElement::new(ANOTHER_POINT_Q_X),
            FieldElement::new(ANOTHER_POINT_Q_Y),
            FieldElement::new(ANOTHER_POINT_Q_Z),
            FieldElement::new(ANOTHER_POINT_Q_T)
        );

        let identity = KummerPoint::identity();
        let expected_p_plus_q = KummerPoint::<GOLDILOCKS_MODULUS>::new(
            FieldElement::new(POINT_P_PLUS_Q_X),
            FieldElement::new(POINT_P_PLUS_Q_Y),
            FieldElement::new(POINT_P_PLUS_Q_Z),
            FieldElement::new(POINT_P_PLUS_Q_T)
        );

        let points: [KummerPoint<GOLDILOCKS_MODULUS>; 3] = [p, q, identity];
        let result = GoldilocksSurface::general_sum(&points);
        assert_partial_eq(result, expected_p_plus_q, "General sum failed");

        let empty: [KummerPoint<GOLDILOCKS_MODULUS>; 0] = [];
        let identity = KummerPoint::identity();
        let result_empty = GoldilocksSurface::general_sum(&empty);
        assert_partial_eq(result_empty, identity, "General sum empty failed");
    }

    // ... (더 많은 테스트 케이스: 항등원, 역원, 결합법칙 등) ...
}
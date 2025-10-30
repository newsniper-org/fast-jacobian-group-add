#[cfg(test)]
mod tests {
    use fast_jacobian_group_add::{field::FieldElement, goldilocks::GOLDILOCKS_MODULUS, kummer::KummerPoint};
    use core::cmp::PartialEq;
    use core::fmt::{Debug, Display};
    use fast_jacobian_group_add::{goldilocks::*, surface::*}; // GoldilocksSurface, KummerPoint 등을 가져옴

    // BASE_POINT_P
    const BASE_POINT_P_X: u64 = 1;
    const BASE_POINT_P_Y: u64 = 17655699729773291524;
    const BASE_POINT_P_Z: u64 = 3105884797251181523;
    const BASE_POINT_P_T: u64 = 8321607302872959222;

    // POINT_2P
    const POINT_2P_X: u64 = 1;
    const POINT_2P_Y: u64 = 4354898723038788164;
    const POINT_2P_Z: u64 = 8837534647543971886;
    const POINT_2P_T: u64 = 10285113801097008171;

    // POINT_3P
    const POINT_3P_X: u64 = 1;
    const POINT_3P_Y: u64 = 10446369131503795997;
    const POINT_3P_Z: u64 = 5798694246855010622;
    const POINT_3P_T: u64 = 14050208420225679127;

    // ANOTHER_POINT_Q
    const ANOTHER_POINT_Q_X: u64 = 1;
    const ANOTHER_POINT_Q_Y: u64 = 12877703657062033561;
    const ANOTHER_POINT_Q_Z: u64 = 13960962000897751102;
    const ANOTHER_POINT_Q_T: u64 = 14096556342107827567;

    // POINT_P_PLUS_Q
    const POINT_P_PLUS_Q_X: u64 = 1;
    const POINT_P_PLUS_Q_Y: u64 = 10497839759115338445;
    const POINT_P_PLUS_Q_Z: u64 = 6147851686400094856;
    const POINT_P_PLUS_Q_T: u64 = 7229985938968236087;

    fn assert_partial_eq(a: KummerPoint<GOLDILOCKS_MODULUS>, b: KummerPoint<GOLDILOCKS_MODULUS>, msg: &'static str) {
        let (ax, ay, az, at) = (a.x.get_value(), a.y.get_value(), a.z.get_value(), a.t.get_value());
        let (bx, by, bz, bt) = (b.x.get_value(), b.y.get_value(), b.z.get_value(), b.t.get_value());
        println!("{0}, {1}, {2}, {3}", ax, ay, az, at);
        println!("{0}, {1}, {2}, {3}", bx, by, bz, bt);
        assert_eq!(a, b, "{}", msg)
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
        let expected_3p = KummerPoint::<GOLDILOCKS_MODULUS>::new(
            FieldElement::new(POINT_3P_X),
            FieldElement::new(POINT_3P_Y),
            FieldElement::new(POINT_3P_Z),
            FieldElement::new(POINT_3P_T)
        );

        let result_3p = scalar_mul::<GOLDILOCKS_MODULUS, GoldilocksSurface>(p, 3u64);
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
    // ... (더 많은 테스트 케이스: 항등원, 역원, 결합법칙 등) ...
}
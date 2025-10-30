#[cfg(test)]
mod tests {
    use fast_jacobian_group_add::{field::FieldElement, goldilocks::GOLDILOCKS_MODULUS, kummer::KummerPoint};
    use core::cmp::PartialEq;
    use core::fmt::{Debug, Display};
    use fast_jacobian_group_add::{goldilocks::*, surface::*}; // GoldilocksSurface, KummerPoint 등을 가져옴

    // BASE_POINT_P
    const BASE_POINT_P_X: u64 = 15061606233535225857;
    const BASE_POINT_P_Y: u64 = 2;
    const BASE_POINT_P_Z: u64 = 1;
    const BASE_POINT_P_T: u64 = 1;

    // POINT_2P
    const POINT_2P_X: u64 = 12759147721386484342;
    const POINT_2P_Y: u64 = 8905241589159209973;
    const POINT_2P_Z: u64 = 9070999827115308119;
    const POINT_2P_T: u64 = 9070999827115308119;

    // POINT_3P
    const POINT_3P_X: u64 = 13023178679034336813;
    const POINT_3P_Y: u64 = 5045590530899231680;
    const POINT_3P_Z: u64 = 477343727921538676;
    const POINT_3P_T: u64 = 2029885930211745262;

    // ANOTHER_POINT_Q
    const ANOTHER_POINT_Q_X: u64 = 15061606233535225857;
    const ANOTHER_POINT_Q_Y: u64 = 18446744069414584319;
    const ANOTHER_POINT_Q_Z: u64 = 1;
    const ANOTHER_POINT_Q_T: u64 = 18446744069414584320;

    // POINT_P_PLUS_Q
    const POINT_P_PLUS_Q_X: u64 = 9396736740326916594;
    const POINT_P_PLUS_Q_Y: u64 = 6470432827125226680;
    const POINT_P_PLUS_Q_Z: u64 = 16719129957299124356;
    const POINT_P_PLUS_Q_T: u64 = 9208394708617477553;

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
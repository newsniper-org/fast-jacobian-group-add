#[cfg(test)]
mod tests {
    use fast_jacobian_group_add::{field::FieldElement, goldilocks::GOLDILOCKS_MODULUS, kummer::KummerPoint};
    use core::cmp::PartialEq;
    use core::fmt::{Debug, Display};
    use fast_jacobian_group_add::{goldilocks::*, surface::*}; // GoldilocksSurface, KummerPoint 등을 가져옴

    // BASE_POINT_P = (x^2 + 16296662328237314642*x + 1669186028084044152, y + 7354741800811361039*x + 9908548626410599850)
    const BASE_POINT_P_X: u64 = 1;
    const BASE_POINT_P_Y: u64 = 3246210666407607993;
    const BASE_POINT_P_Z: u64 = 17885152704720346837;
    const BASE_POINT_P_T: u64 = 7561246142563896202;

    // POINT_2P = (x^2 + 5917290213642972942*x + 10030970424884908572, y + 7489632683136440284*x + 3985803291446337698)
    const POINT_2P_X: u64 = 1;
    const POINT_2P_Y: u64 = 12529453855771611379;
    const POINT_2P_Z: u64 = 10030970424884908572;
    const POINT_2P_T: u64 = 16742554854428075038;

    // POINT_3P = (x^2 + 984268595755948907*x + 3482937140327605782, y + 17260152685397306747*x + 18015323631274404398)
    const POINT_3P_X: u64 = 1;
    const POINT_3P_Y: u64 = 17462475473658635414;
    const POINT_3P_Z: u64 = 3482937140327605782;
    const POINT_3P_T: u64 = 14955838288787281371;

    // ANOTHER_POINT_Q = (x^2 + 2823111159900637483*x + 17335148099271709408, y + 8620993421181944759*x + 6441236615082885796)
    const ANOTHER_POINT_Q_X: u64 = 1;
    const ANOTHER_POINT_Q_Y: u64 = 15623632909513946838;
    const ANOTHER_POINT_Q_Z: u64 = 17335148099271709408;
    const ANOTHER_POINT_Q_T: u64 = 7676648200682955180;

    // POINT_P_PLUS_Q = (x^2 + 8655264668135750963*x + 8155306463330896846, y + 837994865521173681*x + 11966803509546130334)
    const POINT_P_PLUS_Q_X: u64 = 1;
    const POINT_P_PLUS_Q_Y: u64 = 9791479401278833358;
    const POINT_P_PLUS_Q_Z: u64 = 8155306463330896846;
    const POINT_P_PLUS_Q_T: u64 = 9275657350861994433;

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
    // ... (더 많은 테스트 케이스: 항등원, 역원, 결합법칙 등) ...
}
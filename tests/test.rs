#[cfg(test)]
mod tests {
    use fast_jacobian_group_add::{field::FieldElement, goldilocks::GOLDILOCKS_MODULUS, kummer::KummerPoint};
    use core::cmp::PartialEq;
    use core::fmt::{Debug, Display};
    use fast_jacobian_group_add::{goldilocks::*, polynomial::*, surface::*}; // GoldilocksSurface, KummerPoint 등을 가져옴

    // BASE_POINT_P = (x^2 + 11719742734694654949*x + 15364097546034370461, y + 3347697517971866147*x + 13903726950451929177)
    const BASE_POINT_P_X: u64 = 6727001334719929372;
    const BASE_POINT_P_Y: u64 = 15364097546034370461;
    const BASE_POINT_P_Z: u64 = 1;
    const BASE_POINT_P_T: u64 = 9802393014542360963;

    // POINT_2P = (x^2 + 3629428243348774684*x + 11087696467674877453, y + 14728337736687573589*x + 14453060707568762350)
    const POINT_2P_X: u64 = 14817315826065809637;
    const POINT_2P_Y: u64 = 11087696467674877453;
    const POINT_2P_Z: u64 = 1;
    const POINT_2P_T: u64 = 10670996595934404070;

    // POINT_3P = (x^2 + 1174121461783811643*x + 3516562386892946873, y + 15525650249166986676*x + 6387396092266509827)
    const POINT_3P_X: u64 = 17272622607630772678;
    const POINT_3P_Y: u64 = 3516562386892946873;
    const POINT_3P_Z: u64 = 1;
    const POINT_3P_T: u64 = 12083424609178016410;

    // ANOTHER_POINT_Q = (x^2 + 17483148579795022044*x + 14912804666413772890, y + 12972243559817775564*x + 2033040238655317922)
    const ANOTHER_POINT_Q_X: u64 = 963595489619562277;
    const ANOTHER_POINT_Q_Y: u64 = 14912804666413772890;
    const ANOTHER_POINT_Q_Z: u64 = 1;
    const ANOTHER_POINT_Q_T: u64 = 11425551873959640634;

    // POINT_P_PLUS_Q = (x^2 + 17178486123787365234*x + 15039835369987476156, y + 7915246474159583466*x + 11240221835852160944)
    const POINT_P_PLUS_Q_X: u64 = 1268257945627219087;
    const POINT_P_PLUS_Q_Y: u64 = 15039835369987476156;
    const POINT_P_PLUS_Q_Z: u64 = 1;
    const POINT_P_PLUS_Q_T: u64 = 13949707981139874941;

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
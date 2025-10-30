
use creusot_contracts::macros::{ensures, logic,requires};

use crate::{field::FieldElement, kummer::KummerPoint, surface::{KummerOperations}};

pub const GOLDILOCKS_MODULUS: u64 = 0xFFFFFFFF00000001;

/// "Goldilocks Prime" (2^64 - 2^32 + 1) 기반 Kummer Surface.
/// A = 4, B = 2 (K=1) 파라미터를 사용합니다.
pub struct GoldilocksSurface;

impl GoldilocksSurface {
    #[requires(Self::is_on_surface(p))]
    #[requires(Self::is_on_surface(q))]
    #[ensures(Self::is_on_surface(result.0) && Self::is_on_surface(result.1))]
    pub const fn general_add_sum_pair(p:KummerPoint<GOLDILOCKS_MODULUS>, q:KummerPoint<GOLDILOCKS_MODULUS>) -> (KummerPoint<GOLDILOCKS_MODULUS>, KummerPoint<GOLDILOCKS_MODULUS>)  {

        if p.is_identity() {
            return (q, q);
        }
        if q.is_identity() {
            return (p, p);
        }
        
        // 좌표계 변환 (가정: X0=p.x, X1=p.y, X2=p.z, X3=p.t)
        let xs: [FieldElement<GOLDILOCKS_MODULUS>; 4] = [p.x, p.y, p.z, p.t];
        let ys: [FieldElement<GOLDILOCKS_MODULUS>; 4] = [q.x, q.y, q.z, q.t];

        // 1. 중간값 계산 (16M)
        let mut m: [[FieldElement<GOLDILOCKS_MODULUS>; 4]; 4] = [[FieldElement::zero(); 4]; 4];
        let (mut i, mut j): (usize, usize) = (0, 0);
        while i < 4 {
            while j < 4 {
                m[i][j] = xs[i]*ys[j];
                j += 1;
            }
            i += 1;
            j = 0;
        }

        // 2. 16개 선형 결합 (덧셈/뺄셈)
        let s = [
            m[0][0]+m[1][1]+m[2][2]+m[3][3],
            m[0][1]+m[1][0]+m[2][3]+m[3][2],
            m[0][2]+m[2][0]+m[1][3]+m[3][1],
            m[0][3]+m[3][0]+m[1][2]+m[2][1],
            m[0][1]-m[1][0]-m[2][3]+m[3][2],
            m[0][0]-m[1][1]-m[2][2]+m[3][3],
            m[0][3]-m[3][0]-m[1][2]+m[2][1],
            m[0][2]-m[2][0]-m[1][3]+m[3][1],
            m[0][2]-m[2][0]+m[1][3]-m[3][1],
            m[0][3]-m[3][0]+m[1][2]-m[2][1],
            m[0][0]-m[1][1]+m[2][2]-m[3][3],
            m[0][1]-m[1][0]+m[2][3]-m[3][2],
            m[0][3]-m[3][0]-m[1][2]-m[2][1],
            m[0][2]-m[2][0]-m[1][3]-m[3][1],
            m[0][1]-m[1][0]-m[2][3]-m[3][2],
            m[0][0]-m[1][1]-m[2][2]-m[3][3]
        ];

        // 3. 곡면 매개변수 사용 (THETA_K_PARAMS 로드)
        // let k1 = Self::K1; let k2 = Self::K2; /* ... */
        let (k1, k2, k3, k4) = (Self::THETA_K_PARAMS.0, Self::THETA_K_PARAMS.1, Self::THETA_K_PARAMS.2, Self::THETA_K_PARAMS.3);

        // s0 + k1*s2 + k2*s3; let s1 + k1*s3 + k2*s2; /* ... 6 more ... */ let s13 + k3*s15 + k4*s14;
        let u = [
            s[0] + k1*s[2] + k2*s[3],
            s[1] + k1*s[3] + k2*s[2],
            s[4] + k1*s[6] + k2*s[7],
            s[5] + k1*s[7] + k2*s[6],
            s[8] + k3*s[10]+ k4*s[11],
            s[9] + k3*s[11]+ k4*s[10],
            s[12]+ k3*s[14]+ k4*s[15],
            s[13]+ k3*s[15]+ k4*s[14]
        ];

        // 4. 최종 좌표 계산 (P+Q = Z0:Z1:Z2:Z3) (8M)
        let z0 = u[0]*u[3] - u[1]*u[2];
        let z1 = u[0]*u[2] - u[1]*u[3];
        let z2 = u[4]*u[7] - u[5]*u[6];
        let z3 = u[4]*u[6] - u[5]*u[7];

        let (w0, w1, w2, w3) = (
            u[0] * u[5] - u[1]*u[4],
            u[1] * u[5] - u[0]*u[4],
            u[2] * u[7] - u[3]*u[6],
            u[2] * u[6] - u[3]*u[7]
        );

        // 좌표계 변환하여 반환 (가정: Z0=nx, Z1=ny, Z2=nz, Z3=nt)
        (KummerPoint { x: z0, y: z1, z: z2, t: z3 }, KummerPoint { x: w0, y: w1, z: w2, t: w3 })
    }
}

impl const KummerOperations<GOLDILOCKS_MODULUS> for GoldilocksSurface {
    const A: FieldElement<GOLDILOCKS_MODULUS> = FieldElement::new(4);
    const B: FieldElement<GOLDILOCKS_MODULUS> = FieldElement::new(2);
    const THETA_K_PARAMS: (FieldElement<GOLDILOCKS_MODULUS>, FieldElement<GOLDILOCKS_MODULUS>, FieldElement<GOLDILOCKS_MODULUS>, FieldElement<GOLDILOCKS_MODULUS>) = (
        FieldElement::new(10649315194999332865u64), FieldElement::new(4u64), FieldElement::new(6u64), FieldElement::new(1u64)
    );
    const K_PARAM: FieldElement<GOLDILOCKS_MODULUS> = FieldElement::one();

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
        // [수정됨] Gaudry 2005-314.pdf, Section 3.1 (E,F,G,H 상수 필요)
        // (x⁴+y⁴+z⁴+t⁴) + 2Exyzt - F(x²t²+y²z²) - G(x²z²+y²t²) - H(x²y²+z²t²) = 0
        
        // --- E, F, G, H 상수 (a,b,c,d로부터 계산 필요) ---
        let (e, f, g, h) = Self::THETA_EQUATION_PARAMS; // 새로 정의 필요
        
        let x2 = p.x.square_logical(); let y2 = p.y.square_logical();
        let z2 = p.z.square_logical(); let t2 = p.t.square_logical();
        let x4 = x2.square_logical(); let y4 = y2.square_logical();
        let z4 = z2.square_logical(); let t4 = t2.square_logical();

        let term1 = x4 + y4 + z4 + t4;
        let term2 = FieldElement::new_logical(2u64) * e * p.x * p.y * p.z * p.t;
        let term3 = f * (x2*t2 + y2*z2);
        let term4 = g * (x2*z2 + y2*t2);
        let term5 = h * (x2*y2 + z2*t2);

        let result = term1 + term2 - term3 - term4 - term5;
        result.get_logical_value() == 0
    }

    #[requires(Self::is_on_surface(p))]
    #[ensures(Self::is_on_surface(result))]
    fn dbl(p: KummerPoint<GOLDILOCKS_MODULUS>) -> KummerPoint<GOLDILOCKS_MODULUS> {
        // 이 함수는 THETA_K_PARAMS가 아닌,
        // (y₀, z₀, t₀) 및 (y'₀, z'₀, t'₀) 상수가 필요합니다 [cite: 494-495].
        // 이 상수들은 A,B,C,D (세타 상수)로부터 계산됩니다.
        // A,B,C,D는 a,b,c,d (기본 세타 상수)로부터 계산됩니다 [cite: 461-464].
        // K_PARAMS(k₁, k₂, k₃, k₄)와는 다른 값일 수 있습니다.
        
        // --- Gaudry의 DoubleKummer 공식 구현 ---
        let (y0_p, z0_p, t0_p) = Self::THETA_CONSTS_1; // (y₀, z₀, t₀)
        let (y0_dp, z0_dp, t0_dp) = Self::THETA_CONSTS_2; // (y'₀, z'₀, t'₀)

        let x = p.x; let y = p.y; let z = p.z; let t = p.t;
        let x_sq = x.square(); let y_sq = y.square();
        let z_sq = z.square(); let t_sq = t.square();

        // 1. x' = (x² + y² + z² + t²)²
        let xp = (x_sq + y_sq + z_sq + t_sq).square();
        // 2. y' = y'₀ * (x² + y² - z² - t²)²
        let yp = y0_dp * (x_sq + y_sq - z_sq - t_sq).square();
        // 3. z' = z'₀ * (x² - y² + z² - t²)²
        let zp = z0_dp * (x_sq - y_sq + z_sq - t_sq).square();
        // 4. t' = t'₀ * (x² - y² - z² + t²)²
        let tp = t0_dp * (x_sq - y_sq - t_sq + t_sq).square();

        // 5. X = (x' + y' + z' + t')
        let nx = xp + yp + zp + tp;
        // 6. Y = y₀ * (x' + y' - z' - t')
        let ny = y0_p * (xp + yp - zp - tp);
        // 7. Z = z₀ * (x' - y' + z' - t')
        let nz = z0_p * (xp - yp + zp - tp);
        // 8. T = t₀ * (x' - y' - z' + t')
        let nt = t0_p * (xp - yp - zp + tp);
        
        KummerPoint { x: nx, y: ny, z: nz, t: nt }
    }

    #[requires(Self::is_on_surface(p))]
    #[requires(Self::is_on_surface(q))]
    #[requires(Self::is_on_surface(_p_minus_q))]
    #[ensures(Self::is_on_surface(result))]
    fn diff_add(
        p: KummerPoint<GOLDILOCKS_MODULUS>,
        q: KummerPoint<GOLDILOCKS_MODULUS>,
        _p_minus_q: KummerPoint<GOLDILOCKS_MODULUS>, // R
    ) -> KummerPoint<GOLDILOCKS_MODULUS> {        
        /*
        let (y0_dp, z0_dp, t0_dp) = Self::THETA_CONSTS_2; // (y'₀, z'₀, t'₀)

        let (xp, yp, zp, tp) = (
            (p.x.square() + p.y.square() + p.z.square() + p.t.square()) * (q.x.square() + q.y.square() + q.z.square() + q.t.square()),
            y0_dp * (p.x.square() + p.y.square() - p.z.square() - p.t.square()) * (q.x.square() + q.y.square() - q.z.square() - q.t.square()),
            z0_dp * (p.x.square() - p.y.square() + p.z.square() - p.t.square()) * (q.x.square() - q.y.square() + q.z.square() - q.t.square()),
            t0_dp * (p.x.square() - p.y.square() - p.z.square() + p.t.square()) * (q.x.square() - q.y.square() - q.z.square() + q.t.square())
        );

        let (xhi, yhi, zhi, thi) = (
            p_minus_q.x.inv().unwrap_or(FieldElement::zero()),
            p_minus_q.y.inv().unwrap_or(FieldElement::zero()),
            p_minus_q.z.inv().unwrap_or(FieldElement::zero()),
            p_minus_q.t.inv().unwrap_or(FieldElement::zero())
        );
        let (nx, ny, nz, nt) = (
            (xp + yp + zp + tp) * xhi,
            (xp + yp - zp - tp) * yhi,
            (xp - yp + zp - tp) * zhi,
            (xp - yp - zp + tp) * thi
        );
        KummerPoint { x: nx, y: ny, z: nz, t: nt }
         */

        if p.is_identity() {
            return q;
        }
        if q.is_identity() {
            return p;
        }
        
        // 좌표계 변환 (가정: X0=p.x, X1=p.y, X2=p.z, X3=p.t)
        let xs: [FieldElement<GOLDILOCKS_MODULUS>; 4] = [p.x, p.y, p.z, p.t];
        let ys: [FieldElement<GOLDILOCKS_MODULUS>; 4] = [q.x, q.y, q.z, q.t];

        // 1. 중간값 계산 (16M)
        let mut m: [[FieldElement<GOLDILOCKS_MODULUS>; 4]; 4] = [[FieldElement::zero(); 4]; 4];
        let (mut i, mut j): (usize, usize) = (0, 0);
        while i < 4 {
            while j < 4 {
                m[i][j] = xs[i]*ys[j];
                j += 1;
            }
            i += 1;
            j = 0;
        }

        // 2. 16개 선형 결합 (덧셈/뺄셈)
        let s = [
            m[0][0]+m[1][1]+m[2][2]+m[3][3],
            m[0][1]+m[1][0]+m[2][3]+m[3][2],
            m[0][2]+m[2][0]+m[1][3]+m[3][1],
            m[0][3]+m[3][0]+m[1][2]+m[2][1],
            m[0][1]-m[1][0]-m[2][3]+m[3][2],
            m[0][0]-m[1][1]-m[2][2]+m[3][3],
            m[0][3]-m[3][0]-m[1][2]+m[2][1],
            m[0][2]-m[2][0]-m[1][3]+m[3][1],
            m[0][2]-m[2][0]+m[1][3]-m[3][1],
            m[0][3]-m[3][0]+m[1][2]-m[2][1],
            m[0][0]-m[1][1]+m[2][2]-m[3][3],
            m[0][1]-m[1][0]+m[2][3]-m[3][2],
            m[0][3]-m[3][0]-m[1][2]-m[2][1],
            m[0][2]-m[2][0]-m[1][3]-m[3][1],
            m[0][1]-m[1][0]-m[2][3]-m[3][2],
            m[0][0]-m[1][1]-m[2][2]-m[3][3]
        ];

        // 3. 곡면 매개변수 사용 (THETA_K_PARAMS 로드)
        // let k1 = Self::K1; let k2 = Self::K2; /* ... */
        let (k1, k2, k3, k4) = (Self::THETA_K_PARAMS.0, Self::THETA_K_PARAMS.1, Self::THETA_K_PARAMS.2, Self::THETA_K_PARAMS.3);

        // s0 + k1*s2 + k2*s3; let s1 + k1*s3 + k2*s2; /* ... 6 more ... */ let s13 + k3*s15 + k4*s14;
        let u = [
            s[0] + k1*s[2] + k2*s[3],
            s[1] + k1*s[3] + k2*s[2],
            s[4] + k1*s[6] + k2*s[7],
            s[5] + k1*s[7] + k2*s[6],
            s[8] + k3*s[10]+ k4*s[11],
            s[9] + k3*s[11]+ k4*s[10],
            s[12]+ k3*s[14]+ k4*s[15],
            s[13]+ k3*s[15]+ k4*s[14]
        ];

        // 4. 최종 좌표 계산 (P+Q = Z0:Z1:Z2:Z3) (8M)
        let z0 = u[0]*u[3] - u[1]*u[2];
        let z1 = u[0]*u[2] - u[1]*u[3];
        let z2 = u[4]*u[7] - u[5]*u[6];
        let z3 = u[4]*u[6] - u[5]*u[7];

        // 좌표계 변환하여 반환 (가정: Z0=nx, Z1=ny, Z2=nz, Z3=nt)
        KummerPoint { x: z0, y: z1, z: z2, t: z3 }
    }
    
    #[requires(Self::is_on_surface(p))]
    #[requires(Self::is_on_surface(q))]
    #[ensures(Self::is_on_surface(result))]
    fn general_add(p:KummerPoint<GOLDILOCKS_MODULUS>, q:KummerPoint<GOLDILOCKS_MODULUS>) -> KummerPoint<GOLDILOCKS_MODULUS>  {

        if p.is_identity() {
            return q;
        }
        if q.is_identity() {
            return p;
        }
        
        // 좌표계 변환 (가정: X0=p.x, X1=p.y, X2=p.z, X3=p.t)
        let xs: [FieldElement<GOLDILOCKS_MODULUS>; 4] = [p.x, p.y, p.z, p.t];
        let ys: [FieldElement<GOLDILOCKS_MODULUS>; 4] = [q.x, q.y, q.z, q.t];

        // 1. 중간값 계산 (16M)
        let mut m: [[FieldElement<GOLDILOCKS_MODULUS>; 4]; 4] = [[FieldElement::zero(); 4]; 4];
        let (mut i, mut j): (usize, usize) = (0, 0);
        while i < 4 {
            while j < 4 {
                m[i][j] = xs[i]*ys[j];
                j += 1;
            }
            i += 1;
            j = 0;
        }

        // 2. 16개 선형 결합 (덧셈/뺄셈)
        let s = [
            m[0][0]+m[1][1]+m[2][2]+m[3][3],
            m[0][1]+m[1][0]+m[2][3]+m[3][2],
            m[0][2]+m[2][0]+m[1][3]+m[3][1],
            m[0][3]+m[3][0]+m[1][2]+m[2][1],
            m[0][1]-m[1][0]-m[2][3]+m[3][2],
            m[0][0]-m[1][1]-m[2][2]+m[3][3],
            m[0][3]-m[3][0]-m[1][2]+m[2][1],
            m[0][2]-m[2][0]-m[1][3]+m[3][1],
            m[0][2]-m[2][0]+m[1][3]-m[3][1],
            m[0][3]-m[3][0]+m[1][2]-m[2][1],
            m[0][0]-m[1][1]+m[2][2]-m[3][3],
            m[0][1]-m[1][0]+m[2][3]-m[3][2],
            m[0][3]-m[3][0]-m[1][2]-m[2][1],
            m[0][2]-m[2][0]-m[1][3]-m[3][1],
            m[0][1]-m[1][0]-m[2][3]-m[3][2],
            m[0][0]-m[1][1]-m[2][2]-m[3][3]
        ];

        // 3. 곡면 매개변수 사용 (THETA_K_PARAMS 로드)
        // let k1 = Self::K1; let k2 = Self::K2; /* ... */
        let (k1, k2, k3, k4) = (Self::THETA_K_PARAMS.0, Self::THETA_K_PARAMS.1, Self::THETA_K_PARAMS.2, Self::THETA_K_PARAMS.3);

        // s0 + k1*s2 + k2*s3; let s1 + k1*s3 + k2*s2; /* ... 6 more ... */ let s13 + k3*s15 + k4*s14;
        let u = [
            s[0] + k1*s[2] + k2*s[3],
            s[1] + k1*s[3] + k2*s[2],
            s[4] + k1*s[6] + k2*s[7],
            s[5] + k1*s[7] + k2*s[6],
            s[8] + k3*s[10]+ k4*s[11],
            s[9] + k3*s[11]+ k4*s[10],
            s[12]+ k3*s[14]+ k4*s[15],
            s[13]+ k3*s[15]+ k4*s[14]
        ];

        // 4. 최종 좌표 계산 (P+Q = Z0:Z1:Z2:Z3) (8M)
        let z0 = u[0]*u[3] - u[1]*u[2];
        let z1 = u[0]*u[2] - u[1]*u[3];
        let z2 = u[4]*u[7] - u[5]*u[6];
        let z3 = u[4]*u[6] - u[5]*u[7];

        // 좌표계 변환하여 반환 (가정: Z0=nx, Z1=ny, Z2=nz, Z3=nt)
        KummerPoint { x: z0, y: z1, z: z2, t: z3 }
    }
    
    const THETA_CONSTS_1: (FieldElement<GOLDILOCKS_MODULUS>, FieldElement<GOLDILOCKS_MODULUS>, FieldElement<GOLDILOCKS_MODULUS>) = (
        FieldElement::new(7530803116767612929), FieldElement::new(15061606233535225857), FieldElement::new(15061606233535225857)
    );
    
    const THETA_CONSTS_2: (FieldElement<GOLDILOCKS_MODULUS>, FieldElement<GOLDILOCKS_MODULUS>, FieldElement<GOLDILOCKS_MODULUS>) = (
        FieldElement::new(10503129152512301667), FieldElement::new(580306295299841562), FieldElement::new(580306295299841562)
    );
    
    const THETA_EQUATION_PARAMS: (FieldElement<GOLDILOCKS_MODULUS>, FieldElement<GOLDILOCKS_MODULUS>, FieldElement<GOLDILOCKS_MODULUS>, FieldElement<GOLDILOCKS_MODULUS>) = (
        FieldElement::one(), FieldElement::new(18446744069414584318), FieldElement::new(18446744069414584318), FieldElement::one()
    );
}
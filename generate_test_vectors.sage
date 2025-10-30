# --- 1. 기본 설정 ---
p = 0xFFFFFFFF00000001
Fp = GF(p)

# --- 2. Rust 상수와 동일한 상수 정의 ---

# GoldilocksSurface::THETA_CONSTS_1 (y₀, z₀, t₀)
# (a/b, a/c, a/d)
THETA_CONSTS_1 = (
    Fp(7530803116767612929), 
    Fp(15061606233535225857), 
    Fp(15061606233535225857)
)

# GoldilocksSurface::THETA_CONSTS_2 (y'₀, z'₀, t'₀)
# ((A/B)², (A/C)², (A/D)²)
THETA_CONSTS_2 = (
    Fp(10503129152512301667), 
    Fp(580306295299841562), 
    Fp(580306295299841562)
)

# GoldilocksSurface::THETA_K_PARAMS (k₁, k₂, k₃, k₄)
# (파라미터 구하기.pdf 기반)
THETA_K_PARAMS = (
    Fp(10649315194999332865), 
    Fp(4), 
    Fp(6), 
    Fp(1)
)

Fp.<x> = PolynomialRing(Fp)
f = x^5 + Fp(4)*x^3 + Fp(2)*x
C = HyperellipticCurve(f)
J = C.jacobian()
K = J.kummer_surface()

# Generation of a random point on a hyperelliptic curve C
def HEC_random_point():
    while True:
        x_r = f.base_ring().random_element()
        y2 = f(x_r)
        if y2.is_square():
            return [x_r, y2.sqrt()]

# Generation of n random unique points on a hyperelliptic curve C
def HEC_random_points_uniq():
    res = []
    for i in range(1,C.genus()+1):
        tries = 100
        found = False
        while tries > 0 and (not found):
            P = HEC_random_point()
            if not (P in res):
                res.append(P)
                found = True
            tries = tries - 1
    return res

def JC_random_element():
    points = HEC_random_points_uniq()
    u = 1
    for point in points:
        u = u * (x-point[0])
    v = f.parent().lagrange_polynomial(points)
    return J([u, v])




# --- 4. 헬퍼 함수 ---
def print_kummer_coords(label, P):
    """Helper to print Kummer coordinates for Rust tests."""
    (X, Y, Z, T) = P
    print(f"// {label}")
    print(f"const {label}_X: u64 = {int(X)};")
    print(f"const {label}_Y: u64 = {int(Y)};")
    print(f"const {label}_Z: u64 = {int(Z)};")
    print(f"const {label}_T: u64 = {int(T)};\n")

# --- 5. 테스트 벡터 생성 (실행) ---
P = JC_random_element()
Q = JC_random_element()

P2 = 2 * P
P3 = 3 * P
P_plus_Q = P+Q

eff = [0,2,0,4,0,1,0]

def mumford_to_kummer(MP):
    u = MP[0]
    v = MP[1]
    u0 = u[0]
    u1 = u[1]
    v0 = v[0]
    v1 = v[1]
    u1_sq = u1**2
    u0_4 = 4 * u0
    denom = u1_sq - u0_4

    u0_sq = u0**2
    u0_cub = u0 * u0_sq
    num_F0 = 2*eff[0] - eff[1]*u1 + 2*eff[2]*u0 - eff[3]*u0*u1 + 2*eff[4]*u0_sq - eff[5]*u0_sq*u1 + 2*eff[6]*u0_cub

    v1_sq = v1**2
    num_y1y2 = v1_sq*u0 - v1*v0*u1 + v0**2

    T_num = num_F0 - 2*num_y1y2

    return (1, -u1, u0, T_num / denom)

def print_kummer_coords(label, P):
    """Helper to print Kummer coordinates for Rust tests."""
    (X, Y, Z, T) = P
    print(f"// {label}")
    print(f"const {label}_X: u64 = {int(X)};")
    print(f"const {label}_Y: u64 = {int(Y)};")
    print(f"const {label}_Z: u64 = {int(Z)};")
    print(f"const {label}_T: u64 = {int(T)};\n")

KP = mumford_to_kummer(P)
K2P = mumford_to_kummer(P2)
K3P = mumford_to_kummer(P3)
KQ = mumford_to_kummer(Q)
K_P_plus_Q = mumford_to_kummer(P_plus_Q)
IDENTITY_POINT = mumford_to_kummer(J(0))

print("--- Generated Test Vectors ---")
print_kummer_coords("BASE_POINT_P", KP)
print_kummer_coords("POINT_2P", K2P)
print_kummer_coords("POINT_3P", K3P)
print_kummer_coords("ANOTHER_POINT_Q", KQ)
print_kummer_coords("POINT_P_PLUS_Q", K_P_plus_Q)
print_kummer_coords("IDENTITY_O", IDENTITY_POINT)
print_kummer_coords("IDENTITY_Ox2", mumford_to_kummer(J(0)+J(0)))

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

# 항등원 (Rust KummerPoint::identity()와 일치)
IDENTITY_POINT = (Fp(1), Fp(0), Fp(0), Fp(0))

# --- 3. Rust 함수를 SageMath로 동일하게 구현 ---

def rust_dbl(P):
    """ Rust의 dbl 함수를 SageMath로 구현 """
    (y0, z0, t0) = THETA_CONSTS_1
    (y0_p, z0_p, t0_p) = THETA_CONSTS_2
    
    (x, y, z, t) = P
    x_sq = x^2; y_sq = y^2; z_sq = z^2; t_sq = t^2
    
    xp = (x_sq + y_sq + z_sq + t_sq)^2
    yp = y0_p * (x_sq + y_sq - z_sq - t_sq)^2
    zp = z0_p * (x_sq - y_sq + z_sq - t_sq)^2
    tp = t0_p * (x_sq - y_sq - z_sq + t_sq)^2
    
    nx = xp + yp + zp + tp
    ny = y0 * (xp + yp - zp - tp)
    nz = z0 * (xp - yp + zp - tp)
    nt = t0 * (xp - yp - zp + tp)
    
    return (nx, ny, nz, nt)

def rust_general_add(P, Q):
    """ Rust의 general_add 함수를 SageMath로 구현 """
    # 항등원 덧셈 처리
    if P == IDENTITY_POINT: return Q
    if Q == IDENTITY_POINT: return P
    
    xs = [P[0], P[1], P[2], P[3]]
    ys = [Q[0], Q[1], Q[2], Q[3]]
    
    # 1. 16M
    m = [[Fp(0) for _ in range(4)] for _ in range(4)]
    for i in range(4):
        for j in range(4):
            m[i][j] = xs[i] * ys[j]
            
    # 2. 16S
    s = [
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
        m[0][3]-m[3][0]-m[1][2]-m[2][1], # s[12]
        m[0][2]-m[2][0]-m[1][3]-m[3][1], # s[13]
        m[0][1]-m[1][0]-m[2][3]-m[3][2], # s[14]
        m[0][0]-m[1][1]-m[2][2]-m[3][3]  # s[15]
    ]
    
    # 3. K_params
    (k1, k2, k3, k4) = THETA_K_PARAMS
    
    u = [
        s[0] + k1*s[2] + k2*s[3],
        s[1] + k1*s[3] + k2*s[2],
        s[4] + k1*s[6] + k2*s[7],
        s[5] + k1*s[7] + k2*s[6],
        s[8] + k3*s[10]+ k4*s[11],
        s[9] + k3*s[11]+ k4*s[10],
        s[12]+ k3*s[14]+ k4*s[15],
        s[13]+ k3*s[15]+ k4*s[14]
    ]
    
    # 4. Z coords
    z0 = u[0]*u[3] - u[1]*u[2]
    z1 = u[0]*u[2] - u[1]*u[3]
    z2 = u[4]*u[7] - u[5]*u[6]
    z3 = u[4]*u[6] - u[5]*u[7]
    
    return (z0, z1, z2, z3)

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
# [!!] 베이스 포인트를 생성하는 새로운 방법이 필요합니다.
# [!!] Mumford는 더 이상 사용하지 않습니다.
# [!!] Gaudry 논문은 (a:b:c:d)를 2-torsion 점이 아닌
# [!!] 항등원(neutral element)으로 사용합니다. 하지만 우리의 새 항등원은 (1:0:0:0)입니다.
# [!!] 테스트를 위해, Gaudry의 (a:b:c:d)를 베이스 포인트 P로 사용해 봅시다.

P = (
    Fp(15061606233535225857), # a
    Fp(2),                   # b
    Fp(1),                   # c
    Fp(1)                    # d
)
# Q는 임의의 다른 점 (예: (a, -b, c, -d))
Q = (
    Fp(15061606233535225857),
   -Fp(2),
    Fp(1),
   -Fp(1)
)

P2 = rust_dbl(P)
P3 = rust_general_add(P, P2) # 3P = P + 2P
P_plus_Q = rust_general_add(P, Q)

print("--- Generated Test Vectors ---")
print_kummer_coords("BASE_POINT_P", P)
print_kummer_coords("POINT_2P", P2)
print_kummer_coords("POINT_3P", P3)
print_kummer_coords("ANOTHER_POINT_Q", Q)
print_kummer_coords("POINT_P_PLUS_Q", P_plus_Q)
print_kummer_coords("IDENTITY_O", IDENTITY_POINT)
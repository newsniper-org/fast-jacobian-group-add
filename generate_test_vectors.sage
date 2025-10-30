# --- 1. 기본 설정 ---
p = 0xFFFFFFFF00000001
Fp = GF(p)
R.<x> = PolynomialRing(Fp)

# A=4, B=2
f_poly = x^5 + 4*x^3 + 2*x
C = HyperellipticCurve(f_poly)
J = C.jacobian()
O = J(0) # 항등원

# Generation of a random point on a hyperelliptic curve C
def HEC_random_point():
    f = C.hyperelliptic_polynomials()[0]
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

# Generation of a random element in Jacobian of a curve C
def JC_random_element():
    points = HEC_random_points_uniq()
    u = 1
    for point in points:
        u = u * (x-point[0])
    v = f_poly.parent().lagrange_polynomial(points)
    return J([u, v])

# --- 3. Mumford -> Theta 변환 (Gaudry 2005-314.pdf, Sec 4.3) ---
# 이 함수는 placeholder이며, 실제 구현은 Appendix 7.4의 12개 공식을 모두 구현해야 합니다.
def mumford_to_theta(D):
    if D == O:
        return (Fp(1), Fp(0), Fp(0), Fp(0))
    u = D[0]
    v = D[1]

    nx = 1
    ny = -u[1]
    nz = u[0]
    minus_F0 = (Fp(1) * (u[0]**2) + Fp(4) * u[0] + Fp(2)) * u[1]
    minus_nt = minus_F0 + (Fp(2) * (v[1]**2 * u[0] - v[1] * v[0] * u[1] + v[0]**2)) / (u[1]**2 - Fp(4) * u[0])

    return (nx, ny, nz, -minus_nt)

# --- 4. 헬퍼 함수 ---
def print_kummer_coords(label, D):
    coords = mumford_to_theta(D)
    if coords:
        X, Y, Z, T = coords
        print(f"// {label} = {D}")
        print(f"const {label}_X: u64 = {int(X)};")
        print(f"const {label}_Y: u64 = {int(Y)};")
        print(f"const {label}_Z: u64 = {int(Z)};")
        print(f"const {label}_T: u64 = {int(T)};\n")
    else:
        print(f"Could not convert {label} to Kummer coordinates.")

# --- 5. 테스트 벡터 생성 (실행) ---
# (P, Q 정의 - 이전과 동일)
P = JC_random_element()
Q = JC_random_element()

P2 = 2*P
P3 = 3*P
P_plus_Q = P + Q

print_kummer_coords("BASE_POINT_P", P)
print_kummer_coords("POINT_2P", P2)
print_kummer_coords("POINT_3P", P3)
print_kummer_coords("ANOTHER_POINT_Q", Q)
print_kummer_coords("POINT_P_PLUS_Q", P_plus_Q)
print_kummer_coords("IDENTITY_O", O)
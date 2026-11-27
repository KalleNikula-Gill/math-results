from math import factorial, isqrt

F = [0, 1]
for j in range(2, 42):
    F.append(F[-1] + F[-2])

def divisors(a):
    result = set()
    for b in range(1, isqrt(a) + 1):
        if a % b == 0:
            result.update((b, a // b))
    return result

orders_checked = 0
for m in range(4, 40):
    n = max(m, 11)
    u, v, w = F[m-2:m+1]
    orders = (divisors(u) | divisors(v) | divisors(w)) - {1}
    for e in orders:
        s = sum(F[j] % e != 0 for j in range(1, m-2))
        k = sum(2 * F[j] < e for j in range(2, m-2))
        assert (2 * F[n+1])**s * factorial(k) > 2*u*v*w*w * e**s
        orders_checked += 1

pairs_checked = 0
for m in range(4, 11):
    for n in range(m, 11):
        h = (F[m+n+2] - F[m+2] - F[n+2] + 1) // 2
        a = [1] + [0] * h
        for j in range(1, m+1):
            # The leading (1-q) cancels the j=1 denominator.
            if j > 1:
                for i in range(F[j], h+1):
                    a[i] += a[i-F[j]]
            for i in range(h, F[n+j]-1, -1):
                a[i] -= a[i-F[n+j]]
        assert min(a) >= 0
        pairs_checked += 1

assert (orders_checked, pairs_checked) == (1424, 28)

print(f"{orders_checked} divisor inequalities and {pairs_checked} coefficient cases passed.")

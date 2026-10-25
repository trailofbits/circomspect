function Operators(a,b,c) {
    var x = -a + ~b * !c ** 2 / 3 \ 2 % 5 << 1 >> 1 & a ^ b | c;
    x = a == b != c < 1 > 2 <= 3 >= 4 && a || b;
    x += a; x -= b; x *= c; x /= a; x \= b; x %= c;
    x **= a; x <<= b; x >>= c; x &= a; x |= b; x ^= c;
    a --> b; a ==> c; a++; b--;
    return a ? (b+c) : (a*c);
}

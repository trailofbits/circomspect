pragma circom 2.0.5;
pragma custom_templates;
bus B { signal value; }
template custom extern_c parallel T {
    input signal {tag} x;
    B input y;
    var (a,b) = (1,2);
    var plain = [1,2], potential = [(1),x,1?2:3], calls = [T()()];
    var nested = [[T()()]], hole = [_,1], named = T()(i<==x);
    var p = parallel T();
    log("λ", x);
}

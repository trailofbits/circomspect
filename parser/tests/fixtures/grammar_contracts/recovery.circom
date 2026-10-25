// multibyte λ before recovery
function F() {
    1+2;
    { Ordinary(); return MissingBlock(); }
    if (1) { (Sink()()); return MissingIf(); }
    for (var i=0;i<1;i++) { Ordinary(); }
    while (1) { Ordinary(); }
    Sink()();
    return Missing();
}
function Neighbor() { return 7; }

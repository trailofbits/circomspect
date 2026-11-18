pragma circom 2.2.3;
pragma custom_templates;
template custom Empty({
    signal input in; signal output out; out <-- in;
}
template Main(){
    signal output out; out <== 1;
}
component main = Main();

(declare-const x String)
(declare-const y String)
(assert (= x "p2Sma/q_G|>F%u?jb7KV!'\x0c'b|:>GHa<D<&|37Lj&@1T[},f'\x0b'eWB6RGrq@r?,f>$:gD,qLb.~JQ-V8rD]569mO.(ZTF>iVzkI2?qQB:4=-V}W$mX"))
(assert (str.in.re x (re.+ (str.to.re ""))))
(check-sat)
(get-model)

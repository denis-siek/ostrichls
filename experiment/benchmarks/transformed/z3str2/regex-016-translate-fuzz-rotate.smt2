(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (re.++ (str.to.re "_/^XQ") (str.to.re "13")))))
(assert (= 22 (str.to.int x)))
(assert (not (= x "`|/2c2fWf+'![q'0`wj^ho''\x0c''""c#\\%9<9^=")))
(assert (not (= x "HnFZ_j!\\SRQ6k""k8Jr`&k_^{'' ''xq*Ry3")))
(check-sat)
(get-model)

(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.++ (re.+ (str.to.re """C")) (str.to.re "#")))))
(assert (= (str.to.int x) 1))
(assert (not (= x "bq/Jh'\x0b'M")))
(assert (not (= x ",M[t+sK\\j.~")))
(check-sat)
(get-model)

(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (re.++ (str.to.re "|Nq21") (str.to.re "}7")))))
(assert (= 9 (str.to.int x)))
(check-sat)
(get-model)

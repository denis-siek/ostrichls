(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (str.to.re "DbU~>"))))
(assert (str.in.re x (re.* (str.to.re "bmo>e`:i>uRQu//2xXCnAY(j:qbh{:+"))))
(assert (str.in.re x (re.+ (str.to.re "ccatB3gmbaa{u_Ca"))))
(check-sat)
(get-model)

(declare-const x String)
(declare-const y String)
(assert (= x "mH/|ol3:^Qp8nVniN}aaav#bcgQ#''\r''"))
(assert (str.in.re x (re.* (re.+ (str.to.re "D")))))
(check-sat)
(get-model)

(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.++ (re.* (str.to.re "aa")) (str.to.re "bb")))))
(assert (= 6 (str.len x)))
(assert (not (= x "bbaaaa")))
(assert (not (= x "bbbbaa")))
(assert (not (= x "bbaabb")))
(check-sat)
(get-model)

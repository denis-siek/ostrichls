(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.++ (re.* (str.to.re "aa")) (str.to.re "bb")))))
(assert (= 4 (str.len x)))
(assert (not (= x "bbbb")))
(assert (not (= x "bbaa")))
(check-sat)
(get-model)

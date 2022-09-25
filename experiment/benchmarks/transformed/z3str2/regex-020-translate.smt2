(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.++ (re.* (str.to.re "-")) (str.to.re "G")))))
(assert (= (str.len x) 3))
(assert (not (= x "-GG")))
(assert (not (= x "G-G")))
(assert (not (= x "--G")))
(check-sat)
(get-model)

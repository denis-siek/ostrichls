(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (str.in.re x (re.++ (str.to.re "") (re.* (str.to.re "")))))
(assert (str.in.re x (re.union (str.to.re "N") (re.* (str.to.re "s")))))
(assert (str.in.re x (re.++ (str.to.re "s") (re.++ (re.* (str.to.re "")) (re.* (str.to.re "["))))))
(check-sat)
(get-model)

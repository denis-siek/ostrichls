(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (str.in.re x (re.++ (str.to.re ",") (re.* (str.to.re "L")))))
(assert (str.in.re x (re.++ (str.to.re ",") (re.++ (re.* (str.to.re "L")) (re.* (str.to.re "s"))))))
(assert (= 3 (str.len x)))
(check-sat)
(get-model)

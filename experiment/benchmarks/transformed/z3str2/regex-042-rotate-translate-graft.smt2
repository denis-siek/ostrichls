(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (str.in.re x (re.++ (str.to.re "''\t''") (re.* (str.to.re ";")))))
(assert (str.in.re x (re.++ (str.to.re ";") (re.++ (str.to.re "''\t''") (re.* (re.* (str.to.re "y")))))))
(assert (= (str.len x) 3))
(check-sat)
(get-model)

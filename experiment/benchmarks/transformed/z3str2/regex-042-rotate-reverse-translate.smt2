(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (str.in.re x (re.++ (re.* (str.to.re "'")) (str.to.re "'\r'"))))
(assert (str.in.re x (re.++ (re.++ (str.to.re "'") (str.to.re "'\r'")) (re.* (re.* (str.to.re "v"))))))
(assert (= 3 (str.len x)))
(check-sat)
(get-model)

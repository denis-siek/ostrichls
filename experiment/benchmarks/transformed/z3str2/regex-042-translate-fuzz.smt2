(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (str.in.re x (re.++ (str.to.re "") (re.* (str.to.re "''\n''")))))
(assert (str.in.re x (re.union (str.to.re "W") (re.++ (re.+ (str.to.re "''\n''")) (re.* (str.to.re "/"))))))
(assert (= 4 (str.len x)))
(check-sat)
(get-model)

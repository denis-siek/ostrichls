(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (str.in.re x (re.++ (str.to.re "__") (re.* (str.to.re "'''''\x0c''\x0c'''''")))))
(assert (str.in.re x (re.++ (str.to.re "bb") (re.* (str.to.re "bb")))))
(assert (str.in.re x (re.++ (re.* (str.to.re "bb")) (re.++ (re.* (str.to.re "'''''\x0c''\x0c'''''")) (str.to.re "__")))))
(check-sat)
(get-model)

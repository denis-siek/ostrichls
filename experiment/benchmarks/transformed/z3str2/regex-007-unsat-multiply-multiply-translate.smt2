(declare-const x String)
(assert (= (str.len x) 32))
(assert (str.in.re x (re.* (str.to.re "KKKK````****"))))
(assert (str.in.re x (re.* (str.to.re "((((zzzzKKKK****"))))
(check-sat)
(get-model)

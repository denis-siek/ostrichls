(declare-const x String)
(assert (= x "DDBB99@@llBBcc%%"))
(assert (str.in.re x (re.union (re.* (str.to.re ")),,1144AAGGUU")) (re.* (str.to.re "cc>>::``88")))))
(check-sat)
(get-model)

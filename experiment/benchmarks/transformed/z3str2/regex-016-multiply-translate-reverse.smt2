(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.union (str.to.re "yyFFBBNN") (str.to.re "332211")))))
(assert (= 22 (str.len x)))
(assert (not (= x "yyFFBBNN332211yyFFBBNN")))
(assert (not (= x "332211yyFFBBNNyyFFBBNN")))
(check-sat)
(get-model)

(declare-const x String)
(assert (= x "'''''\n''\n'''''``JJ__II'''''\n''\n'''''``'''''\n''\n'''''``JJ"))
(assert (str.in.re x (str.to.re "'''''\n''\n'''''``JJ")))
(check-sat)
(get-model)

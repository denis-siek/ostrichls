(declare-const x String)
(assert (= x "''''\n''''\n''''``JJ__II''''\n''''\n''''``''''\n''''\n''''``JJ"))
(assert (str.in.re x (re.* (re.union (str.to.re "__II''''\n''''\n''''``") (str.to.re "''''\n''''\n''''``JJ")))))
(check-sat)
(get-model)

(declare-const x String)
(declare-const y String)
(assert (= x "bb++''\t''''\t''bb++''\t''''\t''"))
(assert (str.in.re x (re.* (re.* (str.to.re "bb++''\t''''\t''")))))
(check-sat)
(get-model)

(declare-const x String)
(declare-const y String)
(assert (= x "a=|=1|pOwg!,a\\_Fkn,E*vag;'\n'g'\n'oMv"))
(assert (str.in.re x (re.* (str.to.re "\\|Fed"))))
(check-sat)
(get-model)

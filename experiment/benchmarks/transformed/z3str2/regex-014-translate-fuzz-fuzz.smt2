(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (str.to.re "f}0S[@'\r'2#JS!'"))))
(assert (str.in.re y (re.+ (str.to.re "1Z%-T1mlE\\8''\n'@+TQ-'\n'1u+'\t'sy"))))
(assert (= (str.len x) 0))
(assert (= (str.to.int y) 0))
(check-sat)
(get-model)

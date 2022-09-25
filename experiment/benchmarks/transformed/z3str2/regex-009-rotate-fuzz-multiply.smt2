(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (str.to.re "bb33\\\\ZZ33"))))
(assert (str.in.re x (re.* (str.to.re "aabbOO##[[ddbbccdd"))))
(assert (> (str.len x) 56))
(assert (< (str.to.int x) 14))
(check-sat)
(get-model)

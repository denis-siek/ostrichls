(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.* (str.to.re "iK<K<K")))))
(assert (str.in.re x (re.* (str.to.re "<K<K"))))
(assert (str.in.re x (str.to.re "<K")))
(assert (> 1 (str.len x)))
(check-sat)
(get-model)

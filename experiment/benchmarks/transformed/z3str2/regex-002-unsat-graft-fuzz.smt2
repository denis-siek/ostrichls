(declare-const x String)
(declare-const y String)
(assert (= x "9""?w""<^ok`]&{%bb1#'\n'aaaa"))
(assert (str.in.re x (str.to.re "c")))
(check-sat)
(get-model)

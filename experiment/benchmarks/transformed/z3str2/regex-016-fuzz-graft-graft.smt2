(declare-const x String)
(declare-const y String)
(assert (str.in.re x (str.to.re "i0O")))
(assert (= 8 (str.len x)))
(assert (not (= x "a#0BTv4VhW'icdB\\/a@I@3%fPnkdNw[d")))
(assert (not (= x "abbcdo:2")))
(check-sat)
(get-model)

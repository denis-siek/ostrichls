(declare-const x String)
(declare-const y String)
(assert (= x "\\=gSa0/a"))
(assert (str.in.re x (re.* (str.to.re "oG"))))
(check-sat)
(get-model)

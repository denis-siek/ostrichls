(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (not (str.in.re x (re.* (str.to.re "&i&Gg")))))
(assert (= x "&i&Gg"))
(check-sat)
(get-model)

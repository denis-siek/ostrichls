(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (str.in.re (str.++ x y) (re.* (str.to.re "NPA4V\\q'"))))
(check-sat)
(get-model)

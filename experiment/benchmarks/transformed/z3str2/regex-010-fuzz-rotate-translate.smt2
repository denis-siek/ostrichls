(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (str.to.re "E:"))))
(assert (str.in.re x (re.+ (str.to.re ":N"))))
(assert (str.in.re x (re.+ (str.to.re ":c\\yLyVf"))))
(check-sat)
(get-model)

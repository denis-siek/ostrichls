(declare-const x String)
(assert (= x "Y}IPITA<p,4'\n'+Aq5;LR~4L\\#&"))
(assert (str.in.re x (re.* (re.union (str.to.re "m-i@iY*rR+") (str.to.re "\\'\r'IaI-")))))
(check-sat)
(get-model)

(declare-const S String)
(assert (not (str.in.re S (re.union (str.to.re "$>Yh~") re.allchar))))
(assert (str.in.re S (re.++ (re.++ (re.union (str.to.re "%n'\x0c'x") re.allchar) (str.to.re "zm3~")) re.allchar)))
(check-sat)
(get-model)
(get-info :reason-unknown)

(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (str.to.re "?IJe"))))
(assert (str.in.re x (re.+ (str.to.re "Sq'%?xQ1'\n'#$'\x0b'|jv/6g"))))
(assert (str.in.re x (re.* (str.to.re "ER1(vAb9?w?%%|gk?;?|"))))
(check-sat)
(get-model)

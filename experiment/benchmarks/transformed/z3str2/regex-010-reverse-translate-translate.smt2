(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (str.to.re ";i"))))
(assert (str.in.re x (re.* (str.to.re ";i;i"))))
(assert (str.in.re x (re.* (str.to.re "vi;i;i"))))
(check-sat)
(get-model)

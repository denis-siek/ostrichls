(declare-const x String)
(declare-const y String)
(assert (= x "axs,}Lce>79D^S"))
(assert (str.in.re x (re.+ (str.to.re "a"))))
(check-sat)
(get-model)

(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.union (re.+ (str.to.re "CC")) (str.to.re "")))))
(assert (= (str.to.int x) 9))
(assert (not (= x "$)0Vf3|'\n'~ww")))
(assert (not (= x "wO3N@~")))
(assert (not (= x "??s{R'\t'$z' 'E&' 'PR::H\\{M7I&w")))
(check-sat)
(get-model)

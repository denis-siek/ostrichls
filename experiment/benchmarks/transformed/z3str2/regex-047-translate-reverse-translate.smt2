(declare-const key String)
(declare-const val String)
(define-fun QuoteRegex ((aRegex (RegEx String))) (RegEx String) (re.++ (str.to.re "H") (re.++ aRegex (str.to.re "H"))))
(assert (str.in.re key (QuoteRegex (re.* (str.to.re "?")))))
(assert (= (str.len key) 2))
(check-sat)
(get-model)

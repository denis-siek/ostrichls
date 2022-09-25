(declare-const key String)
(declare-const val String)
(define-fun QuoteRegex ((aRegex (RegEx String))) (RegEx String) (re.++ (str.to.re "y") (str.to.re "y")))
(assert (str.in.re key (QuoteRegex (re.* (str.to.re "B")))))
(assert (= 2 (str.len key)))
(check-sat)
(get-model)

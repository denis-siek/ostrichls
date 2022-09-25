(declare-const key String)
(declare-const val String)
(define-fun QuoteRegex ((aRegex (RegEx String))) (RegEx String) (re.++ (re.++ aRegex (str.to.re "B")) (str.to.re "B")))
(assert (str.in.re key (QuoteRegex (re.* (str.to.re "K")))))
(assert (= (str.len key) 2))
(check-sat)
(get-model)

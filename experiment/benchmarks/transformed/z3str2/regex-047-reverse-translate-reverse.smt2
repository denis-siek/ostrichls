(declare-const key String)
(declare-const val String)
(define-fun QuoteRegex ((aRegex (RegEx String))) (RegEx String) (re.++ (re.++ (str.to.re "w") aRegex) (str.to.re "w")))
(assert (str.in.re key (QuoteRegex (re.* (str.to.re "j")))))
(assert (= (str.len key) 2))
(check-sat)
(get-model)

(declare-const key String)
(declare-const val String)
(define-fun QuoteRegex ((aRegex (RegEx String))) (RegEx String) (str.to.re "H"))
(assert (str.in.re key (QuoteRegex (re.+ (re.++ (re.++ (str.to.re "M") aRegex) (str.to.re "F"))))))
(assert (= 2 (str.len key)))
(check-sat)
(get-model)
